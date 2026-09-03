/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.TraceNorm.Spectral

/-!
# Positive part and spectral projector API

Finite-dimensional positive-part support projectors for Hermitian complex
matrices.  This module exposes the trace-max bridge needed by the Audenaert
positive-operator trace inequality route:

* `positiveSpectralProjector H hH`: the spectral projector onto the strictly
  positive eigenspaces of a Hermitian matrix `H`;
* `positiveSpectralProjector_score_eq_posPart_trace`: that projector attains
  `Tr(H⁺)`;
* `hermitian_trace_mul_effect_le_posPart_trace`: every effect `0 ≤ E ≤ 1`
  has `Re Tr(H E) ≤ Re Tr(H⁺)`.

The source route uses the projector onto the range of the positive part and the
maximization of `Tr(QH)` over self-adjoint projectors
[Audenaert2006QuantumChernoff, audenaert-2006-quantum-chernoff.tex:324-331]
and [Audenaert2006QuantumChernoff,
audenaert-2006-quantum-chernoff.tex:345-350].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u

noncomputable section

/-- The spectral projector onto the strictly positive eigenspaces of a Hermitian matrix. -/
def positiveSpectralProjector {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) : CMatrix a :=
  (hH.eigenvectorUnitary : CMatrix a) *
    Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) *
      star (hH.eigenvectorUnitary : CMatrix a)

private def eigenbasisConjugate {a : Type u} [Fintype a] [DecidableEq a]
    {H : CMatrix a} (hH : H.IsHermitian) (E : CMatrix a) : CMatrix a :=
  star (hH.eigenvectorUnitary : CMatrix a) * E * (hH.eigenvectorUnitary : CMatrix a)

private theorem trace_diagonal_mul_eq_sum {a : Type u} [Fintype a] [DecidableEq a]
    (d : a → ℂ) (E : CMatrix a) :
    (Matrix.diagonal d * E).trace = ∑ i, d i * E i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

theorem real_posPart_eq_if (x : ℝ) : x⁺ = if 0 < x then x else 0 := by
  rw [_root_.posPart_def]
  split_ifs with hx
  · exact max_eq_left hx.le
  · exact max_eq_right (le_of_not_gt hx)

/-- The positive spectral projector is positive semidefinite. -/
theorem positiveSpectralProjector_posSemidef {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) :
    (positiveSpectralProjector H hH).PosSemidef := by
  classical
  unfold positiveSpectralProjector
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : 0 < hH.eigenvalues i
  · simp [hi]
  · simp [hi]

/-- The positive spectral projector is Hermitian. -/
theorem positiveSpectralProjector_isHermitian {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) :
    (positiveSpectralProjector H hH).IsHermitian :=
  (positiveSpectralProjector_posSemidef H hH).1

/-- The positive spectral projector is idempotent. -/
theorem positiveSpectralProjector_idempotent {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) :
    positiveSpectralProjector H hH * positiveSpectralProjector H hH =
      positiveSpectralProjector H hH := by
  classical
  unfold positiveSpectralProjector
  let U : CMatrix a := hH.eigenvectorUnitary
  let D : CMatrix a :=
    Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0)
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hH.eigenvectorUnitary]
  have hD : D * D = D := by
    change
      Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) =
        Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0)
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < hH.eigenvalues i <;> simp [hi]
    · simp [Matrix.diagonal, hij]
  calc
    (U * D * star U) * (U * D * star U) =
        U * D * (star U * U) * D * star U := by
          noncomm_ring
    _ = U * D * 1 * D * star U := by rw [hU]
    _ = U * (D * D) * star U := by noncomm_ring
    _ = U * D * star U := by rw [hD]

/-- The positive spectral projector is bounded by the identity effect. -/
theorem positiveSpectralProjector_le_one {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) :
    positiveSpectralProjector H hH ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  unfold positiveSpectralProjector
  have hOne :
      (1 : CMatrix a) =
        (hH.eigenvectorUnitary : CMatrix a) *
          (1 : CMatrix a) *
            star (hH.eigenvectorUnitary : CMatrix a) := by
    simp
  rw [hOne]
  have hsub :
      (hH.eigenvectorUnitary : CMatrix a) * 1 * star (hH.eigenvectorUnitary : CMatrix a) -
        (hH.eigenvectorUnitary : CMatrix a) *
          Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) *
            star (hH.eigenvectorUnitary : CMatrix a) =
        (hH.eigenvectorUnitary : CMatrix a) *
          (1 - Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0)) *
            star (hH.eigenvectorUnitary : CMatrix a) := by
    noncomm_ring
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  have hdiag :
      (1 - Matrix.diagonal (fun i => if 0 < hH.eigenvalues i then (1 : ℂ) else 0) :
        CMatrix a) =
        Matrix.diagonal (fun i => 1 - if 0 < hH.eigenvalues i then (1 : ℂ) else 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal, hij]
  rw [hdiag]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : 0 < hH.eigenvalues i
  · simp [hi]
  · simp [hi]

/-- The trace of the positive part is the sum of positive eigenvalues. -/
theorem posPart_trace_re_eq_positive_eigenvalue_sum {a : Type u}
    [Fintype a] [DecidableEq a] (H : CMatrix a) (hH : H.IsHermitian) :
    (H⁺).trace.re = ∑ i, if 0 < hH.eigenvalues i then hH.eigenvalues i else 0 := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  rw [hH.cfc_eq]
  rw [Matrix.IsHermitian.cfc]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  simp [Matrix.trace, real_posPart_eq_if]

/-- For a trace-zero Hermitian matrix, the trace norm is twice the trace of
the positive part. -/
theorem traceNorm_eq_two_posPart_trace_re_of_trace_zero {a : Type u}
    [Fintype a] [DecidableEq a] (H : CMatrix a) (hH : H.IsHermitian) (htr : H.trace = 0) :
    traceNorm H = 2 * (H⁺).trace.re := by
  have hAbs : H⁺ + H⁻ = CFC.abs H :=
    CFC.posPart_add_negPart H hH.isSelfAdjoint
  have hSub : H⁺ - H⁻ = H :=
    CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have htrace_sub : (H⁺).trace.re - (H⁻).trace.re = 0 := by
    have h := congrArg Complex.re (congrArg Matrix.trace hSub)
    rw [htr] at h
    simpa [Matrix.trace_sub] using h
  have htrace_abs : (CFC.abs H).trace.re = (H⁺).trace.re + (H⁻).trace.re := by
    have h := congrArg Complex.re (congrArg Matrix.trace hAbs)
    simpa [Matrix.trace_add] using h.symm
  rw [show traceNorm H = (CFC.abs H).trace.re by rfl, htrace_abs]
  linarith

/-- The positive part of a matrix is positive semidefinite. -/
theorem posPart_posSemidef {a : Type u} [Fintype a] [DecidableEq a] (H : CMatrix a) :
    H⁺.PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)

/-- The negative part of a matrix is positive semidefinite. -/
theorem negPart_posSemidef {a : Type u} [Fintype a] [DecidableEq a] (H : CMatrix a) :
    H⁻.PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)

/-- The trace of a positive semidefinite matrix is the complex coercion of its real part. -/
theorem posSemidef_trace_eq_re_coe {a : Type u} [Fintype a] [DecidableEq a]
    {M : CMatrix a} (hM : M.PosSemidef) :
    M.trace = (M.trace.re : ℂ) := by
  have him : M.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hM).2.symm
  exact Complex.ext rfl him

/-- The trace of the positive part is real-valued. -/
theorem posPart_trace_eq_re_coe {a : Type u} [Fintype a] [DecidableEq a] (H : CMatrix a) :
    (H⁺).trace = ((H⁺).trace.re : ℂ) :=
  posSemidef_trace_eq_re_coe (posPart_posSemidef H)

/-- The trace of the negative part is real-valued. -/
theorem negPart_trace_eq_re_coe {a : Type u} [Fintype a] [DecidableEq a] (H : CMatrix a) :
    (H⁻).trace = ((H⁻).trace.re : ℂ) :=
  posSemidef_trace_eq_re_coe (negPart_posSemidef H)

/-- For a trace-zero Hermitian matrix, the negative and positive parts have
the same trace mass. -/
theorem negPart_trace_re_eq_posPart_trace_re_of_trace_zero {a : Type u}
    [Fintype a] [DecidableEq a] (H : CMatrix a)
    (hH : H.IsHermitian) (htr : H.trace = 0) :
    (H⁻).trace.re = (H⁺).trace.re := by
  have hdecomp : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have htrace : (H⁺).trace - (H⁻).trace = 0 := by
    rw [← Matrix.trace_sub, hdecomp, htr]
  have hre := congrArg Complex.re htrace
  simp at hre
  linarith

private theorem hermitian_trace_mul_eq_sum_eigenbasis_diag {a : Type u}
    [Fintype a] [DecidableEq a] (H E : CMatrix a) (hH : H.IsHermitian) :
    ((H * E).trace).re =
      ∑ i, hH.eigenvalues i * ((eigenbasisConjugate hH E) i i).re := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hH.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))
  have hHdiag : H = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hH.spectral_theorem
  have htrace :
      (H * E).trace = (D * eigenbasisConjugate hH E).trace := by
    calc
      (H * E).trace =
          (((U : CMatrix a) * D * star (U : CMatrix a)) * E).trace := by
            simp [hHdiag]
      _ = ((U : CMatrix a) * D * (star (U : CMatrix a) * E)).trace := by
            simp [Matrix.mul_assoc]
      _ = ((star (U : CMatrix a) * E) * (U : CMatrix a) * D).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = (D * eigenbasisConjugate hH E).trace := by
            rw [Matrix.trace_mul_comm]
            simp [eigenbasisConjugate, U, Matrix.mul_assoc]
  rw [htrace]
  rw [trace_diagonal_mul_eq_sum]
  simp [Complex.re_sum, mul_comm]

private theorem eigenbasisConjugate_posSemidef {a : Type u} [Fintype a] [DecidableEq a]
    {H E : CMatrix a} (hH : H.IsHermitian) (hE : E.PosSemidef) :
    (eigenbasisConjugate hH E).PosSemidef := by
  unfold eigenbasisConjugate
  rw [Matrix.IsUnit.posSemidef_star_left_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  exact hE

private theorem eigenbasisConjugate_le_one {a : Type u} [Fintype a] [DecidableEq a]
    {H E : CMatrix a} (hH : H.IsHermitian) (hE : E ≤ 1) :
    eigenbasisConjugate hH E ≤ 1 := by
  rw [Matrix.le_iff] at hE ⊢
  unfold eigenbasisConjugate
  have hOne :
      (1 : CMatrix a) =
        star (hH.eigenvectorUnitary : CMatrix a) * 1 *
          (hH.eigenvectorUnitary : CMatrix a) := by
    simp
  rw [hOne]
  have hsub :
      star (hH.eigenvectorUnitary : CMatrix a) * 1 * (hH.eigenvectorUnitary : CMatrix a) -
        star (hH.eigenvectorUnitary : CMatrix a) * E *
          (hH.eigenvectorUnitary : CMatrix a) =
        star (hH.eigenvectorUnitary : CMatrix a) * (1 - E) *
          (hH.eigenvectorUnitary : CMatrix a) := by
    noncomm_ring
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_left_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hH.eigenvectorUnitary : CMatrix a))]
  exact hE

private theorem effect_diag_re_nonneg {a : Type u} {E : CMatrix a} (hE : E.PosSemidef)
    (i : a) :
    0 ≤ (E i i).re :=
  (Complex.nonneg_iff.mp (hE.diag_nonneg (i := i))).1

private theorem effect_diag_re_le_one {a : Type u} [DecidableEq a] {E : CMatrix a}
    (hE : E ≤ 1) (i : a) :
    (E i i).re ≤ 1 := by
  rw [Matrix.le_iff] at hE
  have h := (Complex.nonneg_iff.mp (hE.diag_nonneg (i := i))).1
  have hdiag : ((1 - E) i i).re = 1 - (E i i).re := by
    simp
  linarith

/-- Trace-max upper bound for Hermitian positive parts.  This is stated for
all effects `0 ≤ E ≤ 1`, hence it applies in particular to self-adjoint
projectors. -/
theorem hermitian_trace_mul_effect_le_posPart_trace {a : Type u}
    [Fintype a] [DecidableEq a] (H E : CMatrix a)
    (hH : H.IsHermitian) (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    ((H * E).trace).re ≤ (H⁺).trace.re := by
  classical
  rw [hermitian_trace_mul_eq_sum_eigenbasis_diag H E hH,
    posPart_trace_re_eq_positive_eigenvalue_sum H hH]
  apply Finset.sum_le_sum
  intro i _
  let E' := eigenbasisConjugate hH E
  have hE'pos : E'.PosSemidef := eigenbasisConjugate_posSemidef hH hEpos
  have hE'le : E' ≤ 1 := eigenbasisConjugate_le_one hH hEle
  have hdiag_nonneg : 0 ≤ (E' i i).re := effect_diag_re_nonneg hE'pos i
  have hdiag_le : (E' i i).re ≤ 1 := effect_diag_re_le_one hE'le i
  change hH.eigenvalues i * (E' i i).re ≤
    if 0 < hH.eigenvalues i then hH.eigenvalues i else 0
  by_cases hlam : 0 < hH.eigenvalues i
  · simp [hlam]
    nlinarith
  · have hlam_le : hH.eigenvalues i ≤ 0 := le_of_not_gt hlam
    simp [hlam]
    exact mul_nonpos_of_nonpos_of_nonneg hlam_le hdiag_nonneg

/-- The positive spectral projector attains the positive-part trace. -/
theorem positiveSpectralProjector_score_eq_posPart_trace {a : Type u}
    [Fintype a] [DecidableEq a] (H : CMatrix a) (hH : H.IsHermitian) :
    ((H * positiveSpectralProjector H hH).trace).re = (H⁺).trace.re := by
  classical
  rw [hermitian_trace_mul_eq_sum_eigenbasis_diag H (positiveSpectralProjector H hH) hH,
    posPart_trace_re_eq_positive_eigenvalue_sum H hH]
  apply Finset.sum_congr rfl
  intro i _
  have hdiag :
      (eigenbasisConjugate hH (positiveSpectralProjector H hH)) i i =
        (if 0 < hH.eigenvalues i then (1 : ℂ) else 0) := by
    unfold eigenbasisConjugate positiveSpectralProjector
    have hassoc :
        star (hH.eigenvectorUnitary : CMatrix a) *
              (((hH.eigenvectorUnitary : CMatrix a) *
                  Matrix.diagonal (fun j => if 0 < hH.eigenvalues j then (1 : ℂ) else 0)) *
                star (hH.eigenvectorUnitary : CMatrix a)) *
            (hH.eigenvectorUnitary : CMatrix a) =
          (star (hH.eigenvectorUnitary : CMatrix a) * (hH.eigenvectorUnitary : CMatrix a)) *
              Matrix.diagonal (fun j => if 0 < hH.eigenvalues j then (1 : ℂ) else 0) *
            (star (hH.eigenvectorUnitary : CMatrix a) * (hH.eigenvectorUnitary : CMatrix a)) := by
      noncomm_ring
    rw [hassoc]
    rw [Unitary.coe_star_mul_self]
    simp
  rw [hdiag]
  by_cases hlam : 0 < hH.eigenvalues i
  · simp [hlam]
  · simp [hlam]

/-- Positive-part trace-max package: the positive spectral projector attains
`Tr(H⁺)`, and every effect is bounded above by that value. -/
theorem positiveSpectralProjector_trace_max_effect {a : Type u}
    [Fintype a] [DecidableEq a] (H : CMatrix a) (hH : H.IsHermitian) :
    ((H * positiveSpectralProjector H hH).trace).re = (H⁺).trace.re ∧
      ∀ E : CMatrix a, E.PosSemidef → E ≤ 1 →
        ((H * E).trace).re ≤ (H⁺).trace.re :=
  ⟨positiveSpectralProjector_score_eq_posPart_trace H hH,
    fun E hEpos hEle => hermitian_trace_mul_effect_le_posPart_trace H E hH hEpos hEle⟩

/-- Difference of density matrices has trace zero. -/
theorem state_sub_trace_zero {a : Type u} [Fintype a] [DecidableEq a]
    (rho sigma : State a) :
    (rho.matrix - sigma.matrix).trace = 0 := by
  rw [Matrix.trace_sub, rho.trace_eq_one, sigma.trace_eq_one]
  norm_num

/-- Normalized trace distance between states is the trace of the positive part
of their Hermitian difference. -/
theorem State.normalizedTraceDistance_eq_posPart_trace {a : Type u}
    [Fintype a] [DecidableEq a] (rho sigma : State a) :
    rho.normalizedTraceDistance sigma = ((rho.matrix - sigma.matrix)⁺).trace.re := by
  let H : CMatrix a := rho.matrix - sigma.matrix
  have hH : H.IsHermitian := rho.pos.isHermitian.sub sigma.pos.isHermitian
  have htr : H.trace = 0 := by
    simpa [H] using state_sub_trace_zero rho sigma
  have hnorm := traceNorm_eq_two_posPart_trace_re_of_trace_zero H hH htr
  calc
    rho.normalizedTraceDistance sigma = (1 / 2 : ℝ) * traceNorm H := by rfl
    _ = (1 / 2 : ℝ) * (2 * (H⁺).trace.re) := by rw [hnorm]
    _ = (H⁺).trace.re := by ring

/-- Backward-compatible unqualified spelling of the state positive-part trace
formula. -/
theorem normalizedTraceDistance_eq_posPart_trace {a : Type u}
    [Fintype a] [DecidableEq a] (rho sigma : State a) :
    rho.normalizedTraceDistance sigma = ((rho.matrix - sigma.matrix)⁺).trace.re :=
  State.normalizedTraceDistance_eq_posPart_trace rho sigma

/-- The positive-part trace of a state difference as a complex trace. -/
theorem State.posPart_trace_eq_normalizedTraceDistance {a : Type u}
    [Fintype a] [DecidableEq a] (rho sigma : State a) :
    ((rho.matrix - sigma.matrix)⁺).trace =
      (rho.normalizedTraceDistance sigma : ℂ) := by
  rw [posPart_trace_eq_re_coe]
  rw [← State.normalizedTraceDistance_eq_posPart_trace]

/-- The negative-part trace of a state difference as a real trace. -/
theorem State.negPart_trace_re_eq_normalizedTraceDistance {a : Type u}
    [Fintype a] [DecidableEq a] (rho sigma : State a) :
    ((rho.matrix - sigma.matrix)⁻).trace.re =
      rho.normalizedTraceDistance sigma := by
  let H : CMatrix a := rho.matrix - sigma.matrix
  have hH : H.IsHermitian := rho.pos.isHermitian.sub sigma.pos.isHermitian
  have htr : H.trace = 0 := by
    simpa [H] using state_sub_trace_zero rho sigma
  calc
    ((rho.matrix - sigma.matrix)⁻).trace.re = ((rho.matrix - sigma.matrix)⁺).trace.re := by
      simpa [H] using negPart_trace_re_eq_posPart_trace_re_of_trace_zero H hH htr
    _ = rho.normalizedTraceDistance sigma := by
      rw [← State.normalizedTraceDistance_eq_posPart_trace rho sigma]

/-- The negative-part trace of a state difference as a complex trace. -/
theorem State.negPart_trace_eq_normalizedTraceDistance {a : Type u}
    [Fintype a] [DecidableEq a] (rho sigma : State a) :
    ((rho.matrix - sigma.matrix)⁻).trace =
      (rho.normalizedTraceDistance sigma : ℂ) := by
  rw [negPart_trace_eq_re_coe]
  rw [State.negPart_trace_re_eq_normalizedTraceDistance]

/-- Positive part of the trace-distance decomposition, normalized to a state. -/
def State.traceDistancePosPartState {a : Type u} [Fintype a] [DecidableEq a]
    (rho sigma : State a) (hδ : 0 < rho.normalizedTraceDistance sigma) : State a where
  matrix := (((rho.normalizedTraceDistance sigma)⁻¹ : ℝ) : ℂ) •
    ((rho.matrix - sigma.matrix)⁺)
  pos := Matrix.PosSemidef.smul (posPart_posSemidef (rho.matrix - sigma.matrix))
    (by
      exact_mod_cast (inv_nonneg.mpr hδ.le))
  trace_eq_one := by
    rw [Matrix.trace_smul, State.posPart_trace_eq_normalizedTraceDistance]
    let δ : ℝ := rho.normalizedTraceDistance sigma
    change (((δ⁻¹ : ℝ) : ℂ) * (δ : ℂ)) = 1
    have hδ_ne : δ ≠ 0 := hδ.ne'
    rw [← Complex.ofReal_mul]
    simp [hδ_ne]

/-- Negative part of the trace-distance decomposition, normalized to a state. -/
def State.traceDistanceNegPartState {a : Type u} [Fintype a] [DecidableEq a]
    (rho sigma : State a) (hδ : 0 < rho.normalizedTraceDistance sigma) : State a where
  matrix := (((rho.normalizedTraceDistance sigma)⁻¹ : ℝ) : ℂ) •
    ((rho.matrix - sigma.matrix)⁻)
  pos := Matrix.PosSemidef.smul (negPart_posSemidef (rho.matrix - sigma.matrix))
    (by
      exact_mod_cast (inv_nonneg.mpr hδ.le))
  trace_eq_one := by
    rw [Matrix.trace_smul, State.negPart_trace_eq_normalizedTraceDistance]
    let δ : ℝ := rho.normalizedTraceDistance sigma
    change (((δ⁻¹ : ℝ) : ℂ) * (δ : ℂ)) = 1
    have hδ_ne : δ ≠ 0 := hδ.ne'
    rw [← Complex.ofReal_mul]
    simp [hδ_ne]

@[simp]
theorem State.traceDistancePosPartState_matrix {a : Type u} [Fintype a] [DecidableEq a]
    (rho sigma : State a) (hδ : 0 < rho.normalizedTraceDistance sigma) :
    (rho.traceDistancePosPartState sigma hδ).matrix =
      (((rho.normalizedTraceDistance sigma)⁻¹ : ℝ) : ℂ) •
        ((rho.matrix - sigma.matrix)⁺) :=
  rfl

@[simp]
theorem State.traceDistanceNegPartState_matrix {a : Type u} [Fintype a] [DecidableEq a]
    (rho sigma : State a) (hδ : 0 < rho.normalizedTraceDistance sigma) :
    (rho.traceDistanceNegPartState sigma hδ).matrix =
      (((rho.normalizedTraceDistance sigma)⁻¹ : ℝ) : ℂ) •
        ((rho.matrix - sigma.matrix)⁻) :=
  rfl

/-- Scaling the normalized positive part by the trace distance recovers `H⁺`. -/
theorem State.normalizedTraceDistance_smul_traceDistancePosPartState_matrix {a : Type u}
    [Fintype a] [DecidableEq a]
    (rho sigma : State a) (hδ : 0 < rho.normalizedTraceDistance sigma) :
    ((rho.normalizedTraceDistance sigma : ℝ) : ℂ) •
        (rho.traceDistancePosPartState sigma hδ).matrix =
      ((rho.matrix - sigma.matrix)⁺) := by
  rw [State.traceDistancePosPartState_matrix]
  rw [smul_smul]
  let δ : ℝ := rho.normalizedTraceDistance sigma
  change ((δ : ℂ) * ((δ⁻¹ : ℝ) : ℂ)) • ((rho.matrix - sigma.matrix)⁺) =
    ((rho.matrix - sigma.matrix)⁺)
  have hscalar : ((δ : ℂ) * ((δ⁻¹ : ℝ) : ℂ)) = 1 := by
    have hδ_ne : δ ≠ 0 := hδ.ne'
    rw [← Complex.ofReal_mul]
    simp [hδ_ne]
  rw [hscalar, one_smul]

/-- Scaling the normalized negative part by the trace distance recovers `H⁻`. -/
theorem State.normalizedTraceDistance_smul_traceDistanceNegPartState_matrix {a : Type u}
    [Fintype a] [DecidableEq a]
    (rho sigma : State a) (hδ : 0 < rho.normalizedTraceDistance sigma) :
    ((rho.normalizedTraceDistance sigma : ℝ) : ℂ) •
        (rho.traceDistanceNegPartState sigma hδ).matrix =
      ((rho.matrix - sigma.matrix)⁻) := by
  rw [State.traceDistanceNegPartState_matrix]
  rw [smul_smul]
  let δ : ℝ := rho.normalizedTraceDistance sigma
  change ((δ : ℂ) * ((δ⁻¹ : ℝ) : ℂ)) • ((rho.matrix - sigma.matrix)⁻) =
    ((rho.matrix - sigma.matrix)⁻)
  have hscalar : ((δ : ℂ) * ((δ⁻¹ : ℝ) : ℂ)) = 1 := by
    have hδ_ne : δ ≠ 0 := hδ.ne'
    rw [← Complex.ofReal_mul]
    simp [hδ_ne]
  rw [hscalar, one_smul]

/-- State-difference decomposition into positive and negative parts. -/
theorem State.sub_eq_posPart_sub_negPart {a : Type u} [Fintype a] [DecidableEq a]
    (rho sigma : State a) :
    rho.matrix - sigma.matrix =
      ((rho.matrix - sigma.matrix)⁺) - ((rho.matrix - sigma.matrix)⁻) := by
  let H : CMatrix a := rho.matrix - sigma.matrix
  have hH : H.IsHermitian := rho.pos.isHermitian.sub sigma.pos.isHermitian
  simpa [H] using (CFC.posPart_sub_negPart H hH.isSelfAdjoint).symm

/-- Zero normalized trace distance forces equality of the underlying density
matrices. -/
theorem State.matrix_eq_of_normalizedTraceDistance_eq_zero {a : Type u}
    [Fintype a] [DecidableEq a] {rho sigma : State a}
    (hδ : rho.normalizedTraceDistance sigma = 0) :
    rho.matrix = sigma.matrix := by
  let H : CMatrix a := rho.matrix - sigma.matrix
  have hpos_re : (H⁺).trace.re = 0 := by
    have hdist := State.normalizedTraceDistance_eq_posPart_trace rho sigma
    rw [hδ] at hdist
    simpa [H] using hdist.symm
  have hneg_re : (H⁻).trace.re = 0 := by
    have hdist := State.negPart_trace_re_eq_normalizedTraceDistance rho sigma
    rw [hδ] at hdist
    simpa [H] using hdist
  have hpos_trace : (H⁺).trace = 0 := by
    rw [posPart_trace_eq_re_coe]
    simp [hpos_re]
  have hneg_trace : (H⁻).trace = 0 := by
    rw [negPart_trace_eq_re_coe]
    simp [hneg_re]
  have hpos_zero : H⁺ = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (posPart_posSemidef H)).mp hpos_trace
  have hneg_zero : H⁻ = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (negPart_posSemidef H)).mp hneg_trace
  have hsub : rho.matrix - sigma.matrix = 0 := by
    have hdecomp := State.sub_eq_posPart_sub_negPart rho sigma
    simpa [H, hpos_zero, hneg_zero] using hdecomp
  exact sub_eq_zero.mp hsub

/-- Zero normalized trace distance forces equality of states. -/
theorem State.eq_of_normalizedTraceDistance_eq_zero {a : Type u}
    [Fintype a] [DecidableEq a] {rho sigma : State a}
    (hδ : rho.normalizedTraceDistance sigma = 0) :
    rho = sigma :=
  State.ext (State.matrix_eq_of_normalizedTraceDistance_eq_zero hδ)

/-- Rearranged state-difference decomposition used by the AFW convex split. -/
theorem State.sigma_add_posPart_eq_rho_add_negPart {a : Type u}
    [Fintype a] [DecidableEq a] (rho sigma : State a) :
    sigma.matrix + ((rho.matrix - sigma.matrix)⁺) =
      rho.matrix + ((rho.matrix - sigma.matrix)⁻) := by
  let H : CMatrix a := rho.matrix - sigma.matrix
  let Hp : CMatrix a := H⁺
  let Hn : CMatrix a := H⁻
  have h : rho.matrix - sigma.matrix = Hp - Hn := by
    simpa [H, Hp, Hn] using State.sub_eq_posPart_sub_negPart rho sigma
  change sigma.matrix + Hp = rho.matrix + Hn
  have hpos :
      Hp = rho.matrix - sigma.matrix + Hn := by
    calc
      Hp = (Hp - Hn) + Hn := by
        abel
      _ = rho.matrix - sigma.matrix + Hn := by
        rw [← h]
  calc
    sigma.matrix + Hp = sigma.matrix + (rho.matrix - sigma.matrix + Hn) := by
      rw [hpos]
    _ = rho.matrix + Hn := by
      ext i j
      simp
      ring

/-- AFW matrix split after normalizing the positive and negative parts to
states and scaling them back by the trace distance. -/
theorem State.sigma_add_normalizedTraceDistance_smul_traceDistancePosPartState_eq
    {a : Type u} [Fintype a] [DecidableEq a]
    (rho sigma : State a) (hδ : 0 < rho.normalizedTraceDistance sigma) :
    sigma.matrix +
        ((rho.normalizedTraceDistance sigma : ℝ) : ℂ) •
          (rho.traceDistancePosPartState sigma hδ).matrix =
      rho.matrix +
        ((rho.normalizedTraceDistance sigma : ℝ) : ℂ) •
          (rho.traceDistanceNegPartState sigma hδ).matrix := by
  rw [State.normalizedTraceDistance_smul_traceDistancePosPartState_matrix,
    State.normalizedTraceDistance_smul_traceDistanceNegPartState_matrix]
  exact State.sigma_add_posPart_eq_rho_add_negPart rho sigma

end

end QIT
