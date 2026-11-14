/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.TraceNorm.Variational
public import QIT.States.PosSqrtOrder
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import Mathlib.Analysis.Matrix.Order

/-!
# Gentle operator and gentle projector lemmas

Wilde's gentle-operator lemma: for a density operator `ρ` and a measurement
effect `Λ` with `0 ≤ Λ ≤ I` whose detection probability
`Tr{Λρ}` on `ρ` is high (`Tr{Λρ} ≥ 1 - ε`), the post-measurement
un-normalized operator `√Λ ρ √Λ` is `2√ε`-close to `ρ` in trace norm,
`‖ρ - √Λ ρ √Λ‖₁ ≤ 2√ε`. The bound is independent of the dimension and of
everything but the detection deficit `ε`.

The proof follows the direct Wilde chain: split
`ρ - √Λ ρ √Λ = (I - √Λ) ρ + √Λ ρ (I - √Λ)`, apply the trace-norm triangle,
then a trace-norm Hilbert--Schmidt Cauchy--Schwarz inequality
(`‖A B‖₁ ≤ ‖A‖_F ‖B‖_F`, reached here through the finite-dimensional
variational characterization of `‖·‖₁` together with the
Hilbert--Schmidt inner product `⟨X, Y⟩ = Tr(Y Xᴴ)`) applied to the
factorizations `(I - √Λ) ρ = (I - √Λ) √ρ · √ρ` and
`√Λ ρ (I - √Λ) = √Λ √ρ · √ρ (I - √Λ)`, and finally the scalar
inequality `(1 - √x)² ≤ 1 - x` for `x ∈ [0, 1]` (equivalently `Λ ≤ √Λ`),
`Tr ρ = 1`, and `Tr{Λρ} ≤ 1`.
[Wilde2011Qst, qit-notes.tex:15961-16010] -/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Auxiliary: the trace-norm Hilbert--Schmidt Cauchy--Schwarz inequality
`‖A B‖₁ ≤ ‖A‖_F ‖B‖_F`, where `‖·‖_F` is the Frobenius (Hilbert--Schmidt)
norm `‖A‖_F² = Tr(A Aᴴ)`. Reached via the finite-dimensional variational
characterization of the trace norm (`‖X‖₁` is the supremum of
`|Tr(U X)|` over unitaries `U`): for an attaining unitary `U`,
`|Tr(U A B)| = |⟨Bᴴ, (U A)ᴴ⟩_HS| ≤ ‖Bᴴ‖_F ‖U A‖_F = ‖B‖_F ‖A‖_F`,
using unitary invariance of the Frobenius norm
(`Tr(U A Aᴴ Uᴴ) = Tr(A Aᴴ)` by cyclicity of trace and `Uᴴ U = I`).
[Wilde2011Qst, qit-notes.tex:15961-16010] -/
private theorem traceNorm_mul_le_frobenius (A B : CMatrix a) :
    traceNorm (A * B) ≤
      Real.sqrt ((A * Matrix.conjTranspose A).trace).re *
        Real.sqrt ((B * Matrix.conjTranspose B).trace).re := by
  -- Frobenius / Hilbert--Schmidt inner product `⟨X, Y⟩ = Tr(Y Xᴴ)` from `M = 1`.
  letI iSemi : SeminormedAddCommGroup (CMatrix a) :=
    (1 : CMatrix a).toMatrixSeminormedAddCommGroup Matrix.PosSemidef.one
  letI iInner : InnerProductSpace ℂ (CMatrix a) :=
    (1 : CMatrix a).toMatrixInnerProductSpace Matrix.PosSemidef.one
  -- Local Frobenius-norm squared helper: `‖X‖² = Re Tr(X Xᴴ)`.
  -- Uses the local `iInner`/`iSemi` (both induced by the identity `M = 1`).
  have hnorm_sq_eq (X : CMatrix a) :
      @norm (CMatrix a) iSemi.toNorm X ^ 2 =
        ((X * Matrix.conjTranspose X).trace).re := by
    rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ (CMatrix a)
        Complex.instRCLike iSemi iInner X]
    show ((X * (1 : CMatrix a) * Matrix.conjTranspose X).trace).re = _
    rw [Matrix.mul_one]
  have hApos : 0 ≤ ((A * Matrix.conjTranspose A).trace).re := by
    have hpsd : (A * Matrix.conjTranspose A).PosSemidef :=
      Matrix.posSemidef_self_mul_conjTranspose A
    exact (Matrix.PosSemidef.trace_nonneg hpsd).1
  have hBpos : 0 ≤ ((B * Matrix.conjTranspose B).trace).re := by
    have hpsd : (B * Matrix.conjTranspose B).PosSemidef :=
      Matrix.posSemidef_self_mul_conjTranspose B
    exact (Matrix.PosSemidef.trace_nonneg hpsd).1
  -- Pick an attaining unitary for `‖A * B‖₁`.
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (A * B)
  -- `Tr((A B) U) = Tr((U A) B)` by cyclicity of the trace.
  have hcycle : ((A * B) * (U : CMatrix a)).trace =
      ((U : CMatrix a) * A * B).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  -- Identify `Tr((U A) B)` with the HS inner product `⟨Bᴴ, (U A)⟩`
  -- (`⟨x, y⟩ = Tr(y xᴴ)`, so `⟨Bᴴ, U A⟩ = Tr((U A) B)`).
  have hinner : inner ℂ (Matrix.conjTranspose B) ((U : CMatrix a) * A) =
      ((U : CMatrix a) * A * B).trace := by
    show ((U : CMatrix a) * A * (1 : CMatrix a) *
            (Matrix.conjTranspose B).conjTranspose).trace = _
    rw [Matrix.mul_one, Matrix.conjTranspose_conjTranspose]
  -- Hilbert--Schmidt Cauchy--Schwarz, with the inner product's own norm.
  have hcs : ‖inner ℂ (Matrix.conjTranspose B) ((U : CMatrix a) * A)‖ ≤
      @norm (CMatrix a) iSemi.toNorm (Matrix.conjTranspose B) *
        @norm (CMatrix a) iSemi.toNorm ((U : CMatrix a) * A) :=
    norm_inner_le_norm (𝕜 := ℂ) _ _
  have hbabs : ‖(((A * B) * (U : CMatrix a)).trace)‖ ≤
      @norm (CMatrix a) iSemi.toNorm (Matrix.conjTranspose B) *
        @norm (CMatrix a) iSemi.toNorm ((U : CMatrix a) * A) := by
    rw [hinner] at hcs
    rw [hcycle]
    exact hcs
  -- `‖Bᴴ‖² = Tr(Bᴴ B) = Tr(B Bᴴ)` by cyclicity of trace.
  have hnormB : @norm (CMatrix a) iSemi.toNorm (Matrix.conjTranspose B) ^ 2 =
      ((B * Matrix.conjTranspose B).trace).re := by
    rw [hnorm_sq_eq, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  -- `‖U A‖² = Tr((U A)(U A)ᴴ) = Tr(U A Aᴴ Uᴴ) = Tr(A Aᴴ)` (U unitary, cyclic).
  have hUstarU : (Matrix.conjTranspose (U : CMatrix a)) * (U : CMatrix a) = 1 :=
    (Matrix.mem_unitaryGroup_iff'.mp U.prop : _)
  have hnormUA : @norm (CMatrix a) iSemi.toNorm ((U : CMatrix a) * A) ^ 2 =
      ((A * Matrix.conjTranspose A).trace).re := by
    rw [hnorm_sq_eq, Matrix.conjTranspose_mul]
    -- Goal: `Re Tr((U A)(Aᴴ Uᴴ))`. Reassociate to the 3-factor form `U (A Aᴴ) Uᴴ`,
    -- then cycle, cancel `Uᴴ U = 1`.
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hUstarU, Matrix.one_mul]
  have hnnA : 0 ≤ @norm (CMatrix a) iSemi.toNorm ((U : CMatrix a) * A) :=
    norm_nonneg _
  have hnnB : 0 ≤ @norm (CMatrix a) iSemi.toNorm (Matrix.conjTranspose B) :=
    norm_nonneg _
  -- Take square roots on both sides of the squared bound (`a² = b²`, `a,b ≥ 0`).
  have hUA_sqrt : @norm (CMatrix a) iSemi.toNorm ((U : CMatrix a) * A) =
      Real.sqrt ((A * Matrix.conjTranspose A).trace).re := by
    have h1 : @norm (CMatrix a) iSemi.toNorm ((U : CMatrix a) * A) ^ 2 =
        Real.sqrt ((A * Matrix.conjTranspose A).trace).re ^ 2 := by
      rw [hnormUA, Real.sq_sqrt hApos]
    exact (sq_eq_sq₀ hnnA (Real.sqrt_nonneg _)).mp h1
  have hB_sqrt : @norm (CMatrix a) iSemi.toNorm (Matrix.conjTranspose B) =
      Real.sqrt ((B * Matrix.conjTranspose B).trace).re := by
    have h1 : @norm (CMatrix a) iSemi.toNorm (Matrix.conjTranspose B) ^ 2 =
        Real.sqrt ((B * Matrix.conjTranspose B).trace).re ^ 2 := by
      rw [hnormB, Real.sq_sqrt hBpos]
    exact (sq_eq_sq₀ hnnB (Real.sqrt_nonneg _)).mp h1
  -- Assemble: `‖A B‖₁ = |Tr((A B) U)| = ‖Tr((A B) U)‖` (attainment).
  -- `Complex.abs` is definitionally the complex norm.
  have habs_eq : traceNorm (A * B) =
      ‖(((A * B) * (U : CMatrix a)).trace)‖ := hU.symm
  calc traceNorm (A * B)
      = ‖(((A * B) * (U : CMatrix a)).trace)‖ := habs_eq
    _ ≤ @norm (CMatrix a) iSemi.toNorm (Matrix.conjTranspose B) *
          @norm (CMatrix a) iSemi.toNorm ((U : CMatrix a) * A) := hbabs
    _ = Real.sqrt ((A * Matrix.conjTranspose A).trace).re *
          Real.sqrt ((B * Matrix.conjTranspose B).trace).re := by
            rw [hB_sqrt, hUA_sqrt]; exact mul_comm _ _

/-- Auxiliary: the operator inequality `(1 - √Λ)² ≤ 1 - Λ` for `0 ≤ Λ ≤ 1`,
equivalent (after expanding) to `Λ ≤ √Λ`, which is the
`posSemidef_le_psdSqrt_of_le_one` half of the operator-monotone square-root
chain. This is the scalar inequality `(1 - √x)² ≤ 1 - x` for `x ∈ [0, 1]`,
lifted to the Loewner order.
[Wilde2011Qst, qit-notes.tex:15961-16010] -/
private lemma one_sub_psdSqrt_sq_le {Λ : CMatrix a}
    (hΛ0 : Λ.PosSemidef) (hΛ1 : Λ ≤ 1) :
    (1 - psdSqrt Λ) * (1 - psdSqrt Λ) ≤ 1 - Λ := by
  rw [Matrix.le_iff]
  -- `(1 - Λ) - (1 - √Λ)² = √Λ - Λ`, and `√Λ - Λ` is PSD = `Λ ≤ √Λ`.
  have hsq : psdSqrt Λ * psdSqrt Λ = Λ := psdSqrt_mul_self_of_posSemidef hΛ0
  -- `(1-Λ) - (1-√Λ)² = 2•(√Λ - Λ)`, which is PSD since `√Λ - Λ` is PSD
  -- (= `Λ ≤ √Λ`, the promoted `posSemidef_le_psdSqrt_of_le_one`).
  have hred : (1 - Λ) - (1 - psdSqrt Λ) * (1 - psdSqrt Λ) = (2 : ℝ) • (psdSqrt Λ - Λ) := by
    have e : (1 - psdSqrt Λ) * (1 - psdSqrt Λ) =
        1 - psdSqrt Λ - psdSqrt Λ + psdSqrt Λ * psdSqrt Λ := by noncomm_ring
    rw [e, hsq]
    have h2 : (2 : ℝ) • (psdSqrt Λ - Λ) = psdSqrt Λ - Λ + (psdSqrt Λ - Λ) := by
      rw [two_smul]
    rw [h2]
    abel
  rw [hred]
  refine Matrix.PosSemidef.smul ?_ (by norm_num : (0 : ℝ) ≤ 2)
  exact (Matrix.le_iff.mp (posSemidef_le_psdSqrt_of_le_one hΛ0 hΛ1) : _)

/-- Auxiliary: `Tr((1 - √Λ)² ρ) ≤ Tr((1 - Λ) ρ)` from `(1 - √Λ)² ≤ 1 - Λ`,
using that conjugation by `ρ^{1/2}` and the trace are order-monotone on PSD
matrices (since `(1 - √Λ)² ρ ≤ (1 - Λ) ρ` in trace against PSD, equivalently
`√ρ ((1 - Λ) - (1 - √Λ)²) √ρ` is PSD).
[Wilde2011Qst, qit-notes.tex:15961-16010] -/
private lemma trace_one_sub_sq_rho_le {Λ : CMatrix a} {ρ : CMatrix a}
    (hΛ0 : Λ.PosSemidef) (hΛ1 : Λ ≤ 1) (hρ : ρ.PosSemidef) :
    (((1 - psdSqrt Λ) * (1 - psdSqrt Λ) * ρ).trace).re ≤
      (((1 - Λ) * ρ).trace).re := by
  -- `D := (1 - Λ) - (1 - √Λ)²` is PSD; conjugating by `√ρ` keeps it PSD.
  set D : CMatrix a := (1 - Λ) - (1 - psdSqrt Λ) * (1 - psdSqrt Λ)
  have hD_psd : D.PosSemidef := one_sub_psdSqrt_sq_le hΛ0 hΛ1
  set S : CMatrix a := psdSqrt ρ
  have hS_herm : S.IsHermitian := psdSqrt_isHermitian ρ
  have hSS : S * S = ρ := psdSqrt_mul_self_of_posSemidef hρ
  have hconj_psd : (S * D * S).PosSemidef := by
    have h := hD_psd.mul_mul_conjTranspose_same S
    rw [show Matrix.conjTranspose S = S from hS_herm.eq] at h
    exact h
  have htr_nonneg : 0 ≤ ((S * D * S).trace).re :=
    (Matrix.PosSemidef.trace_nonneg hconj_psd).1
  -- `(S D S).trace = (ρ D).trace = (D ρ).trace` by cyclicity and commutativity.
  have hcyc : (S * D * S).trace = (ρ * D).trace := by
    rw [Matrix.trace_mul_cycle, ← hSS]
  have hDr_re_nonneg : 0 ≤ ((D * ρ).trace).re := by
    rw [show (D * ρ).trace = (ρ * D).trace from by rw [Matrix.trace_mul_comm]]
    rw [hcyc] at htr_nonneg
    exact htr_nonneg
  -- `Re((D ρ).trace) = Re((1-Λ)ρ) - Re((1-√Λ)²ρ)`, and it is `≥ 0`.
  have hsplit : (D * ρ).trace = ((1 - Λ) * ρ).trace -
      ((1 - psdSqrt Λ) * (1 - psdSqrt Λ) * ρ).trace := by
    show (((1 - Λ) - (1 - psdSqrt Λ) * (1 - psdSqrt Λ)) * ρ).trace = _
    rw [Matrix.sub_mul, Matrix.trace_sub]
  have hkey : 0 ≤ (((1 - Λ) * ρ).trace - ((1 - psdSqrt Λ) *
      (1 - psdSqrt Λ) * ρ).trace).re := by rw [← hsplit]; exact hDr_re_nonneg
  rw [Complex.sub_re] at hkey
  linarith

/-- **Gentle operator lemma.** For a density operator `ρ` and a measurement
effect `Λ` with `0 ≤ Λ ≤ I`, the post-measurement un-normalized operator
`√Λ ρ √Λ` is `2√(1 - Re Tr(Λρ))`-close to `ρ` in trace norm. When the
detection probability `Re Tr(Λρ)` is at least `1 - ε`, this yields the
`2√ε` bound of Wilde's gentle-operator lemma.
[Wilde2011Qst, qit-notes.tex:15961-16010] -/
theorem gentle_operator (Λ : CMatrix a) (hΛ0 : Λ.PosSemidef)
    (hΛ1 : (1 - Λ).PosSemidef) (ρ : State a) :
    traceNorm (psdSqrt Λ * ρ.matrix * psdSqrt Λ - ρ.matrix) ≤
      2 * Real.sqrt (1 - ((Λ * ρ.matrix).trace).re) := by
  have hΛsq_herm : (psdSqrt Λ).IsHermitian := psdSqrt_isHermitian Λ
  have hΛsq_pos : (psdSqrt Λ).PosSemidef := psdSqrt_pos Λ
  have hΛ_le_one : Λ ≤ 1 := by simpa [Matrix.le_iff] using hΛ1
  set R : CMatrix a := psdSqrt Λ with hR_def
  have hR_herm : R.IsHermitian := hΛsq_herm
  have hR_pos : R.PosSemidef := hΛsq_pos
  have hRR : R * R = Λ := psdSqrt_mul_self_of_posSemidef hΛ0
  have hρ : ρ.matrix.PosSemidef := ρ.pos
  have hρ_herm : ρ.matrix.IsHermitian := hρ.isHermitian
  have htrρ : ρ.matrix.trace = 1 := ρ.trace_eq_one
  set P : CMatrix a := psdSqrt ρ.matrix with hP_def
  have hP_herm : P.IsHermitian := psdSqrt_isHermitian ρ.matrix
  have hPP : P * P = ρ.matrix := psdSqrt_mul_self_of_posSemidef hρ
  -- Split `ρ - √Λ ρ √Λ = (1 - √Λ) ρ + √Λ ρ (1 - √Λ)`.
  have hsplit : ρ.matrix - R * ρ.matrix * R = (1 - R) * ρ.matrix + R * ρ.matrix * (1 - R) := by
    have : R * R = Λ := hRR
    noncomm_ring
  -- Term 1: `‖(1 - R) ρ‖₁ = ‖(1 - R) P · P‖₁ ≤ ‖(1-R) P‖_F · ‖P‖_F`.
  have hfact1 : (1 - R) * ρ.matrix = ((1 - R) * P) * P := by
    rw [← hPP, Matrix.mul_assoc]
  have hterm1 : traceNorm ((1 - R) * ρ.matrix) ≤
      Real.sqrt (((1 - R) * (1 - R) * ρ.matrix).trace).re := by
    have h1 := traceNorm_mul_le_frobenius ((1 - R) * P) P
    -- `‖P‖_F² = Tr(P Pᴴ) = Tr(P P) = Tr ρ = 1`.
    have hnormP : ((P * Matrix.conjTranspose P).trace).re = 1 := by
      have : P * Matrix.conjTranspose P = P * P := by
        rw [show Matrix.conjTranspose P = P from hP_herm.eq]
      rw [this, hPP, htrρ]; simp
    -- `‖(1-R) P‖_F² = Tr((1-R) P P (1-R)) = Tr((1-R)² ρ)` (cycle, PP = ρ).
    have hnormLRP : (((1 - R) * P * Matrix.conjTranspose ((1 - R) * P)).trace).re =
        (((1 - R) * (1 - R) * ρ.matrix).trace).re := by
      have hconjP : Matrix.conjTranspose ((1 - R) * P) = P * (1 - R) := by
        rw [Matrix.conjTranspose_mul,
          show Matrix.conjTranspose (1 - R) = 1 - R from by
            rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hR_herm.eq],
          show Matrix.conjTranspose P = P from hP_herm.eq]
      have e1 : (1 - R) * P * (P * (1 - R)) = (1 - R) * ρ.matrix * (1 - R) := by
        rw [show (1 - R) * P * (P * (1 - R)) = ((1 - R) * P * P) * (1 - R) from by
              noncomm_ring,
            Matrix.mul_assoc (1 - R) P P, hPP]
      rw [hconjP, e1, Matrix.trace_mul_cycle]
    -- `(1-R)ρ = (1-R)P·P`, then apply HS-CS, simplify `‖P‖_F = √1 = 1`.
    calc traceNorm ((1 - R) * ρ.matrix)
        = traceNorm ((1 - R) * P * P) := by rw [hfact1]
      _ ≤ Real.sqrt (((1 - R) * P * Matrix.conjTranspose ((1 - R) * P)).trace).re *
            Real.sqrt ((P * Matrix.conjTranspose P).trace).re := h1
      _ = Real.sqrt (((1 - R) * (1 - R) * ρ.matrix).trace).re *
            Real.sqrt 1 := by rw [hnormLRP, hnormP]
      _ = Real.sqrt (((1 - R) * (1 - R) * ρ.matrix).trace).re := by simp
  -- Term 2: `‖R ρ (1-R)‖₁ = ‖R P · P (1-R)‖₁ ≤ ‖R P‖_F · ‖P(1-R)‖_F`.
  have hfact2 : R * ρ.matrix * (1 - R) = (R * P) * (P * (1 - R)) := by
    rw [← hPP, Matrix.mul_assoc, Matrix.mul_assoc]; noncomm_ring
  have hterm2 : traceNorm (R * ρ.matrix * (1 - R)) ≤
      Real.sqrt (((Λ * ρ.matrix).trace).re *
        (((1 - R) * (1 - R) * ρ.matrix).trace).re) := by
    have h2 := traceNorm_mul_le_frobenius (R * P) (P * (1 - R))
    -- `‖R P‖_F² = Tr(R P P R) = Tr(R ρ R) = Tr(R² ρ) = Tr(Λ ρ)`.
    have hnormRP : (((R * P) * Matrix.conjTranspose (R * P)).trace).re =
        ((Λ * ρ.matrix).trace).re := by
      have hconjRP : Matrix.conjTranspose (R * P) = P * R := by
        rw [Matrix.conjTranspose_mul,
          show Matrix.conjTranspose R = R from hR_herm.eq,
          show Matrix.conjTranspose P = P from hP_herm.eq]
      -- `R * P * (P * R) = R * ρ.matrix * R`, then cycle to `R * R * ρ.matrix = Λ * ρ.matrix`.
      have e1 : R * P * (P * R) = R * ρ.matrix * R := by
        rw [show R * P * (P * R) = (R * P * P) * R from by noncomm_ring,
          Matrix.mul_assoc R P P, hPP]
      rw [hconjRP, e1, Matrix.trace_mul_cycle, ← hRR]
    -- `‖P(1-R)‖_F² = Tr(P (1-R)² P) = Tr(ρ (1-R)²)`.
    have hnormP1R : (((P * (1 - R)) * Matrix.conjTranspose (P * (1 - R))).trace).re =
        (((1 - R) * (1 - R) * ρ.matrix).trace).re := by
      have hconj : Matrix.conjTranspose (P * (1 - R)) = (1 - R) * P := by
        rw [Matrix.conjTranspose_mul,
          show Matrix.conjTranspose (1 - R) = 1 - R from by
            rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hR_herm.eq],
          show Matrix.conjTranspose P = P from hP_herm.eq]
      rw [hconj, Matrix.trace_mul_comm]
      -- After comm: `((1-R)*P * P*(1-R)).trace`, reduce `P*P` to ρ, then cycle.
      have e1 : (1 - R) * P * (P * (1 - R)) = (1 - R) * ρ.matrix * (1 - R) := by
        rw [show (1 - R) * P * (P * (1 - R)) = ((1 - R) * P * P) * (1 - R) from by
              noncomm_ring,
            Matrix.mul_assoc (1 - R) P P, hPP]
      rw [e1, Matrix.trace_mul_cycle]
    -- Assemble.
    calc traceNorm (R * ρ.matrix * (1 - R))
        = traceNorm ((R * P) * (P * (1 - R))) := by rw [hfact2]
      _ ≤ Real.sqrt (((R * P) * Matrix.conjTranspose (R * P)).trace).re *
            Real.sqrt (((P * (1 - R)) * Matrix.conjTranspose (P * (1 - R))).trace).re := h2
      _ = Real.sqrt ((Λ * ρ.matrix).trace).re *
            Real.sqrt (((1 - R) * (1 - R) * ρ.matrix).trace).re := by
            rw [hnormRP, hnormP1R]
      _ = Real.sqrt (((Λ * ρ.matrix).trace).re *
            (((1 - R) * (1 - R) * ρ.matrix).trace).re) := by
            have hΛρ_nonneg : 0 ≤ ((Λ * ρ.matrix).trace).re :=
              cMatrix_trace_mul_posSemidef_re_nonneg hΛ0 hρ
            rw [← Real.sqrt_mul hΛρ_nonneg _]
  -- Operator-inequality reduction `(1-R)² ρ`-trace ≤ `(1-Λ) ρ`-trace.
  have honeR_sq_le : (((1 - R) * (1 - R) * ρ.matrix).trace).re ≤
      (((1 - Λ) * ρ.matrix).trace).re := by
    have := trace_one_sub_sq_rho_le hΛ0 hΛ_le_one hρ
    simpa [R, hR_def] using this
  -- Detection traces: `Re Tr(Λ ρ) ≥ 0`, `≤ 1`; `Re Tr((1-Λ)ρ) = 1 - Re Tr(Λρ)`.
  have htrΛρ_nonneg : 0 ≤ ((Λ * ρ.matrix).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hΛ0 hρ
  have htrΛρ_le_one : ((Λ * ρ.matrix).trace).re ≤ 1 := by
    have hkey : 0 ≤ (((1 - Λ) * ρ.matrix).trace).re :=
      cMatrix_trace_mul_posSemidef_re_nonneg
        (by simpa [Matrix.le_iff] using hΛ1 : (1 - Λ).PosSemidef) hρ
    have hcyc : ((1 - Λ) * ρ.matrix).trace = (1 : ℂ) - (Λ * ρ.matrix).trace := by
      have : (1 - Λ) * ρ.matrix = ρ.matrix - Λ * ρ.matrix := by noncomm_ring
      rw [this, Matrix.trace_sub]
      rw [show ρ.matrix.trace = (1 : ℂ) from htrρ]
    rw [hcyc] at hkey
    rw [Complex.sub_re, Complex.one_re] at hkey
    linarith
  have honeΛ_def : 0 ≤ 1 - ((Λ * ρ.matrix).trace).re := by linarith
  -- `Re Tr((1-Λ)ρ) = 1 - Re Tr(Λρ)`.
  have htr1Lρ_re : (((1 - Λ) * ρ.matrix).trace).re = 1 - ((Λ * ρ.matrix).trace).re := by
    have hcyc : ((1 - Λ) * ρ.matrix).trace = (1 : ℂ) - (Λ * ρ.matrix).trace := by
      have : (1 - Λ) * ρ.matrix = ρ.matrix - Λ * ρ.matrix := by noncomm_ring
      rw [this, Matrix.trace_sub, show ρ.matrix.trace = (1 : ℂ) from htrρ]
    rw [hcyc, Complex.sub_re, Complex.one_re]
  -- Assemble the two-term chain.
  -- `‖...‖₁ ≤ √(Tr((1-R)²ρ)) + √(Tr(Λρ) · Tr((1-R)²ρ))`
  --        ≤ √(Tr((1-Λ)ρ)) + √(Tr(Λρ) · Tr((1-Λ)ρ))`   (operator-ineq on both sqrt args)
  --        = √(Tr((1-Λ)ρ)) (1 + √(Tr(Λρ)))
  --        ≤ √(Tr((1-Λ)ρ)) · 2                          (Tr(Λρ) ≤ 1)
  --        = 2 √(1 - Re Tr(Λρ))`.
  have hs1 : Real.sqrt (((1 - R) * (1 - R) * ρ.matrix).trace).re +
      Real.sqrt (((Λ * ρ.matrix).trace).re *
        (((1 - R) * (1 - R) * ρ.matrix).trace).re) ≤
    Real.sqrt (((1 - Λ) * ρ.matrix).trace).re +
      Real.sqrt (((Λ * ρ.matrix).trace).re *
        (((1 - Λ) * ρ.matrix).trace).re) := by
    refine add_le_add ?_ ?_
    · exact Real.sqrt_le_sqrt honeR_sq_le
    · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left honeR_sq_le htrΛρ_nonneg)
  have hs2 : Real.sqrt (((1 - Λ) * ρ.matrix).trace).re +
      Real.sqrt (((Λ * ρ.matrix).trace).re *
        (((1 - Λ) * ρ.matrix).trace).re) =
      Real.sqrt (((1 - Λ) * ρ.matrix).trace).re *
        (1 + Real.sqrt ((Λ * ρ.matrix).trace).re) := by
    rw [Real.sqrt_mul htrΛρ_nonneg]
    ring
  have hΛρ_root_le_one : Real.sqrt ((Λ * ρ.matrix).trace).re ≤ 1 :=
    Real.sqrt_le_one.mpr htrΛρ_le_one
  have hs3 : Real.sqrt (((1 - Λ) * ρ.matrix).trace).re *
      (1 + Real.sqrt ((Λ * ρ.matrix).trace).re) ≤
      2 * Real.sqrt (((1 - Λ) * ρ.matrix).trace).re := by
    have h0 : 0 ≤ Real.sqrt (((1 - Λ) * ρ.matrix).trace).re := Real.sqrt_nonneg _
    have h1 : 1 + Real.sqrt ((Λ * ρ.matrix).trace).re ≤ 2 := by
      linarith [hΛρ_root_le_one]
    linarith [mul_le_mul_of_nonneg_left h1 h0]
  have hs4 : 2 * Real.sqrt (((1 - Λ) * ρ.matrix).trace).re =
      2 * Real.sqrt (1 - ((Λ * ρ.matrix).trace).re) := by
    rw [htr1Lρ_re]
  -- Final chain: `‖RρR - ρ‖₁ = ‖ρ - RρR‖ = ‖(1-R)ρ + Rρ(1-R)‖ ≤ ... ≤ 2√(1-Tr(Λρ))`.
  have hsymm : traceNorm (R * ρ.matrix * R - ρ.matrix) =
      traceNorm (ρ.matrix - R * ρ.matrix * R) := by
    rw [show R * ρ.matrix * R - ρ.matrix = -(ρ.matrix - R * ρ.matrix * R) from
        (neg_sub _ _).symm, traceNorm_neg]
  calc traceNorm (R * ρ.matrix * R - ρ.matrix)
      = traceNorm (ρ.matrix - R * ρ.matrix * R) := hsymm
    _ = traceNorm ((1 - R) * ρ.matrix + R * ρ.matrix * (1 - R)) := by rw [hsplit]
    _ ≤ traceNorm ((1 - R) * ρ.matrix) + traceNorm (R * ρ.matrix * (1 - R)) :=
        traceNorm_add_le _ _
    _ ≤ Real.sqrt (((1 - R) * (1 - R) * ρ.matrix).trace).re +
        Real.sqrt (((Λ * ρ.matrix).trace).re *
          (((1 - R) * (1 - R) * ρ.matrix).trace).re) :=
        add_le_add hterm1 hterm2
    _ ≤ Real.sqrt (((1 - Λ) * ρ.matrix).trace).re +
        Real.sqrt (((Λ * ρ.matrix).trace).re *
          (((1 - Λ) * ρ.matrix).trace).re) := hs1
    _ = Real.sqrt (((1 - Λ) * ρ.matrix).trace).re *
        (1 + Real.sqrt ((Λ * ρ.matrix).trace).re) := hs2
    _ ≤ 2 * Real.sqrt (((1 - Λ) * ρ.matrix).trace).re := hs3
    _ = 2 * Real.sqrt (1 - ((Λ * ρ.matrix).trace).re) := hs4

/-- A positive semidefinite idempotent matrix has positive semidefinite
orthogonal complement. -/
theorem projector_one_sub_posSemidef (P : CMatrix a) (hP : P.PosSemidef)
    (hPid : P * P = P) :
    (1 - P).PosSemidef := by
  have h1P_herm : (1 - P).IsHermitian :=
    (Matrix.isHermitian_one).sub hP.isHermitian
  have h1P_conj : Matrix.conjTranspose (1 - P) = 1 - P := h1P_herm.eq
  have h1P_sq : (1 - P) * (1 - P) = 1 - P := by
    have e : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [e, hPid]
    abel
  have hkey : (1 - P) = Matrix.conjTranspose (1 - P) * (1 - P) := by
    rw [h1P_conj, h1P_sq]
  rw [hkey]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

/-- **Gentle projector lemma.** Specialization of the gentle-operator lemma to
a measurement described by an orthogonal projector `Π` (`Π.PosSemidef`,
`Π * Π = Π`): the post-measurement un-normalized operator `Π ρ Π` is
`2√(1 - Re Tr(Πρ))`-close to `ρ` in trace norm. Since a PSD idempotent has
eigenvalues in `{0, 1}`, one has `Π ≤ I` (i.e. `(1 - Π).PosSemidef`) and
`psdSqrt Π = Π`, reducing the bound to that of `gentle_operator`.
[Wilde2011Qst, qit-notes.tex:15961-16010] -/
theorem gentle_projector (Λ : CMatrix a) (hΛ : Λ.PosSemidef)
    (hΛid : Λ * Λ = Λ) (ρ : State a) :
    traceNorm (Λ * ρ.matrix * Λ - ρ.matrix) ≤
      2 * Real.sqrt (1 - ((Λ * ρ.matrix).trace).re) := by
  -- `psdSqrt Λ = Λ`: `Λ` is itself a PSD square root of `Λ` (since `Λ*Λ = Λ`),
  -- and the PSD square root is unique (`CFC.sqrt_unique`).
  have hsqrt : psdSqrt Λ = Λ := by
    rw [psdSqrt]
    exact CFC.sqrt_unique hΛid (Matrix.nonneg_iff_posSemidef.mpr hΛ)
  have hΛ_le_one : (1 - Λ).PosSemidef :=
    projector_one_sub_posSemidef Λ hΛ hΛid
  -- Reduce to `gentle_operator` with the projector as the effect.
  -- `gentle_operator` concludes `traceNorm (psdSqrt Λ * ρ * psdSqrt Λ - ρ) ≤ ...`;
  -- rewrite `psdSqrt Λ = Λ` (via `hsqrt`) into its conclusion.
  have hgo := gentle_operator Λ hΛ hΛ_le_one ρ
  rw [hsqrt] at hgo
  exact hgo

/-- Projector sandwiches of states are positive semidefinite. -/
theorem projector_sandwich_posSemidef (P : CMatrix a) (hP : P.PosSemidef)
    (ρ : State a) :
    (P * ρ.matrix * P).PosSemidef := by
  have h := ρ.pos.mul_mul_conjTranspose_same P
  simpa [hP.isHermitian.eq, Matrix.mul_assoc] using h

/-- The real trace of a projector sandwich is the projector acceptance
probability. -/
theorem projector_sandwich_trace_re_eq_acceptance (P : CMatrix a)
    (hPid : P * P = P) (ρ : State a) :
    ((P * ρ.matrix * P).trace).re = ((P * ρ.matrix).trace).re := by
  have htrace : (P * ρ.matrix * P).trace = (P * ρ.matrix).trace := by
    calc
      (P * ρ.matrix * P).trace = (P * P * ρ.matrix).trace := by
        rw [Matrix.trace_mul_cycle]
      _ = (P * ρ.matrix).trace := by
        rw [hPid]
  exact congrArg Complex.re htrace

/-- A projector sandwich with acceptance at least `1 - η` has nonzero trace
when `η < 1`. -/
theorem projector_sandwich_trace_re_ne_zero_of_acceptance (P : CMatrix a)
    (hPid : P * P = P) (ρ : State a) {η : ℝ} (hη_lt_one : η < 1)
    (hacc : 1 - η ≤ ((P * ρ.matrix).trace).re) :
    (P * ρ.matrix * P).trace.re ≠ 0 := by
  have htrace := projector_sandwich_trace_re_eq_acceptance P hPid ρ
  have hpos_one_sub : 0 < 1 - η := by linarith
  have hpos : 0 < (P * ρ.matrix * P).trace.re := by
    rw [htrace]
    exact lt_of_lt_of_le hpos_one_sub hacc
  exact hpos.ne'

/-- Normalizing a high-acceptance projector sandwich gives a state close to the
original state in normalized trace distance. The bound is intentionally
generic and dimension-free: the unnormalized disturbance is controlled by
`gentle_projector`, and the extra normalization cost is at most the rejection
probability. -/
theorem normalizedTraceDistance_normalize_projector_sandwich_le
    (P : CMatrix a) (hP : P.PosSemidef) (hPid : P * P = P)
    (ρ : State a) {η : ℝ} (hη_nonneg : 0 ≤ η) (hη_lt_one : η < 1)
    (hacc : 1 - η ≤ ((P * ρ.matrix).trace).re) :
    let τM := P * ρ.matrix * P
    let hτ : τM.PosSemidef := projector_sandwich_posSemidef P hP ρ
    let htr : τM.trace.re ≠ 0 :=
      projector_sandwich_trace_re_ne_zero_of_acceptance P hPid ρ hη_lt_one hacc
    (State.normalizePSD τM hτ htr).normalizedTraceDistance ρ ≤
      Real.sqrt η + η := by
  dsimp only
  let τM : CMatrix a := P * ρ.matrix * P
  have hτ : τM.PosSemidef := by
    simpa [τM] using projector_sandwich_posSemidef P hP ρ
  have htr : τM.trace.re ≠ 0 := by
    simpa [τM] using
      projector_sandwich_trace_re_ne_zero_of_acceptance P hPid ρ hη_lt_one hacc
  have htrace : τM.trace.re = ((P * ρ.matrix).trace).re := by
    simpa [τM] using projector_sandwich_trace_re_eq_acceptance P hPid ρ
  have htr_pos : 0 < τM.trace.re := by
    rw [htrace]
    exact lt_of_lt_of_le (by linarith : 0 < 1 - η) hacc
  have hacc_le_one : ((P * ρ.matrix).trace).re ≤ 1 := by
    have hkey : 0 ≤ (((1 - P) * ρ.matrix).trace).re :=
      cMatrix_trace_mul_posSemidef_re_nonneg
        (projector_one_sub_posSemidef P hP hPid) ρ.pos
    have hcyc : ((1 - P) * ρ.matrix).trace =
        (1 : ℂ) - (P * ρ.matrix).trace := by
      have : (1 - P) * ρ.matrix = ρ.matrix - P * ρ.matrix := by
        noncomm_ring
      rw [this, Matrix.trace_sub, ρ.trace_eq_one]
    rw [hcyc, Complex.sub_re, Complex.one_re] at hkey
    linarith
  have htr_le_one : τM.trace.re ≤ 1 := by
    rw [htrace]
    exact hacc_le_one
  have hgentle_eta : traceNorm (τM - ρ.matrix) ≤ 2 * Real.sqrt η := by
    have hgentle := gentle_projector P hP hPid ρ
    have hsqrt : Real.sqrt (1 - ((P * ρ.matrix).trace).re) ≤ Real.sqrt η := by
      refine Real.sqrt_le_sqrt ?_
      linarith [hη_nonneg]
    calc
      traceNorm (τM - ρ.matrix)
          = traceNorm (P * ρ.matrix * P - ρ.matrix) := by rfl
      _ ≤ 2 * Real.sqrt (1 - ((P * ρ.matrix).trace).re) := hgentle
      _ ≤ 2 * Real.sqrt η := by
        exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  have hcoeff_nonneg : 0 ≤ (τM.trace.re)⁻¹ - 1 := by
    have hone_le_inv : 1 ≤ (τM.trace.re)⁻¹ :=
      (one_le_inv₀ htr_pos).mpr htr_le_one
    linarith
  have hnorm_norm : traceNorm ((τM.trace.re)⁻¹ • τM - τM) ≤ η := by
    have hdiff : (τM.trace.re)⁻¹ • τM - τM =
        ((((τM.trace.re)⁻¹ - 1 : ℝ) : ℂ) • τM) := by
      ext i j
      simp [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
      ring
    have hscale :
        traceNorm ((τM.trace.re)⁻¹ • τM - τM) ≤
          ((τM.trace.re)⁻¹ - 1) * traceNorm τM := by
      rw [hdiff]
      exact traceNorm_real_smul_le hcoeff_nonneg τM
    have htrace_norm : traceNorm τM = τM.trace.re :=
      traceNorm_posSemidef_eq_trace_re τM hτ
    have hmul : ((τM.trace.re)⁻¹ - 1) * traceNorm τM =
        1 - τM.trace.re := by
      rw [htrace_norm]
      have hne : τM.trace.re ≠ 0 := htr
      field_simp [hne]
    have hrejection_le : 1 - τM.trace.re ≤ η := by
      rw [htrace]
      linarith
    calc
      traceNorm ((τM.trace.re)⁻¹ • τM - τM)
          ≤ ((τM.trace.re)⁻¹ - 1) * traceNorm τM := hscale
      _ = 1 - τM.trace.re := hmul
      _ ≤ η := hrejection_le
  have htri : traceNorm ((τM.trace.re)⁻¹ • τM - ρ.matrix) ≤
      traceNorm ((τM.trace.re)⁻¹ • τM - τM) +
        traceNorm (τM - ρ.matrix) := by
    have hdecomp : (τM.trace.re)⁻¹ • τM - ρ.matrix =
        ((τM.trace.re)⁻¹ • τM - τM) + (τM - ρ.matrix) := by
      ext i j
      simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    rw [hdecomp]
    exact traceNorm_add_le _ _
  calc
    (State.normalizePSD (P * ρ.matrix * P)
        (projector_sandwich_posSemidef P hP ρ)
        (projector_sandwich_trace_re_ne_zero_of_acceptance P hPid ρ hη_lt_one hacc)
      ).normalizedTraceDistance ρ
        = (1 / 2 : ℝ) * traceNorm ((τM.trace.re)⁻¹ • τM - ρ.matrix) := by
          simp [τM, State.normalizedTraceDistance, normalizedTraceDistance,
            traceNormDistance, State.normalizePSD_matrix]
    _ ≤ (1 / 2 : ℝ) *
        (traceNorm ((τM.trace.re)⁻¹ • τM - τM) +
          traceNorm (τM - ρ.matrix)) := by
          exact mul_le_mul_of_nonneg_left htri (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (η + 2 * Real.sqrt η) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact add_le_add hnorm_norm hgentle_eta
    _ ≤ Real.sqrt η + η := by
          nlinarith [hη_nonneg]

end

end QIT
