/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.GentleMeasurement
public import QIT.Coding.Classical.HayashiNagaoka
public import QIT.Measurements.SquareRootMeasurement
public import QIT.Coding.Classical.HSW
public import QIT.States.TraceNorm.PositivePart
public import QIT.Classical.Ensemble

/-!
# Packing lemma: coated operator and own-codeword error bound

Wilde's packing lemma controls the error probability of a classical code
`{c_m}` transmitted through a cq-channel by a square-root measurement built
from the codeword operators `{σ_{c_m}}`. The analysis splits the message
error into an *own-codeword* term `Tr{(I − Υ_{c_m}) σ_{c_m}}` (the squared
measurement fails to detect the transmitted codeword) and a *cross-codeword*
sum `Σ_{m'≠m} Tr{Υ_{c_{m'}} σ_{c_m}}` (the measurement confuses the
transmitted message with a different one).

This module introduces the **coated codeword operator**
`Υ_x = Π Π_x Π` — the codeword projector `Π_x` conjugated by the
typical-subspace projector `Π` — and proves the **own-codeword error bound**
`Re Tr{(I − Υ_x) σ_x} ≤ ε + 2√ε`, following the Wilde inequality chain:

```
Re Tr(Υ_x σ_x)
  = Re Tr(Π_x Π σ_x Π)                    [cyclicity of trace]
  ≥ Re Tr(Π_x σ_x) − ‖Π σ_x Π − σ_x‖₁    [trace-ineq-herm for effects]
  ≥ (1 − ε) − ‖Π σ_x Π − σ_x‖₁            [pack-2]
  ≥ (1 − ε) − 2√(1 − Re Tr(Π σ_x))        [gentle projector lemma]
  ≥ (1 − ε) − 2√ε                          [pack-1]
```

so that `Re Tr{(I − Υ_x) σ_x} = 1 − Re Tr(Υ_x σ_x) ≤ ε + 2√ε`.

The cross-codeword term is handled separately and is not proved here.
[Wilde2011Qst, qit-notes.tex:29680-29850] -/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v uIn uOut uEnsemble uMessage uAux

noncomputable section

/-- The coated codeword operator `Υ_x = Π Π_x Π`: the codeword projector
`Π_x` sandwiched by the typical-subspace projector `Π`. Coating by `Π`
ensures `Υ_x` is supported on the typical subspace while retaining the
spectral properties of `Π_x`. -/
noncomputable def PackingLemma.coatedOp {a : Type u} {𝒳 : Type v}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (P : CMatrix a) (Px : 𝒳 → CMatrix a) (x : 𝒳) : CMatrix a :=
  P * Px x * P

/-- The coated operator `Υ_x = Π Π_x Π` is positive semidefinite: it is the
conjugation `Πᴴ Π_x Π` of the PSD codeword projector `Π_x` by the typical-
subspace projector `Π` (Hermitian), hence PSD by `conjTranspose_mul_mul_same`.
[Wilde2011Qst, qit-notes.tex:29680-29850] -/
private lemma PackingLemma.coatedOp_posSemidef {a : Type u} {𝒳 : Type v}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (P : CMatrix a) (hP : P.PosSemidef) (Px : 𝒳 → CMatrix a)
    (hPx : ∀ x, (Px x).PosSemidef) (x : 𝒳) :
    (coatedOp P Px x).PosSemidef := by
  have hPstar : Matrix.conjTranspose P = P := hP.isHermitian.eq
  show (P * Px x * P).PosSemidef
  have hconj : (Matrix.conjTranspose P * Px x * P).PosSemidef :=
    (hPx x).conjTranspose_mul_mul_same P
  rwa [hPstar] at hconj

/-- The positive part of a Hermitian matrix is trace-dominated by the trace
norm: for Hermitian `H`, `Re Tr(H⁺) ≤ ‖H‖₁`. This follows because, by the
continuous functional calculus, `‖H‖₁ = Re Tr(|H|) = Re Tr(H⁺ + H⁻)` and
`Re Tr(H⁻) ≥ 0` (the negative part is positive semidefinite). -/
private lemma posPart_trace_le_traceNorm {a : Type u} [Fintype a] [DecidableEq a]
    (H : CMatrix a) (hH : H.IsHermitian) :
    (H⁺).trace.re ≤ traceNorm H := by
  -- `‖H‖₁` is definitionally `Re Tr(|H|)` where `|H| = CFC.abs H`.
  have hAbs : H⁺ + H⁻ = CFC.abs H := CFC.posPart_add_negPart H hH.isSelfAdjoint
  have hneg : H⁻.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hneg_tr : 0 ≤ (H⁻).trace.re := (Matrix.PosSemidef.trace_nonneg hneg).1
  have hkey : traceNorm H = (H⁺).trace.re + (H⁻).trace.re := by
    rw [show traceNorm H = (CFC.abs H).trace.re by rfl,
        show (CFC.abs H).trace.re = (H⁺ + H⁻).trace.re from by rw [← hAbs]]
    simp [Matrix.trace_add]
  rw [hkey]
  linarith

/-- Wilde's "trace-ineq-herm": for a measurement effect `E` (`0 ≤ E ≤ 1`) and
a Hermitian matrix `X`, `−‖X‖₁ ≤ Re Tr(X · E)`. This is the dual of
`hermitian_trace_mul_effect_le_posPart_trace` (applied to `−X`):
`Re Tr(−X · E) ≤ Re Tr((−X)⁺)`, hence `−Re Tr(X · E) ≤ Re Tr((−X)⁺) ≤ ‖X‖₁`. -/
private lemma re_trace_mul_effect_ge_neg_traceNorm {a : Type u}
    [Fintype a] [DecidableEq a] (E X : CMatrix a)
    (hEpos : E.PosSemidef) (hEle : E ≤ 1) (hX : X.IsHermitian) :
    - traceNorm X ≤ ((X * E).trace).re := by
  have hXneg_herm : (-X).IsHermitian := hX.neg
  -- Upper bound `Re Tr(−X · E)` by the positive-part trace of `−X`.
  have hupper :=
    hermitian_trace_mul_effect_le_posPart_trace (-X) E hXneg_herm hEpos hEle
  -- Rewrite `(-X) * E = -(X * E)` and unfold the trace.
  rw [Matrix.neg_mul] at hupper
  have htr_neg : (-(X * E)).trace = -(X * E).trace := Matrix.trace_neg (X * E)
  rw [htr_neg, Complex.neg_re] at hupper
  -- The positive part of `-X` is trace-dominated by `‖X‖₁` (and `‖-X‖₁ = ‖X‖₁`).
  have hle : ((-X)⁺).trace.re ≤ traceNorm X := by
    rw [← traceNorm_neg X]
    exact posPart_trace_le_traceNorm (-X) hXneg_herm
  -- Combine: `-Re Tr(X*E) ≤ Re Tr((-X)⁺) ≤ ‖X‖₁`.
  linarith

/-- Auxiliary: a PSD idempotent projector `P` satisfies `P ≤ 1` in the
Loewner order. The proof is the standard one: `1 - P` is Hermitian and
idempotent (`(1-P)² = 1 - P`), hence `1 - P = (1-P)ᴴ(1-P)` is PSD. -/
private lemma projector_le_one {a : Type u} [Fintype a] [DecidableEq a]
    (P : CMatrix a) (hP : P.PosSemidef) (hPid : P * P = P) :
    P ≤ 1 := by
  have hP_herm : P.IsHermitian := hP.isHermitian
  have h1P_herm : (1 - P).IsHermitian := (Matrix.isHermitian_one).sub hP_herm
  have h1P_conj : Matrix.conjTranspose (1 - P) = 1 - P := h1P_herm.eq
  have h1P_sq : (1 - P) * (1 - P) = 1 - P := by
    have e : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [e, hPid]; abel
  have hkey : (1 - P) = Matrix.conjTranspose (1 - P) * (1 - P) := by
    rw [h1P_conj, h1P_sq]
  -- Goal `P ≤ 1` is definitionally `(1 - P).PosSemidef`; rewrite the goal
  -- into the conjugate-square form and conclude via the PSD product lemma.
  show (1 - P).PosSemidef
  rw [hkey]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

/-- If `Π` is a projector and `Π_x ≤ 1`, the coated operator satisfies
`Υ_x = Π Π_x Π ≤ Π Π Π = Π ≤ 1`. The deficit `Π − Π Π_x Π = Π (1 − Π_x) Π` is
PSD (conjugation of the PSD `1 − Π_x`), and `Π ≤ 1` (projector).
[Wilde2011Qst, qit-notes.tex:29680-29850] -/
private lemma PackingLemma.coatedOp_le_one {a : Type u} {𝒳 : Type v}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (P : CMatrix a) (hP : P.PosSemidef) (hPid : P * P = P)
    (Px : 𝒳 → CMatrix a) (hPxle1 : ∀ x, Px x ≤ 1) (x : 𝒳) :
    coatedOp P Px x ≤ 1 := by
  have hP_le_one : P ≤ 1 := projector_le_one P hP hPid
  -- `P − P·(Px x)·P = P·(1 − Px x)·P` is PSD (conjugation of `1 − Px x`).
  have hDiff : (P - P * Px x * P).PosSemidef := by
    have h1Px_psd : (1 - Px x).PosSemidef := hPxle1 x
    have hPstar : Matrix.conjTranspose P = P := hP.isHermitian.eq
    -- `(Pᴴ) · (1 − Px x) · P = P · (1 − Px x) · P = P − P·Px x·P`.
    have hPP1P : Matrix.conjTranspose P * (1 - Px x) * P = P - P * Px x * P := by
      rw [hPstar, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hPid]
    have hconj : (Matrix.conjTranspose P * (1 - Px x) * P).PosSemidef :=
      h1Px_psd.conjTranspose_mul_mul_same P
    rw [← hPP1P]; exact hconj
  have hU_le_P : coatedOp P Px x ≤ P := Matrix.le_iff.mpr hDiff
  exact le_trans hU_le_P hP_le_one

/-- Auxiliary: for a measurement effect `E` (`E ≤ 1`) and a state `ρ`, the
detection probability is at most one: `Re Tr(E ρ) ≤ 1`. The deficit
`1 - Re Tr(E ρ) = Re Tr((I - E) ρ)` is nonnegative because `I - E` is PSD
and conjugation by `√ρ` preserves positivity, so
`Re Tr((I-E) ρ) = Re Tr(√ρ (I-E) √ρ) ≥ 0`. -/
private lemma re_trace_effect_state_le_one {a : Type u} [Fintype a] [DecidableEq a]
    (E : CMatrix a) (hEle : E ≤ 1) (ρ : State a) :
    ((E * ρ.matrix).trace).re ≤ 1 := by
  -- `D := I - E` is PSD (effect hypothesis); conjugate by `√ρ`.
  have hD_psd : (1 - E).PosSemidef := hEle
  set S : CMatrix a := psdSqrt ρ.matrix
  have hS_herm : S.IsHermitian := psdSqrt_isHermitian ρ.matrix
  have hSS : S * S = ρ.matrix := psdSqrt_mul_self_of_posSemidef ρ.pos
  have hconj_psd : (S * (1 - E) * S).PosSemidef := by
    have h := hD_psd.mul_mul_conjTranspose_same S
    rw [show Matrix.conjTranspose S = S from hS_herm.eq] at h
    exact h
  have htr_nonneg : 0 ≤ ((S * (1 - E) * S).trace).re :=
    (Matrix.PosSemidef.trace_nonneg hconj_psd).1
  -- `Re Tr(√ρ (I-E) √ρ) = Re Tr((I-E) ρ) = Re Tr(ρ) - Re Tr(E ρ)`.
  have hcyc : (S * (1 - E) * S).trace = (ρ.matrix * (1 - E)).trace := by
    rw [Matrix.trace_mul_cycle, ← hSS]
  rw [hcyc] at htr_nonneg
  have hDr_comm : (ρ.matrix * (1 - E)).trace = ((1 - E) * ρ.matrix).trace := by
    rw [Matrix.trace_mul_comm]
  rw [hDr_comm] at htr_nonneg
  -- `((1-E) ρ).trace = ρ.trace - (E ρ).trace` via `sub_mul` / `one_mul`.
  have hsplit : ((1 - E) * ρ.matrix).trace = ρ.matrix.trace - (E * ρ.matrix).trace := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  rw [hsplit, Complex.sub_re] at htr_nonneg
  -- `ρ.trace = 1`, so `0 ≤ 1 - Re Tr(E ρ)`, i.e. `Re Tr(E ρ) ≤ 1`.
  have hρ_one : ρ.matrix.trace.re = 1 := by rw [ρ.trace_eq_one]; simp
  linarith

/-- **Own-codeword error bound** (Wilde's packing lemma, first term). For a
typical-subspace projector `Π`, codeword projectors `{Π_x}`, codeword states
`{σ_x}`, and detection deficit `ε` satisfying the packing hypotheses
`pack-1` (`Re Tr(Π σ_x) ≥ 1 − ε`) and `pack-2` (`Re Tr(Π_x σ_x) ≥ 1 − ε`),
the coated operator `Υ_x = Π Π_x Π` leaves only an `ε + 2√ε` deficit:
`Re Tr{(I − Υ_x) σ_x} ≤ ε + 2√ε`.

The proof follows Wilde's chain: cyclicity of trace rewrites
`Re Tr(Υ_x σ_x) = Re Tr(Π_x Π σ_x Π)`; the trace-ineq-herm bound lowers this
by `‖Π σ_x Π − σ_x‖₁`; pack-2 and the gentle projector lemma bound that trace
norm by `2√(1 − Re Tr(Π σ_x))`; and pack-1 reduces the surd to `2√ε`.
[Wilde2011Qst, qit-notes.tex:29680-29850] -/
theorem PackingLemma.ownTerm_bound {a : Type u} {𝒳 : Type v}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (P : CMatrix a) (hP : P.PosSemidef) (hPid : P * P = P)
    (Px : 𝒳 → CMatrix a) (hPx : ∀ x, (Px x).PosSemidef)
    (hPxid : ∀ x, Px x * Px x = Px x)
    (σ : 𝒳 → State a) (ε : ℝ) (hε : 0 ≤ ε)
    (h1 : ∀ x, 1 - ε ≤ ((P * (σ x).matrix).trace).re)
    (h2 : ∀ x, 1 - ε ≤ ((Px x * (σ x).matrix).trace).re) :
    ∀ x, (((1 - PackingLemma.coatedOp P Px x) * (σ x).matrix).trace).re
        ≤ ε + 2 * Real.sqrt ε := by
  intro x
  -- Shorthand for the coated operator and the codeword state's matrix.
  set U : CMatrix a := P * Px x * P with hU_def
  set ρx : CMatrix a := (σ x).matrix
  -- Hermiticity needed for the trace-ineq-herm step.
  have hP_herm : P.IsHermitian := hP.isHermitian
  have hρx_herm : ρx.IsHermitian := (σ x).pos.isHermitian
  -- The deviation `X := P ρ P − ρ` is Hermitian (`(P ρ P)ᴴ = Pᴴ ρᴴ Pᴴ = P ρ P`).
  have hX_herm : (P * ρx * P - ρx).IsHermitian := by
    have h1 : (P * ρx * P).IsHermitian := by
      show Matrix.conjTranspose (P * ρx * P) = _
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        show Matrix.conjTranspose P = P from hP_herm.eq,
        show Matrix.conjTranspose ρx = ρx from hρx_herm.eq,
        Matrix.mul_assoc]
    exact h1.sub hρx_herm
  -- `Px x` and `P` are effects (projectors ⇒ `≤ 1`).
  have hPx_le_one : Px x ≤ 1 := projector_le_one (Px x) (hPx x) (hPxid x)
  -- Gentle projector lemma: `‖P ρ P − ρ‖₁ ≤ 2√(1 − Re Tr(P ρ))`.
  have hgentle : traceNorm (P * ρx * P - ρx)
      ≤ 2 * Real.sqrt (1 - ((P * ρx).trace).re) :=
    gentle_projector P hP hPid (σ x)
  -- Step 1 (cyclicity): `Re Tr(U ρ) = Re Tr(Px P ρ P)`, since
  -- `Tr(P · Px · P · ρ) = Tr(Px · P · ρ · P)` (rotate the leading `P` to the end).
  have hcycle : (U * ρx).trace = (Px x * (P * ρx * P)).trace := by
    rw [hU_def]
    -- `Tr(P · (Px x · P · ρx)) = Tr((Px x · P · ρx) · P)` by commutativity.
    rw [show P * Px x * P * ρx = P * (Px x * P * ρx) from by noncomm_ring]
    rw [Matrix.trace_mul_comm]
    show (Px x * P * ρx * P).trace = (Px x * (P * ρx * P)).trace
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  -- Step 2 (trace-ineq-herm with effect `Px x`, Hermitian `P ρ P − ρ`):
  -- `Re Tr((PρP − ρ) Px) ≥ −‖PρP − ρ‖₁`. Decompose by linearity and cycle.
  have hcrux : - traceNorm (P * ρx * P - ρx)
      ≤ ((Px x * (P * ρx * P)).trace).re - ((Px x * ρx).trace).re := by
    have hstep :=
      re_trace_mul_effect_ge_neg_traceNorm (Px x) (P * ρx * P - ρx)
        (hPx x) hPx_le_one hX_herm
    -- Expand `(PρP − ρ) Px = PρP·Px − ρ·Px` and split the trace.
    have hmul : (P * ρx * P - ρx) * Px x = P * ρx * P * Px x - ρx * Px x := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [hmul, Matrix.trace_sub, Complex.sub_re] at hstep
    -- `Re Tr(PρP·Px) = Re Tr(Px·PρP)` by trace commutativity.
    have hcomm : ((P * ρx * P * Px x).trace).re = ((Px x * (P * ρx * P)).trace).re := by
      have heq : (P * ρx * P * Px x).trace = (Px x * (P * ρx * P)).trace :=
        Matrix.trace_mul_comm _ _
      rw [heq]
    rw [hcomm] at hstep
    -- `Re Tr(ρ·Px) = Re Tr(Px·ρ)` by trace commutativity.
    have hcomm2 : ((ρx * Px x).trace).re = ((Px x * ρx).trace).re := by
      have heq : (ρx * Px x).trace = (Px x * ρx).trace := Matrix.trace_mul_comm _ _
      rw [heq]
    rw [hcomm2] at hstep
    exact hstep
  -- Combine steps 1–2 with pack-2:
  -- `Re Tr(U ρ) ≥ Re Tr(Px ρ) − ‖PρP − ρ‖₁ ≥ (1−ε) − ‖PρP − ρ‖₁`.
  have hpack2 := h2 x
  have hU_re : ((U * ρx).trace).re
      ≥ (1 - ε) - traceNorm (P * ρx * P - ρx) := by
    have hU_eq : ((U * ρx).trace).re = ((Px x * (P * ρx * P)).trace).re := by
      rw [hcycle]
    rw [hU_eq]
    linarith [hcrux, hpack2]
  -- Step 3 (gentle projector): bound `‖PρP − ρ‖₁` by `2√(1 − Re Tr(Pρ))`.
  have hU_re' : ((U * ρx).trace).re
      ≥ (1 - ε) - 2 * Real.sqrt (1 - ((P * ρx).trace).re) := by
    linarith [hgentle]
  -- Step 4 (pack-1 + monotonicity): `1 − Re Tr(Pρ) ≤ ε`, so the surd ≤ √ε.
  have hpack1 := h1 x
  have hP_le_one : P ≤ 1 := projector_le_one P hP hPid
  have hPρ_le_one : ((P * ρx).trace).re ≤ 1 :=
    re_trace_effect_state_le_one P hP_le_one (σ x)
  have hdef_le : 1 - ((P * ρx).trace).re ≤ ε := by linarith
  -- `Real.sqrt_le_sqrt : √x ≤ √y ↔ x ≤ y`. The regime `0 ≤ ε` (hypothesis
  -- `hε`) is the meaningful range of the bound `ε + 2√ε`; `0 ≤ √ε` there.
  have hsqr_le : Real.sqrt (1 - ((P * ρx).trace).re) ≤ Real.sqrt ε :=
    Real.sqrt_le_sqrt hdef_le
  -- `hε` also keeps `√ε` a genuine magnitude (`0 ≤ √ε`).
  have _ : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have _ : (0 : ℝ) ≤ ε := hε
  have hU_re'' : ((U * ρx).trace).re ≥ (1 - ε) - 2 * Real.sqrt ε := by
    linarith
  -- Final: `Re Tr((I − U) ρ) = Re Tr(ρ) − Re Tr(U ρ) = 1 − Re Tr(U ρ) ≤ ε + 2√ε`.
  have hsplit_one_minus :
      ((1 - U) * ρx).trace = ρx.trace - (U * ρx).trace := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  calc (((1 - U) * ρx).trace).re
      = (ρx.trace - (U * ρx).trace).re := by rw [hsplit_one_minus]
    _ = 1 - ((U * ρx).trace).re := by rw [(σ x).trace_eq_one]; simp
    _ ≤ 1 - ((1 - ε) - 2 * Real.sqrt ε) := by linarith
    _ = ε + 2 * Real.sqrt ε := by ring

/-! ## Random-code expectation and pair-independence

The packing-lemma random-code argument averages the per-codeword error bound
over all codes `𝒞 : 𝒳 → 𝒳` drawn iid from the distribution `p`. Because QIT
has no probability monad, we build the expectation directly as the finite sum
`𝔼_𝒞{f} = Σ_𝒞 (∏_m p(𝒞_m))·f(𝒞)`. The only nontrivial fact we need is the
iid *pair-independence* factorization: the joint law of `(𝒞_m, 𝒞_m')` is the
product `p ⊗ p`, so `𝔼_𝒞{g(𝒞_m, 𝒞_m')} = Σ_{x,x'} p(x) p(x') g(x,x')`.
[Wilde2011Qst, qit-notes.tex:29680-29850] -/

/-- Expectation of `f : (M → 𝒳) → ℝ` over iid random codes drawn from the
distribution `p`, i.e. `𝔼_𝒞{f} = Σ_{𝒞 : M→𝒳} (∏_m p(𝒞_m)) · f(𝒞)`. The
product factor `∏_m p(𝒞_m)` is the iid mass of the code `𝒞`.
[Wilde2011Qst, qit-notes.tex:29750-29780] -/
noncomputable def PackingLemma.codeExpectation
    {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype 𝒳] [DecidableEq 𝒳] [Fintype M] [DecidableEq M]
    (p : 𝒳 → ℝ) (f : (M → 𝒳) → ℝ) : ℝ :=
  ∑ C : M → 𝒳, (∏ m : M, p (C m)) * f C

/-- One-coordinate marginal of the random-code expectation: a functional
depending only on the `m`-th codeword averages to the one-variable mean
`Σ_x p(x)·h(x)`. This is the Fubini/tensorization step for the iid product
measure: every coordinate `k ≠ m` contributes `Σ_{x_k} p(x_k) = 1`, leaving
only the `m`-th marginal.
[Wilde2011Qst, qit-notes.tex:29750-29780] -/
private lemma PackingLemma.codeExpectation_marginal
    {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype 𝒳] [DecidableEq 𝒳] [Fintype M] [DecidableEq M]
    (p : 𝒳 → ℝ) (hpsum : ∑ x, p x = 1) (m : M) (h : 𝒳 → ℝ) :
    codeExpectation p (fun C => h (C m)) = ∑ x, p x * h x := by
  -- Per-coordinate factor `φ k x = p x · (h x if k = m else 1)`, so that the
  -- summand `∏_k p(𝒞_k) · h(𝒞_m)` equals `∏_k φ k (𝒞_k)`.
  set φ : ∀ k : M, 𝒳 → ℝ := fun k x => p x * (if k = m then h x else 1)
  -- (1) Summand identity: `∏_k p(𝒞_k) · h(𝒞_m) = ∏_k φ k (𝒞_k)`.
  have hsummand : ∀ C : M → 𝒳, (∏ k, p (C k)) * h (C m) = ∏ k, φ k (C k) := by
    intro C
    rw [Finset.prod_mul_distrib]
    -- Collapse the selection product `∏_k (if k=m then h(C k) else 1)` to `h(C m)`:
    -- filter `univ` down to the singleton `{m}` and read off the single factor.
    have hsel : ∏ k, (if k = m then h (C k) else (1 : ℝ)) = h (C m) := by
      classical
      rw [← Finset.prod_filter (p := (· = m)),
          Finset.filter_eq' _ m, if_pos (Finset.mem_univ _),
          Finset.prod_singleton]
    rw [hsel]
  -- (2) Re-index the function-type sum as a product of per-coordinate sums via
  -- `prod_univ_sum` (read right-to-left): `Σ_𝒞 ∏_k φ k (𝒞_k) = ∏_k Σ_x φ k x`.
  -- Swap the summand to the product form, then reindex `Σ_{𝒞 : M→𝒳}` to
  -- `Σ_{𝒞 ∈ piFinset univ}`, which equals `Σ_{𝒞 ∈ univ}`.
  unfold codeExpectation
  simp only []
  refine (Finset.sum_congr rfl (fun C _ => hsummand C)).trans ?_
  -- `Finset.univ` for `M → 𝒳` is `Fintype.piFinset (fun _ => univ)` definitionally;
  -- expose it via the symmetric identity, then apply `prod_univ_sum`.
  have huniv : (Finset.univ : Finset (M → 𝒳)) =
      Fintype.piFinset (fun _ : M => (Finset.univ : Finset 𝒳)) :=
    (Fintype.piFinset_univ (α := M) (β := fun _ : M => 𝒳)).symm
  rw [huniv, ← Finset.prod_univ_sum (t := fun _ : M => (Finset.univ : Finset 𝒳))]
  -- (3) Evaluate each factor: the `m`-th factor is `Σ_x p x·h x`, every other
  -- factor is `Σ_x p x = 1`; the whole product therefore collapses to the
  -- `m`-th factor. Pull the `m`-th factor out via `prod_erase_mul`, then
  -- discharge each remaining factor with `Σ_x p x = 1`.
  have hm : ∑ x, φ m x = ∑ x, p x * h x := by
    simp only [φ, if_true]
  have ho : ∀ k : M, k ≠ m → ∑ x, φ k x = 1 := by
    intro k hk
    have hφ : φ k = fun x => p x := by
      funext x; simp only [φ, if_neg hk, mul_one]
    rw [hφ, ← hpsum]
  have hmem : m ∈ (Finset.univ : Finset M) := Finset.mem_univ _
  rw [← Finset.prod_erase_mul Finset.univ (fun k => ∑ x, φ k x) hmem,
      Finset.prod_eq_one (fun k hk => ho k (Finset.mem_erase.mp hk).1),
      one_mul, hm]

/-- Pair-independence factorization for iid random codes: the joint law of
`(𝒞_m, 𝒞_m')` for `m ≠ m'` is the product distribution `p ⊗ p`, hence
`𝔼_𝒞{g(𝒞_m, 𝒞_m')} = Σ_{x,x'} p(x)·p(x')·g(x,x')`. This follows by applying
the one-coordinate marginal twice: marginalize `𝒞_m'` first (treating
`𝒞_m` as part of the rest), then marginalize `𝒞_m`.
[Wilde2011Qst, qit-notes.tex:29750-29780] -/
theorem PackingLemma.codeExpectation_pair_indep
    {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype 𝒳] [DecidableEq 𝒳] [Fintype M] [DecidableEq M]
    (p : 𝒳 → ℝ) (hpsum : ∑ x, p x = 1) (m : M) (m' : M) (hmm' : m ≠ m')
    (g : 𝒳 → 𝒳 → ℝ) :
    codeExpectation p (fun C => g (C m) (C m')) = ∑ x, ∑ x', p x * p x' * g x x' := by
  -- Split off the `m`-coordinate via `funSplitAt`; the residual code on
  -- `{j // j ≠ m}` is itself iid, so the one-coordinate marginal applies to it
  -- on the `m'`-th residual coordinate.
  classical
  set R := {j : M // j ≠ m}
  set mr : R := ⟨m', hmm'.symm⟩
  set e : (M → 𝒳) ≃ 𝒳 × (R → 𝒳) := Equiv.funSplitAt m 𝒳
  -- `e C = (C m, C|_{j ≠ m})` and `e.symm (xm, rest) = ` the recombined code.
  have heC (C : M → 𝒳) : (e C).1 = C m ∧ ∀ k : R, (e C).2 k = C k.1 := by
    constructor
    · show ((Equiv.funSplitAt m 𝒳) C).1 = C m
      simp only [Equiv.funSplitAt_apply]
    · intro k
      show ((Equiv.funSplitAt m 𝒳) C).2 k = C k.1
      simp only [Equiv.funSplitAt_apply]
  have heC_mr (C : M → 𝒳) : C m' = (e C).2 mr := by
    have h : (e C).2 mr = C mr.1 := (heC C).2 mr
    exact h.symm
  have hprd (C : M → 𝒳) : (∏ k : M, p (C k)) = p (C m) * ∏ k : R, p (C k.1) := by
    have hmem : m ∈ (Finset.univ : Finset M) := Finset.mem_univ _
    have hsub : ∀ j : M, j ∈ (Finset.univ : Finset M).erase m ↔ j ≠ m := fun j =>
      Finset.mem_erase.trans <| by simp
    rw [show (∏ k : M, p (C k)) =
            (∏ k ∈ (Finset.univ : Finset M).erase m, p (C k)) * p (C m) from
        (Finset.prod_erase_mul _ _ hmem).symm,
      Finset.prod_subtype (s := (Finset.univ : Finset M).erase m) hsub]
    ac_rfl
  -- Reindex the code sum via the bijection `e`.
  show ∑ C : M → 𝒳, (∏ k, p (C k)) * g (C m) (C m') = _
  rw [show (∑ C : M → 𝒳, (∏ k, p (C k)) * g (C m) (C m')) =
        ∑ Cr : 𝒳 × (R → 𝒳), p Cr.1 * (∏ k : R, p (Cr.2 k)) * g Cr.1 (Cr.2 mr) from
      Fintype.sum_bijective e e.bijective
        (fun C => (∏ k, p (C k)) * g (C m) (C m'))
        (fun Cr => p Cr.1 * (∏ k : R, p (Cr.2 k)) * g Cr.1 (Cr.2 mr))
        (by
          intro C
          dsimp only
          rw [heC_mr C, hprd C]
          have h1 : (e C).1 = C m := (heC C).1
          have h2 : ∀ k : R, (e C).2 k = C k.1 := (heC C).2
          rw [h1]; simp only [← h2])]
  -- The sum is now `Σ_{(xm, rest)} p xm · (∏_{k:R} p(rest k)) · g xm (rest mr)`.
  -- Split the product-typed sum into nested sums via `Fintype.sum_prod_type`,
  -- then apply the one-coordinate marginal to the inner `rest`-sum on `mr`.
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun xm _ => ?_)
  -- Reduce the `(xm, y)` projections (`(xm, y).1 = xm`, `(xm, y).2 = y`).
  show ∑ y : R → 𝒳, (p xm * ∏ k, p (y k)) * g xm (y mr) = _
  -- Reassociate each summand so `p xm` factors out: `p xm * ((∏_k p) · g)`.
  refine (Finset.sum_congr rfl (fun y _ => by ac_rfl)).trans ?_
  rw [← Finset.mul_sum,
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  -- Inner sum is the one-coordinate marginal on the residual code, coordinate `mr`.
  have hmarg := codeExpectation_marginal (𝒳 := 𝒳) (M := R) p hpsum mr (g xm)
  simp only [codeExpectation] at hmarg
  rw [hmarg, Finset.mul_sum]
  ring_nf

/-! ## Cross-codeword expectation bound

The cross-codeword term `Re Tr(Υ_{c_{m'}} σ_{c_m})`, averaged over the random
code, factorizes via pair-independence into a single ℂ-level trace
`Re Tr(Φ Π σ̄ Π)` (with `Φ = Σ_{x'} p(x')·Π_{x'}` and `σ̄ = E.averageState`),
then decays as `d / D` by the packing hypotheses `pack-4` (`Π σ̄ Π ≤ D⁻¹·Π`),
`Π ≤ 1`, `pack-3` (`Tr Π_x ≤ d`), and `weights_sum`.
[Wilde2011Qst, qit-notes.tex:29680-29850] -/

/-- Auxiliary: the real part of a finite `ℂ`-sum is the finite `ℝ`-sum of the
real parts. -/
private lemma re_sum_eq_sum_re {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.sum_cons, Complex.add_re, Finset.sum_cons, ih]

/-- **Cross-codeword expectation bound** (Wilde's packing lemma, second term).
For an ensemble `E` of codeword states, the typical-subspace projector `Π`
(PSD, idempotent, `Π ≤ 1`), codeword projectors `{Π_x}`, and the packing
hypotheses `pack-3` (`Re Tr(Π_x) ≤ d`) and `pack-4` (`Π σ̄ Π ≤ D⁻¹·Π`, where
`σ̄ = E.averageState`), the random-code expectation of the cross-codeword
detection term decays as `d / D`:

`𝔼_𝒞{ Re Tr(Υ_{𝒞_{m'}} σ_{𝒞_m}) } ≤ d / D`.

The proof linearizes the bilinear trace at the `ℂ` level first (cyclicity
`Tr(Π Π_{x'} Π σ_x) = Tr(Π_{x'} Π σ_x Π)`, then `Finset.sum_mul` /
`Matrix.trace_sum` to pull `Σ_x p(x) σ_x` and `Σ_{x'} p(x') Π_{x'}` out of
the trace into `Tr(Φ Π σ̄ Π)`), and only projects to `ℝ` once via
`re_sum_eq_sum_re`. The two Loewner-order steps use
`cMatrix_trace_mul_posSemidef_re_nonneg` on `Φ·(D⁻¹·Π − Πσ̄Π)` (PSD by
pack-4) and on `Φ·(1 − Π)` (PSD because `Π ≤ 1`).
[Wilde2011Qst, qit-notes.tex:29680-29850] -/
theorem PackingLemma.crossTerm_expectation_bound
    {a : Type u} {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype M] [DecidableEq M]
    (E : Ensemble 𝒳 a) (P : CMatrix a) (_hP : P.PosSemidef) (_hPid : P * P = P)
    (hP_le_one : P ≤ 1)
    (Px : 𝒳 → CMatrix a) (hPx : ∀ x, (Px x).PosSemidef)
    (d D : ℝ) (hD : 0 < D)
    (hpack3 : ∀ x, ((Px x).trace).re ≤ d)
    (hpack4 : P * E.averageState.matrix * P ≤ ((D : ℝ)⁻¹) • P)
    (m : M) (m' : M) (hmm' : m ≠ m') :
    codeExpectation (fun x => (E.probs x : ℝ))
      (fun C => ((coatedOp P Px (C m') * (E.states (C m)).matrix).trace).re) ≤ d / D := by
  -- Distribution `p x = (E.probs x : ℝ)`; its mass sums to `1` (`weights_sum`).
  set p : 𝒳 → ℝ := fun x => (E.probs x : ℝ) with hp_def
  have hpsum : ∑ x, p x = 1 := by
    simp only [hp_def]; exact_mod_cast E.weights_sum
  have hp_nonneg : ∀ x, 0 ≤ p x := fun x => NNReal.coe_nonneg (E.probs x)
  -- Codeword states `σ_x` as matrices.
  set σx : 𝒳 → CMatrix a := fun x => (E.states x).matrix with hσx_def
  -- Step 1: marginalize the random code via pair-independence. The functional
  -- depends only on `(𝒞_m, 𝒞_m')`, so `𝔼_𝒞{g(𝒞_m,𝒞_m')} = Σ_{x,x'} p x p x' g x x'`.
  set g : 𝒳 → 𝒳 → ℝ := fun x x' =>
    ((coatedOp P Px x' * σx x).trace).re with hg_def
  rw [show codeExpectation p (fun C => g (C m) (C m')) =
        ∑ x, ∑ x', p x * p x' * g x x' from
      codeExpectation_pair_indep p hpsum m m' hmm' g]
  -- Step 2: cyclicity of trace. `coatedOp P Px x' = P Px x' P`, so
  -- `Tr((P Px x' P) σ_x) = Tr(Px x' P σ_x P)` (rotate the leading `P` to the end).
  have hcyc : ∀ x x',
      (coatedOp P Px x' * σx x).trace = (Px x' * (P * σx x * P)).trace := by
    intro x x'
    show (P * Px x' * P * σx x).trace = (Px x' * (P * σx x * P)).trace
    rw [show P * Px x' * P * σx x = P * (Px x' * (P * σx x)) from by noncomm_ring,
        Matrix.trace_mul_comm]
    show (Px x' * (P * σx x) * P).trace = (Px x' * (P * σx x * P)).trace
    ac_rfl
  -- The ℂ-level linearization target. Define
  -- `Φ = Σ_{x'} p(x') · Px x'` and `σ̄ = Σ_x p(x) · σ_x` (both as `CMatrix`).
  set Φ : CMatrix a := ∑ x', p x' • Px x' with hΦ_def
  set σbar : CMatrix a := ∑ x, p x • σx x with hσbar_def
  -- `σ̄` coincides with `E.averageState.matrix` (the ensemble's mean state).
  have hσbar_avg : σbar = E.averageState.matrix := by
    rw [hσbar_def, E.averageState_matrix, hp_def, hσx_def]
    simp only [NNReal.smul_def]
  -- Step 3 (key ℂ-level identity): `Σ_{x,x'} p x p x' Tr(Px x' P σ_x P) = Tr(Φ P σ̄ P)`,
  -- proved at the `ℂ` level; project to `ℝ` once at the end.
  -- For each fixed `x`: `Tr(Φ · (P σ_x P)) = Σ_{x'} p x' Tr(Px x' · (P σ_x P))`
  -- by `ℂ`-linearity of `Tr` (`sum_mul`, `trace_sum`, `trace_smul`).
  have hinner : ∀ x, (Φ * (P * σx x * P)).trace =
      ∑ x', p x' • (Px x' * (P * σx x * P)).trace := by
    intro x
    set X := P * σx x * P
    -- `(Σ_{x'} p x' • Px x') · X = Σ_{x'} p x' • (Px x' · X)`, then trace-distribute.
    have hprod : (∑ x', p x' • Px x') * X = ∑ x', p x' • (Px x' * X) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x' _ => Matrix.smul_mul _ _ _)
    rw [show Φ = ∑ x', p x' • Px x' from hΦ_def, hprod, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun x' _ => Matrix.trace_smul _ _)
  -- `Tr(Φ P σ̄ P) = Σ_{x,x'} (p x p x') • Tr(Px x' P σ_x P)` (the FLAT ℂ-sum).
  -- Pull `Σ_x p x σ_x` out of the middle factor, then apply `hinner` per `x`.
  have hlin : (Φ * P * σbar * P).trace =
      ∑ x, ∑ x', (p x * p x') • (Px x' * (P * σx x * P)).trace := by
    -- `(Φ*P) · (Σ_x p x σ_x) · P = Σ_x p x • ((Φ*P) σ_x P) = Σ_x p x • (Φ (P σ_x P))`.
    have hprod : (Φ * P) * (∑ x, p x • σx x : CMatrix a) * P =
        ∑ x, p x • (Φ * (P * σx x * P)) := by
      -- Distribute both the leading `(Φ*P)` and the trailing `P` over the sum.
      have key : ∀ x, (Φ * P) * (p x • σx x) * P = p x • (Φ * (P * σx x * P)) := by
        intro x
        rw [Matrix.mul_smul, Matrix.smul_mul]
        ac_rfl
      conv =>
        congr
        · rw [show (Φ * P) * (∑ x, p x • σx x : CMatrix a) =
              ∑ x, (Φ * P) * (p x • σx x) from
            Finset.mul_sum Finset.univ (fun x => p x • σx x) (Φ * P)]
        · rfl
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x _ => key x)
    rw [show σbar = ∑ x, p x • σx x from hσbar_def,
        show (Φ * P * σbar * P) = (Φ * P) * σbar * P from rfl, hprod, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.trace_smul, hinner x, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    rw [smul_smul, mul_comm]
  -- Step 4: project to `ℝ` once. With `g x x' = Re Tr(coatedOp · σ_x) =
  -- Re Tr(Px x' P σ_x P)` (by `hcyc`), the double sum equals `Re Tr(Φ P σ̄ P)`.
  have hg_rew : ∀ x x', g x x' = (Px x' * (P * σx x * P)).trace.re := by
    intro x x'
    show (coatedOp P Px x' * σx x).trace.re = (Px x' * (P * σx x * P)).trace.re
    rw [hcyc]
  -- Bridge: `(c : ℝ) * z.re = (c • z).re` (used to lift the ℝ-sum to a ℂ-sum's `.re`).
  have hre_smul (c : ℝ) (z : ℂ) : c * z.re = (c • z).re := by
    rw [Complex.real_smul]; simp [Complex.mul_re]
  have hsum_re : (∑ x, ∑ x', p x * p x' * g x x') = (Φ * P * σbar * P).trace.re := by
    -- Rewrite each `g x x'` to `.re` form.
    have hrew : (∑ x, ∑ x', p x * p x' * g x x') =
        (∑ x, ∑ x', p x * p x' * (Px x' * (P * σx x * P)).trace.re) := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
      rw [hg_rew]
    -- Lift each ℝ-summand to the real part of a ℂ-smul summand.
    have hflat : (∑ x, ∑ x', p x * p x' * (Px x' * (P * σx x * P)).trace.re) =
        (∑ x, ∑ x', (p x * p x') • (Px x' * (P * σx x * P)).trace).re := by
      rw [re_sum_eq_sum_re]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [re_sum_eq_sum_re]
      refine Finset.sum_congr rfl (fun x' _ => hre_smul _ _)
    rw [hrew, hflat, ← hlin]
  rw [hsum_re]
  clear hsum_re hg_rew hinner hre_smul
  -- Step 5: pack-4 `P σ̄ P ≤ D⁻¹ · P` ⇒ `Re Tr(Φ P σ̄ P) ≤ Re Tr(Φ (D⁻¹ · P))`.
  have hDiff_psd : (((D : ℝ)⁻¹) • P - P * E.averageState.matrix * P).PosSemidef := by
    have heq : ((D : ℝ)⁻¹) • P - P * E.averageState.matrix * P =
        ((D : ℝ)⁻¹) • P - P * σbar * P := by rw [hσbar_avg]
    rw [heq]; exact Matrix.le_iff.mp hpack4
  have hΦ_psd : Φ.PosSemidef := by
    have hΦ_nonneg : 0 ≤ (∑ x', p x' • Px x') :=
      Finset.sum_nonneg (fun i _ =>
        Matrix.PosSemidef.nonneg (Matrix.PosSemidef.smul (hPx i) (hp_nonneg i)))
    have hΦ_eq : (∑ x', p x' • Px x') = Φ := hΦ_def.symm
    rw [hΦ_eq] at hΦ_nonneg
    exact Matrix.nonneg_iff_posSemidef.mp hΦ_nonneg
  have hΦDiff : ((Φ * (((D : ℝ)⁻¹) • P - P * E.averageState.matrix * P)).trace).re ≥ 0 :=
    cMatrix_trace_mul_posSemidef_re_nonneg hΦ_psd hDiff_psd
  have htr_split : (Φ * (((D : ℝ)⁻¹) • P)).trace.re -
        (Φ * (P * E.averageState.matrix * P)).trace.re =
      ((Φ * (((D : ℝ)⁻¹) • P - P * E.averageState.matrix * P)).trace).re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have heq_LHS : (Φ * P * σbar * P).trace = (Φ * (P * E.averageState.matrix * P)).trace := by
    rw [hσbar_avg]; ac_rfl
  rw [heq_LHS]
  have hstep5 : (Φ * (P * E.averageState.matrix * P)).trace.re ≤
      (Φ * (((D : ℝ)⁻¹) • P)).trace.re := by linarith
  -- Step 6: `Re Tr(Φ (D⁻¹ · P)) = D⁻¹ · Re Tr(Φ P)` by cyclicity + `ℂ`-linearity.
  have htr_Dinv : (Φ * (((D : ℝ)⁻¹) • P)).trace = ((D : ℝ)⁻¹) • (Φ * P).trace := by
    rw [Matrix.trace_mul_comm Φ ((D : ℝ)⁻¹ • P), Matrix.smul_mul,
        Matrix.trace_smul, ← Matrix.trace_mul_comm]
  have hDinv_pos : (0 : ℝ) < (D : ℝ)⁻¹ := inv_pos.mpr hD
  -- Step 7: `Re Tr(Φ P) ≤ Re Tr(Φ)` since `P ≤ 1` ⇒ `(1 − P)` PSD ⇒
  -- `Re Tr(Φ (1 − P)) ≥ 0` ⇒ `Re Tr(Φ P) ≤ Re Tr(Φ)`.
  have hone_minus_P_psd : (1 - P).PosSemidef := hP_le_one
  have hΦ_one_minus_P : ((Φ * (1 - P)).trace).re ≥ 0 :=
    cMatrix_trace_mul_posSemidef_re_nonneg hΦ_psd hone_minus_P_psd
  have htr_one_minus_P : (Φ * (1 - P)).trace = (Φ - Φ * P).trace := by
    rw [show Φ * (1 - P) = Φ - Φ * P from by rw [Matrix.mul_sub, Matrix.mul_one]]
  have htrace_sub : (Φ - Φ * P).trace = Φ.trace - (Φ * P).trace := Matrix.trace_sub _ _
  have hΦP_le_Φ : (Φ * P).trace.re ≤ Φ.trace.re := by
    have h0 : 0 ≤ ((Φ * (1 - P)).trace).re := hΦ_one_minus_P
    rw [htr_one_minus_P, htrace_sub, Complex.sub_re] at h0
    linarith
  -- Step 8: `Re Tr(Φ) = Σ_{x'} p(x') Re Tr(Px x') ≤ Σ_{x'} p(x') · d ≤ d`.
  have hΦ_trace : Φ.trace = ∑ x', p x' • (Px x').trace := by
    rw [hΦ_def, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun x' _ => Matrix.trace_smul _ _)
  have hΦ_trace_re : Φ.trace.re = ∑ x', p x' * (Px x').trace.re := by
    rw [hΦ_trace, re_sum_eq_sum_re]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    rw [Complex.real_smul, Complex.mul_re]
    simp
  have hbound : (Φ * P).trace.re ≤ d := by
    refine le_trans hΦP_le_Φ ?_
    rw [hΦ_trace_re]
    refine le_trans (Finset.sum_le_sum (fun x' _ =>
      mul_le_mul_of_nonneg_left (hpack3 x') (hp_nonneg x'))) ?_
    rw [← Finset.sum_mul, hpsum, one_mul]
  -- Final: `Re Tr(Φ P σ̄ P) ≤ Re Tr(Φ (D⁻¹ P)) = D⁻¹ · Re Tr(Φ P) ≤ D⁻¹ · d = d/D`.
  calc (Φ * (P * E.averageState.matrix * P)).trace.re
      ≤ (Φ * (((D : ℝ)⁻¹) • P)).trace.re := hstep5
    _ = ((D : ℝ)⁻¹) * (Φ * P).trace.re := by
      rw [htr_Dinv, Complex.real_smul, Complex.mul_re]; simp
    _ ≤ ((D : ℝ)⁻¹) * d := mul_le_mul_of_nonneg_left hbound (le_of_lt hDinv_pos)
    _ = d / D := by rw [div_eq_mul_inv, mul_comm]

/-! ## Randomized average error (packing lemma conclusion)

Averaging the Hayashi–Nagaoka per-codeword error bound over the random code and
over the uniform message `m ∈ M` yields the randomized packing-lemma error
`2(ε+2√ε) + 4(|M|−1)·d/D`: the own-codeword term `2(ε+2√ε)` survives the
average unchanged, while each of the `|M|−1` cross-codeword terms contributes
`d/D` by `crossTerm_expectation_bound`.
[Wilde2011Qst, qit-notes.tex:29680-29850] -/

/-- **Randomized average error bound** (Wilde's packing lemma, conclusion). For
an ensemble `E` of codeword states, the typical-subspace projector `Π`, codeword
projectors `{Π_x}`, and the packing hypotheses `pack-3`/`pack-4` as in
`crossTerm_expectation_bound`, suppose each per-codeword error `p_e(m,𝒞)` is
controlled by the Hayashi–Nagaoka split
`p_e(m,𝒞) ≤ 2(ε+2√ε) + 4·Σ_{m'≠m} Re Tr(Υ_{𝒞_{m'}} σ_{𝒞_m})`. Then the
random-code expectation of the uniform-message average error satisfies

`𝔼_𝒞{ (1/|M|)·Σ_m p_e(m,𝒞) } ≤ 2(ε+2√ε) + 4·(|M|−1)·d/D`.

The proof uses linearity of `codeExpectation` to swap the message average with
the code expectation, applies the per-codeword hypothesis, then bounds each
cross-codeword expectation by `d/D` via `crossTerm_expectation_bound`, counting
the `|M|−1` off-diagonal messages via `Finset.card_erase_of_mem`.
[Wilde2011Qst, qit-notes.tex:29680-29850] -/
theorem PackingLemma.lemma_avgError
    {a : Type u} {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype M] [DecidableEq M] [Nonempty M]
    (E : Ensemble 𝒳 a) (P : CMatrix a) (hP : P.PosSemidef) (hPid : P * P = P)
    (hP_le_one : P ≤ 1)
    (Px : 𝒳 → CMatrix a) (hPx : ∀ x, (Px x).PosSemidef)
    (d D : ℝ) (hD : 0 < D) (ε : ℝ)
    (hpack3 : ∀ x, ((Px x).trace).re ≤ d)
    (hpack4 : P * E.averageState.matrix * P ≤ ((D : ℝ)⁻¹) • P)
    (p_e : (M → 𝒳) → M → ℝ)
    (hpe : ∀ C m, p_e C m ≤
      2 * (ε + 2 * Real.sqrt ε) +
        4 * ∑ m' ∈ (Finset.univ : Finset M).erase m,
          ((coatedOp P Px (C m') * (E.states (C m)).matrix).trace).re) :
    codeExpectation (fun x => (E.probs x : ℝ))
      (fun C => (Fintype.card M : ℝ)⁻¹ * ∑ m, p_e C m) ≤
    2 * (ε + 2 * Real.sqrt ε) + 4 * ((Fintype.card M : ℝ) - 1) * (d / D) := by
  set p : 𝒳 → ℝ := fun x => (E.probs x : ℝ) with hp_def
  have hpsum : ∑ x, p x = 1 := by
    simp only [hp_def]; exact_mod_cast E.weights_sum
  have hp_nonneg : ∀ x, 0 ≤ p x := fun x => NNReal.coe_nonneg (E.probs x)
  -- The iid code weight `∏_m p(𝒞_m)` is nonnegative.
  have hw_nonneg : ∀ C : M → 𝒳, 0 ≤ (∏ m : M, p (C m)) := by
    intro C; exact Finset.prod_nonneg (fun m _ => hp_nonneg (C m))
  -- `M` is nonempty ⇒ `|M| ≥ 1` ⇒ `(1/|M|)` nonneg.
  have hcard_pos : (0 : ℝ) < Fintype.card M := by
    have : (0 : ℕ) < Fintype.card M := Fintype.card_pos_iff.mpr ‹Nonempty M›
    exact_mod_cast this
  have hinv_nonneg : 0 ≤ ((Fintype.card M : ℝ))⁻¹ := le_of_lt (inv_pos.mpr hcard_pos)
  -- Helper: monotonicity of `codeExpectation` under pointwise `≤`.
  have hmono : ∀ (f g : (M → 𝒳) → ℝ), (∀ C, f C ≤ g C) →
      codeExpectation p f ≤ codeExpectation p g := by
    intro f g hfg
    unfold codeExpectation
    exact Finset.sum_le_sum (fun C _ => mul_le_mul_of_nonneg_left (hfg C) (hw_nonneg C))
  -- Helper: linearity `𝔼{f + g} = 𝔼{f} + 𝔼{g}`.
  have hadd : ∀ (f g : (M → 𝒳) → ℝ),
      codeExpectation p (fun C => f C + g C) = codeExpectation p f + codeExpectation p g := by
    intro f g
    unfold codeExpectation
    simp only [mul_add, Finset.sum_add_distrib]
  -- Helper: constant expectation `𝔼{c} = c` (mass-1 distribution).
  have hconst : ∀ c, (codeExpectation (M := M) p fun _ => c) = c := by
    intro c
    have h := @codeExpectation_marginal 𝒳 M _ _ _ _ p hpsum (‹Nonempty M›).some (fun _ => c)
    rw [h, ← Finset.sum_mul, hpsum, one_mul]
  -- Helper: scalar-linearity `𝔼{c * f} = c * 𝔼{f}`.
  have hsmul : ∀ (c : ℝ) (f : (M → 𝒳) → ℝ),
      codeExpectation p (fun C => c * f C) = c * codeExpectation p f := by
    intro c f
    unfold codeExpectation
    simp only [mul_left_comm, Finset.mul_sum]
  -- Helper: expectation of a finite sum `𝔼{Σ_{i∈s} f i} = Σ_{i∈s} 𝔼{f i}`.
  have hsum_swap : ∀ (s : Finset M) (f : M → (M → 𝒳) → ℝ),
      codeExpectation p (fun C => ∑ i ∈ s, f i C) =
        ∑ i ∈ s, codeExpectation p (fun C => f i C) := by
    intro s f
    unfold codeExpectation
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun C _ => ?_)
    rw [Finset.mul_sum]
  -- Per-message uniform bound: `𝔼_𝒞{p_e(m,𝒞)} ≤ 2(ε+2√ε) + 4·(|M|−1)·(d/D)`.
  have hmsg_bound : ∀ m, codeExpectation p (fun C => p_e C m) ≤
      2 * (ε + 2 * Real.sqrt ε) + 4 * ((Fintype.card M : ℝ) - 1) * (d / D) := by
    intro m
    -- Apply `hpe` pointwise, then split into own-term (constant) + cross-sum.
    refine le_trans (hmono _ _ (hpe · m)) ?_
    -- `𝔼{2(ε+2√ε) + 4 Σ_{m'≠m} h(C,m')} = 2(ε+2√ε) + 4 Σ_{m'≠m} 𝔼{h(·,m')}`.
    have hsplit : codeExpectation p (fun C =>
        2 * (ε + 2 * Real.sqrt ε) +
          4 * ∑ m' ∈ (Finset.univ : Finset M).erase m,
            ((coatedOp P Px (C m') * (E.states (C m)).matrix).trace).re) =
        2 * (ε + 2 * Real.sqrt ε) +
          4 * ∑ m' ∈ (Finset.univ : Finset M).erase m,
            codeExpectation p (fun C =>
              ((coatedOp P Px (C m') * (E.states (C m)).matrix).trace).re) := by
      have h1 : codeExpectation p (fun C =>
          2 * (ε + 2 * Real.sqrt ε) +
            4 * ∑ m' ∈ (Finset.univ : Finset M).erase m,
              ((coatedOp P Px (C m') * (E.states (C m)).matrix).trace).re) =
          codeExpectation p (fun _ => 2 * (ε + 2 * Real.sqrt ε)) +
            codeExpectation p (fun C =>
              4 * ∑ m' ∈ (Finset.univ : Finset M).erase m,
                ((coatedOp P Px (C m') * (E.states (C m)).matrix).trace).re) :=
        hadd _ _
      rw [h1, hconst]
      congr 1
      rw [hsmul]
      refine congrArg (4 * ·) (hsum_swap _ _)
    rw [hsplit]
    -- Own-term (constant) + cross-term (bounded by `4(|M|−1)d/D`).
    refine add_le_add (le_refl _) ?_
    -- Each cross-codeword expectation `≤ d/D` via `crossTerm_expectation_bound`.
    have hcross : ∀ m' ∈ (Finset.univ : Finset M).erase m,
        codeExpectation p (fun C =>
          ((coatedOp P Px (C m') * (E.states (C m)).matrix).trace).re) ≤ d / D := by
      intro m' hm'
      exact crossTerm_expectation_bound E P hP hPid hP_le_one Px hPx d D hD
        hpack3 hpack4 m m' (Finset.mem_erase.mp hm').1.symm
    -- Sum over `|M|−1` off-diagonal messages, then scale by `4`.
    have hsum_bound : (∑ m' ∈ (Finset.univ : Finset M).erase m,
        codeExpectation p (fun C =>
          ((coatedOp P Px (C m') * (E.states (C m)).matrix).trace).re)) ≤
        ((Fintype.card M : ℝ) - 1) * (d / D) := by
      refine le_trans (Finset.sum_le_sum hcross) ?_
      have hcard_erase : ((Finset.univ : Finset M).erase m).card = Fintype.card M - 1 :=
        Finset.card_erase_of_mem (Finset.mem_univ m)
      have hone_le : 1 ≤ Fintype.card M := by
        have : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
        omega
      rw [Finset.sum_const, hcard_erase, nsmul_eq_mul,
        Nat.cast_sub hone_le, Nat.cast_one]
    refine le_trans (mul_le_mul_of_nonneg_left hsum_bound (by norm_num : (0 : ℝ) ≤ 4)) ?_
    exact le_of_eq (by ring)
  -- Final: pull `(1/|M|)` out, swap message-average with expectation, average.
  -- `𝔼{(1/|M|) Σ_m p_e} = (1/|M|) Σ_m 𝔼{p_e} ≤ (1/|M|) Σ_m bound = bound`.
  have havg : codeExpectation p (fun C => ((Fintype.card M : ℝ))⁻¹ * ∑ m, p_e C m) =
      ((Fintype.card M : ℝ))⁻¹ * ∑ m, codeExpectation p (fun C => p_e C m) := by
    have h1 : codeExpectation p (fun C => ((Fintype.card M : ℝ))⁻¹ * ∑ m, p_e C m) =
        ((Fintype.card M : ℝ))⁻¹ *
          codeExpectation p (fun C => ∑ m, p_e C m) := hsmul _ _
    rw [h1]
    congr 1
    -- `𝔼{Σ_m p_e} = Σ_m 𝔼{p_e}` by linearity (induction on the finite sum).
    have h2 : codeExpectation p (fun C => ∑ m, p_e C m) =
        ∑ m, codeExpectation p (fun C => p_e C m) := by
      unfold codeExpectation
      rw [Finset.sum_comm]
      congr 1; funext C; rw [Finset.mul_sum]
    rw [h2]
  rw [havg]
  have hsum_le : (∑ m, codeExpectation p (fun C => p_e C m)) ≤
      (Fintype.card M : ℝ) * (2 * (ε + 2 * Real.sqrt ε) +
        4 * ((Fintype.card M : ℝ) - 1) * (d / D)) := by
    refine le_trans (Finset.sum_le_sum (fun m _ => hmsg_bound m)) ?_
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
    exact le_of_eq (by ring)
  calc ((Fintype.card M : ℝ))⁻¹ * ∑ m, codeExpectation p (fun C => p_e C m)
        ≤ ((Fintype.card M : ℝ))⁻¹ *
            ((Fintype.card M : ℝ) * (2 * (ε + 2 * Real.sqrt ε) +
              4 * ((Fintype.card M : ℝ) - 1) * (d / D))) :=
        mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
    _ = 2 * (ε + 2 * Real.sqrt ε) + 4 * ((Fintype.card M : ℝ) - 1) * (d / D) := by
      field_simp [hcard_pos.ne']

/-! ## Derandomized average-error and maximal-error corollaries

The randomized bound `lemma_avgError` controls the *expected* average error over
iid random codes. Wilde's derandomization observes that some code attains at
most the expected average error (the minimum is at most the mean), yielding a
*single* code `𝒞₀` and the square-root-measurement decoder whose average error
is bounded by `2(ε+2√ε) + 4(|M|−1)·d/D`. A further expurgation (Markov
counting) promotes average to maximal error.
[Wilde2011Qst, qit-notes.tex:29853-29920] -/

/-- The square-root-measurement effect `pgmEffect Sᵢ` agrees with the inverse
square root of the family total `Σⱼ Sⱼ` for any Hermitian witness on the total.
This is the witness-irrelevance of `psdInvSqrt` (a `CMatrix` equality, proved by
`congr` exploiting proof-irrelevance of the `IsHermitian` proposition).
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
private lemma pgmEffect_eq_total {a : Type u} {ι : Type*}
    [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    (Sf : ι → CMatrix a) (hSf : ∀ i, (Sf i).PosSemidef) (i : ι)
    (hH : (∑ j, Sf j).IsHermitian) :
    pgmEffect Sf hSf i =
      psdInvSqrt (∑ j, Sf j) hH * Sf i * psdInvSqrt (∑ j, Sf j) hH := by
  unfold pgmEffect pgmTotal
  all_goals congr 1

/-- `psdInvSqrt` is invariant under transport of both its matrix argument and
Hermitian witness across a matrix equality. The witness irrelevance is
proof-irrelevance of the proposition `M.IsHermitian := Mᴴ = M`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
private lemma psdInvSqrt_heq {a : Type u}
    [Fintype a] [DecidableEq a]
    {M N : CMatrix a} (hMN : M = N) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    psdInvSqrt M hM = psdInvSqrt N hN := by
  subst hMN; congr 1

/-- **Per-codeword Hayashi–Nagaoka operator inequality** for the square-root
measurement. For a PSD family `{Sⱼ}` with `Sᵢ ≤ 1`, the detection deficit of the
`i`-th PGM effect is Loewner-bounded by twice the own-codeword deficit plus four
times the cross-codeword mass:

`(1 − Λᵢ) ≤ 2•(1 − Sᵢ) + 4•Σ_{j≠i} Sⱼ`,

where `Λᵢ = pgmEffect{Sⱼ}(i)`. This is the `c = 1` Hayashi–Nagaoka inequality
(`hayashi_nagaoka_one`) instantiated at `S := Sᵢ`, `T := Σ_{j≠i} Sⱼ`, with the
PGM effect aligned to the family total `Σⱼ Sⱼ = Sᵢ + Σ_{j≠i} Sⱼ` via
`pgmEffect_eq_total` and witness transport.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
private lemma pgm_hn_operator {a : Type u} {ι : Type*}
    [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    (Sf : ι → CMatrix a) (hSf : ∀ i, (Sf i).PosSemidef) (i : ι)
    (hSle1 : Sf i ≤ 1) :
    ((2 : ℝ) • (1 - Sf i) + (4 : ℝ) • (∑ j ∈ (Finset.univ : Finset ι).erase i, Sf j) -
      (1 - pgmEffect Sf hSf i)).PosSemidef := by
  have hcross_psd : (∑ j ∈ (Finset.univ : Finset ι).erase i, Sf j).PosSemidef :=
    Matrix.posSemidef_sum _ (fun j _ => hSf j)
  have hsplit : (∑ j, Sf j) = Sf i + ∑ j ∈ (Finset.univ : Finset ι).erase i, Sf j := by
    rw [Finset.add_sum_erase Finset.univ Sf (Finset.mem_univ i)]
  have hHsum : (∑ j, Sf j).IsHermitian := hsplit ▸ ((hSf i).add hcross_psd).isHermitian
  have hEff : pgmEffect Sf hSf i =
      psdInvSqrt (Sf i + ∑ j ∈ (Finset.univ : Finset ι).erase i, Sf j)
        ((hSf i).add hcross_psd).isHermitian * Sf i *
      psdInvSqrt (Sf i + ∑ j ∈ (Finset.univ : Finset ι).erase i, Sf j)
        ((hSf i).add hcross_psd).isHermitian := by
    rw [pgmEffect_eq_total Sf hSf i hHsum]
    simp only [psdInvSqrt_heq hsplit hHsum ((hSf i).add hcross_psd).isHermitian]
  rw [hEff]
  exact hayashi_nagaoka_one (S := Sf i)
    (T := ∑ j ∈ (Finset.univ : Finset ι).erase i, Sf j)
    (hSf i) hcross_psd (Matrix.le_iff.mp hSle1)

/-- Trace monotonicity against a state: if `A ≤ B` (Loewner) then for any state
`ρ`, `Re Tr(ρ·A) ≤ Re Tr(ρ·B)`. The deficit `Re Tr(ρ·(B−A))` is nonnegative
because `B − A` is PSD and `ρ` is PSD, so `Re Tr((B−A)·ρ) ≥ 0` by
`cMatrix_trace_mul_posSemidef_re_nonneg`, and trace commutativity moves the
state to the right. -/
private lemma trace_re_le_of_le {a : Type u} [Fintype a] [DecidableEq a]
    (A B : CMatrix a) (hAB : A ≤ B) (ρ : State a) :
    ((ρ.matrix * A).trace).re ≤ ((ρ.matrix * B).trace).re := by
  have hDiff_psd : (B - A).PosSemidef := hAB
  have hρ_psd : ρ.matrix.PosSemidef := ρ.pos
  -- `Re Tr((B−A)·ρ) ≥ 0` by PSD-PSD trace duality.
  have hBA_nonneg : 0 ≤ (((B - A) * ρ.matrix).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hDiff_psd hρ_psd
  -- Expand `(B−A)·ρ = B·ρ − A·ρ` and split the real trace.
  have hmul : ((B - A) * ρ.matrix).trace = (B * ρ.matrix).trace - (A * ρ.matrix).trace := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
  rw [hmul, Complex.sub_re] at hBA_nonneg
  -- Move the state to the right via trace commutativity (real parts agree).
  have hBA : ((B * ρ.matrix).trace).re = ((ρ.matrix * B).trace).re :=
    congrArg Complex.re (Matrix.trace_mul_comm B ρ.matrix)
  have hAA : ((A * ρ.matrix).trace).re = ((ρ.matrix * A).trace).re :=
    congrArg Complex.re (Matrix.trace_mul_comm A ρ.matrix)
  rw [hBA, hAA] at hBA_nonneg
  linarith

/-- **Per-codeword error bound for the square-root-measurement decoder** (Wilde's
packing lemma, Hayashi–Nagaoka split). For the typical-subspace projector `Π`,
codeword projectors `{Π_x}`, a code `C : M → 𝒳`, and codeword states `{σ_x}`,
the square-root-measurement effect `Λ_m = pgmEffect{Υ_{C_m'}}(m)` on the coated
operators `Υ_{C_m'} = Π Π_{C_m'} Π` leaves a per-message error

`1 − Re Tr(Λ_m σ_{C_m}) ≤ 2(ε + 2√ε) + 4·Σ_{m'≠m} Re Tr(Υ_{C_m'} σ_{C_m})`.

The proof traces `pgm_hn_operator` against the codeword state `σ_{C_m}` (trace
monotonicity), giving `1 − Re Tr(Λ_m σ) ≤ 2·Re Tr((1−Υ_{C_m})σ) +
4·Σ_{m'≠m} Re Tr(Υ_{C_m'} σ)`, then bounds the own-codeword term
`Re Tr((1−Υ_{C_m})σ_{C_m}) ≤ ε + 2√ε` via `ownTerm_bound`.
[Wilde2011Qst, qit-notes.tex:29680-29850] -/
private theorem PackingLemma.pgmError_bound
    {a : Type u} {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype M] [DecidableEq M]
    (P : CMatrix a) (hP : P.PosSemidef) (hPid : P * P = P)
    (Px : 𝒳 → CMatrix a) (hPx : ∀ x, (Px x).PosSemidef)
    (hPxid : ∀ x, Px x * Px x = Px x)
    (σ : 𝒳 → State a) (ε : ℝ) (hε : 0 ≤ ε)
    (h1 : ∀ x, 1 - ε ≤ ((P * (σ x).matrix).trace).re)
    (h2 : ∀ x, 1 - ε ≤ ((Px x * (σ x).matrix).trace).re)
    (C : M → 𝒳) (m : M) :
    1 - (((pgmEffect (fun m' => coatedOp P Px (C m'))
        (fun m' => coatedOp_posSemidef P hP Px hPx (C m')) m)
        * (σ (C m)).matrix).trace).re ≤
      2 * (ε + 2 * Real.sqrt ε) +
        4 * ∑ m' ∈ (Finset.univ : Finset M).erase m,
          ((coatedOp P Px (C m') * (σ (C m)).matrix).trace).re := by
  -- The coated-operator family `Υ_{C_m'} = Π Π_{C_m'} Π`, indexed by messages.
  set Sf : M → CMatrix a := fun m' => coatedOp P Px (C m') with hSf_def
  have hSf : ∀ m', (Sf m').PosSemidef := fun m' => coatedOp_posSemidef P hP Px hPx (C m')
  -- `Υ_{C_m} ≤ 1` (a coated projector is an effect).
  have hPxle1 : ∀ x, Px x ≤ 1 := fun x => projector_le_one (Px x) (hPx x) (hPxid x)
  have hSm_le_one : Sf m ≤ 1 := coatedOp_le_one P hP hPid Px hPxle1 (C m)
  set ρ : State a := σ (C m) with hρ_def
  have hρ_one : (ρ.matrix.trace).re = 1 := by rw [ρ.trace_eq_one]; simp
  -- Per-codeword Hayashi–Nagaoka operator inequality for the PGM on `{Υ_{C_m'}}`.
  have hHN := pgm_hn_operator Sf hSf m hSm_le_one
  -- Trace against `ρ` on the LEFT (ρ·X order): `Re Tr(ρ (1−Λ_m)) ≤ Re Tr(ρ RHS)`.
  have hmono_σ : ((ρ.matrix * (1 - pgmEffect Sf hSf m)).trace).re ≤
      ((ρ.matrix * ((2 : ℝ) • (1 - Sf m) +
        (4 : ℝ) • (∑ m' ∈ (Finset.univ : Finset M).erase m, Sf m'))).trace).re :=
    trace_re_le_of_le _ _ (Matrix.le_iff.mp hHN) ρ
  -- Commute each `ρ·X` to `X·ρ` (real parts agree by `trace_mul_comm`).
  have hcomm (X : CMatrix a) :
      ((ρ.matrix * X).trace).re = ((X * ρ.matrix).trace).re :=
    congrArg Complex.re (Matrix.trace_mul_comm ρ.matrix X)
  rw [hcomm (1 - pgmEffect Sf hSf m),
      hcomm ((2 : ℝ) • (1 - Sf m) + (4 : ℝ) •
        (∑ m' ∈ (Finset.univ : Finset M).erase m, Sf m'))] at hmono_σ
  -- Expand `Re Tr((1−Λ_m) ρ) = Re Tr(ρ) − Re Tr(Λ_m ρ) = 1 − Re Tr(Λ_m ρ)`.
  have hLHS_eq : (((1 - pgmEffect Sf hSf m) * ρ.matrix).trace).re =
      1 - ((pgmEffect Sf hSf m * ρ.matrix).trace).re := by
    have hsplit : ((1 - pgmEffect Sf hSf m) * ρ.matrix).trace =
        ρ.matrix.trace - (pgmEffect Sf hSf m * ρ.matrix).trace := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
    rw [hsplit, Complex.sub_re, hρ_one]
  -- Expand the RHS real trace by `ℝ`-linearity.
  have hsmul_re (c : ℝ) (z : ℂ) : (c • z).re = c * z.re := by
    rw [Complex.real_smul, Complex.mul_re]; simp
  have hRHS_expand :
      ((((2 : ℝ) • (1 - Sf m) + (4 : ℝ) •
          (∑ m' ∈ (Finset.univ : Finset M).erase m, Sf m')) * ρ.matrix).trace).re =
        2 * (((1 - Sf m) * ρ.matrix).trace).re +
          4 * ∑ m' ∈ (Finset.univ : Finset M).erase m,
            ((Sf m' * ρ.matrix).trace).re := by
    -- Distribute the matrix product over the sum and smul, then traces.
    have hcross : ((∑ m' ∈ (Finset.univ : Finset M).erase m, Sf m') * ρ.matrix).trace =
        ∑ m' ∈ (Finset.univ : Finset M).erase m, (Sf m' * ρ.matrix).trace := by
      rw [Finset.sum_mul, Matrix.trace_sum]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hcross]
    rw [Complex.add_re, hsmul_re, hsmul_re, re_sum_eq_sum_re]
  rw [hRHS_expand] at hmono_σ
  rw [hLHS_eq] at hmono_σ
  -- Own-codeword term `Re Tr((1 − Υ_{C_m}) ρ) ≤ ε + 2√ε` (ownTerm_bound).
  have hown : (((1 - Sf m) * ρ.matrix).trace).re ≤ ε + 2 * Real.sqrt ε :=
    ownTerm_bound P hP hPid Px hPx hPxid σ ε hε h1 h2 (C m)
  -- The PGM effect equals the goal's literal form (defeq after `Sf` unfolds).
  have hEff_eq : pgmEffect Sf hSf m =
      pgmEffect (fun m' => coatedOp P Px (C m'))
        (fun m' => coatedOp_posSemidef P hP Px hPx (C m')) m := by
    rfl
  have hcross_eq : ∀ m' ∈ (Finset.univ : Finset M).erase m,
      ((Sf m' * ρ.matrix).trace).re = ((coatedOp P Px (C m') * ρ.matrix).trace).re := by
    intro m' _; rw [hSf_def]
  have hcross_sum : (∑ m' ∈ (Finset.univ : Finset M).erase m, ((Sf m' * ρ.matrix).trace).re) =
      ∑ m' ∈ (Finset.univ : Finset M).erase m, ((coatedOp P Px (C m') * ρ.matrix).trace).re :=
    Finset.sum_congr rfl (fun m' hm' => hcross_eq m' hm')
  rw [hEff_eq, hρ_def, hcross_sum] at hmono_σ
  linarith

/-- **Derandomization** (Wilde's Shannon-style argument). If the random-code
expectation of a per-code functional `f : (M → 𝒳) → ℝ` is at most `η`, where the
expectation is the iid-weighted mean `Σ_𝒞 (∏_m p(𝒞_m))·f(𝒞)` with nonnegative
weights summing to `1`, then some code `𝒞₀` attains `f(𝒞₀) ≤ η`. This is the
"minimum is at most the mean" principle for a convex combination: if every code
exceeded `η`, the weighted mean would exceed `η` as well.
[Wilde2011Qst, qit-notes.tex:29853-29920] -/
private theorem PackingLemma.exists_code_le_expectation
    {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype 𝒳] [DecidableEq 𝒳] [Fintype M] [DecidableEq M] [Nonempty M]
    (p : 𝒳 → ℝ) (hpsum : ∑ x, p x = 1) (hp_nonneg : ∀ x, 0 ≤ p x)
    (f : (M → 𝒳) → ℝ) (η : ℝ)
    (hexp : codeExpectation p f ≤ η) :
    ∃ C : M → 𝒳, f C ≤ η := by
  -- Weights `w C = ∏_m p(C m)` are nonnegative.
  have hw_nonneg : ∀ C : M → 𝒳, 0 ≤ (∏ m : M, p (C m)) := fun C =>
    Finset.prod_nonneg (fun m _ => hp_nonneg (C m))
  -- The weights sum to `1`: `codeExpectation p (fun _ => 1) = 1` (constant
  -- functional marginalizes to `Σ_x p x · 1 = 1`), and this expectation is the
  -- weight sum by `codeExpectation`'s definition.
  have hw_sum : ∑ C : M → 𝒳, (∏ m : M, p (C m)) = 1 := by
    -- `codeExpectation p (fun _ => 1) = Σ_x p x · 1 = 1` (constant functional),
    -- and unfolds to `Σ_C (∏_m p (C m)) · 1 = Σ_C ∏_m p (C m)`.
    have h := codeExpectation_marginal p hpsum (‹Nonempty M›).some (fun _ => (1 : ℝ))
    simp only [codeExpectation, mul_one] at h
    -- `h : Σ_C ∏ p(C_m) = Σ_x p x`. Conclude `Σ ∏ = Σ p = 1`.
    rw [h, hpsum]
  -- Some weight is strictly positive (else the sum could not equal `1 > 0`).
  have hpos_exists : ∃ C : M → 𝒳, (0 : ℝ) < (∏ m : M, p (C m)) := by
    have h0 : (0 : ℝ) < ∑ C : M → 𝒳, (∏ m : M, p (C m)) := by rw [hw_sum]; norm_num
    -- If every weight were `≤ 0`, the sum would be `≤ 0`; contradicting `1 > 0`.
    by_contra hneg
    push Not at hneg
    have hle0 : (∑ C : M → 𝒳, (∏ m : M, p (C m))) ≤ 0 :=
      Finset.sum_nonpos fun C _ => hneg C
    linarith
  -- Contrapositive: assume every code strictly exceeds `η`.
  by_contra hcontra
  push Not at hcontra
  have hbelow : ∀ C, η < f C := hcontra
  -- `Σ_C w_C · η = η · Σ_C w_C = η`.
  have hsum_eta : (∑ C : M → 𝒳, (∏ m : M, p (C m)) * η) = η := by
    rw [← Finset.sum_mul, hw_sum, one_mul]
  -- `Σ_C w_C · (f C − η) ≥ w_{C₀} · (f C₀ − η) > 0`, since each summand is
  -- nonnegative (`w_C ≥ 0`, `f C − η > 0`) and one is strictly positive.
  obtain ⟨C₀, hC₀pos⟩ := hpos_exists
  have hdiff_pos : ∀ C, (0 : ℝ) < f C - η := fun C => by have := hbelow C; linarith
  have hterm_pos : (0 : ℝ) < (∏ m : M, p (C₀ m)) * (f C₀ - η) :=
    mul_pos hC₀pos (hdiff_pos C₀)
  have hsummand_nonneg : ∀ C ∈ (Finset.univ : Finset (M → 𝒳)),
      (0 : ℝ) ≤ (∏ m : M, p (C m)) * (f C - η) := fun C _ =>
    mul_nonneg (hw_nonneg C) (le_of_lt (hdiff_pos C))
  -- The sum of nonneg terms containing a positive one is positive.
  have hsum_pos : (0 : ℝ) < ∑ C : M → 𝒳, (∏ m : M, p (C m)) * (f C - η) := by
    have hge : (∏ m : M, p (C₀ m)) * (f C₀ - η) ≤
        ∑ C : M → 𝒳, (∏ m : M, p (C m)) * (f C - η) :=
      Finset.single_le_sum hsummand_nonneg (Finset.mem_univ _)
    linarith
  -- Therefore `Σ_C w_C · f C − Σ_C w_C · η > 0`, i.e. `Σ_C w_C · f C > η`.
  have hsplit : (∑ C : M → 𝒳, (∏ m : M, p (C m)) * (f C - η)) =
      (∑ C : M → 𝒳, (∏ m : M, p (C m)) * f C) -
        ∑ C : M → 𝒳, (∏ m : M, p (C m)) * η := by
    simp only [Finset.sum_sub_distrib, mul_sub]
  unfold codeExpectation at hexp
  rw [hsplit, hsum_eta] at hsum_pos
  linarith

set_option maxHeartbeats 1000000 in
/-- **Derandomized average-error packing-lemma corollary** (Wilde 2011). For an
ensemble `E` of codeword states satisfying the packing hypotheses `pack-1`–`pack-4`,
there exists a code `𝒞₀ : M → 𝒳` and a square-root-measurement decoder POVM
`{Λ_m}` on the coated operators `Υ_{𝒞₀_m'} = Π Π_{𝒞₀_m'} Π` whose average error
satisfies

`avgError ≤ 2(ε + 2√ε) + 4(|M| − 1)·d/D`.

The proof derandomizes the random-code bound `lemma_avgError` via
`exists_code_le_expectation` (the weighted-mean argument), building the per-code
average-error functional `p_e` from the PGM decoder and applying the Hayashi–
Nagaoka per-codeword split `pgmError_bound`. The decoder is the square-root
measurement on the code's coated operators, completed to a POVM on `M` by
absorbing the failure outcome `none` into one message (which only *reduces* that
message's error).
[Wilde2011Qst, qit-notes.tex:29853-29920] -/
theorem PackingLemma.packingLemma_avgError
    {a : Type u} {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype M] [DecidableEq M] [Nonempty M]
    (E : Ensemble 𝒳 a) (P : CMatrix a) (hP : P.PosSemidef) (hPid : P * P = P)
    (hP_le_one : P ≤ 1)
    (Px : 𝒳 → CMatrix a)
    (hPx : ∀ x, (Px x).PosSemidef ∧ Px x * Px x = Px x ∧ Px x ≤ 1)
    (d D ε : ℝ) (hD : 0 < D) (hε : 0 ≤ ε)
    (h1 : ∀ x, 1 - ε ≤ ((P * (E.states x).matrix).trace).re)
    (h2 : ∀ x, 1 - ε ≤ ((Px x * (E.states x).matrix).trace).re)
    (h3 : ∀ x, ((Px x).trace).re ≤ d)
    (h4 : P * E.averageState.matrix * P ≤ ((D : ℝ)⁻¹) • P) :
    ∃ (C : M → 𝒳) (dec : POVM M a),
      let code : DecoderCode M a := ⟨fun m => E.states (C m), dec⟩
      code.averageErrorAtMost
        (2 * (ε + 2 * Real.sqrt ε) + 4 * ((Fintype.card M : ℝ) - 1) * (d / D)) := by
  -- Unpack the codeword-projector hypotheses.
  have hPx_psd : ∀ x, (Px x).PosSemidef := fun x => (hPx x).1
  have hPx_id : ∀ x, Px x * Px x = Px x := fun x => (hPx x).2.1
  have hPx_le1 : ∀ x, Px x ≤ 1 := fun x => (hPx x).2.2
  -- The iid code distribution `p x = E.probs x` (mass 1, nonnegative).
  set p : 𝒳 → ℝ := fun x => (E.probs x : ℝ)
  have hpsum : ∑ x, p x = 1 := by
    have h : ∑ x, (E.probs x : ℝ) = 1 := by exact_mod_cast E.weights_sum
    exact h
  have hp_nonneg : ∀ x, 0 ≤ p x := fun x => NNReal.coe_nonneg (E.probs x)
  -- Per-code per-message decoder error `p_e C m` for the square-root measurement
  -- on the code's coated operators `Υ_{C_m'}` (the `pgmEffect` of that family).
  have hCoated_psd (C : M → 𝒳) : ∀ m', (coatedOp P Px (C m')).PosSemidef := fun m' =>
    coatedOp_posSemidef P hP Px hPx_psd (C m')
  set p_e : (M → 𝒳) → M → ℝ := fun C m =>
    1 - (((pgmEffect (fun m' => coatedOp P Px (C m')) (hCoated_psd C) m
          * (E.states (C m)).matrix).trace).re)
  -- The Hayashi–Nagaoka per-codeword split: `p_e C m ≤ 2(ε+2√ε) + 4 Σ_cross`.
  have hpe : ∀ (C : M → 𝒳) (m : M), p_e C m ≤
      2 * (ε + 2 * Real.sqrt ε) +
        4 * ∑ m' ∈ (Finset.univ : Finset M).erase m,
          ((coatedOp P Px (C m') * (E.states (C m)).matrix).trace).re := by
    intro C m
    exact pgmError_bound P hP hPid Px hPx_psd hPx_id (E.states ·) ε hε h1 h2 C m
  -- Randomized average-error bound: `𝔼_C{(1/|M|) Σ_m p_e C m} ≤ η`.
  set η : ℝ := 2 * (ε + 2 * Real.sqrt ε) + 4 * ((Fintype.card M : ℝ) - 1) * (d / D)
  have havg := lemma_avgError E P hP hPid hP_le_one Px hPx_psd d D hD ε h3 h4 p_e hpe
  -- Derandomize: some code `C₀` has `(1/|M|) Σ_m p_e C₀ m ≤ η`.
  obtain ⟨C₀, hC₀⟩ := exists_code_le_expectation p hpsum hp_nonneg
    (fun C => (Fintype.card M : ℝ)⁻¹ * ∑ m, p_e C m) η havg
  -- Build the decoder `POVM M a`: the square-root measurement on `{Υ_{C₀_m'}}`,
  -- with the `none` failure outcome absorbed into the distinguished message `m₀`.
  let Sf₀ : M → CMatrix a := fun m' => coatedOp P Px (C₀ m')
  have hSf₀ : ∀ m', (Sf₀ m').PosSemidef := hCoated_psd C₀
  have hSf₀_le_one : ∀ m', Sf₀ m' ≤ 1 := fun m' =>
    coatedOp_le_one P hP hPid Px hPx_le1 (C₀ m')
  -- The PGM sub-POVM sum is at most `1` (`sum_pgmEffect_le_one`).
  have hsub_sum_le_one : (∑ m, pgmEffect Sf₀ hSf₀ m) ≤ 1 := sum_pgmEffect_le_one Sf₀ hSf₀
  -- The failure mass `1 − ΣΛ_m` (PSD, carried by message `m₀`).
  let failMass : CMatrix a := 1 - ∑ m', pgmEffect Sf₀ hSf₀ m'
  have hfail_psd : failMass.PosSemidef := Matrix.le_iff.mp hsub_sum_le_one
  let m₀ : M := (‹Nonempty M›).some
  -- Effects: `Λ_m` for `m ≠ m₀`, and `Λ_{m₀} + failMass` for `m₀`.
  let decEffects (m : M) : CMatrix a :=
    pgmEffect Sf₀ hSf₀ m + if m = m₀ then failMass else 0
  have hdec_pos : ∀ m, (decEffects m).PosSemidef := fun m => by
    have hpgm : (pgmEffect Sf₀ hSf₀ m).PosSemidef := pgmEffect_posSemidef Sf₀ hSf₀ m
    by_cases hm : m = m₀
    · have : decEffects m = pgmEffect Sf₀ hSf₀ m + failMass := by
        show _ + (if m = m₀ then failMass else 0) = _ + failMass
        rw [if_pos hm]
      rw [this]; exact hpgm.add hfail_psd
    · have : decEffects m = pgmEffect Sf₀ hSf₀ m := by
        show _ + (if m = m₀ then failMass else 0) = _
        rw [if_neg hm]; rw [add_zero]
      rw [this]; exact hpgm
  have hdec_sum : (∑ m, decEffects m) = 1 := by
    simp only [decEffects, Finset.sum_add_distrib]
    -- `Σ_m (if m = m₀ then failMass else 0) = failMass` (exactly one equals `m₀`).
    have hsingle : (∑ m, (if m = m₀ then failMass else (0 : CMatrix a))) = failMass := by
      have := @Finset.sum_eq_single M (CMatrix a) _ (Finset.univ : Finset M)
        (fun m => if m = m₀ then failMass else (0 : CMatrix a)) m₀
        (fun b _ hb => if_neg hb)
        (fun h => absurd (Finset.mem_univ m₀) h)
      rw [this]
      simp
    rw [hsingle]
    show (∑ m, pgmEffect Sf₀ hSf₀ m) + failMass = 1
    rw [show failMass = 1 - ∑ m', pgmEffect Sf₀ hSf₀ m' from rfl]
    have h2 : (∑ m, pgmEffect Sf₀ hSf₀ m) = ∑ m', pgmEffect Sf₀ hSf₀ m' := rfl
    rw [h2]; abel
  let dec : POVM M a := ⟨decEffects, hdec_pos, hdec_sum⟩
  -- The decoder's per-message error is at most `p_e C₀ m` (absorbing `none` only
  -- helps message `m₀`).
  have herr_le : ∀ m, 1 - (dec.prob (E.states (C₀ m)) m : ℝ) ≤ p_e C₀ m := by
    intro m
    rw [POVM.prob_eq_trace_re]
    -- Unfold the decoder effect field to `decEffects m`.
    show 1 - (((E.states (C₀ m)).matrix * decEffects m).trace).re ≤ p_e C₀ m
    have hσ_psd : (E.states (C₀ m)).matrix.PosSemidef := (E.states (C₀ m)).pos
    have hextra_psd : (if m = m₀ then failMass else (0 : CMatrix a)).PosSemidef := by
      by_cases hm : m = m₀
      · simp [hm]; exact hfail_psd
      · simp [hm]; exact Matrix.PosSemidef.zero
    have heff_split : decEffects m =
        pgmEffect Sf₀ hSf₀ m + (if m = m₀ then failMass else (0 : CMatrix a)) := rfl
    rw [heff_split, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    have hextra_nonneg : (0 : ℝ) ≤
        (((E.states (C₀ m)).matrix *
          (if m = m₀ then failMass else (0 : CMatrix a))).trace).re :=
      cMatrix_trace_mul_posSemidef_re_nonneg hσ_psd hextra_psd
    -- `p_e C₀ m` uses effect-first order `Re Tr(pgmEffect · σ)`; the goal LHS (from
    -- `prob_eq_trace_re`) uses state-first `Re Tr(σ · pgmEffect)`. These real parts
    -- agree by trace commutativity.
    have hcomm_pgm : (((E.states (C₀ m)).matrix * pgmEffect Sf₀ hSf₀ m).trace).re =
        ((pgmEffect Sf₀ hSf₀ m * (E.states (C₀ m)).matrix).trace).re :=
      congrArg Complex.re (Matrix.trace_mul_comm (E.states (C₀ m)).matrix _)
    -- The PGM effect on `Sf₀` equals the `p_e`-form effect (same family/witness).
    have hpgm_eq : pgmEffect Sf₀ hSf₀ m =
        pgmEffect (fun m' => coatedOp P Px (C₀ m')) (hCoated_psd C₀) m := rfl
    rw [show p_e C₀ m =
        1 - (((pgmEffect (fun m' => coatedOp P Px (C₀ m')) (hCoated_psd C₀) m
              * (E.states (C₀ m)).matrix).trace).re) from rfl, ← hpgm_eq, ← hcomm_pgm]
    linarith
  -- Assemble the average-error bound.
  refine ⟨C₀, dec, ?_⟩
  rw [DecoderCode.averageErrorAtMost_iff]
  -- Goal: `(1/|M|) Σ_m (1 − successProbability) ≤ η`.
  show (Fintype.card M : ℝ)⁻¹ * ∑ m : M,
        (1 - (dec.prob (E.states (C₀ m)) m : ℝ)) ≤ η
  have hcard_pos : (0 : ℝ) < Fintype.card M := by
    have : (0 : ℕ) < Fintype.card M := Fintype.card_pos_iff.mpr ‹Nonempty M›
    exact_mod_cast this
  -- Bound each per-message error by `p_e C₀ m`, then use `hC₀`.
  have hsum_le : (∑ m : M, (1 - (dec.prob (E.states (C₀ m)) m : ℝ))) ≤
      ∑ m : M, p_e C₀ m :=
    Finset.sum_le_sum (fun m _ => herr_le m)
  calc (Fintype.card M : ℝ)⁻¹ * ∑ m : M, (1 - (dec.prob (E.states (C₀ m)) m : ℝ))
      ≤ (Fintype.card M : ℝ)⁻¹ * ∑ m : M, p_e C₀ m :=
        mul_le_mul_of_nonneg_left hsum_le (le_of_lt (inv_pos.mpr hcard_pos))
    _ ≤ η := hC₀

/-- Bridge from the packing lemma's average-error bound to an
`HSWClassicalCode`: a codeword lift `φ` whose channel outputs realise the
output ensemble `E` induces an HSW code (encoder `φ ∘ C₀`, decoder = packing
decoder) whose derandomized average error is bounded by the packing-lemma
constant `2*(ε+2√ε) + 4*((card M:ℝ)-1)*(d/D)`.

This is the average-error analogue of the per-message HSW bridge: it composes
the existence statement `packingLemma_avgError` (which supplies the random-code
codeword map `C₀` and the square-root decoder `dec`) with the output-state
agreement `houtput` to obtain the derandomized `HSWClassicalCode`. The packing
lemma is applied on the channel *output* system `TensorPower b n`: the codeword
operators `P`, `Px`, the output ensemble `E`, and the decoder `dec` all live
there, while `φ` lifts each classical codeword to an *input* state on
`TensorPower a n`.
[Wilde2011Qst, qit-notes.tex:33634-33808] -/
theorem PackingLemma.hswCode_averageErrorAtMost_of_packing
    {a : Type uIn} {b : Type uOut} {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype 𝒳] [DecidableEq 𝒳] [Fintype M] [DecidableEq M] [Nonempty M]
    (N : Channel a b) (n : ℕ)
    (E : Ensemble 𝒳 (TensorPower b n)) (P : CMatrix (TensorPower b n))
    (hP : P.PosSemidef) (hPid : P * P = P) (hP_le_one : P ≤ 1)
    (Px : 𝒳 → CMatrix (TensorPower b n))
    (hPx : ∀ x, (Px x).PosSemidef ∧ Px x * Px x = Px x ∧ Px x ≤ 1)
    (φ : 𝒳 → State (TensorPower a n))
    (houtput : ∀ x, (N.tensorPower n).applyState (φ x) = E.states x)
    (d D ε : ℝ) (hD : 0 < D) (hε : 0 ≤ ε)
    (h1 : ∀ x, 1 - ε ≤ ((P * (E.states x).matrix).trace).re)
    (h2 : ∀ x, 1 - ε ≤ ((Px x * (E.states x).matrix).trace).re)
    (h3 : ∀ x, ((Px x).trace).re ≤ d)
    (h4 : P * E.averageState.matrix * P ≤ ((D : ℝ)⁻¹) • P) :
    ∃ (C : HSWClassicalCode N n M),
      C.toPackingDecoderCode.averageErrorAtMost
        (2 * (ε + 2 * Real.sqrt ε) + 4 * ((Fintype.card M : ℝ) - 1) * (d / D)) := by
  -- Obtain the packing-lemma codeword map `C₀` and square-root decoder `dec`,
  -- together with the average-error bound on the induced `DecoderCode`.
  obtain ⟨C₀ : M → 𝒳, dec : POVM M (TensorPower b n), hcode⟩ :=
    @packingLemma_avgError (TensorPower b n) 𝒳 M
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      E P hP hPid hP_le_one Px hPx d D ε hD hε h1 h2 h3 h4
  -- Build the HSW code: encoder lifts each codeword `C₀ m` to an `A^n` state,
  -- decoder is the packing POVM (both live on the output system).
  set myCode : HSWClassicalCode N n M :=
    { encoder := fun m => φ (C₀ m), decoder := dec }
  refine ⟨myCode, ?_⟩
  rw [PackingLemma.DecoderCode.averageErrorAtMost_iff]
  -- Unfold the HSW code's per-message packing-decoder success probability,
  -- using `houtput` to replace the channel output state by `E.states (C₀ m)`.
  have hprob_eq : ∀ m : M,
      myCode.toPackingDecoderCode.successProbability m =
        (dec.prob (E.states (C₀ m)) m : ℝ) := by
    intro m
    show (dec.prob ((N.tensorPower n).applyState (φ (C₀ m))) m : ℝ) =
        (dec.prob (E.states (C₀ m)) m : ℝ)
    rw [houtput (C₀ m)]
  -- The packing-lemma bound unfolds to the same average over `E.states (C₀ m)`.
  rw [PackingLemma.DecoderCode.averageErrorAtMost_iff] at hcode
  show (Fintype.card M : ℝ)⁻¹ * ∑ m : M,
        (1 - (myCode.toPackingDecoderCode.successProbability m : ℝ)) ≤
      (2 * (ε + 2 * Real.sqrt ε) + 4 * ((Fintype.card M : ℝ) - 1) * (d / D))
  have hsum_eq : ∑ m : M,
        (1 - (myCode.toPackingDecoderCode.successProbability m : ℝ)) =
      ∑ m : M, (1 - (dec.prob (E.states (C₀ m)) m : ℝ)) :=
    Finset.sum_congr rfl (fun m _ => by rw [hprob_eq])
  rw [hsum_eq]
  exact hcode

/-- Package the HSW packing-lemma average-error code as the average-error
witness consumed by the HSW direct-achievability assembly layer.

The packing lemma supplies the code and its average-error estimate.  The caller
supplies the message-cardinality/rate estimate, since that estimate comes from
the separate HSW message-size choice `|M| ≈ 2^{n(χ-\delta)}` rather than from
the square-root-measurement error analysis itself. -/
theorem PackingLemma.hswAverageErrorPackingWitness_of_packing
    {a : Type uIn} {b : Type uOut} {ι : Type uEnsemble}
    {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype ι] [DecidableEq ι] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype M] [DecidableEq M] [Nonempty M]
    (N : Channel a b) (E₀ : Ensemble ι a) (n : ℕ) (δ : ℝ)
    (E : Ensemble 𝒳 (TensorPower b n)) (P : CMatrix (TensorPower b n))
    (hP : P.PosSemidef) (hPid : P * P = P) (hP_le_one : P ≤ 1)
    (Px : 𝒳 → CMatrix (TensorPower b n))
    (hPx : ∀ x, (Px x).PosSemidef ∧ Px x * Px x = Px x ∧ Px x ≤ 1)
    (φ : 𝒳 → State (TensorPower a n))
    (houtput : ∀ x, (N.tensorPower n).applyState (φ x) = E.states x)
    (d D ε : ℝ) (hD : 0 < D) (hε : 0 ≤ ε)
    (h1 : ∀ x, 1 - ε ≤ ((P * (E.states x).matrix).trace).re)
    (h2 : ∀ x, 1 - ε ≤ ((Px x * (E.states x).matrix).trace).re)
    (h3 : ∀ x, ((Px x).trace).re ≤ d)
    (h4 : P * E.averageState.matrix * P ≤ ((D : ℝ)⁻¹) • P)
    (hrate : hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ) :
    Nonempty
      (HSWAverageErrorPackingWitness N E₀ n δ
        (2 * (ε + 2 * Real.sqrt ε) + 4 * ((Fintype.card M : ℝ) - 1) * (d / D)) M) := by
  obtain ⟨C, havg⟩ :=
    @PackingLemma.hswCode_averageErrorAtMost_of_packing a b 𝒳 M
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
      N n E P hP hPid hP_le_one Px hPx φ houtput d D ε hD hε h1 h2 h3 h4
  refine ⟨{ code := C, rate_ge := ?_, packing_average_error_le := havg }⟩
  simpa [HSWClassicalCode.rate] using hrate

end

end QIT
