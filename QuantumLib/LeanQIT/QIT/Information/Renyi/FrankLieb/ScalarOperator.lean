/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.Renyi
public import QIT.Information.Renyi.RenyiDPI.Domain
public import QIT.States.TraceNorm.Audenaert
public import QIT.Util.BlockMatrix
import QIT.Util.CMatrixCLM
public import Mathlib.Data.EReal.Basic

/-!
# Frank--Lieb scalar and operator support

Low-level scalar, matrix, integral, and operator inequality support for the
Frank--Lieb sandwiched Renyi route.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology Matrix.Norms.L2Operator

universe u v w

namespace Matrix

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Tensoring on opposite sides commutes: `(A ⊗ I) (I ⊗ B) = (I ⊗ B) (A ⊗ I)`. -/
theorem kronecker_left_right_commute
    (A : QIT.CMatrix a) (B : QIT.CMatrix b) :
    Matrix.kronecker A (1 : QIT.CMatrix b) *
        Matrix.kronecker (1 : QIT.CMatrix a) B =
      Matrix.kronecker (1 : QIT.CMatrix a) B *
        Matrix.kronecker A (1 : QIT.CMatrix b) := by
  calc
    Matrix.kronecker A (1 : QIT.CMatrix b) *
        Matrix.kronecker (1 : QIT.CMatrix a) B =
      Matrix.kronecker (A * (1 : QIT.CMatrix a)) ((1 : QIT.CMatrix b) * B) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul A (1 : QIT.CMatrix a)
            (1 : QIT.CMatrix b) B).symm
    _ = Matrix.kronecker ((1 : QIT.CMatrix a) * A) (B * (1 : QIT.CMatrix b)) := by
        simp
    _ =
      Matrix.kronecker (1 : QIT.CMatrix a) B *
        Matrix.kronecker A (1 : QIT.CMatrix b) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul (1 : QIT.CMatrix a) A
            B (1 : QIT.CMatrix b))

/-- Trace form of the positive weighted Ando resolvent-integrand concavity.

The matrix inequality above is stronger; this trace form is the one that
matches the Frank--Lieb trace concavity statement after the Audenaert
fractional-power integral representation is inserted. -/
theorem andoResolventIntegrand_rpow_weighted_trace_concave_posDef
    {A₁ A₂ : QIT.CMatrix a} {B₁ B₂ : QIT.CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p r t : ℝ} (hr : 0 < r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (((r ^ (p - 1)) •
            andoResolventIntegrand (a := a) (b := b) r A₁ B₁).trace).re +
        (1 - t) * (((r ^ (p - 1)) •
            andoResolventIntegrand (a := a) (b := b) r A₂ B₂).trace).re ≤
      (((r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r
        (t • A₁ + (1 - t) • A₂)
        (t • B₁ + (1 - t) • B₂)).trace).re := by
  let L : QIT.CMatrix (a × b) :=
    t • ((r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
      (1 - t) •
        ((r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r A₂ B₂)
  let R : QIT.CMatrix (a × b) :=
    (r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hmat : L ≤ R := by
    simpa [L, R] using
      andoResolventIntegrand_rpow_weighted_concave_posDef
        hA₁ hA₂ hB₁ hB₂ hr ht0 ht1 (p := p)
  have hdiff : (R - L).PosSemidef := Matrix.le_iff.mp hmat
  have htrace_nonneg : 0 ≤ ((R - L).trace).re :=
    (Matrix.PosSemidef.trace_nonneg hdiff).1
  have hle : L.trace.re ≤ R.trace.re := by
    simpa [Matrix.trace_sub] using htrace_nonneg
  simpa [L, R, Matrix.trace_add, Matrix.trace_smul, Complex.mul_re] using hle

end

end Matrix

namespace QIT

noncomputable section

open MeasureTheory

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- For a positive definite matrix, real powers of the nonsingular inverse
are the negative real powers of the original matrix. -/
public theorem cMatrix_rpow_nonsing_inv_eq_rpow_neg
    {B : CMatrix a} (hB : B.PosDef) (p : ℝ) :
    CFC.rpow B⁻¹ p = CFC.rpow B (-p) := by
  obtain ⟨u, hu⟩ := hB.isUnit
  have hBnonneg : (0 : CMatrix a) ≤ B :=
    Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef
  have hinv : B⁻¹ = (↑u⁻¹ : CMatrix a) := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu]
    simp
  calc
    CFC.rpow B⁻¹ p = CFC.rpow (↑u⁻¹ : CMatrix a) p := by
      rw [hinv]
    _ = CFC.rpow (↑u : CMatrix a) (-p) := by
      exact (CFC.rpow_neg u p (ha' := by simpa [hu] using hBnonneg)).symm
    _ = CFC.rpow B (-p) := by
      rw [hu]

/-- Multiplying the inverse-reference tensor power by `I ⊗ B` converts it
to the tensor power term in the Lieb--Ando trace concavity statement:
`(A ⊗ B⁻¹)^p (I ⊗ B) = A^p ⊗ B^(1-p)`. -/
public theorem cMatrix_rpow_kronecker_inv_mul_right_eq_tensor_one_sub
    {b : Type v} [Fintype b] [DecidableEq b]
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
    rw [cMatrix_rpow_nonsing_inv_eq_rpow_neg hB p]
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

/-- Integrability is preserved by right-multiplication with a fixed complex
matrix. -/
public theorem cMatrix_integrableOn_mul_right
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (R : CMatrix a) :
    IntegrableOn (fun r => f r * R) s μ := by
  have hf' : Integrable f (μ.restrict s) := by
    simpa [IntegrableOn] using hf
  have h :=
    (ContinuousLinearMap.mulLeftRight ℝ (CMatrix a) (1 : CMatrix a) R).integrable_comp hf'
  simpa [ContinuousLinearMap.mulLeftRight_apply, IntegrableOn] using h

/-- Right-multiplication by a fixed matrix commutes with Bochner integration. -/
public theorem cMatrix_setIntegral_mul_right
    {μ : Measure ℝ} {s : Set ℝ} {f : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (R : CMatrix a) :
    (∫ r in s, f r ∂μ) * R = ∫ r in s, f r * R ∂μ := by
  have hf' : Integrable f (μ.restrict s) := by
    simpa [IntegrableOn] using hf
  have h :=
    (ContinuousLinearMap.mulLeftRight ℝ (CMatrix a) (1 : CMatrix a) R).integral_comp_comm hf'
  simpa [ContinuousLinearMap.mulLeftRight_apply] using h.symm

/-- Right-multiplying `A ⊗ B⁻¹` by `I ⊗ B` recovers `A ⊗ I`. -/
public theorem cMatrix_kronecker_inv_ref_mul_right
    {b : Type v} [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hB : B.PosDef) :
    Matrix.kronecker A B⁻¹ * Matrix.kronecker (1 : CMatrix a) B =
      Matrix.kronecker A (1 : CMatrix b) := by
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  calc
    Matrix.kronecker A B⁻¹ * Matrix.kronecker (1 : CMatrix a) B =
      Matrix.kronecker (A * (1 : CMatrix a)) (B⁻¹ * B) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul A (1 : CMatrix a) B⁻¹ B).symm
    _ = Matrix.kronecker A (1 : CMatrix b) := by
        rw [Matrix.nonsing_inv_mul B hdet]
        simp

/-- The shifted Audenaert denominator is the Ando denominator after
right-multiplication by `(I ⊗ B)⁻¹`. -/
public theorem cMatrix_andoDenom_mul_ref_inv_eq_shift
    {b : Type v} [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b} (hB : B.PosDef) {r : ℝ} :
    (Matrix.kronecker A (1 : CMatrix b) +
        r • Matrix.kronecker (1 : CMatrix a) B) *
      Matrix.kronecker (1 : CMatrix a) B⁻¹ =
    Matrix.kronecker A B⁻¹ + r • (1 : CMatrix (a × b)) := by
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  calc
    (Matrix.kronecker A (1 : CMatrix b) +
        r • Matrix.kronecker (1 : CMatrix a) B) *
      Matrix.kronecker (1 : CMatrix a) B⁻¹ =
      Matrix.kronecker A (1 : CMatrix b) *
          Matrix.kronecker (1 : CMatrix a) B⁻¹ +
        (r • Matrix.kronecker (1 : CMatrix a) B) *
          Matrix.kronecker (1 : CMatrix a) B⁻¹ := by
        rw [add_mul]
    _ = Matrix.kronecker A B⁻¹ + r • (1 : CMatrix (a × b)) := by
        have h₁ :
            Matrix.kronecker A (1 : CMatrix b) *
                Matrix.kronecker (1 : CMatrix a) B⁻¹ =
              Matrix.kronecker A B⁻¹ := by
          calc
            Matrix.kronecker A (1 : CMatrix b) *
                Matrix.kronecker (1 : CMatrix a) B⁻¹ =
              Matrix.kronecker (A * (1 : CMatrix a))
                ((1 : CMatrix b) * B⁻¹) := by
                simpa [Matrix.kronecker] using
                  (Matrix.mul_kronecker_mul
                    A (1 : CMatrix a) (1 : CMatrix b) B⁻¹).symm
            _ = Matrix.kronecker A B⁻¹ := by
                simp
        have h₂ :
            (r • Matrix.kronecker (1 : CMatrix a) B) *
                Matrix.kronecker (1 : CMatrix a) B⁻¹ =
              r • (1 : CMatrix (a × b)) := by
          calc
            (r • Matrix.kronecker (1 : CMatrix a) B) *
                Matrix.kronecker (1 : CMatrix a) B⁻¹ =
              r •
                (Matrix.kronecker (1 : CMatrix a) B *
                  Matrix.kronecker (1 : CMatrix a) B⁻¹) := by
                simp
            _ = r • (1 : CMatrix (a × b)) := by
                have hmul :
                    Matrix.kronecker (1 : CMatrix a) B *
                        Matrix.kronecker (1 : CMatrix a) B⁻¹ =
                      1 := by
                  calc
                    Matrix.kronecker (1 : CMatrix a) B *
                        Matrix.kronecker (1 : CMatrix a) B⁻¹ =
                      Matrix.kronecker
                        ((1 : CMatrix a) * (1 : CMatrix a)) (B * B⁻¹) := by
                        simpa [Matrix.kronecker] using
                          (Matrix.mul_kronecker_mul
                            (1 : CMatrix a) (1 : CMatrix a) B B⁻¹).symm
                    _ = 1 := by
                        rw [Matrix.mul_nonsing_inv B hdet]
                        simp
                rw [hmul]
        rw [h₁, h₂]

/-- Inverse bridge between the shifted Audenaert resolvent denominator and
the Ando denominator. -/
public theorem cMatrix_shiftedKroneckerInv_inv_eq_ref_mul_andoDenom_inv
    {b : Type v} [Fintype b] [DecidableEq b]
    {r : ℝ} {A : CMatrix a} {B : CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosDef) (hr : 0 < r) :
    (Matrix.kronecker A B⁻¹ + r • (1 : CMatrix (a × b)))⁻¹ =
      Matrix.kronecker (1 : CMatrix a) B *
        (Matrix.kronecker A (1 : CMatrix b) +
          r • Matrix.kronecker (1 : CMatrix a) B)⁻¹ := by
  let X : CMatrix (a × b) := Matrix.kronecker A (1 : CMatrix b)
  let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
  let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
  let D : CMatrix (a × b) := X + r • Y
  have hYpd : Y.PosDef := by
    simpa [Y] using Matrix.PosDef.one.kronecker hB
  have hYdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hYpd.isUnit
  have hDpd : D.PosDef := by
    simpa [X, Y, D] using Matrix.andoDenom_posDef (a := a) (b := b) hA hB hr
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDpd.isUnit
  have hYinv : Y⁻¹ = Matrix.kronecker (1 : CMatrix a) B⁻¹ := by
    simpa [Y] using (Matrix.inv_kronecker (1 : CMatrix a) B)
  have hDYinv : D * Y⁻¹ = C + r • (1 : CMatrix (a × b)) := by
    rw [hYinv]
    simpa [X, Y, C, D] using
      cMatrix_andoDenom_mul_ref_inv_eq_shift
        (a := a) (b := b) (A := A) (B := B) (r := r) hB
  apply Matrix.inv_eq_right_inv
  calc
    (C + r • (1 : CMatrix (a × b))) * (Y * D⁻¹) =
        (D * Y⁻¹) * (Y * D⁻¹) := by
      rw [hDYinv]
    _ = D * (Y⁻¹ * (Y * D⁻¹)) := by
      exact Matrix.mul_assoc D Y⁻¹ (Y * D⁻¹)
    _ = D * ((Y⁻¹ * Y) * D⁻¹) := by
      exact congrArg (fun Z : CMatrix (a × b) => D * Z)
        (Matrix.mul_assoc Y⁻¹ Y D⁻¹).symm
    _ = D * (1 * D⁻¹) := by
      rw [Matrix.nonsing_inv_mul Y hYdet]
    _ = 1 := by
      rw [Matrix.one_mul, Matrix.mul_nonsing_inv D hDdet]

/-- Pointwise bridge from Audenaert's fractional-power integrand applied to
`A ⊗ B⁻¹` to the weighted Ando resolvent integrand.

After right-multiplication by `I ⊗ B`, the resolvent form of
`audenaertRpowIntegrand` becomes exactly the integrand whose integral yields
the Lieb--Ando tensor trace-concavity term. -/
public theorem audenaertRpowIntegrand_kronecker_inv_mul_right_eq_ando
    {b : Type v} [Fintype b] [DecidableEq b]
    {p r : ℝ} {A : CMatrix a} {B : CMatrix b}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hr : 0 < r)
    (hA : A.PosSemidef) (hB : B.PosDef) :
    audenaertRpowIntegrand p r (Matrix.kronecker A B⁻¹) *
        Matrix.kronecker (1 : CMatrix a) B =
      (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A B := by
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
  calc
    audenaertRpowIntegrand p r (Matrix.kronecker A B⁻¹) *
        Matrix.kronecker (1 : CMatrix a) B =
      (r ^ (p - 1) • (C * (C + r • (1 : CMatrix (a × b)))⁻¹)) * Y := by
        rw [audenaertRpowIntegrand_eq_resolvent hp hr hCpsd]
        simp [audenaertResolventIntegrand, C, Y]
    _ = r ^ (p - 1) • (C * (C + r • (1 : CMatrix (a × b)))⁻¹ * Y) := by
        simp
    _ = r ^ (p - 1) • (C * (Y * D⁻¹) * Y) := by
        rw [hinv]
    _ = r ^ (p - 1) • ((C * Y) * D⁻¹ * Y) := by
        congr 1
        rw [← Matrix.mul_assoc C Y D⁻¹, Matrix.mul_assoc]
    _ = r ^ (p - 1) • (X * D⁻¹ * Y) := by
        rw [hCmulY]
    _ = (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A B := by
        simp [Matrix.andoResolventIntegrand, X, Y, D]

/-- Audenaert's fractional-power representation gives the Ando integral
representation of the Lieb tensor power term, with one measure depending
only on `p` and the tensor dimension.

This is the analytic representation identity that closes the gap between
the pointwise Ando resolvent concavity and the finite-dimensional
Lieb--Ando trace concavity theorem for a positive definite reference
argument. -/
public theorem andoIntegralRepresentation_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1) :
    ∃ μ : Measure ℝ,
      (∀ ⦃A : CMatrix a⦄ ⦃B : CMatrix b⦄,
        A.PosSemidef → B.PosDef →
        IntegrableOn (fun r : ℝ => (r ^ ((p : ℝ) - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A B)
          (Set.Ioi 0) μ) ∧
      (∀ ⦃A : CMatrix a⦄ ⦃B : CMatrix b⦄,
        A.PosSemidef → B.PosDef →
        Matrix.kronecker (CFC.rpow A (p : ℝ)) (CFC.rpow B (1 - (p : ℝ))) =
          ∫ r in Set.Ioi 0, (r ^ ((p : ℝ) - 1)) •
            Matrix.andoResolventIntegrand (a := a) (b := b) r A B ∂μ) := by
  obtain ⟨μ, hint, hpow⟩ := audenaertRpowIntegralRepresentation (a := a × b) hp
  refine ⟨μ, ?_, ?_⟩
  · intro A B hA hB
    let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
    let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
    have hpReal : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩
    have hCpsd : C.PosSemidef := by
      simpa [C] using hA.kronecker hB.inv.posSemidef
    have hAudInt :
        IntegrableOn (fun r : ℝ => audenaertRpowIntegrand (p : ℝ) r C)
          (Set.Ioi 0) μ :=
      hint hCpsd
    have hAudRightInt :
        IntegrableOn (fun r : ℝ => audenaertRpowIntegrand (p : ℝ) r C * Y)
          (Set.Ioi 0) μ :=
      cMatrix_integrableOn_mul_right hAudInt Y
    let F : ℝ → CMatrix (a × b) := fun r =>
      audenaertRpowIntegrand (p : ℝ) r C * Y
    let G : ℝ → CMatrix (a × b) := fun r =>
      (r ^ ((p : ℝ) - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A B
    have hEqOn : Set.EqOn F G (Set.Ioi 0) := by
      intro r hr
      simpa [F, G, C, Y] using
        audenaertRpowIntegrand_kronecker_inv_mul_right_eq_ando
          (a := a) (b := b) (p := (p : ℝ)) (r := r) (A := A) (B := B)
          hpReal hr hA hB
    have hGInt : IntegrableOn G (Set.Ioi 0) μ :=
      hAudRightInt.congr_fun hEqOn measurableSet_Ioi
    simpa [G] using hGInt
  · intro A B hA hB
    let C : CMatrix (a × b) := Matrix.kronecker A B⁻¹
    let Y : CMatrix (a × b) := Matrix.kronecker (1 : CMatrix a) B
    have hpReal : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩
    have hp0 : 0 ≤ (p : ℝ) := by
      exact_mod_cast (show (0 : ℝ≥0) ≤ p from zero_le)
    have hCpsd : C.PosSemidef := by
      simpa [C] using hA.kronecker hB.inv.posSemidef
    have hAudInt :
        IntegrableOn (fun r : ℝ => audenaertRpowIntegrand (p : ℝ) r C)
          (Set.Ioi 0) μ :=
      hint hCpsd
    let F : ℝ → CMatrix (a × b) := fun r =>
      audenaertRpowIntegrand (p : ℝ) r C * Y
    let G : ℝ → CMatrix (a × b) := fun r =>
      (r ^ ((p : ℝ) - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A B
    have hEqOn : Set.EqOn F G (Set.Ioi 0) := by
      intro r hr
      simpa [F, G, C, Y] using
        audenaertRpowIntegrand_kronecker_inv_mul_right_eq_ando
          (a := a) (b := b) (p := (p : ℝ)) (r := r) (A := A) (B := B)
          hpReal hr hA hB
    have hCpow := hpow hCpsd
    have hLeft : CFC.rpow C (p : ℝ) * Y = ∫ r in Set.Ioi 0, F r ∂μ := by
      calc
        CFC.rpow C (p : ℝ) * Y =
            (∫ r in Set.Ioi 0, audenaertRpowIntegrand (p : ℝ) r C ∂μ) * Y := by
          rw [hCpow]
        _ = ∫ r in Set.Ioi 0, audenaertRpowIntegrand (p : ℝ) r C * Y ∂μ := by
          rw [cMatrix_setIntegral_mul_right hAudInt Y]
        _ = ∫ r in Set.Ioi 0, F r ∂μ := by
          rfl
    have hFGint : ∫ r in Set.Ioi 0, F r ∂μ = ∫ r in Set.Ioi 0, G r ∂μ := by
      apply integral_congr_ae
      exact ae_restrict_of_forall_mem measurableSet_Ioi hEqOn
    have hTensor :
        CFC.rpow C (p : ℝ) * Y =
          Matrix.kronecker (CFC.rpow A (p : ℝ)) (CFC.rpow B (1 - (p : ℝ))) := by
      simpa [C, Y] using
        cMatrix_rpow_kronecker_inv_mul_right_eq_tensor_one_sub
          (a := a) (b := b) (A := A) (B := B) hA hB hp0
    calc
      Matrix.kronecker (CFC.rpow A (p : ℝ)) (CFC.rpow B (1 - (p : ℝ))) =
          CFC.rpow C (p : ℝ) * Y := by
        exact hTensor.symm
      _ = ∫ r in Set.Ioi 0, F r ∂μ := hLeft
      _ = ∫ r in Set.Ioi 0, G r ∂μ := hFGint
      _ = ∫ r in Set.Ioi 0, (r ^ ((p : ℝ) - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A B ∂μ := by
        rfl

private theorem cMatrix_integral_conjTranspose {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) :
    Matrix.conjTranspose (∫ x, f x ∂μ) =
      ∫ x, Matrix.conjTranspose (f x) ∂μ := by
  simpa [cMatrixConjTransposeCLM] using
    ((cMatrixConjTransposeCLM (ι := ι)).integral_comp_comm hf).symm

private theorem cMatrix_integral_dotProduct_mulVec {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) (x : ι → ℂ) :
    dotProduct (star x) (Matrix.mulVec (∫ t, f t ∂μ) x) =
      ∫ t, dotProduct (star x) (Matrix.mulVec (f t) x) ∂μ := by
  simp_rw [← cMatrixQuadraticCLM_apply x]
  exact
    ((cMatrixQuadraticCLM x).integral_comp_comm hf).symm

private theorem isClosed_setOf_zero_le_complex_frankLieb :
    IsClosed ({z : ℂ | 0 ≤ z} : Set ℂ) := by
  have h : ({z : ℂ | 0 ≤ z} : Set ℂ) = {z | 0 ≤ z.re} ∩ {z | z.im = 0} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hz
      simp [Complex.le_def] at hz ⊢
      tauto
    · rintro ⟨hre, him⟩
      simp [Complex.le_def]
      exact ⟨hre, him.symm⟩
  rw [h]
  exact (isClosed_Ici.preimage Complex.continuous_re).inter
    (isClosed_singleton.preimage Complex.continuous_im)

private theorem continuous_cMatrix_quadraticForm {ι : Type v}
    [Fintype ι] [DecidableEq ι] (x : ι →₀ ℂ) :
    Continuous (fun A : CMatrix ι =>
      (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj)) := by
  classical
  simp only [Finsupp.sum, Finsupp.sum]
  exact continuous_finsetSum x.support fun i _ =>
    continuous_finsetSum x.support fun j _ =>
      Continuous.mul (Continuous.mul continuous_const
        (cMatrixEntryCLM_complex (ι := ι) i j).continuous) continuous_const

/-- The finite-dimensional cone of positive semidefinite complex matrices is
closed in the norm topology. -/
public theorem isClosed_cMatrix_posSemidef {ι : Type v}
    [Fintype ι] [DecidableEq ι] :
    IsClosed ({A : CMatrix ι | A.PosSemidef} : Set (CMatrix ι)) := by
  classical
  have h : ({A : CMatrix ι | A.PosSemidef} : Set (CMatrix ι)) =
      ({A | A.IsHermitian} ∩
        (⋂ x : ι →₀ ℂ,
          {A : CMatrix ι | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj})) := by
    ext A
    simp [Matrix.PosSemidef, Set.mem_iInter]
  rw [h]
  refine IsClosed.inter ?herm ?quad
  · have hH : ({A : CMatrix ι | A.IsHermitian} : Set (CMatrix ι)) =
        {A | Matrix.conjTranspose A = A} := by
      ext A
      simp [Matrix.IsHermitian]
    rw [hH]
    exact isClosed_eq (cMatrixConjTransposeCLM (ι := ι)).continuous continuous_id
  · exact isClosed_iInter fun x =>
      isClosed_setOf_zero_le_complex_frankLieb.preimage
        (continuous_cMatrix_quadraticForm (ι := ι) x)

/-- Positive semidefiniteness is preserved under limits of eventually PSD
matrix-valued filters. -/
public theorem cMatrix_posSemidef_of_tendsto {ι : Type v}
    [Fintype ι] [DecidableEq ι] {X : Type*} {l : Filter X} [l.NeBot]
    {F : X → CMatrix ι} {A : CMatrix ι}
    (hF : Filter.Tendsto F l (nhds A))
    (hpsd : ∀ᶠ x in l, (F x).PosSemidef) :
    A.PosSemidef :=
  (isClosed_cMatrix_posSemidef (ι := ι)).mem_of_tendsto hF hpsd

/-- Loewner inequalities are preserved under simultaneous limits. -/
public theorem cMatrix_le_of_tendsto {ι : Type v}
    [Fintype ι] [DecidableEq ι] {X : Type*} {l : Filter X} [l.NeBot]
    {F G : X → CMatrix ι} {A B : CMatrix ι}
    (hF : Filter.Tendsto F l (nhds A))
    (hG : Filter.Tendsto G l (nhds B))
    (hle : ∀ᶠ x in l, F x ≤ G x) :
    A ≤ B := by
  have hdiff :
      Filter.Tendsto (fun x : X => G x - F x) l (nhds (B - A)) :=
    hG.sub hF
  have hpsd : (B - A).PosSemidef :=
    cMatrix_posSemidef_of_tendsto hdiff
      (hle.mono fun _ hx => Matrix.le_iff.mp hx)
  exact Matrix.le_iff.mpr hpsd

/-- Bochner integration preserves positive semidefiniteness for matrix-valued
functions, up to almost-everywhere equality. -/
public theorem cMatrix_integral_posSemidef_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ)
    (hpos : ∀ᵐ t ∂μ, (f t).PosSemidef) :
    (∫ t, f t ∂μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, cMatrix_integral_conjTranspose (hf := hf)]
    apply integral_congr_ae
    exact hpos.mono fun _ ht => ht.isHermitian.eq
  · intro x
    rw [cMatrix_integral_dotProduct_mulVec (hf := hf) x]
    exact integral_nonneg_of_ae (hpos.mono fun _ ht => ht.dotProduct_mulVec_nonneg x)

/-- Monotonicity of Bochner set integration for matrix-valued functions in
Loewner order.

Mathlib's scalar/order lemma needs a closed-order-topology instance which is
not available for `CMatrix`; this version proves the PSD difference directly
from quadratic forms. -/
public theorem cMatrix_setIntegral_mono
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hle : ∀ r ∈ s, f r ≤ g r) :
    ∫ r in s, f r ∂μ ≤ ∫ r in s, g r ∂μ := by
  have hdiffInt : IntegrableOn (fun r : ℝ => g r - f r) s μ := hg.sub hf
  have hdiffPSD :
      (∫ r in s, (g r - f r) ∂μ).PosSemidef := by
    have hdiffInt' : Integrable (fun r : ℝ => g r - f r) (μ.restrict s) := by
      simpa [IntegrableOn] using hdiffInt
    exact
      cMatrix_integral_posSemidef_of_ae (μ := μ.restrict s) hdiffInt'
        ((ae_restrict_iff' hs).mpr
          (ae_of_all μ fun r hr => Matrix.le_iff.mp (hle r hr)))
  have hsub :
      ∫ r in s, (g r - f r) ∂μ =
        (∫ r in s, g r ∂μ) - (∫ r in s, f r ∂μ) := by
    simpa [IntegrableOn] using
      integral_sub (μ := μ.restrict s)
        (by simpa [IntegrableOn] using hg)
        (by simpa [IntegrableOn] using hf)
  rw [hsub] at hdiffPSD
  exact Matrix.le_iff.mpr hdiffPSD

/-- Monotonicity of the real trace after Bochner integration of matrix-valued
functions.

This is the integration bridge needed by the Frank--Lieb/Ando route: once a
pointwise Loewner-order inequality is available for the resolvent integrand,
its trace inequality survives integration against the Audenaert measure. -/
theorem cMatrix_setIntegral_trace_re_mono
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → CMatrix a}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hle : ∀ r ∈ s, f r ≤ g r) :
    ((∫ r in s, f r ∂μ).trace).re ≤
      ((∫ r in s, g r ∂μ).trace).re := by
  have hdiffInt : IntegrableOn (fun r : ℝ => g r - f r) s μ := hg.sub hf
  have htraceIntegral :
      (((∫ r in s, (g r - f r) ∂μ).trace).re) =
        ∫ r in s, ((g r - f r).trace).re ∂μ := by
    simpa [Matrix.mul_one, Matrix.one_mul] using
      audenaertTraceLeftRight_setIntegral (a := a) hdiffInt
        (1 : CMatrix a) (1 : CMatrix a)
  have htraceNonneg :
      0 ≤ ∫ r in s, ((g r - f r).trace).re ∂μ := by
    apply setIntegral_nonneg hs
    intro r hr
    have hdiff : (g r - f r).PosSemidef := Matrix.le_iff.mp (hle r hr)
    exact (Matrix.PosSemidef.trace_nonneg hdiff).1
  have hnonneg :
      0 ≤ (((∫ r in s, (g r - f r) ∂μ).trace).re) := by
    simpa [htraceIntegral] using htraceNonneg
  have hsub :
      ∫ r in s, (g r - f r) ∂μ =
        (∫ r in s, g r ∂μ) - (∫ r in s, f r ∂μ) := by
    simpa [IntegrableOn] using
      integral_sub (μ := μ.restrict s)
        (by simpa [IntegrableOn] using hg)
        (by simpa [IntegrableOn] using hf)
  rw [hsub, Matrix.trace_sub, Complex.sub_re] at hnonneg
  linarith

/-- Integrated trace concavity of the positive weighted Ando resolvent
integrand.

The hypotheses isolate the purely measure-theoretic side of the
Audenaert representation: once the three resolvent integrands are integrable,
the pointwise Ando Loewner inequality integrates to the corresponding trace
inequality. -/
theorem andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ) :
    (((∫ r in s,
      (t • ((r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
        (1 - t) • ((r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂)) ∂μ).trace).re)
      ≤
    (((∫ r in s, (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂) ∂μ).trace).re) := by
  let F₁ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let F₂ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ft : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hLeftInt : IntegrableOn (fun r : ℝ => t • F₁ r + (1 - t) • F₂ r) s μ :=
    (hI₁.smul t).add (hI₂.smul (1 - t))
  have hmono :
      ∀ r ∈ s, t • F₁ r + (1 - t) • F₂ r ≤ Ft r := by
    intro r hrs
    simpa [F₁, F₂, Ft] using
      Matrix.andoResolventIntegrand_rpow_weighted_concave_posDef
        hA₁ hA₂ hB₁ hB₂ (hr_pos r hrs) ht0 ht1 (p := p)
  simpa [F₁, F₂, Ft] using
    cMatrix_setIntegral_trace_re_mono (a := a × b) hs hLeftInt hIt hmono

/-- Integrated Loewner concavity of the positive weighted Ando resolvent
integrand.

This is the matrix-order strengthening of
`andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef`.
It is the bridge needed to apply arbitrary positive trace functionals, rather
than only the ordinary trace. -/
theorem andoResolventIntegrand_rpow_weighted_setIntegral_concave_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ) :
    (∫ r in s,
      (t • ((r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
        (1 - t) • ((r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂)) ∂μ)
      ≤
    (∫ r in s, (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂) ∂μ) := by
  let F₁ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let F₂ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ft : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hLeftInt : IntegrableOn (fun r : ℝ => t • F₁ r + (1 - t) • F₂ r) s μ :=
    (hI₁.smul t).add (hI₂.smul (1 - t))
  have hmono :
      ∀ r ∈ s, t • F₁ r + (1 - t) • F₂ r ≤ Ft r := by
    intro r hrs
    simpa [F₁, F₂, Ft] using
      Matrix.andoResolventIntegrand_rpow_weighted_concave_posDef
        hA₁ hA₂ hB₁ hB₂ (hr_pos r hrs) ht0 ht1 (p := p)
  simpa [F₁, F₂, Ft] using
    cMatrix_setIntegral_mono (a := a × b) hs hLeftInt hIt hmono

/-- Standard separated-left form of the integrated Ando trace concavity. -/
theorem andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef'
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ) :
    t * (((∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁ ∂μ).trace).re) +
        (1 - t) * (((∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂ ∂μ).trace).re)
      ≤
    (((∫ r in s, (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂) ∂μ).trace).re) := by
  let F₁ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let F₂ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ft : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hbase :
      (((∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ).trace).re) ≤
        (((∫ r in s, Ft r ∂μ).trace).re) := by
    simpa [F₁, F₂, Ft] using
      andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef
        (a := a) (b := b) hs hA₁ hA₂ hB₁ hB₂ ht0 ht1 hr_pos hI₁ hI₂ hIt
  have hI₁' : Integrable F₁ (μ.restrict s) := by
    simpa [IntegrableOn, F₁] using hI₁
  have hI₂' : Integrable F₂ (μ.restrict s) := by
    simpa [IntegrableOn, F₂] using hI₂
  have hleftIntegral :
      ∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ =
        t • (∫ r in s, F₁ r ∂μ) + (1 - t) • (∫ r in s, F₂ r ∂μ) := by
    have hadd :=
      integral_add (μ := μ.restrict s) (hI₁'.smul t) (hI₂'.smul (1 - t))
    have hsmul₁ :
        ∫ r in s, t • F₁ r ∂μ = t • (∫ r in s, F₁ r ∂μ) := by
      simpa using (integral_smul (μ := μ.restrict s) t F₁)
    have hsmul₂ :
        ∫ r in s, (1 - t) • F₂ r ∂μ = (1 - t) • (∫ r in s, F₂ r ∂μ) := by
      simpa using (integral_smul (μ := μ.restrict s) (1 - t) F₂)
    simpa [Pi.add_apply, hsmul₁, hsmul₂] using hadd
  have hleftTrace :
      (((∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ).trace).re) =
        t * (((∫ r in s, F₁ r ∂μ).trace).re) +
          (1 - t) * (((∫ r in s, F₂ r ∂μ).trace).re) := by
    rw [hleftIntegral]
    simp [Matrix.trace_add, Matrix.trace_smul, Complex.mul_re]
  rw [hleftTrace] at hbase
  simpa [F₁, F₂, Ft] using hbase

/-- Standard separated-left form of the integrated Ando Loewner concavity. -/
theorem andoResolventIntegrand_rpow_weighted_setIntegral_concave_posDef'
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ) :
    t • (∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁ ∂μ) +
        (1 - t) • (∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂ ∂μ)
      ≤
    (∫ r in s, (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂) ∂μ) := by
  let F₁ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁
  let F₂ : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let Ft : ℝ → CMatrix (a × b) := fun r =>
    (r ^ (p - 1)) • Matrix.andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hbase :
      (∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ) ≤
        (∫ r in s, Ft r ∂μ) := by
    simpa [F₁, F₂, Ft] using
      andoResolventIntegrand_rpow_weighted_setIntegral_concave_posDef
        (a := a) (b := b) hs hA₁ hA₂ hB₁ hB₂ ht0 ht1 hr_pos hI₁ hI₂ hIt
  have hI₁' : Integrable F₁ (μ.restrict s) := by
    simpa [IntegrableOn, F₁] using hI₁
  have hI₂' : Integrable F₂ (μ.restrict s) := by
    simpa [IntegrableOn, F₂] using hI₂
  have hleftIntegral :
      ∫ r in s, (t • F₁ r + (1 - t) • F₂ r) ∂μ =
        t • (∫ r in s, F₁ r ∂μ) + (1 - t) • (∫ r in s, F₂ r ∂μ) := by
    have hadd :=
      integral_add (μ := μ.restrict s) (hI₁'.smul t) (hI₂'.smul (1 - t))
    have hsmul₁ :
        ∫ r in s, t • F₁ r ∂μ = t • (∫ r in s, F₁ r ∂μ) := by
      simpa using (integral_smul (μ := μ.restrict s) t F₁)
    have hsmul₂ :
        ∫ r in s, (1 - t) • F₂ r ∂μ = (1 - t) • (∫ r in s, F₂ r ∂μ) := by
      simpa using (integral_smul (μ := μ.restrict s) (1 - t) F₂)
    simpa [Pi.add_apply, hsmul₁, hsmul₂] using hadd
  rw [hleftIntegral] at hbase
  simpa [F₁, F₂, Ft] using hbase

/-- Handoff from the Ando integral representation to the Lieb--Ando tensor
trace-concavity statement.

This theorem isolates the remaining analytic identity: once each tensor power
term is represented by the Audenaert/Ando resolvent integral, the already
proved integrated Ando trace concavity gives the desired Lieb trace
concavity. -/
theorem liebAndo_tensorTraceConcavity_of_andoIntegralRepresentation_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ)
    (hRep₁ :
      Matrix.kronecker (CFC.rpow A₁ p) (CFC.rpow B₁ (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁ ∂μ)
    (hRep₂ :
      Matrix.kronecker (CFC.rpow A₂ p) (CFC.rpow B₂ (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂ ∂μ)
    (hRept :
      Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) p)
          (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r
            (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) ∂μ) :
    t * ((Matrix.kronecker (CFC.rpow A₁ p) (CFC.rpow B₁ (1 - p))).trace).re +
        (1 - t) *
          ((Matrix.kronecker (CFC.rpow A₂ p) (CFC.rpow B₂ (1 - p))).trace).re
      ≤
    ((Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) p)
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - p))).trace).re := by
  have hconc :=
    andoResolventIntegrand_rpow_weighted_setIntegral_trace_concave_posDef'
      (a := a) (b := b) hs hA₁ hA₂ hB₁ hB₂ ht0 ht1 hr_pos hI₁ hI₂ hIt
  rw [hRep₁, hRep₂, hRept]
  exact hconc

/-- Handoff from the Ando integral representation to the Lieb--Ando tensor
Loewner-concavity statement.

This matrix-order version is stronger than the trace form and is the right
input for Epstein/Frank--Lieb positive trace functionals. -/
theorem liebAndo_tensorConcavity_of_andoIntegralRepresentation_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr_pos : ∀ r ∈ s, 0 < r)
    (hI₁ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁) s μ)
    (hI₂ : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂) s μ)
    (hIt : IntegrableOn
      (fun r : ℝ => (r ^ (p - 1)) •
        Matrix.andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂)) s μ)
    (hRep₁ :
      Matrix.kronecker (CFC.rpow A₁ p) (CFC.rpow B₁ (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₁ B₁ ∂μ)
    (hRep₂ :
      Matrix.kronecker (CFC.rpow A₂ p) (CFC.rpow B₂ (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r A₂ B₂ ∂μ)
    (hRept :
      Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) p)
          (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - p)) =
        ∫ r in s, (r ^ (p - 1)) •
          Matrix.andoResolventIntegrand (a := a) (b := b) r
            (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) ∂μ) :
    t • Matrix.kronecker (CFC.rpow A₁ p) (CFC.rpow B₁ (1 - p)) +
        (1 - t) •
          Matrix.kronecker (CFC.rpow A₂ p) (CFC.rpow B₂ (1 - p))
      ≤
    Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) p)
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - p)) := by
  have hconc :=
    andoResolventIntegrand_rpow_weighted_setIntegral_concave_posDef'
      (a := a) (b := b) hs hA₁ hA₂ hB₁ hB₂ ht0 ht1 hr_pos hI₁ hI₂ hIt
  rw [hRep₁, hRep₂, hRept]
  exact hconc

/-- Lieb--Ando tensor trace concavity with a positive definite right
argument.

This is the completed Frank--Lieb/Epstein core for the nonsingular reference
case: Audenaert's CFC integral representation supplies the tensor power term,
and Ando's resolvent concavity supplies the integrated trace inequality. -/
public theorem liebAndo_tensorTraceConcavity_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ)))).trace).re +
        (1 - t) *
          ((Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))).trace).re
      ≤
    ((Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ)))).trace).re := by
  obtain ⟨μ, hint, hrep⟩ := andoIntegralRepresentation_posDef (a := a) (b := b) hp
  have hAbar : (t • A₁ + (1 - t) • A₂).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hA₁ ht0)
      (Matrix.PosSemidef.smul hA₂ (sub_nonneg.mpr ht1))
  have hBbar : (t • B₁ + (1 - t) • B₂).PosDef :=
    Matrix.PosDef.convexCombination hB₁ hB₂ ht0 ht1
  exact
    liebAndo_tensorTraceConcavity_of_andoIntegralRepresentation_posDef
      (a := a) (b := b) (μ := μ) (s := Set.Ioi 0) measurableSet_Ioi
      hA₁ hA₂ hB₁ hB₂ ht0 ht1
      (by intro r hr; exact hr)
      (hint hA₁ hB₁)
      (hint hA₂ hB₂)
      (hint hAbar hBbar)
      (hrep hA₁ hB₁)
      (hrep hA₂ hB₂)
      (hrep hAbar hBbar)

/-- Lieb--Ando tensor Loewner concavity with a positive definite right
argument.

This strengthens `liebAndo_tensorTraceConcavity_posDef` from ordinary trace
to Loewner order, so any positive trace functional can be applied downstream. -/
public theorem liebAndo_tensorConcavity_posDef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ))) +
        (1 - t) •
          Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))
      ≤
    Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ))) := by
  obtain ⟨μ, hint, hrep⟩ := andoIntegralRepresentation_posDef (a := a) (b := b) hp
  have hAbar : (t • A₁ + (1 - t) • A₂).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hA₁ ht0)
      (Matrix.PosSemidef.smul hA₂ (sub_nonneg.mpr ht1))
  have hBbar : (t • B₁ + (1 - t) • B₂).PosDef :=
    Matrix.PosDef.convexCombination hB₁ hB₂ ht0 ht1
  exact
    liebAndo_tensorConcavity_of_andoIntegralRepresentation_posDef
      (a := a) (b := b) (μ := μ) (s := Set.Ioi 0) measurableSet_Ioi
      hA₁ hA₂ hB₁ hB₂ ht0 ht1
      (by intro r hr; exact hr)
      (hint hA₁ hB₁)
      (hint hA₂ hB₂)
      (hint hAbar hBbar)
      (hrep hA₁ hB₁)
      (hrep hA₂ hB₂)
      (hrep hAbar hBbar)

omit [DecidableEq a] in
/-- The real trace of `K ⊗ F x` is continuous in the right tensor factor. -/
public theorem cMatrix_kronecker_trace_re_tendsto_right
    {b : Type v} [Fintype b] [DecidableEq b]
    {X : Type*} {l : Filter X} {F : X → CMatrix b} {B : CMatrix b}
    (K : CMatrix a) (hF : Filter.Tendsto F l (nhds B)) :
    Filter.Tendsto
      (fun x : X => ((Matrix.kronecker K (F x)).trace).re)
      l
      (nhds ((Matrix.kronecker K B).trace.re)) := by
  have hcont :
      Continuous fun M : CMatrix b =>
        ((Matrix.kronecker K M).trace).re := by
    rw [continuous_iff_continuousAt]
    intro M
    have htrace : ContinuousAt (fun M : CMatrix b =>
        (Matrix.kronecker K M).trace) M := by
      simpa [Matrix.trace_kronecker] using
        ((continuous_const.mul
          (Continuous.matrix_trace continuous_id)).continuousAt : ContinuousAt
          (fun M : CMatrix b => K.trace * M.trace) M)
    exact Complex.continuous_re.continuousAt.comp htrace
  exact (hcont.tendsto B).comp hF

/-- Tensor-power trace continuity in the right tensor factor along
PSD-constrained filters. -/
public theorem cMatrix_tensorTrace_rpow_tendsto_right_of_tendsto_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {X : Type*} {l : Filter X} {F : X → CMatrix b} {B : CMatrix b}
    (A : CMatrix a) (p : ℝ)
    (hF : Filter.Tendsto F l (nhds B))
    (hFpsd : ∀ᶠ x in l, (F x).PosSemidef)
    (hB : B.PosSemidef) {q : ℝ} (hq : 0 < q) :
    Filter.Tendsto
      (fun x : X =>
        ((Matrix.kronecker (CFC.rpow A p) (CFC.rpow (F x) q)).trace).re)
      l
      (nhds ((Matrix.kronecker (CFC.rpow A p) (CFC.rpow B q)).trace.re)) := by
  have hpow :
      Filter.Tendsto (fun x : X => CFC.rpow (F x) q) l
        (nhds (CFC.rpow B q)) :=
    cMatrix_rpow_tendsto_of_tendsto_posSemidef hq hF hFpsd hB
  exact
    cMatrix_kronecker_trace_re_tendsto_right
      (a := a) (b := b) (K := CFC.rpow A p) hpow

omit [Fintype a] [DecidableEq a] in
/-- Tensoring on the right by a convergent matrix family is continuous. -/
public theorem cMatrix_kronecker_tendsto_right
    {b : Type v} [Fintype b] [DecidableEq b]
    {X : Type*} {l : Filter X} {F : X → CMatrix b} {B : CMatrix b}
    (K : CMatrix a) (hF : Filter.Tendsto F l (nhds B)) :
    Filter.Tendsto (fun x : X => Matrix.kronecker K (F x)) l
      (nhds (Matrix.kronecker K B)) := by
  have hcont : Continuous fun M : CMatrix b => Matrix.kronecker K M := by
    apply continuous_matrix
    intro i j
    rcases i with ⟨ia, ib⟩
    rcases j with ⟨ja, jb⟩
    simpa [Matrix.kronecker, Matrix.kroneckerMap_apply] using
      (continuous_const.mul (continuous_apply_apply ib jb) :
        Continuous fun M : CMatrix b => K ia ja * M ib jb)
  exact (hcont.tendsto B).comp hF

/-- Tensor-power continuity in the right tensor factor along PSD-constrained
filters. -/
public theorem cMatrix_tensor_rpow_tendsto_right_of_tendsto_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {X : Type*} {l : Filter X} {F : X → CMatrix b} {B : CMatrix b}
    (A : CMatrix a) (p : ℝ)
    (hF : Filter.Tendsto F l (nhds B))
    (hFpsd : ∀ᶠ x in l, (F x).PosSemidef)
    (hB : B.PosSemidef) {q : ℝ} (hq : 0 < q) :
    Filter.Tendsto
      (fun x : X =>
        Matrix.kronecker (CFC.rpow A p) (CFC.rpow (F x) q))
      l
      (nhds (Matrix.kronecker (CFC.rpow A p) (CFC.rpow B q))) := by
  have hpow :
      Filter.Tendsto (fun x : X => CFC.rpow (F x) q) l
        (nhds (CFC.rpow B q)) :=
    cMatrix_rpow_tendsto_of_tendsto_posSemidef hq hF hFpsd hB
  exact
    cMatrix_kronecker_tendsto_right
      (a := a) (b := b) (K := CFC.rpow A p) hpow

/-- Lieb--Ando tensor trace concavity with unrestricted PSD right arguments.

This is the PSD closure of `liebAndo_tensorTraceConcavity_posDef`, obtained by
regularizing the right tensor factors by `ε I` and passing to the limit from the
positive side. -/
public theorem liebAndo_tensorTraceConcavity_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ)))).trace).re +
        (1 - t) *
          ((Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))).trace).re
      ≤
    ((Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ)))).trace).re := by
  let q : ℝ := 1 - (p : ℝ)
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let B₁ε : ℝ → CMatrix b := fun ε => B₁ + ε • (1 : CMatrix b)
  let B₂ε : ℝ → CMatrix b := fun ε => B₂ + ε • (1 : CMatrix b)
  let Bbar : CMatrix b := t • B₁ + (1 - t) • B₂
  let Bbarε : ℝ → CMatrix b := fun ε => t • B₁ε ε + (1 - t) • B₂ε ε
  have hq_pos : 0 < q := by
    have hp_lt_one : (p : ℝ) < 1 := by exact_mod_cast hp.2
    dsimp [q]
    linarith
  have hBbar : Bbar.PosSemidef := by
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hB₁ ht0)
      (Matrix.PosSemidef.smul hB₂ (sub_nonneg.mpr ht1))
  have hB₁ε_tend : Filter.Tendsto B₁ε l (nhds B₁) := by
    simpa [B₁ε, l] using cMatrix_tendsto_add_pos_smul_one (A := B₁)
  have hB₂ε_tend : Filter.Tendsto B₂ε l (nhds B₂) := by
    simpa [B₂ε, l] using cMatrix_tendsto_add_pos_smul_one (A := B₂)
  have hBbarε_tend : Filter.Tendsto Bbarε l (nhds Bbar) := by
    have htend :
        Filter.Tendsto
          (fun ε : ℝ => t • B₁ε ε + (1 - t) • B₂ε ε)
          l (nhds (t • B₁ + (1 - t) • B₂)) :=
      (hB₁ε_tend.const_smul t).add (hB₂ε_tend.const_smul (1 - t))
    simpa [Bbarε, Bbar] using htend
  have hB₁ε_psd : ∀ᶠ ε in l, (B₁ε ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hB₁ hε.le
  have hB₂ε_psd : ∀ᶠ ε in l, (B₂ε ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hB₂ hε.le
  have hBbarε_psd : ∀ᶠ ε in l, (Bbarε ε).PosSemidef := by
    filter_upwards [hB₁ε_psd, hB₂ε_psd] with ε h₁ h₂
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul h₁ ht0)
      (Matrix.PosSemidef.smul h₂ (sub_nonneg.mpr ht1))
  have hleft₁ :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q)).trace).re)
        l
        (nhds ((Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ q)).trace.re)) :=
    cMatrix_tensorTrace_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := A₁) (p := (p : ℝ))
      hB₁ε_tend hB₁ε_psd hB₁ hq_pos
  have hleft₂ :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q)).trace).re)
        l
        (nhds ((Matrix.kronecker
          (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ q)).trace.re)) :=
    cMatrix_tensorTrace_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := A₂) (p := (p : ℝ))
      hB₂ε_tend hB₂ε_psd hB₂ hq_pos
  have hright :
      Filter.Tendsto
        (fun ε : ℝ =>
          ((Matrix.kronecker
            (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
            (CFC.rpow (Bbarε ε) q)).trace).re)
        l
        (nhds ((Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
          (CFC.rpow Bbar q)).trace.re)) :=
    cMatrix_tensorTrace_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := t • A₁ + (1 - t) • A₂) (p := (p : ℝ))
      hBbarε_tend hBbarε_psd hBbar hq_pos
  have hleft :
      Filter.Tendsto
        (fun ε : ℝ =>
          t * ((Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q)).trace).re +
            (1 - t) * ((Matrix.kronecker
              (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q)).trace).re)
        l
        (nhds
          (t * ((Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ q)).trace).re +
            (1 - t) * ((Matrix.kronecker
              (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ q)).trace).re)) :=
    (hleft₁.const_mul t).add (hleft₂.const_mul (1 - t))
  have hineq_eventual :
      (fun ε : ℝ =>
        t * ((Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q)).trace).re +
          (1 - t) * ((Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q)).trace).re)
        ≤ᶠ[l]
      (fun ε : ℝ =>
        ((Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
          (CFC.rpow (Bbarε ε) q)).trace).re) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    have hB₁ε_pos : (B₁ε ε).PosDef := by
      simpa [B₁ε] using
        State.cMatrix_posSemidef_add_pos_smul_one_posDef hB₁ hε
    have hB₂ε_pos : (B₂ε ε).PosDef := by
      simpa [B₂ε] using
        State.cMatrix_posSemidef_add_pos_smul_one_posDef hB₂ hε
    have hpos :=
      liebAndo_tensorTraceConcavity_posDef
        (a := a) (b := b) (p := p) hp
        (A₁ := A₁) (A₂ := A₂)
        (B₁ := B₁ε ε) (B₂ := B₂ε ε)
        hA₁ hA₂ hB₁ε_pos hB₂ε_pos ht0 ht1
    simpa [Bbarε, q] using hpos
  have hlimit :=
    le_of_tendsto_of_tendsto hleft hright hineq_eventual
  simpa [q, Bbar] using hlimit

/-- Lieb--Ando tensor Loewner concavity with unrestricted PSD right arguments.

This is the matrix-order PSD closure of `liebAndo_tensorConcavity_posDef`.
It is stronger than `liebAndo_tensorTraceConcavity_posSemidef` and is the
Frank--Lieb core needed before applying positive trace functionals in the
low-alpha Q-functional route. -/
public theorem liebAndo_tensorConcavity_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ))) +
        (1 - t) •
          Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))
      ≤
    Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ))) := by
  let q : ℝ := 1 - (p : ℝ)
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let B₁ε : ℝ → CMatrix b := fun ε => B₁ + ε • (1 : CMatrix b)
  let B₂ε : ℝ → CMatrix b := fun ε => B₂ + ε • (1 : CMatrix b)
  let Bbar : CMatrix b := t • B₁ + (1 - t) • B₂
  let Bbarε : ℝ → CMatrix b := fun ε => t • B₁ε ε + (1 - t) • B₂ε ε
  have hq_pos : 0 < q := by
    have hp_lt_one : (p : ℝ) < 1 := by exact_mod_cast hp.2
    dsimp [q]
    linarith
  have hBbar : Bbar.PosSemidef := by
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hB₁ ht0)
      (Matrix.PosSemidef.smul hB₂ (sub_nonneg.mpr ht1))
  have hB₁ε_tend : Filter.Tendsto B₁ε l (nhds B₁) := by
    simpa [B₁ε, l] using cMatrix_tendsto_add_pos_smul_one (A := B₁)
  have hB₂ε_tend : Filter.Tendsto B₂ε l (nhds B₂) := by
    simpa [B₂ε, l] using cMatrix_tendsto_add_pos_smul_one (A := B₂)
  have hBbarε_tend : Filter.Tendsto Bbarε l (nhds Bbar) := by
    have htend :
        Filter.Tendsto
          (fun ε : ℝ => t • B₁ε ε + (1 - t) • B₂ε ε)
          l (nhds (t • B₁ + (1 - t) • B₂)) :=
      (hB₁ε_tend.const_smul t).add (hB₂ε_tend.const_smul (1 - t))
    simpa [Bbarε, Bbar] using htend
  have hB₁ε_psd : ∀ᶠ ε in l, (B₁ε ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hB₁ hε.le
  have hB₂ε_psd : ∀ᶠ ε in l, (B₂ε ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact cMatrix_posSemidef_add_nonneg_smul_one_posSemidef hB₂ hε.le
  have hBbarε_psd : ∀ᶠ ε in l, (Bbarε ε).PosSemidef := by
    filter_upwards [hB₁ε_psd, hB₂ε_psd] with ε h₁ h₂
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul h₁ ht0)
      (Matrix.PosSemidef.smul h₂ (sub_nonneg.mpr ht1))
  have hleft₁ :
      Filter.Tendsto
        (fun ε : ℝ =>
          Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q))
        l
        (nhds (Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ q))) :=
    cMatrix_tensor_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := A₁) (p := (p : ℝ))
      hB₁ε_tend hB₁ε_psd hB₁ hq_pos
  have hleft₂ :
      Filter.Tendsto
        (fun ε : ℝ =>
          Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q))
        l
        (nhds (Matrix.kronecker
          (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ q))) :=
    cMatrix_tensor_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := A₂) (p := (p : ℝ))
      hB₂ε_tend hB₂ε_psd hB₂ hq_pos
  have hright :
      Filter.Tendsto
        (fun ε : ℝ =>
          Matrix.kronecker
            (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
            (CFC.rpow (Bbarε ε) q))
        l
        (nhds (Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
          (CFC.rpow Bbar q))) :=
    cMatrix_tensor_rpow_tendsto_right_of_tendsto_posSemidef
      (a := a) (b := b) (A := t • A₁ + (1 - t) • A₂) (p := (p : ℝ))
      hBbarε_tend hBbarε_psd hBbar hq_pos
  have hleft :
      Filter.Tendsto
        (fun ε : ℝ =>
          t • Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q) +
          (1 - t) • Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q))
        l
        (nhds
          (t • Matrix.kronecker
            (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ q) +
          (1 - t) • Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ q))) :=
    (hleft₁.const_smul t).add (hleft₂.const_smul (1 - t))
  have hineq_eventual :
      (fun ε : ℝ =>
        t • Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow (B₁ε ε) q) +
        (1 - t) • Matrix.kronecker
          (CFC.rpow A₂ (p : ℝ)) (CFC.rpow (B₂ε ε) q))
        ≤ᶠ[l]
      (fun ε : ℝ =>
        Matrix.kronecker
          (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
          (CFC.rpow (Bbarε ε) q)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    have hB₁ε_pos : (B₁ε ε).PosDef := by
      simpa [B₁ε] using
        State.cMatrix_posSemidef_add_pos_smul_one_posDef hB₁ hε
    have hB₂ε_pos : (B₂ε ε).PosDef := by
      simpa [B₂ε] using
        State.cMatrix_posSemidef_add_pos_smul_one_posDef hB₂ hε
    have hpos :=
      liebAndo_tensorConcavity_posDef
        (a := a) (b := b) (p := p) hp
        (A₁ := A₁) (A₂ := A₂)
        (B₁ := B₁ε ε) (B₂ := B₂ε ε)
        hA₁ hA₂ hB₁ε_pos hB₂ε_pos ht0 ht1
    simpa [Bbarε, q] using hpos
  have hlimit :=
    cMatrix_le_of_tendsto hleft hright hineq_eventual
  simpa [q, Bbar] using hlimit

/-- Lieb--Ando tensor concavity after applying an arbitrary positive trace
functional.

This is the positive-functional form needed for the Epstein/Frank--Lieb
handoff: after vectorizing the fixed Kraus/weight matrix into a PSD tensor
weight `W`, the remaining concavity is exactly this theorem. -/
public theorem liebAndo_tensorWeightedTraceConcavity_posSemidef
    {b : Type v} [Fintype b] [DecidableEq b]
    {p : ℝ≥0} (hp : p ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A₁ A₂ : CMatrix a} {B₁ B₂ : CMatrix b} {W : CMatrix (a × b)}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    (hW : W.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * ((W * Matrix.kronecker
          (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ)))).trace).re +
        (1 - t) *
          ((W * Matrix.kronecker
            (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))).trace).re
      ≤
    ((W * Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ)))).trace).re := by
  let M₁ : CMatrix (a × b) :=
    Matrix.kronecker (CFC.rpow A₁ (p : ℝ)) (CFC.rpow B₁ (1 - (p : ℝ)))
  let M₂ : CMatrix (a × b) :=
    Matrix.kronecker (CFC.rpow A₂ (p : ℝ)) (CFC.rpow B₂ (1 - (p : ℝ)))
  let Mt : CMatrix (a × b) :=
    Matrix.kronecker
      (CFC.rpow (t • A₁ + (1 - t) • A₂) (p : ℝ))
      (CFC.rpow (t • B₁ + (1 - t) • B₂) (1 - (p : ℝ)))
  have hmat : t • M₁ + (1 - t) • M₂ ≤ Mt := by
    simpa [M₁, M₂, Mt] using
      liebAndo_tensorConcavity_posSemidef
        (a := a) (b := b) (p := p) hp
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
        hA₁ hA₂ hB₁ hB₂ ht0 ht1
  have htrace :=
    cMatrix_trace_mul_le_of_le_posSemidef_left hW hmat
  have hleft :
      ((W * (t • M₁ + (1 - t) • M₂)).trace).re =
        t * ((W * M₁).trace).re + (1 - t) * ((W * M₂).trace).re := by
    rw [mul_add, Matrix.trace_add, Complex.add_re]
    simp [Matrix.trace_smul, Complex.mul_re]
  rw [hleft] at htrace
  simpa [M₁, M₂, Mt] using htrace

end

end QIT
