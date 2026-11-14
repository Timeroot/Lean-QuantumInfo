/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.RandomnessExtractionOptimized
public import QIT.Classical.Bridge
public import QIT.Information.Entropy.Log2Lemmas

/-!
# Converse-side randomness-extraction helpers

This module starts the converse route for source-strength randomness extraction
with the reusable deterministic postprocessing step from the source proof:
applying a function to the classical register cannot improve the conditional
min-entropy feasibility constraint.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe uF uZ uS ue

noncomputable section

/-- Reindex a deterministic graph state from `((Z × S) × E)` to
`S × (Z × E)`, so tracing out `S` leaves the original `Z × E` cq state. -/
def deterministicGraphSourceMarginalEquiv
    (Z : Type uZ) (S : Type uS) (e : Type ue) :
    Prod (Prod Z S) e ≃ Prod S (Prod Z e) where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun y := ((y.2.1, y.1), y.2.2)
  left_inv := by
    intro x
    rcases x with ⟨⟨z, s⟩, i⟩
    rfl
  right_inv := by
    intro y
    rcases y with ⟨s, ⟨z, i⟩⟩
    rfl

/-- The source proof's graph embedding isometry on the classical source
register, sending `z` to `(z, g z)`. -/
def deterministicGraphSourceIsometry
    {Z : Type uZ} {S : Type uS} [Fintype Z] [DecidableEq Z]
    [Fintype S] [DecidableEq S] (g : Z → S) :
    ReferenceIsometry Z (Prod Z S) :=
  ReferenceIsometry.ofInjective (fun z => (z, g z)) (by
    intro z z' h
    exact congrArg Prod.fst h)

section FiberPsdSplit

open scoped Matrix
open Matrix
local postfix:1024 "ᴴ" => Matrix.conjTranspose

variable {ι : Type uZ} {β : Type ue}
variable [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

private def fiberGram (Y : Matrix β (Prod ι β) ℂ) (i : ι) : CMatrix β :=
  let Yi : CMatrix β := fun x y => Y x (i, y)
  Yi * Yiᴴ

private def stackedPsdSqrt (A : ι → CMatrix β) : Matrix β (Prod ι β) ℂ :=
  fun x ib => psdSqrt (A ib.1) x ib.2

private def fiberMatrix (Y : Matrix β (Prod ι β) ℂ) (i : ι) : CMatrix β :=
  fun x y => Y x (i, y)

omit [DecidableEq ι] in
private theorem stacked_psdSqrt_gram
    (A : ι → CMatrix β) (hA : ∀ i, (A i).PosSemidef) :
    stackedPsdSqrt A * (stackedPsdSqrt A)ᴴ = ∑ i : ι, A i := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  change
    (∑ ib : Prod ι β,
        psdSqrt (A ib.1) x ib.2 * star (psdSqrt (A ib.1) y ib.2)) =
      (∑ i : ι, A i) x y
  rw [Matrix.sum_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    (∑ b : β, psdSqrt (A i) x b * star (psdSqrt (A i) y b)) =
        (psdSqrt (A i) * psdSqrt (A i)) x y := by
          simp only [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← (psdSqrt_isHermitian (A i)).apply b y]
    _ = A i x y := by
          rw [psdSqrt_mul_self_of_posSemidef (hA i)]

omit [DecidableEq ι] [DecidableEq β] in
private theorem fiber_gram_sum
    (Y : Matrix β (Prod ι β) ℂ) :
    (∑ i : ι, fiberGram Y i) = Y * Yᴴ := by
  classical
  ext x y
  rw [Matrix.sum_apply]
  simp only [fiberGram, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]

omit [Fintype ι] [DecidableEq ι] [DecidableEq β] in
private theorem fiber_gram_pos
    (Y : Matrix β (Prod ι β) ℂ) (i : ι) :
    (fiberGram Y i).PosSemidef := by
  let Yi : CMatrix β := fun x y => Y x (i, y)
  simpa [Yi, Matrix.conjTranspose_conjTranspose] using
    Matrix.posSemidef_conjTranspose_mul_self (Matrix.conjTranspose Yi)

omit [DecidableEq ι] in
private theorem stacked_overlap_trace
    (A : ι → CMatrix β) (Y : Matrix β (Prod ι β) ℂ) :
    (((stackedPsdSqrt A)ᴴ * Y).trace) =
      ∑ i : ι, (((psdSqrt (A i))ᴴ * fiberMatrix Y i).trace) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, stackedPsdSqrt,
    fiberMatrix]
  rw [Fintype.sum_prod_type]

omit [DecidableEq ι] in
private theorem stacked_overlap_abs_le_sum_abs
    (A : ι → CMatrix β) (Y : Matrix β (Prod ι β) ℂ) :
    Complex.abs (((stackedPsdSqrt A)ᴴ * Y).trace) ≤
      ∑ i : ι, Complex.abs ((((psdSqrt (A i))ᴴ * fiberMatrix Y i).trace)) := by
  rw [stacked_overlap_trace]
  simpa [Complex.abs] using
    norm_sum_le (Finset.univ : Finset ι)
      (fun i : ι => (((psdSqrt (A i))ᴴ * fiberMatrix Y i).trace))

private def stateOfPsdTracePos
    (M : CMatrix β) (hM : M.PosSemidef) (htr : 0 < M.trace.re) : State β where
  matrix := (M.trace.re)⁻¹ • M
  pos := Matrix.PosSemidef.smul hM (by
    exact_mod_cast inv_nonneg.mpr htr.le)
  trace_eq_one := by
    rw [Matrix.trace_smul]
    have htrC : ((M.trace.re : ℂ) ≠ 0) := by exact_mod_cast htr.ne'
    have htrace_im : M.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hM).2.symm
    apply Complex.ext
    · simp [Complex.real_smul, htr.ne']
    · simp [Complex.real_smul, htrace_im]

private theorem stateOfPsdTracePos_matrix
    (M : CMatrix β) (hM : M.PosSemidef) (htr : 0 < M.trace.re) :
    (stateOfPsdTracePos M hM htr).matrix = (M.trace.re)⁻¹ • M :=
  rfl

private theorem sqrtMatrix_stateOfPsdTracePos
    (M : CMatrix β) (hM : M.PosSemidef) (htr : 0 < M.trace.re) :
    (stateOfPsdTracePos M hM htr).sqrtMatrix =
      (((Real.sqrt M.trace.re)⁻¹ : ℝ) : ℂ) • psdSqrt M := by
  rw [State.sqrtMatrix, stateOfPsdTracePos_matrix]
  change psdSqrt ((((M.trace.re)⁻¹ : ℝ) : ℂ) • M) =
    (((Real.sqrt M.trace.re)⁻¹ : ℝ) : ℂ) • psdSqrt M
  have hinv_nonneg : 0 ≤ (M.trace.re)⁻¹ := inv_nonneg.mpr htr.le
  rw [psdSqrt_real_smul hinv_nonneg hM]
  congr 1
  rw [Real.sqrt_inv]

private theorem normalized_psdSqrt_gram
    (A : CMatrix β) (hA : A.PosSemidef) (htr : 0 < A.trace.re) :
    let c : ℂ := (((Real.sqrt A.trace.re)⁻¹ : ℝ) : ℂ)
    (c • psdSqrt A) * (c • psdSqrt A)ᴴ =
      (stateOfPsdTracePos A hA htr).matrix := by
  let ρ : State β := stateOfPsdTracePos A hA htr
  have hsqrt : ρ.sqrtMatrix =
      (((Real.sqrt A.trace.re)⁻¹ : ℝ) : ℂ) • psdSqrt A := by
    simpa [ρ] using sqrtMatrix_stateOfPsdTracePos A hA htr
  dsimp only
  rw [← hsqrt]
  rw [ρ.sqrtMatrix_isHermitian.eq, ρ.sqrtMatrix_mul_self]

omit [DecidableEq β] in
private theorem amplitude_self_mul_conjTranspose_pos
    (Y : CMatrix β) : (Y * Yᴴ).PosSemidef := by
  simpa [Matrix.conjTranspose_conjTranspose] using
    Matrix.posSemidef_conjTranspose_mul_self Yᴴ

private theorem normalized_amplitude_gram
    (Y : CMatrix β) (htr : 0 < (Y * Yᴴ).trace.re) :
    let B : CMatrix β := Y * Yᴴ
    let c : ℂ := (((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ)
    (c • Y) * (c • Y)ᴴ =
      (stateOfPsdTracePos B
        (by
          dsimp [B]
          exact amplitude_self_mul_conjTranspose_pos Y)
        htr).matrix := by
  let B : CMatrix β := Y * Yᴴ
  have hB : B.PosSemidef := by
    dsimp [B]
    exact amplitude_self_mul_conjTranspose_pos Y
  change
    ((((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ) • Y) *
        ((((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ) • Y)ᴴ =
      (stateOfPsdTracePos B hB htr).matrix
  rw [stateOfPsdTracePos_matrix]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  change
    ((((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ) *
        star (((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ)) • B =
      (((B.trace.re)⁻¹ : ℝ) : ℂ) • B
  congr 1
  have hstar :
      star ((((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ)) =
        (((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hstar, ← Complex.ofReal_mul]
  congr 1
  have hsqrt_ne : Real.sqrt B.trace.re ≠ 0 := (Real.sqrt_pos.mpr htr).ne'
  field_simp [hsqrt_ne, htr.ne']
  rw [Real.sq_sqrt htr.le]
  rw [div_self htr.ne']

omit [DecidableEq ι] in
private theorem normalized_stackedPsdSqrt_gram
    (A : ι → CMatrix β) (hA : ∀ i, (A i).PosSemidef)
    (htr : 0 < (∑ i : ι, A i).trace.re) :
    let Asum : CMatrix β := ∑ i : ι, A i
    let c : ℂ := (((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ)
    (c • stackedPsdSqrt A) * (c • stackedPsdSqrt A)ᴴ =
      (stateOfPsdTracePos Asum
        (by
          dsimp [Asum]
          exact Matrix.posSemidef_sum Finset.univ fun i _ => hA i)
        htr).matrix := by
  classical
  let Asum : CMatrix β := ∑ i : ι, A i
  have hAsum : Asum.PosSemidef := by
    dsimp [Asum]
    exact Matrix.posSemidef_sum Finset.univ fun i _ => hA i
  change
    ((((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ) • stackedPsdSqrt A) *
        ((((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ) • stackedPsdSqrt A)ᴴ =
      (stateOfPsdTracePos Asum hAsum htr).matrix
  rw [stateOfPsdTracePos_matrix]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [stacked_psdSqrt_gram A hA]
  change
    ((((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ) *
        star (((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ)) • Asum =
      (((Asum.trace.re)⁻¹ : ℝ) : ℂ) • Asum
  congr 1
  have hstar :
      star ((((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ)) =
        (((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hstar, ← Complex.ofReal_mul]
  congr 1
  have hsqrt_ne : Real.sqrt Asum.trace.re ≠ 0 := (Real.sqrt_pos.mpr htr).ne'
  field_simp [hsqrt_ne, htr.ne']
  rw [Real.sq_sqrt htr.le]
  rw [div_self htr.ne']

private theorem abs_trace_psdSqrt_mul_amplitude_le
    (A : CMatrix β) (hA : A.PosSemidef) (Y : CMatrix β) :
    Complex.abs (((psdSqrt A)ᴴ * Y).trace) ≤
      traceNorm (psdSqrt A * psdSqrt (Y * Yᴴ)) := by
  classical
  let B : CMatrix β := Y * Yᴴ
  have hB : B.PosSemidef := by
    dsimp [B]
    exact amplitude_self_mul_conjTranspose_pos Y
  by_cases hAtr0 : A.trace.re = 0
  · have hAtrace : A.trace = 0 := by
      apply Complex.ext
      · exact hAtr0
      · exact (Matrix.PosSemidef.trace_nonneg hA).2.symm
    have hAzero : A = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hA).mp hAtrace
    simp [hAzero, psdSqrt]
  by_cases hBtr0 : B.trace.re = 0
  · have hBtrace : B.trace = 0 := by
      apply Complex.ext
      · exact hBtr0
      · exact (Matrix.PosSemidef.trace_nonneg hB).2.symm
    have hBzero : B = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hB).mp hBtrace
    have hYzero : Y = 0 := by
      exact Matrix.self_mul_conjTranspose_eq_zero.mp (by simpa [B] using hBzero)
    simp [hYzero]
  have hAtr_pos : 0 < A.trace.re := by
    exact lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hA).1 (Ne.symm hAtr0)
  have hBtr_pos : 0 < B.trace.re := by
    exact lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hB).1 (Ne.symm hBtr0)
  let ρ : State β := stateOfPsdTracePos A hA hAtr_pos
  let σ : State β := stateOfPsdTracePos B hB hBtr_pos
  let cA : ℂ := (((Real.sqrt A.trace.re)⁻¹ : ℝ) : ℂ)
  let cB : ℂ := (((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ)
  let Xn : CMatrix β := cA • psdSqrt A
  let Yn : CMatrix β := cB • Y
  have hXgram : Xn * Xnᴴ = ρ.matrix := by
    change
      ((((Real.sqrt A.trace.re)⁻¹ : ℝ) : ℂ) • psdSqrt A) *
          ((((Real.sqrt A.trace.re)⁻¹ : ℝ) : ℂ) • psdSqrt A)ᴴ =
        ρ.matrix
    simpa [ρ] using normalized_psdSqrt_gram A hA hAtr_pos
  have hYgram : Yn * Ynᴴ = σ.matrix := by
    change
      ((((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ) • Y) *
          ((((Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ) • Y)ᴴ =
        σ.matrix
    simpa [σ, B] using normalized_amplitude_gram Y hBtr_pos
  have hXtrace : (Xn * Xnᴴ).trace = 1 := by
    rw [hXgram, ρ.trace_eq_one]
  have hYtrace : (Yn * Ynᴴ).trace = 1 := by
    rw [hYgram, σ.trace_eq_one]
  let Ψ : PureVector (Prod β β) := PureVector.ofAmplitudeMatrix Xn hXtrace
  let Φ : PureVector (Prod β β) := PureVector.ofAmplitudeMatrix Yn hYtrace
  have hΨ : Ψ.Purifies ρ := by
    exact PureVector.ofAmplitudeMatrix_purifies hXgram hXtrace
  have hΦ : Φ.Purifies σ := by
    exact PureVector.ofAmplitudeMatrix_purifies hYgram hYtrace
  have hbound :
      Complex.abs ((Xnᴴ * Yn).trace) ≤
        traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix) := by
    have h := PureVector.abs_overlap_le_fidelity hΨ hΦ
    have hoverlap : Ψ.overlap Φ = (Xnᴴ * Yn).trace := by
      rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
      simp [Ψ, Φ, PureVector.ofAmplitudeMatrix_amplitudeMatrix]
    simpa [hoverlap, State.fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix]
      using h
  let a : ℝ := Real.sqrt A.trace.re
  let b : ℝ := Real.sqrt B.trace.re
  let k : ℝ := a * b
  have ha_pos : 0 < a := by
    simpa [a] using Real.sqrt_pos.mpr hAtr_pos
  have hb_pos : 0 < b := by
    simpa [b] using Real.sqrt_pos.mpr hBtr_pos
  have hk_pos : 0 < k := by
    exact mul_pos ha_pos hb_pos
  have hleft_norm :
      Complex.abs ((Xnᴴ * Yn).trace) =
        k⁻¹ * Complex.abs (((psdSqrt A)ᴴ * Y).trace) := by
    subst Xn
    subst Yn
    subst cA
    subst cB
    subst k
    subst a
    subst b
    simp [Matrix.conjTranspose_smul, Matrix.trace_smul, Complex.abs,
      Real.sqrt_nonneg, abs_of_nonneg, mul_assoc, mul_comm]
  have hright_norm :
      traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix) =
        k⁻¹ * traceNorm (psdSqrt A * psdSqrt (Y * Yᴴ)) := by
    have hρsqrt := sqrtMatrix_stateOfPsdTracePos A hA hAtr_pos
    have hσsqrt := sqrtMatrix_stateOfPsdTracePos B hB hBtr_pos
    rw [hρsqrt, hσsqrt]
    subst k
    subst a
    subst b
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hscalar :
        (↑(√(Matrix.trace A).re)⁻¹ * ↑(√(Matrix.trace B).re)⁻¹ : ℂ) =
          ((((Real.sqrt A.trace.re)⁻¹ * (Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ)) := by
      rw [Complex.ofReal_mul]
    rw [hscalar]
    change
      traceNorm
          (((((Real.sqrt A.trace.re)⁻¹ * (Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ) •
            (psdSqrt A * psdSqrt B))) =
        (Real.sqrt A.trace.re * Real.sqrt B.trace.re)⁻¹ *
          traceNorm (psdSqrt A * psdSqrt (Y * Yᴴ))
    have hscale_nonneg :
        0 ≤ (Real.sqrt A.trace.re)⁻¹ * (Real.sqrt B.trace.re)⁻¹ := by
      exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    rw [traceNorm_real_smul_eq hscale_nonneg]
    congr 1
    field_simp [(Real.sqrt_pos.mpr hAtr_pos).ne',
      (Real.sqrt_pos.mpr hBtr_pos).ne']
  have hscaled := mul_le_mul_of_nonneg_left hbound hk_pos.le
  rw [hleft_norm, hright_norm] at hscaled
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  field_simp [hk_ne] at hscaled
  simpa [mul_assoc] using hscaled

private theorem exists_fiber_psd_split_traceNorm_bound
    [Nonempty ι] (A : ι → CMatrix β) (hA : ∀ i, (A i).PosSemidef)
    (B : CMatrix β) (hB : B.PosSemidef) :
    ∃ blocks : ι → CMatrix β,
      (∀ i, (blocks i).PosSemidef) ∧
      (∑ i : ι, blocks i) = B ∧
      traceNorm (psdSqrt (∑ i : ι, A i) * psdSqrt B) ≤
        ∑ i : ι, traceNorm (psdSqrt (A i) * psdSqrt (blocks i)) := by
  classical
  let Asum : CMatrix β := ∑ i : ι, A i
  have hAsum : Asum.PosSemidef := by
    dsimp [Asum]
    exact Matrix.posSemidef_sum Finset.univ fun i _ => hA i
  by_cases hBtr0 : B.trace.re = 0
  · have hBtrace : B.trace = 0 := by
      apply Complex.ext
      · exact hBtr0
      · exact (Matrix.PosSemidef.trace_nonneg hB).2.symm
    have hBzero : B = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hB).mp hBtrace
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro i
      exact Matrix.PosSemidef.zero
    · simp [hBzero]
    · simp [hBzero]
  by_cases hAtr0 : Asum.trace.re = 0
  · have hAtrace : Asum.trace = 0 := by
      apply Complex.ext
      · exact hAtr0
      · exact (Matrix.PosSemidef.trace_nonneg hAsum).2.symm
    have hAzero : Asum = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hAsum).mp hAtrace
    let i0 : ι := Classical.choice inferInstance
    let blocks : ι → CMatrix β := fun i => if i = i0 then B else 0
    refine ⟨blocks, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = i0
      · simp [blocks, hi, hB]
      · change (if i = i0 then B else 0).PosSemidef
        rw [if_neg hi]
        exact Matrix.PosSemidef.zero
    · dsimp [blocks]
      rw [Finset.sum_eq_single i0]
      · simp
      · intro i _ hi
        simp [hi]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i0))
    · have hleft_zero :
          traceNorm (psdSqrt (∑ i : ι, A i) * psdSqrt B) = 0 := by
        have hsum_eq : (∑ i : ι, A i) = 0 := by simpa [Asum] using hAzero
        simp [hsum_eq]
      rw [hleft_zero]
      exact Finset.sum_nonneg fun i _ => traceNorm_nonneg _
  have hAtr_pos : 0 < Asum.trace.re := by
    exact lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hAsum).1 (Ne.symm hAtr0)
  have hBtr_pos : 0 < B.trace.re := by
    exact lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hB).1 (Ne.symm hBtr0)
  let ρ : State β := stateOfPsdTracePos Asum hAsum hAtr_pos
  let σ : State β := stateOfPsdTracePos B hB hBtr_pos
  let cA : ℂ := (((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ)
  let X : Matrix β (Prod ι β) ℂ := stackedPsdSqrt A
  let Xn : Matrix β (Prod ι β) ℂ := cA • X
  have hXgram : Xn * Xnᴴ = ρ.matrix := by
    change
      ((((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ) • stackedPsdSqrt A) *
          ((((Real.sqrt Asum.trace.re)⁻¹ : ℝ) : ℂ) • stackedPsdSqrt A)ᴴ =
        ρ.matrix
    simpa [ρ, Asum] using normalized_stackedPsdSqrt_gram A hA hAtr_pos
  have hXtrace : (Xn * Xnᴴ).trace = 1 := by
    rw [hXgram, ρ.trace_eq_one]
  let Ψ : PureVector (Prod (Prod ι β) β) := PureVector.ofAmplitudeMatrix Xn hXtrace
  have hΨ : Ψ.Purifies ρ := by
    exact PureVector.ofAmplitudeMatrix_purifies hXgram hXtrace
  have hcard : Fintype.card β ≤ Fintype.card (Prod ι β) := by
    have hιpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    calc
      Fintype.card β ≤ Fintype.card ι * Fintype.card β :=
        Nat.le_mul_of_pos_left (Fintype.card β) hιpos
      _ = Fintype.card (Prod ι β) := by simp [Fintype.card_prod]
  obtain ⟨Φ, hΦ, hoverlap_sq⟩ :=
    PureVector.exists_purification_with_overlapSq_eq_squaredFidelity
      (Ψ := Ψ) (ρ := ρ) (σ := σ) hΨ hcard
  have hoverlap_abs :
      Complex.abs (Ψ.overlap Φ) = ρ.fidelity σ := by
    rw [PureVector.overlapSq_eq_normSq, Complex.normSq_eq_norm_sq,
      State.squaredFidelity_eq_fidelity_sq] at hoverlap_sq
    exact (sq_eq_sq₀ (norm_nonneg _) (State.fidelity_nonneg ρ σ)).mp hoverlap_sq
  let b : ℝ := Real.sqrt B.trace.re
  let Y : Matrix β (Prod ι β) ℂ := ((b : ℝ) : ℂ) • Φ.amplitudeMatrix
  have hYgram : Y * Yᴴ = B := by
    dsimp [Y, b]
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hΦgram : Φ.amplitudeMatrix * Φ.amplitudeMatrixᴴ = σ.matrix :=
      PureVector.purifies_amplitudeMatrix_mul_conjTranspose_eq hΦ
    rw [hΦgram]
    rw [stateOfPsdTracePos_matrix]
    rw [smul_smul]
    have hcoefR : Real.sqrt B.trace.re * Real.sqrt B.trace.re * (B.trace.re)⁻¹ = 1 := by
      calc
        Real.sqrt B.trace.re * Real.sqrt B.trace.re * (B.trace.re)⁻¹ =
            (Real.sqrt B.trace.re) ^ 2 * (B.trace.re)⁻¹ := by ring
        _ = B.trace.re * (B.trace.re)⁻¹ := by rw [Real.sq_sqrt hBtr_pos.le]
        _ = 1 := mul_inv_cancel₀ hBtr0
    have hcoefRstar :
        Real.sqrt B.trace.re * star (Real.sqrt B.trace.re) * (B.trace.re)⁻¹ = 1 := by
      simpa using hcoefR
    rw [hcoefRstar]
    simp
  have hoverlap_trace :
      Ψ.overlap Φ = (Xnᴴ * Φ.amplitudeMatrix).trace := by
    rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
    simp [Ψ, PureVector.ofAmplitudeMatrix_amplitudeMatrix]
  let a : ℝ := Real.sqrt Asum.trace.re
  let k : ℝ := a * b
  have ha_pos : 0 < a := by
    simpa [a] using Real.sqrt_pos.mpr hAtr_pos
  have hb_pos : 0 < b := by
    simpa [b] using Real.sqrt_pos.mpr hBtr_pos
  have hk_pos : 0 < k := mul_pos ha_pos hb_pos
  have htotal_scale :
      Complex.abs (Ψ.overlap Φ) =
        k⁻¹ * Complex.abs ((Xᴴ * Y).trace) := by
    rw [hoverlap_trace]
    subst Xn
    subst X
    subst cA
    subst Y
    subst k
    subst a
    subst b
    simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, Complex.abs, Real.sqrt_nonneg, abs_of_nonneg,
      mul_assoc, mul_left_comm, mul_comm]
    rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr hBtr_pos).ne', one_mul]
  have hfidelity_scale :
      ρ.fidelity σ =
        k⁻¹ * traceNorm (psdSqrt Asum * psdSqrt B) := by
    rw [State.fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix]
    have hρsqrt := sqrtMatrix_stateOfPsdTracePos Asum hAsum hAtr_pos
    have hσsqrt := sqrtMatrix_stateOfPsdTracePos B hB hBtr_pos
    rw [hρsqrt, hσsqrt]
    subst k
    subst a
    subst b
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hscalar :
        (↑(√(Matrix.trace Asum).re)⁻¹ * ↑(√(Matrix.trace B).re)⁻¹ : ℂ) =
          ((((Real.sqrt Asum.trace.re)⁻¹ * (Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ)) := by
      rw [Complex.ofReal_mul]
    rw [hscalar]
    change
      traceNorm
          (((((Real.sqrt Asum.trace.re)⁻¹ * (Real.sqrt B.trace.re)⁻¹ : ℝ) : ℂ) •
            (psdSqrt Asum * psdSqrt B))) =
        (Real.sqrt Asum.trace.re * Real.sqrt B.trace.re)⁻¹ *
          traceNorm (psdSqrt Asum * psdSqrt B)
    have hscale_nonneg :
        0 ≤ (Real.sqrt Asum.trace.re)⁻¹ * (Real.sqrt B.trace.re)⁻¹ := by
      exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    rw [traceNorm_real_smul_eq hscale_nonneg]
    congr 1
    field_simp [(Real.sqrt_pos.mpr hAtr_pos).ne',
      (Real.sqrt_pos.mpr hBtr_pos).ne']
  have htotal_eq :
      traceNorm (psdSqrt Asum * psdSqrt B) =
        Complex.abs ((Xᴴ * Y).trace) := by
    have hscaled : k⁻¹ * Complex.abs ((Xᴴ * Y).trace) =
        k⁻¹ * traceNorm (psdSqrt Asum * psdSqrt B) := by
      rw [← htotal_scale, ← hfidelity_scale, hoverlap_abs]
    have hk_ne : k ≠ 0 := ne_of_gt hk_pos
    exact (mul_left_cancel₀ (inv_ne_zero hk_ne) hscaled).symm
  refine ⟨fun i => fiberGram Y i, ?_, ?_, ?_⟩
  · intro i
    exact fiber_gram_pos Y i
  · rw [fiber_gram_sum, hYgram]
  · calc
      traceNorm (psdSqrt (∑ i : ι, A i) * psdSqrt B) =
          traceNorm (psdSqrt Asum * psdSqrt B) := by rfl
      _ = Complex.abs ((Xᴴ * Y).trace) := htotal_eq
      _ = Complex.abs (((stackedPsdSqrt A)ᴴ * Y).trace) := by rfl
      _ ≤ ∑ i : ι, Complex.abs ((((psdSqrt (A i))ᴴ * fiberMatrix Y i).trace)) :=
        stacked_overlap_abs_le_sum_abs A Y
      _ ≤ ∑ i : ι, traceNorm (psdSqrt (A i) * psdSqrt (fiberGram Y i)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [fiberGram, fiberMatrix] using
          abs_trace_psdSqrt_mul_amplitude_le (A i) (hA i) (fiberMatrix Y i)

private theorem sum_fiber_subtype_eq_if
    {α : Type uZ} {δ : Type uS} {M : Type*}
    [Fintype α] [DecidableEq δ] [AddCommMonoid M]
    (g : α → δ) (s : δ) (fb : {x : α // g x = s} → M) :
    (∑ x : α, if h : g x = s then fb ⟨x, h⟩ else 0) =
      ∑ xf : {x : α // g x = s}, fb xf := by
  classical
  let f : α → M := fun x => if h : g x = s then fb ⟨x, h⟩ else 0
  have hsub :
      (∑ x : {x : α // g x = s}, f x.1) =
        ∑ x ∈ (Finset.univ : Finset α) with g x = s, f x := by
    simpa [f] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset α))
        (p := fun x : α => g x = s) (f := f))
  calc
    (∑ x : α, if h : g x = s then fb ⟨x, h⟩ else 0) =
        ∑ x ∈ (Finset.univ : Finset α) with g x = s, f x := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : g x = s
          · simp [f, hx]
          · simp [f, hx]
    _ = ∑ x : {x : α // g x = s}, f x.1 := hsub.symm
    _ = ∑ xf : {x : α // g x = s}, fb xf := by
          refine Finset.sum_congr rfl fun xf _ => ?_
          simp [f, xf.2]

end FiberPsdSplit

namespace Ensemble

variable {Z : Type uZ} {S : Type uS} {e : Type ue}
variable [Fintype Z] [DecidableEq Z]
variable [Fintype S] [DecidableEq S]
variable [Fintype e] [DecidableEq e]

/-- The cq state obtained by applying a deterministic function to the classical
label of an ensemble. -/
def deterministicPostprocessCqState (E : Ensemble Z e) (g : Z → S) : State (Prod S e) where
  matrix := ∑ z, (E.probs z) •
    Matrix.kronecker (Matrix.single (g z) (g z) (1 : ℂ)) (E.states z).matrix
  pos := by
    exact Matrix.posSemidef_sum Finset.univ fun z _ =>
      (((posSemidef_single (g z)).kronecker (E.states z).pos).smul
        (NNReal.coe_nonneg (E.probs z)))
  trace_eq_one := by
    simp only [Matrix.trace_sum, Matrix.trace_smul]
    calc
      (∑ z : Z, (E.probs z) •
          (Matrix.kronecker (Matrix.single (g z) (g z) (1 : ℂ))
            (E.states z).matrix).trace) =
          ∑ z : Z, ((E.probs z : ℝ≥0) : ℂ) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        have htrace :
            (Matrix.kronecker (Matrix.single (g z) (g z) (1 : ℂ))
              (E.states z).matrix).trace = 1 := by
          simpa [Matrix.kronecker] using
            (Matrix.trace_kronecker
              (Matrix.single (g z) (g z) (1 : ℂ))
              (E.states z).matrix).trans
              (by rw [trace_single_one, if_pos rfl, (E.states z).trace_eq_one]; norm_num)
        rw [htrace]
        exact (Algebra.algebraMap_eq_smul_one _).symm
      _ = ↑(∑ z : Z, E.probs z) := by simp
      _ = 1 := by rw [E.weights_sum]; rfl

omit [DecidableEq Z] in
@[simp]
theorem deterministicPostprocessCqState_matrix (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicPostprocessCqState g).matrix =
      ∑ z, (E.probs z) •
        Matrix.kronecker (Matrix.single (g z) (g z) (1 : ℂ)) (E.states z).matrix :=
  rfl

omit [DecidableEq Z] in
/-- The deterministically postprocessed cq center is already diagonal in its
source coordinate, hence source-coordinate pinching fixes it. -/
theorem deterministicPostprocessCqState_toSubnormalized_sourceCoordinatePinch
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicPostprocessCqState g).toSubnormalized.sourceCoordinatePinch =
      (E.deterministicPostprocessCqState g).toSubnormalized := by
  apply SubnormalizedState.ext
  rw [SubnormalizedState.sourceCoordinatePinch_matrix, State.toSubnormalized_matrix]
  change (SubnormalizedState.sourceCoordinatePinchChannel (a := S) (b := e)).map
      (E.deterministicPostprocessCqState g).matrix =
    (E.deterministicPostprocessCqState g).matrix
  rw [deterministicPostprocessCqState_matrix]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  change (SubnormalizedState.sourceCoordinatePinchChannel (a := S) (b := e)).map
      ((E.probs z : ℂ) •
        Matrix.kronecker (Matrix.single (g z) (g z) (1 : ℂ)) (E.states z).matrix) =
    (E.probs z : ℂ) •
      Matrix.kronecker (Matrix.single (g z) (g z) (1 : ℂ)) (E.states z).matrix
  rw [map_smul]
  rw [SubnormalizedState.sourceCoordinatePinchChannel_map_singleTensor]

/-- The cq graph state that remembers both the original classical label `z`
and the deterministic image `g z`. -/
def deterministicGraphCqState (E : Ensemble Z e) (g : Z → S) : State (Prod (Prod Z S) e) :=
  E.deterministicPostprocessCqState fun z => (z, g z)

@[simp]
theorem deterministicGraphCqState_matrix (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicGraphCqState g).matrix =
      ∑ z, (E.probs z) •
        Matrix.kronecker (Matrix.single (z, g z) (z, g z) (1 : ℂ)) (E.states z).matrix :=
  rfl

/-- The deterministic graph cq center is the original cq center with the
source register embedded by `z ↦ (z, g z)`. -/
theorem deterministicGraphCqState_toSubnormalized_eq_sourceIsometryApply
    (E : Ensemble Z e) (g : Z → S) :
    E.cqState.toSubnormalized.sourceIsometryApply
        (deterministicGraphSourceIsometry g) =
      (E.deterministicGraphCqState g).toSubnormalized := by
  apply SubnormalizedState.ext
  rw [SubnormalizedState.sourceIsometryApply_matrix,
    State.toSubnormalized_matrix, State.toSubnormalized_matrix]
  rw [← MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]
  change MatrixMap.kron (MatrixMap.ofReferenceIsometry (deterministicGraphSourceIsometry g))
      (Channel.idChannel e).map E.cqState.matrix =
    (E.deterministicGraphCqState g).matrix
  rw [Ensemble.cqState_matrix, deterministicGraphCqState_matrix]
  rw [map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  change MatrixMap.kron (MatrixMap.ofReferenceIsometry (deterministicGraphSourceIsometry g))
      (Channel.idChannel e).map
        ((E.probs z : ℂ) •
          Matrix.kronecker (Matrix.single z z (1 : ℂ)) (E.states z).matrix) =
    (E.probs z : ℂ) •
      Matrix.kronecker (Matrix.single (z, g z) (z, g z) (1 : ℂ)) (E.states z).matrix
  rw [map_smul]
  congr 1
  rw [MatrixMap.kron_apply_kronecker]
  rw [deterministicGraphSourceIsometry]
  rw [MatrixMap.ofReferenceIsometry_ofInjective_single
    (fun z : Z => (z, g z)) (by
      intro z z' h
      exact congrArg Prod.fst h) z z]
  simp [Channel.idChannel, MatrixMap.ofKraus]

/-- The graph state as an ensemble over the enlarged classical label
`Z × S`, with zero probability away from the graph of `g`. -/
def deterministicGraphEnsemble (E : Ensemble Z e) (g : Z → S) :
    Ensemble (Prod Z S) e where
  probs := fun zs => if zs.2 = g zs.1 then E.probs zs.1 else 0
  weights_sum := by
    classical
    calc
      (∑ zs : Prod Z S, if zs.2 = g zs.1 then E.probs zs.1 else 0) =
          ∑ z : Z, ∑ s : S, if s = g z then E.probs z else 0 := by
        rw [Fintype.sum_prod_type]
      _ = ∑ z : Z, E.probs z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_eq_single (g z)]
        · simp
        · intro s _ hs
          simp [hs]
        · simp
      _ = 1 := E.weights_sum
  states := fun zs => E.states zs.1

omit [DecidableEq Z] in
@[simp]
theorem deterministicGraphEnsemble_probs (E : Ensemble Z e) (g : Z → S)
    (zs : Prod Z S) :
    (E.deterministicGraphEnsemble g).probs zs =
      if zs.2 = g zs.1 then E.probs zs.1 else 0 :=
  rfl

omit [DecidableEq Z] in
@[simp]
theorem deterministicGraphEnsemble_states (E : Ensemble Z e) (g : Z → S)
    (zs : Prod Z S) :
    (E.deterministicGraphEnsemble g).states zs = E.states zs.1 :=
  rfl

/-- The enlarged-label graph ensemble realizes the same cq state as
`deterministicGraphCqState`. -/
theorem deterministicGraphEnsemble_cqState (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicGraphEnsemble g).cqState =
      E.deterministicGraphCqState g := by
  apply State.ext
  ext x y
  rcases x with ⟨⟨zx, sx⟩, i⟩
  rcases y with ⟨⟨zy, sy⟩, j⟩
  simp only [Ensemble.cqState_matrix, deterministicGraphCqState_matrix, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    deterministicGraphEnsemble_probs, deterministicGraphEnsemble_states]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single (g z)]
  · simp [Matrix.single_apply]
  · intro s _ hs
    simp [hs]
  · simp

omit [DecidableEq Z] in
/-- Applying the second projection to the graph ensemble recovers the
deterministically postprocessed cq state. -/
theorem deterministicGraphEnsemble_postprocess_snd
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicGraphEnsemble g).deterministicPostprocessCqState Prod.snd =
      E.deterministicPostprocessCqState g := by
  apply State.ext
  ext x y
  rcases x with ⟨s, i⟩
  rcases y with ⟨s', j⟩
  simp only [deterministicPostprocessCqState_matrix, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    deterministicGraphEnsemble_probs, deterministicGraphEnsemble_states]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single (g z)]
  · simp [Matrix.single_apply]
  · intro s0 _ hs0
    simp [hs0]
  · simp

/-- Applying the first projection to the graph ensemble recovers the original
cq state. -/
theorem deterministicGraphEnsemble_postprocess_fst
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicGraphEnsemble g).deterministicPostprocessCqState Prod.fst =
      E.cqState := by
  apply State.ext
  ext x y
  rcases x with ⟨z, i⟩
  rcases y with ⟨z', j⟩
  simp only [deterministicPostprocessCqState_matrix, Ensemble.cqState_matrix,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    deterministicGraphEnsemble_probs, deterministicGraphEnsemble_states]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z0 _ => ?_
  rw [Finset.sum_eq_single (g z0)]
  · simp [Matrix.single_apply]
  · intro s0 _ hs0
    simp [hs0]
  · simp

/-- Tracing the graph state's original `Z` register leaves the deterministic
postprocessed `S × E` cq state. -/
theorem deterministicGraphCqState_marginalSE (E : Ensemble Z e) (g : Z → S) :
    ((E.deterministicGraphCqState g).reindex (Equiv.prodAssoc Z S e)).marginalB =
      E.deterministicPostprocessCqState g := by
  apply State.ext
  ext x y
  rcases x with ⟨s, i⟩
  rcases y with ⟨s', j⟩
  simp only [State.marginalB_matrix, State.reindex_matrix, deterministicGraphCqState_matrix,
    deterministicPostprocessCqState_matrix, partialTraceA, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [Equiv.prodAssoc, Matrix.single_apply, NNReal.smul_def]
  by_cases hs : g z = s
  · by_cases hs' : g z = s'
    · rw [if_pos ⟨hs, hs'⟩]
      have hss' : s = s' := hs.symm.trans hs'
      subst s'
      rw [Finset.sum_eq_single z]
      · simp [hs]
      · intro x _ hx
        rw [if_neg]
        intro h
        exact hx h.1.1.symm
      · simp
    · rw [if_neg (fun h => hs' h.2)]
      exact Finset.sum_eq_zero fun x _ => by simp [hs']
  · rw [if_neg (fun h => hs h.1)]
    exact Finset.sum_eq_zero fun x _ => by simp [hs]

/-- The subnormalized `S × E` marginal of the embedded graph center is the
subnormalized deterministic postprocessed center. -/
theorem deterministicGraphCqState_toSubnormalized_marginalSE
    (E : Ensemble Z e) (g : Z → S) :
    ((E.deterministicGraphCqState g).reindex
        (Equiv.prodAssoc Z S e)).toSubnormalized.marginalB =
      (E.deterministicPostprocessCqState g).toSubnormalized := by
  apply SubnormalizedState.ext
  simpa [SubnormalizedState.marginalB_matrix, State.toSubnormalized_matrix] using
    congrArg State.matrix (E.deterministicGraphCqState_marginalSE g)

/-- Tracing the graph state's deterministic `S` register leaves the original
`Z × E` cq state. -/
theorem deterministicGraphCqState_marginalZE (E : Ensemble Z e) (g : Z → S) :
    ((E.deterministicGraphCqState g).reindex
        (deterministicGraphSourceMarginalEquiv Z S e)).marginalB =
      E.cqState := by
  apply State.ext
  ext x y
  rcases x with ⟨z, i⟩
  rcases y with ⟨z', j⟩
  simp only [State.marginalB_matrix, State.reindex_matrix, deterministicGraphCqState_matrix,
    Ensemble.cqState_matrix, partialTraceA, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z0 _ => ?_
  simp [deterministicGraphSourceMarginalEquiv, Matrix.single_apply, NNReal.smul_def]
  by_cases hz : z0 = z
  · by_cases hz' : z0 = z'
    · rw [if_pos ⟨hz, hz'⟩]
      have hzz' : z = z' := hz.symm.trans hz'
      subst z'
      rw [Finset.sum_eq_single (g z0)]
      · simp [hz]
      · intro s _ hs
        rw [if_neg]
        intro h
        exact hs h.1.2.symm
      · simp
    · rw [if_neg (fun h => hz' h.2)]
      exact Finset.sum_eq_zero fun s _ => by simp [hz']
  · rw [if_neg (fun h => hz h.1)]
    exact Finset.sum_eq_zero fun s _ => by simp [hz]

/-- The subnormalized `Z × E` marginal of the embedded graph center is the
subnormalized original cq center. -/
theorem deterministicGraphCqState_toSubnormalized_marginalZE
    (E : Ensemble Z e) (g : Z → S) :
    ((E.deterministicGraphCqState g).reindex
        (deterministicGraphSourceMarginalEquiv Z S e)).toSubnormalized.marginalB =
      E.cqState.toSubnormalized := by
  apply SubnormalizedState.ext
  simpa [SubnormalizedState.marginalB_matrix, State.toSubnormalized_matrix] using
    congrArg State.matrix (E.deterministicGraphCqState_marginalZE g)

/-- Any subnormalized state in a purified-distance ball around the graph center
projects to a state in the corresponding ball around the deterministic
postprocessed center. -/
theorem deterministicGraphCqState_purifiedBall_marginalSE_of_purifiedBall
    (E : Ensemble Z e) (g : Z → S)
    {τ : SubnormalizedState (Prod Z (Prod S e))} {ε : ℝ}
    (hτ : ((E.deterministicGraphCqState g).reindex
        (Equiv.prodAssoc Z S e)).toSubnormalized.purifiedBall ε τ) :
    (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
      ε τ.marginalB := by
  have h :=
    SubnormalizedState.purifiedBall_marginalB_of_purifiedBall
      (ρ := ((E.deterministicGraphCqState g).reindex
        (Equiv.prodAssoc Z S e)).toSubnormalized) (σ := τ) hτ
  rwa [E.deterministicGraphCqState_toSubnormalized_marginalSE g] at h

/-- A graph-ball witness induces a smooth min-entropy candidate for the
deterministic postprocessed center by tracing out the original `Z` register. -/
theorem deterministicGraphCqState_marginalSE_smoothCandidate_of_purifiedBall
    (E : Ensemble Z e) (g : Z → S)
    {τ : SubnormalizedState (Prod Z (Prod S e))} {ε : ℝ}
    (hτ : ((E.deterministicGraphCqState g).reindex
        (Equiv.prodAssoc Z S e)).toSubnormalized.purifiedBall ε τ) :
    SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := S)
      (E.deterministicPostprocessCqState g).toSubnormalized ε
      τ.marginalB.conditionalMinEntropyRaw :=
  ⟨τ.marginalB, E.deterministicGraphCqState_purifiedBall_marginalSE_of_purifiedBall g hτ,
    rfl⟩

/-- Any subnormalized state in a purified-distance ball around the graph center
projects to a state in the corresponding ball around the original cq center. -/
theorem deterministicGraphCqState_purifiedBall_marginalZE_of_purifiedBall
    (E : Ensemble Z e) (g : Z → S)
    {τ : SubnormalizedState (Prod S (Prod Z e))} {ε : ℝ}
    (hτ : ((E.deterministicGraphCqState g).reindex
        (deterministicGraphSourceMarginalEquiv Z S e)).toSubnormalized.purifiedBall ε τ) :
    E.cqState.toSubnormalized.purifiedBall ε τ.marginalB := by
  have h :=
    SubnormalizedState.purifiedBall_marginalB_of_purifiedBall
      (ρ := ((E.deterministicGraphCqState g).reindex
        (deterministicGraphSourceMarginalEquiv Z S e)).toSubnormalized) (σ := τ) hτ
  rwa [E.deterministicGraphCqState_toSubnormalized_marginalZE g] at h

/-- A graph-ball witness induces a smooth min-entropy candidate for the
original cq center by tracing out the deterministic `S` register. -/
theorem deterministicGraphCqState_marginalZE_smoothCandidate_of_purifiedBall
    (E : Ensemble Z e) (g : Z → S)
    {τ : SubnormalizedState (Prod S (Prod Z e))} {ε : ℝ}
    (hτ : ((E.deterministicGraphCqState g).reindex
        (deterministicGraphSourceMarginalEquiv Z S e)).toSubnormalized.purifiedBall ε τ) :
    SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := Z)
      E.cqState.toSubnormalized ε τ.marginalB.conditionalMinEntropyRaw :=
  ⟨τ.marginalB, E.deterministicGraphCqState_purifiedBall_marginalZE_of_purifiedBall g hτ,
    rfl⟩

omit [DecidableEq Z] in
/-- A diagonal output block is the sum of all input cq blocks in its preimage. -/
theorem deterministicPostprocessCqState_block (E : Ensemble Z e) (g : Z → S) (s : S) :
    Classical.block (E.deterministicPostprocessCqState g).matrix s s =
      ∑ z, if g z = s then E.cqBlock z else 0 := by
  ext i j
  simp only [deterministicPostprocessCqState_matrix, Classical.block, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : g z = s
  · subst hz
    simp [Ensemble.cqBlock, NNReal.smul_def]
  · simp [hz]

omit [DecidableEq Z] in
/-- Filtering the deterministically postprocessed cq center to the image of
`g` leaves it unchanged. -/
theorem deterministicPostprocessCqState_toSubnormalized_sourceBlockFilter_image
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicPostprocessCqState g).toSubnormalized.sourceBlockFilter
        (fun s : S => ∃ z : Z, g z = s) =
      (E.deterministicPostprocessCqState g).toSubnormalized := by
  classical
  apply SubnormalizedState.ext
  rw [SubnormalizedState.sourceBlockFilter_matrix_eq_blockDiagonal]
  have hcenter :
      (E.deterministicPostprocessCqState g).toSubnormalized.matrix =
        Classical.blockDiagonal
          (fun s : S =>
            Classical.block
              (E.deterministicPostprocessCqState g).toSubnormalized.matrix s s) := by
    have h :=
      congrArg SubnormalizedState.matrix
        (E.deterministicPostprocessCqState_toSubnormalized_sourceCoordinatePinch g)
    rw [SubnormalizedState.sourceCoordinatePinch_matrix_eq_blockDiagonal] at h
    exact h.symm
  rw [hcenter]
  have hblocks :
      (fun s : S =>
          if ∃ z : Z, g z = s then
            Classical.block
              (Classical.blockDiagonal
                (fun s : S =>
                  Classical.block
                    (E.deterministicPostprocessCqState g).toSubnormalized.matrix s s))
              s s
          else 0) =
        (fun s : S =>
          Classical.block
            (E.deterministicPostprocessCqState g).toSubnormalized.matrix s s) := by
    funext s
    by_cases hs : ∃ z : Z, g z = s
    · simp [hs]
    · have hblock_zero :
          Classical.block
              (E.deterministicPostprocessCqState g).toSubnormalized.matrix s s = 0 := by
        rw [State.toSubnormalized_matrix, deterministicPostprocessCqState_block]
        apply Finset.sum_eq_zero
        intro z _
        have hz : g z ≠ s := fun h => hs ⟨z, h⟩
        simp [hz]
      simpa [hs] using hblock_zero.symm
  rw [hblocks]

/-- Each original cq block is dominated by the output block of its image under
the deterministic postprocessing function. -/
theorem cqBlock_le_deterministicPostprocessCqState_block
    (E : Ensemble Z e) (g : Z → S) (z : Z) :
    E.cqBlock z ≤ Classical.block (E.deterministicPostprocessCqState g).matrix (g z) (g z) := by
  classical
  rw [deterministicPostprocessCqState_block]
  have hzmem : z ∈ (Finset.univ : Finset Z) := Finset.mem_univ z
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hzmem]
  simp only [if_true]
  exact le_add_of_nonneg_right (by
    have hrest_psd :
        (∑ z' ∈ (Finset.univ : Finset Z).erase z,
          if g z' = g z then E.cqBlock z' else 0).PosSemidef := by
      exact Matrix.posSemidef_sum ((Finset.univ : Finset Z).erase z) fun z' _ => by
        by_cases hz' : g z' = g z
        · simpa [hz'] using (E.cqBlock_posSemidef z')
        · simpa [hz'] using (Matrix.PosSemidef.zero : (0 : CMatrix e).PosSemidef)
    simpa [Matrix.le_iff] using hrest_psd)

/-- Any source-coordinate-pinched postprocessed witness filtered to the image of
`g` has an exact algebraic preimage under deterministic source coarse-graining.
The construction assigns each reachable output block to one chosen source label
in its fiber and assigns zero to all other source labels. -/
theorem sourceImageFilteredWitness_exactSourcePreimage
    (E : Ensemble Z e) (g : Z → S)
    (ρSE' : SubnormalizedState (Prod S e)) :
    ∃ ρZE' : SubnormalizedState (Prod Z e),
      ρZE'.sourceDeterministicPostprocess g =
        ρSE'.sourceCoordinatePinch.sourceBlockFilter
          (fun s : S => ∃ z : Z, g z = s) := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  let imagePred : S → Prop := fun s : S => ∃ z : Z, g z = s
  let σSE : SubnormalizedState (Prod S e) :=
    ρSE'.sourceCoordinatePinch.sourceBlockFilter imagePred
  let rep : S → Z := fun s =>
    if hs : imagePred s then Classical.choose hs else Classical.choice inferInstance
  have hrep {s : S} (hs : imagePred s) : g (rep s) = s := by
    simpa [rep, hs] using (Classical.choose_spec hs)
  let blocks : Z → CMatrix e := fun z =>
    if z = rep (g z) then Classical.block σSE.matrix (g z) (g z) else 0
  have hσ_matrix :
      σSE.matrix =
        Classical.blockDiagonal
          (fun s : S =>
            if imagePred s then
              Classical.block ρSE'.sourceCoordinatePinch.matrix s s
            else 0) := by
    simpa [σSE, imagePred] using
      (SubnormalizedState.sourceBlockFilter_matrix_eq_blockDiagonal
        (ρSE'.sourceCoordinatePinch) imagePred)
  have hσ_blockDiagonal :
      Classical.blockDiagonal (fun s : S => Classical.block σSE.matrix s s) =
        σSE.matrix := by
    rw [hσ_matrix]
    apply congrArg Classical.blockDiagonal
    funext s
    exact Classical.blockDiagonal_block_self
      (fun s : S =>
        if imagePred s then Classical.block ρSE'.sourceCoordinatePinch.matrix s s else 0) s
  have hcoarse_matrix :
      SubnormalizedState.sourceDeterministicPostprocessMap (a := Z) (b := e) g
          (Classical.blockDiagonal blocks) =
        σSE.matrix := by
    rw [SubnormalizedState.sourceDeterministicPostprocessMap_apply_eq_blockDiagonal]
    have hblocks :
        (fun s : S =>
            ∑ z : Z,
              if g z = s then
                Classical.block (Classical.blockDiagonal blocks) z z
              else 0) =
          (fun s : S => Classical.block σSE.matrix s s) := by
      funext s
      by_cases hs : imagePred s
      · rw [Finset.sum_eq_single (rep s)]
        · have hrep_s : g (rep s) = s := hrep hs
          have hselected : rep s = rep (g (rep s)) := by
            rw [hrep_s]
          rw [if_pos hrep_s]
          rw [Classical.blockDiagonal_block_self]
          change blocks (rep s) = Classical.block σSE.matrix s s
          change
            (if rep s = rep (g (rep s)) then
                Classical.block σSE.matrix (g (rep s)) (g (rep s))
              else 0) =
            Classical.block σSE.matrix s s
          rw [if_pos hselected, hrep_s]
        · intro z _ hz
          by_cases hgz : g z = s
          · have hz_not_selected : z ≠ rep (g z) := by
              intro hz_selected
              apply hz
              calc
                z = rep (g z) := hz_selected
                _ = rep s := by rw [hgz]
            rw [if_pos hgz]
            rw [Classical.blockDiagonal_block_self]
            change blocks z = 0
            change
              (if z = rep (g z) then Classical.block σSE.matrix (g z) (g z) else 0) =
                0
            rw [if_neg hz_not_selected]
          · rw [if_neg hgz]
        · simp
      · have hsum_zero :
            (∑ z : Z,
              if g z = s then
                Classical.block (Classical.blockDiagonal blocks) z z
              else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro z _
          have hgz : g z ≠ s := fun h => hs ⟨z, h⟩
          rw [if_neg hgz]
        have hblock_zero : Classical.block σSE.matrix s s = 0 := by
          rw [hσ_matrix]
          rw [Classical.blockDiagonal_block_self]
          rw [if_neg hs]
        rw [hsum_zero, hblock_zero]
    rw [hblocks, hσ_blockDiagonal]
  have hpos : ∀ z, (blocks z).PosSemidef := by
    intro z
    by_cases hz : z = rep (g z)
    · change
        (if z = rep (g z) then Classical.block σSE.matrix (g z) (g z) else 0).PosSemidef
      rw [if_pos hz]
      exact σSE.pos.submatrix (fun i : e => (g z, i))
    · change
        (if z = rep (g z) then Classical.block σSE.matrix (g z) (g z) else 0).PosSemidef
      rw [if_neg hz]
      exact Matrix.PosSemidef.zero
  have htrace : (∑ z, (blocks z).trace).re ≤ 1 := by
    have htrace_eq :
        (∑ z : Z, (blocks z).trace) = σSE.matrix.trace := by
      have htp :=
        SubnormalizedState.sourceDeterministicPostprocessMap_tracePreserving
          (a := Z) (b := e) g (Classical.blockDiagonal blocks)
      rw [hcoarse_matrix] at htp
      rw [← Classical.blockDiagonal_trace blocks]
      exact htp.symm
    rw [htrace_eq]
    exact σSE.trace_le_one
  let ρZE' : SubnormalizedState (Prod Z e) :=
    SubnormalizedState.ofClassicalBlocks blocks hpos htrace
  refine ⟨ρZE', ?_⟩
  apply SubnormalizedState.ext
  rw [← ρZE'.sourceDeterministicPostprocessMap_apply_matrix g]
  simpa [ρZE', σSE, imagePred, SubnormalizedState.ofClassicalBlocks_matrix] using hcoarse_matrix

/-- A fiberwise block split with an exact deterministic coarse-graining and the
corresponding trace-norm fidelity bound gives the exact-source generalized
fidelity lift needed by the smooth postprocessing endpoint.  This separates the
smooth bookkeeping from the remaining matrix-analysis split theorem. -/
theorem sourceImageFilteredWitness_exactSourceFidelityLift_of_blocks
    (E : Ensemble Z e) (g : Z → S)
    (ρSE' : SubnormalizedState (Prod S e))
    (blocks : Z → CMatrix e)
    (hblocks : ∀ z, (blocks z).PosSemidef)
    (htrace : (∑ z, (blocks z).trace).re ≤ 1)
    (hcoarse :
      SubnormalizedState.sourceDeterministicPostprocessMap
          (a := Z) (b := e) g (Classical.blockDiagonal blocks) =
        (ρSE'.sourceCoordinatePinch.sourceBlockFilter
          (fun s : S => ∃ z : Z, g z = s)).matrix)
    (hnorm :
      traceNorm
          (psdSqrt (E.deterministicPostprocessCqState g).toSubnormalized.matrix *
            psdSqrt
              (ρSE'.sourceCoordinatePinch.sourceBlockFilter
                (fun s : S => ∃ z : Z, g z = s)).matrix) ≤
        traceNorm
          (psdSqrt E.cqState.toSubnormalized.matrix *
            psdSqrt (Classical.blockDiagonal blocks))) :
    ∃ ρZE' : SubnormalizedState (Prod Z e),
      (E.deterministicPostprocessCqState g).toSubnormalized.generalizedFidelity
          (ρSE'.sourceCoordinatePinch.sourceBlockFilter
            (fun s : S => ∃ z : Z, g z = s)) ≤
        E.cqState.toSubnormalized.generalizedFidelity ρZE' ∧
      ρZE'.sourceDeterministicPostprocess g =
        ρSE'.sourceCoordinatePinch.sourceBlockFilter
          (fun s : S => ∃ z : Z, g z = s) := by
  classical
  let imagePred : S → Prop := fun s : S => ∃ z : Z, g z = s
  let σSE : SubnormalizedState (Prod S e) :=
    ρSE'.sourceCoordinatePinch.sourceBlockFilter imagePred
  let ρZE' : SubnormalizedState (Prod Z e) :=
    SubnormalizedState.ofClassicalBlocks blocks hblocks htrace
  have hpost_trace :
      (E.deterministicPostprocessCqState g).toSubnormalized.matrix.trace.re = 1 := by
    change (E.deterministicPostprocessCqState g).matrix.trace.re = 1
    rw [(E.deterministicPostprocessCqState g).trace_eq_one]
    norm_num
  have hsource_trace :
      E.cqState.toSubnormalized.matrix.trace.re = 1 := by
    change E.cqState.matrix.trace.re = 1
    rw [E.cqState.trace_eq_one]
    norm_num
  refine ⟨ρZE', ?_, ?_⟩
  · exact
      SubnormalizedState.generalizedFidelity_le_of_traceNorm_psdSqrt_mul_le_of_trace_one
        (ρ := (E.deterministicPostprocessCqState g).toSubnormalized)
        (σ := σSE)
        (τ := E.cqState.toSubnormalized)
        (υ := ρZE') hpost_trace hsource_trace
        (by
          simpa [σSE, ρZE', imagePred, SubnormalizedState.ofClassicalBlocks_matrix]
            using hnorm)
  · apply SubnormalizedState.ext
    rw [← ρZE'.sourceDeterministicPostprocessMap_apply_matrix g]
    simpa [σSE, ρZE', imagePred, SubnormalizedState.ofClassicalBlocks_matrix]
      using hcoarse

/-- Blockwise fidelity bounds over the output fibers imply the exact-source
generalized-fidelity lift.  This is the handoff expected from a future
fiberwise PSD fidelity-decomposition theorem. -/
theorem sourceImageFilteredWitness_exactSourceFidelityLift_of_block_bounds
    (E : Ensemble Z e) (g : Z → S)
    (ρSE' : SubnormalizedState (Prod S e))
    (blocks : Z → CMatrix e)
    (hblocks : ∀ z, (blocks z).PosSemidef)
    (htrace : (∑ z, (blocks z).trace).re ≤ 1)
    (hcoarse :
      SubnormalizedState.sourceDeterministicPostprocessMap
          (a := Z) (b := e) g (Classical.blockDiagonal blocks) =
        (ρSE'.sourceCoordinatePinch.sourceBlockFilter
          (fun s : S => ∃ z : Z, g z = s)).matrix)
    (hblock :
      ∀ s : S,
        traceNorm
            (psdSqrt
                (Classical.block
                  (E.deterministicPostprocessCqState g).toSubnormalized.matrix s s) *
              psdSqrt
                (Classical.block
                  (ρSE'.sourceCoordinatePinch.sourceBlockFilter
                    (fun s : S => ∃ z : Z, g z = s)).matrix s s)) ≤
          ∑ z : Z,
            if g z = s then
              traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z))
            else 0) :
    ∃ ρZE' : SubnormalizedState (Prod Z e),
      (E.deterministicPostprocessCqState g).toSubnormalized.generalizedFidelity
          (ρSE'.sourceCoordinatePinch.sourceBlockFilter
            (fun s : S => ∃ z : Z, g z = s)) ≤
        E.cqState.toSubnormalized.generalizedFidelity ρZE' ∧
      ρZE'.sourceDeterministicPostprocess g =
        ρSE'.sourceCoordinatePinch.sourceBlockFilter
          (fun s : S => ∃ z : Z, g z = s) := by
  classical
  let imagePred : S → Prop := fun s : S => ∃ z : Z, g z = s
  let ρS : SubnormalizedState (Prod S e) :=
    (E.deterministicPostprocessCqState g).toSubnormalized
  let σSE : SubnormalizedState (Prod S e) :=
    ρSE'.sourceCoordinatePinch.sourceBlockFilter imagePred
  have hρS_blockDiagonal :
      ρS.matrix =
        Classical.blockDiagonal (fun s : S => Classical.block ρS.matrix s s) := by
    have h :=
      congrArg SubnormalizedState.matrix
        (E.deterministicPostprocessCqState_toSubnormalized_sourceCoordinatePinch g)
    rw [SubnormalizedState.sourceCoordinatePinch_matrix_eq_blockDiagonal] at h
    simpa [ρS] using h.symm
  have hσ_matrix :
      σSE.matrix =
        Classical.blockDiagonal
          (fun s : S =>
            if imagePred s then
              Classical.block ρSE'.sourceCoordinatePinch.matrix s s
            else 0) := by
    simpa [σSE, imagePred] using
      (SubnormalizedState.sourceBlockFilter_matrix_eq_blockDiagonal
        (ρSE'.sourceCoordinatePinch) imagePred)
  have hσ_blockDiagonal :
      σSE.matrix =
        Classical.blockDiagonal (fun s : S => Classical.block σSE.matrix s s) := by
    have hdiag :
        Classical.blockDiagonal (fun s : S => Classical.block σSE.matrix s s) =
          σSE.matrix := by
      rw [hσ_matrix]
      apply congrArg Classical.blockDiagonal
      funext s
      exact Classical.blockDiagonal_block_self
        (fun s : S =>
          if imagePred s then Classical.block ρSE'.sourceCoordinatePinch.matrix s s else 0) s
    exact hdiag.symm
  have hρS_blocks : ∀ s : S, (Classical.block ρS.matrix s s).PosSemidef := by
    intro s
    exact ρS.pos.submatrix (fun i : e => (s, i))
  have hσ_blocks : ∀ s : S, (Classical.block σSE.matrix s s).PosSemidef := by
    intro s
    exact σSE.pos.submatrix (fun i : e => (s, i))
  have hleft :
      traceNorm (psdSqrt ρS.matrix * psdSqrt σSE.matrix) =
        ∑ s : S,
          traceNorm
            (psdSqrt (Classical.block ρS.matrix s s) *
              psdSqrt (Classical.block σSE.matrix s s)) := by
    have hleft0 :=
      Classical.traceNorm_psdSqrt_blockDiagonal_mul_psdSqrt_blockDiagonal
        (fun s : S => Classical.block ρS.matrix s s)
        (fun s : S => Classical.block σSE.matrix s s)
        hρS_blocks hσ_blocks
    rw [← hρS_blockDiagonal, ← hσ_blockDiagonal] at hleft0
    exact hleft0
  have hsource_blockDiagonal :
      E.cqState.toSubnormalized.matrix =
        Classical.blockDiagonal (fun z : Z => E.cqBlock z) := by
    simpa [State.toSubnormalized_matrix, Ensemble.cqBlock] using
      (Classical.cqState_eq_blockDiagonal E)
  have hright :
      traceNorm
          (psdSqrt E.cqState.toSubnormalized.matrix *
            psdSqrt (Classical.blockDiagonal blocks)) =
        ∑ z : Z,
          traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z)) := by
    rw [hsource_blockDiagonal]
    exact
      Classical.traceNorm_psdSqrt_blockDiagonal_mul_psdSqrt_blockDiagonal
        (fun z : Z => E.cqBlock z) blocks
        (fun z => E.cqBlock_posSemidef z) hblocks
  have hsum :
      (∑ s : S,
          traceNorm
            (psdSqrt (Classical.block ρS.matrix s s) *
              psdSqrt (Classical.block σSE.matrix s s))) ≤
        ∑ z : Z,
          traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z)) := by
    calc
      (∑ s : S,
          traceNorm
            (psdSqrt (Classical.block ρS.matrix s s) *
              psdSqrt (Classical.block σSE.matrix s s))) ≤
          ∑ s : S, ∑ z : Z,
            if g z = s then
              traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z))
            else 0 := by
            refine Finset.sum_le_sum fun s _ => ?_
            simpa [ρS, σSE, imagePred] using hblock s
      _ = ∑ z : Z,
          traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.sum_eq_single (g z)]
            · rw [if_pos rfl]
            · intro s _ hs
              rw [if_neg (fun h => hs h.symm)]
            · intro hnot
              exact False.elim (hnot (Finset.mem_univ _))
  have hnorm :
      traceNorm
          (psdSqrt (E.deterministicPostprocessCqState g).toSubnormalized.matrix *
            psdSqrt
              (ρSE'.sourceCoordinatePinch.sourceBlockFilter
                (fun s : S => ∃ z : Z, g z = s)).matrix) ≤
        traceNorm
          (psdSqrt E.cqState.toSubnormalized.matrix *
            psdSqrt (Classical.blockDiagonal blocks)) := by
    calc
      traceNorm
          (psdSqrt (E.deterministicPostprocessCqState g).toSubnormalized.matrix *
            psdSqrt
              (ρSE'.sourceCoordinatePinch.sourceBlockFilter
                (fun s : S => ∃ z : Z, g z = s)).matrix) =
          ∑ s : S,
            traceNorm
              (psdSqrt (Classical.block ρS.matrix s s) *
                psdSqrt (Classical.block σSE.matrix s s)) := by
            simpa [ρS, σSE, imagePred] using hleft
      _ ≤ ∑ z : Z,
            traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z)) := hsum
      _ = traceNorm
          (psdSqrt E.cqState.toSubnormalized.matrix *
            psdSqrt (Classical.blockDiagonal blocks)) := hright.symm
  exact
    E.sourceImageFilteredWitness_exactSourceFidelityLift_of_blocks
      g ρSE' blocks hblocks htrace hcoarse hnorm

variable {a : Type uS} {b : Type ue}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A subnormalized conditional-min-entropy feasible bound controls every
diagonal classical block. -/
theorem subnormalizedBlock_le_of_conditionalMinEntropyFeasible
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b) (x : a) {lam : ℝ}
    (h : SubnormalizedState.ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    Classical.block ρ.matrix x x ≤ (Real.rpow 2 (-lam) : ℂ) • σ.matrix := by
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  rw [Matrix.le_iff]
  have hdiff :
      (c • SubnormalizedState.identityTensorStateMatrix (a := a) σ - ρ.matrix).PosSemidef := by
    simpa [c, SubnormalizedState.ConditionalMinEntropyFeasible, Matrix.le_iff] using h
  have hblock := hdiff.submatrix (fun i : b => (x, i))
  have hblock_eq :
      Matrix.submatrix
          (c • SubnormalizedState.identityTensorStateMatrix (a := a) σ - ρ.matrix)
          (fun i : b => (x, i)) (fun i : b => (x, i)) =
        c • σ.matrix - Classical.block ρ.matrix x x := by
    ext i j
    simp [Classical.block, SubnormalizedState.identityTensorStateMatrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, c]
  rwa [hblock_eq] at hblock

private theorem subnormalizedIdentityTensorStateMatrix_trace (σ : SubnormalizedState b) :
    (SubnormalizedState.identityTensorStateMatrix (a := a) σ).trace =
      (Fintype.card a : ℂ) * σ.matrix.trace := by
  change (Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) σ.matrix).trace =
    (Fintype.card a : ℂ) * σ.matrix.trace
  rw [Matrix.trace_kronecker, Matrix.trace_one]

private theorem cqState_eq_subnormalizedBlockDiagonal_cqBlock (E : Ensemble a b) :
    E.cqState.matrix = Classical.blockDiagonal fun x => E.cqBlock x := by
  rw [Classical.cqState_eq_blockDiagonal]
  rfl

/-- Blockwise domination by the same scaled subnormalized `B` state is the
global cq order constraint used by subnormalized conditional min-entropy. -/
theorem subnormalizedConditionalMinEntropyFeasible_of_cqBlock_le
    (E : Ensemble a b) (σ : SubnormalizedState b) (lam : ℝ)
    (hblock : ∀ x, E.cqBlock x ≤ (Real.rpow 2 (-lam) : ℂ) • σ.matrix) :
    SubnormalizedState.ConditionalMinEntropyFeasible (a := a)
      E.cqState.toSubnormalized σ lam := by
  classical
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  rw [SubnormalizedState.ConditionalMinEntropyFeasible_eq, Matrix.le_iff]
  have hblocks : ∀ x, (c • σ.matrix - E.cqBlock x).PosSemidef := by
    intro x
    simpa [c, Matrix.le_iff] using hblock x
  have hmatrix :
      (c • SubnormalizedState.identityTensorStateMatrix (a := a) σ -
          E.cqState.toSubnormalized.matrix) =
        Classical.blockDiagonal fun x => c • σ.matrix - E.cqBlock x := by
    calc
      c • SubnormalizedState.identityTensorStateMatrix (a := a) σ -
          E.cqState.toSubnormalized.matrix =
          c • Classical.blockDiagonal (fun _ : a => σ.matrix) -
            Classical.blockDiagonal (fun x => E.cqBlock x) := by
            rw [SubnormalizedState.identityTensorStateMatrix_eq_blockDiagonal]
            rw [State.toSubnormalized_matrix, cqState_eq_subnormalizedBlockDiagonal_cqBlock]
      _ = Classical.blockDiagonal (fun x => c • σ.matrix - E.cqBlock x) := by
            rw [← Classical.blockDiagonal_smul]
            rw [← Classical.blockDiagonal_sub]
  rw [hmatrix]
  exact Classical.blockDiagonal_posSemidef
    (fun x => c • σ.matrix - E.cqBlock x) hblocks

/-- Feasible subnormalized exponents for a normalized state embedded by
`State.toSubnormalized` are bounded by the classical-register dimension. -/
theorem subnormalizedConditionalMinEntropyFeasible_toSubnormalized_le_log2_card_left
    {ρ : State (Prod a b)} {σ : SubnormalizedState b} {lam : ℝ}
    (h : SubnormalizedState.ConditionalMinEntropyFeasible (a := a)
      ρ.toSubnormalized σ lam) :
    lam ≤ log2 (Fintype.card a : ℝ) := by
  classical
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  let r : ℝ := Real.rpow 2 (-lam)
  have htrace := State.trace_re_le_of_le h
  have hleft : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hid_trace_re :
      (SubnormalizedState.identityTensorStateMatrix (a := a) σ).trace.re =
        (Fintype.card a : ℝ) * σ.matrix.trace.re := by
    rw [subnormalizedIdentityTensorStateMatrix_trace]
    simp [Complex.mul_re, σ.trace_im_zero]
  have htrace_bound' :
      ρ.matrix.trace.re ≤
        r * ((Fintype.card a : ℝ) * σ.matrix.trace.re) := by
    simpa [State.toSubnormalized_matrix, r, hid_trace_re] using htrace
  have htrace_bound : 1 ≤ r * ((Fintype.card a : ℝ) * σ.matrix.trace.re) := by
    simpa [hleft] using htrace_bound'
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam)
  have hprod_le : r * ((Fintype.card a : ℝ) * σ.matrix.trace.re) ≤
      r * (Fintype.card a : ℝ) := by
    have hmul_nonneg : 0 ≤ r * (Fintype.card a : ℝ) :=
      mul_nonneg hr_nonneg hcard_pos.le
    have hmul :=
      mul_le_mul_of_nonneg_left σ.trace_le_one hmul_nonneg
    nlinarith
  have hscale : (Fintype.card a : ℝ)⁻¹ ≤ r := by
    rw [inv_le_iff_one_le_mul₀ hcard_pos]
    simpa [mul_comm] using htrace_bound.trans hprod_le
  have hlog := Real.log_le_log (inv_pos.mpr hcard_pos) hscale
  have hlog2_nonneg : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos one_lt_two)
  have hdiv := div_le_div_of_nonneg_right hlog hlog2_nonneg
  change log2 ((Fintype.card a : ℝ)⁻¹) ≤ log2 (Real.rpow 2 (-lam)) at hdiv
  have hneg := neg_le_neg hdiv
  have hcard :
      -log2 ((Fintype.card a : ℝ)⁻¹) = log2 (Fintype.card a : ℝ) := by
    unfold log2
    rw [Real.log_inv]
    ring
  rw [neg_log2_rpow_two_neg lam, hcard] at hneg
  exact hneg

/-- The subnormalized feasible exponent set of an embedded normalized state is
bounded above. -/
theorem subnormalizedConditionalMinEntropyFeasibleExponentValueSet_toSubnormalized_bddAbove
    (ρ : State (Prod a b)) :
    BddAbove (ρ.toSubnormalized.conditionalMinEntropyFeasibleExponentValueSet (a := a)) := by
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro lam hlam
  rcases hlam with ⟨σ, hσ⟩
  exact subnormalizedConditionalMinEntropyFeasible_toSubnormalized_le_log2_card_left
    (a := a) hσ

/-- Deterministic postprocessing feasibility pushes back to the original cq
state, the unsmoothed core of `H_min(g(Z)|E) ≤ H_min(Z|E)`. -/
theorem conditionalMinEntropyFeasible_of_deterministicPostprocessCqState
    (E : Ensemble Z e) (g : Z → S) (σ : State e) {lam : ℝ}
    (hpost : State.ConditionalMinEntropyFeasible (a := S)
      (E.deterministicPostprocessCqState g) σ lam) :
    State.ConditionalMinEntropyFeasible (a := Z) E.cqState σ lam := by
  refine Ensemble.conditionalMinEntropyFeasible_of_cqBlock_le E σ lam ?_
  intro z
  exact (E.cqBlock_le_deterministicPostprocessCqState_block g z).trans
    (State.block_le_of_conditionalMinEntropyFeasible
      (E.deterministicPostprocessCqState g) σ (g z) hpost)

/-- Deterministic postprocessing cannot increase normalized cq conditional
min-entropy. -/
theorem conditionalMinEntropy_deterministicPostprocessCqState_le
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicPostprocessCqState g).conditionalMinEntropy ≤
      E.cqState.conditionalMinEntropy := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hpost_prod : Nonempty (Prod S e) := (E.deterministicPostprocessCqState g).nonempty
  letI : Nonempty S := ⟨(Classical.choice hpost_prod).1⟩
  let spost : Set ℝ :=
    (E.deterministicPostprocessCqState g).conditionalMinEntropyFeasibleExponentValueSet
      (a := S)
  let ssource : Set ℝ := E.cqState.conditionalMinEntropyFeasibleExponentValueSet (a := Z)
  have hpost_nonempty : spost.Nonempty := by
    simpa [spost] using
      (E.deterministicPostprocessCqState g).conditionalMinEntropyFeasibleExponentValueSet_nonempty
        (a := S)
  have hsource_bdd : BddAbove ssource := by
    simpa [ssource] using
      State.conditionalMinEntropyFeasibleExponentValueSet_bddAbove (a := Z) E.cqState
  have hpost_eq :
      (E.deterministicPostprocessCqState g).conditionalMinEntropy = sSup spost := by
    simp [spost, State.conditionalMinEntropy_eq,
      State.conditionalMinEntropyFeasibleExponentValueSet]
  have hsource_eq :
      E.cqState.conditionalMinEntropy = sSup ssource := by
    simp [ssource, State.conditionalMinEntropy_eq,
      State.conditionalMinEntropyFeasibleExponentValueSet]
  rw [hpost_eq, hsource_eq]
  refine csSup_le hpost_nonempty ?_
  intro lam hlam
  rcases hlam with ⟨σ, hσ⟩
  exact le_csSup hsource_bdd
    ⟨σ, E.conditionalMinEntropyFeasible_of_deterministicPostprocessCqState g σ hσ⟩

/-- Subnormalized deterministic postprocessing feasibility pushes back to the
original cq state. This is the subnormalized unsmoothed core needed by the
smooth deterministic-function DPI route. -/
theorem subnormalizedConditionalMinEntropyFeasible_of_deterministicPostprocessCqState
    (E : Ensemble Z e) (g : Z → S) (σ : SubnormalizedState e) {lam : ℝ}
    (hpost : SubnormalizedState.ConditionalMinEntropyFeasible (a := S)
      (E.deterministicPostprocessCqState g).toSubnormalized σ lam) :
    SubnormalizedState.ConditionalMinEntropyFeasible (a := Z)
      E.cqState.toSubnormalized σ lam := by
  refine subnormalizedConditionalMinEntropyFeasible_of_cqBlock_le E σ lam ?_
  intro z
  exact (E.cqBlock_le_deterministicPostprocessCqState_block g z).trans
    (subnormalizedBlock_le_of_conditionalMinEntropyFeasible
      (E.deterministicPostprocessCqState g).toSubnormalized σ (g z) hpost)

/-- Deterministic postprocessing cannot increase subnormalized cq conditional
min-entropy after embedding the normalized cq states. -/
theorem subnormalizedConditionalMinEntropy_deterministicPostprocessCqState_le
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicPostprocessCqState g).toSubnormalized.conditionalMinEntropyRaw ≤
      E.cqState.toSubnormalized.conditionalMinEntropyRaw := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hpost_prod : Nonempty (Prod S e) := (E.deterministicPostprocessCqState g).nonempty
  letI : Nonempty S := ⟨(Classical.choice hpost_prod).1⟩
  let spost : Set ℝ :=
    (E.deterministicPostprocessCqState g).toSubnormalized
      |>.conditionalMinEntropyFeasibleExponentValueSet (a := S)
  let ssource : Set ℝ :=
    E.cqState.toSubnormalized.conditionalMinEntropyFeasibleExponentValueSet (a := Z)
  have hpost_nonempty : spost.Nonempty := by
    obtain ⟨lam, σ, hσ⟩ :=
      (E.deterministicPostprocessCqState g).conditionalMinEntropyFeasibleExponentValueSet_nonempty
        (a := S)
    refine ⟨lam, ?_⟩
    exact ⟨σ.toSubnormalized,
      (State.toSubnormalized_ConditionalMinEntropyFeasible_iff
        (a := S) (E.deterministicPostprocessCqState g) σ lam).2 hσ⟩
  have hsource_bdd : BddAbove ssource := by
    simpa [ssource] using
      subnormalizedConditionalMinEntropyFeasibleExponentValueSet_toSubnormalized_bddAbove
        (a := Z) E.cqState
  have hpost_eq :
      (E.deterministicPostprocessCqState g).toSubnormalized.conditionalMinEntropyRaw = sSup spost := by
    simp [spost, SubnormalizedState.conditionalMinEntropyRaw_eq]
  have hsource_eq :
      E.cqState.toSubnormalized.conditionalMinEntropyRaw = sSup ssource := by
    simp [ssource, SubnormalizedState.conditionalMinEntropyRaw_eq]
  rw [hpost_eq, hsource_eq]
  refine csSup_le hpost_nonempty ?_
  intro lam hlam
  rcases hlam with ⟨σ, hσ⟩
  exact le_csSup hsource_bdd
    ⟨σ, E.subnormalizedConditionalMinEntropyFeasible_of_deterministicPostprocessCqState g σ hσ⟩

/-- Source-shaped unsmoothed graph bridge: forgetting the original classical
label from the deterministic graph state cannot increase conditional
min-entropy. This is a reusable normalized-state form of the first half of the
source proof of `pr:func`. -/
theorem conditionalMinEntropy_deterministicPostprocessCqState_le_deterministicGraphCqState
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicPostprocessCqState g).conditionalMinEntropy ≤
      (E.deterministicGraphCqState g).conditionalMinEntropy := by
  have h :=
    (E.deterministicGraphEnsemble g).conditionalMinEntropy_deterministicPostprocessCqState_le
      Prod.snd
  rwa [E.deterministicGraphEnsemble_postprocess_snd g,
    E.deterministicGraphEnsemble_cqState g] at h

/-- Subnormalized version of
`conditionalMinEntropy_deterministicPostprocessCqState_le_deterministicGraphCqState`. -/
theorem subnormalizedConditionalMinEntropy_deterministicPostprocessCqState_le_deterministicGraphCqState
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicPostprocessCqState g).toSubnormalized.conditionalMinEntropyRaw ≤
      (E.deterministicGraphCqState g).toSubnormalized.conditionalMinEntropyRaw := by
  have h :=
    (E.deterministicGraphEnsemble g).subnormalizedConditionalMinEntropy_deterministicPostprocessCqState_le
      Prod.snd
  rwa [E.deterministicGraphEnsemble_postprocess_snd g,
    E.deterministicGraphEnsemble_cqState g] at h

/-- The deterministic graph state has the same normalized conditional
min-entropy as the original cq state. This packages the graph/source
isometry part of the unsmoothed source proof using the existing deterministic
postprocessing DPI in both directions. -/
theorem conditionalMinEntropy_deterministicGraphCqState_eq_cqState
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicGraphCqState g).conditionalMinEntropy =
      E.cqState.conditionalMinEntropy := by
  apply le_antisymm
  · simpa [deterministicGraphCqState] using
      E.conditionalMinEntropy_deterministicPostprocessCqState_le
        (fun z => (z, g z))
  · have h :=
      (E.deterministicGraphEnsemble g).conditionalMinEntropy_deterministicPostprocessCqState_le
        Prod.fst
    rwa [E.deterministicGraphEnsemble_postprocess_fst g,
      E.deterministicGraphEnsemble_cqState g] at h

/-- Subnormalized graph/source version of
`conditionalMinEntropy_deterministicGraphCqState_eq_cqState`. -/
theorem subnormalizedConditionalMinEntropy_deterministicGraphCqState_eq_cqState
    (E : Ensemble Z e) (g : Z → S) :
    (E.deterministicGraphCqState g).toSubnormalized.conditionalMinEntropyRaw =
      E.cqState.toSubnormalized.conditionalMinEntropyRaw := by
  apply le_antisymm
  · simpa [deterministicGraphCqState] using
      E.subnormalizedConditionalMinEntropy_deterministicPostprocessCqState_le
        (fun z => (z, g z))
  · have h :=
      (E.deterministicGraphEnsemble g).subnormalizedConditionalMinEntropy_deterministicPostprocessCqState_le
        Prod.fst
    rwa [E.deterministicGraphEnsemble_postprocess_fst g,
      E.deterministicGraphEnsemble_cqState g] at h

/-- Graph-shaped smooth endpoint: if every nearby postprocessed witness lifts
to a nearby graph witness with no smaller ordinary min-entropy, then the smooth
postprocessed min-entropy is bounded by the smooth graph min-entropy. This
isolates the endpoint step for the smooth version of the first half of
`pr:class/bounds-1`. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_deterministicGraphCqState_of_witness_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE',
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall ε ρSE' →
        ∃ τ : SubnormalizedState (Prod (Prod Z S) e),
          (E.deterministicGraphCqState g).toSubnormalized.purifiedBall ε τ ∧
          ρSE'.conditionalMinEntropyRaw ≤ τ.conditionalMinEntropyRaw) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      (E.deterministicGraphCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicGraphCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hgraph_prod : Nonempty (Prod (Prod Z S) e) :=
    (E.deterministicGraphCqState g).nonempty
  letI : Nonempty (Prod Z S) := ⟨(Classical.choice hgraph_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hgraph_prod).2⟩
  have hεgraph : ε < Real.sqrt
      (E.deterministicGraphCqState g).toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt (E.deterministicGraphCqState g).matrix.trace.re
    have htrace : (E.deterministicGraphCqState g).matrix.trace.re = 1 := by
      rw [(E.deterministicGraphCqState g).trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  exact
    SubnormalizedState.smoothConditionalMinEntropyRaw_le_of_witness_lift_of_lt_sqrt_trace
      (a := S) (source := Prod Z S)
      (E.deterministicPostprocessCqState g).toSubnormalized
      (E.deterministicGraphCqState g).toSubnormalized
      hε0 hεgraph hlift

/-- Graph/source smooth endpoint: if every smooth graph candidate can be
lifted to a smooth source candidate with no smaller endpoint value, then the
smooth graph min-entropy is bounded by the smooth source min-entropy. This is
the endpoint wrapper for the source proof's graph/source isometry step. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicGraphCqState_le_cqState_of_candidate_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ h,
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := Prod Z S)
        (E.deterministicGraphCqState g).toSubnormalized ε h →
        ∃ h',
          SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := Z)
            E.cqState.toSubnormalized ε h' ∧ h ≤ h') :
    (E.deterministicGraphCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicGraphCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hεsource : ε < Real.sqrt E.cqState.toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt E.cqState.matrix.trace.re
    have htrace : E.cqState.matrix.trace.re = 1 := by
      rw [E.cqState.trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  exact
    SubnormalizedState.smoothConditionalMinEntropyRaw_le_of_candidate_lift_of_lt_sqrt_trace
      (a := Prod Z S) (source := Z)
      (E.deterministicGraphCqState g).toSubnormalized E.cqState.toSubnormalized
      hε0 hεsource hlift

/-- The concrete graph/source isometry compresses any smooth graph candidate
back to a smooth source candidate with no smaller endpoint value. -/
theorem deterministicGraphCqState_smoothCandidate_lift_to_cqState
    (E : Ensemble Z e) (g : Z → S) {ε h : ℝ}
    (hε1 : ε < 1)
    (hcand :
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := Prod Z S)
        (E.deterministicGraphCqState g).toSubnormalized ε h) :
    ∃ h',
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := Z)
        E.cqState.toSubnormalized ε h' ∧ h ≤ h' := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  letI : Nonempty S := ⟨g (Classical.choice hsource_prod).1⟩
  have hεsource : ε < Real.sqrt E.cqState.toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt E.cqState.matrix.trace.re
    have htrace : E.cqState.matrix.trace.re = 1 := by
      rw [E.cqState.trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  have hcandIso :
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := Prod Z S)
        (E.cqState.toSubnormalized.sourceIsometryApply
          (deterministicGraphSourceIsometry g)) ε h := by
    simpa [E.deterministicGraphCqState_toSubnormalized_eq_sourceIsometryApply g] using hcand
  exact
    SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw.sourceIsometryApply_compress
      (a := Z) E.cqState.toSubnormalized
      (deterministicGraphSourceIsometry g) hεsource hcandIso

/-- The concrete graph/source isometry preserves the smooth conditional
min-entropy of the source cq center. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicGraphCqState_eq_cqState
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (E.deterministicGraphCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicGraphCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) =
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  letI : Nonempty S := ⟨g (Classical.choice hsource_prod).1⟩
  have hεsource : ε < Real.sqrt E.cqState.toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt E.cqState.matrix.trace.re
    have htrace : E.cqState.matrix.trace.re = 1 := by
      rw [E.cqState.trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  change
    (E.deterministicGraphCqState g).toSubnormalized.smoothConditionalMinEntropyRaw ε =
      E.cqState.toSubnormalized.smoothConditionalMinEntropyRaw ε
  rw [← E.deterministicGraphCqState_toSubnormalized_eq_sourceIsometryApply g]
  exact
    E.cqState.toSubnormalized.smoothConditionalMinEntropy_sourceIsometryApply
      (deterministicGraphSourceIsometry g) hε0 hεsource

/-- Concrete graph/source smooth endpoint obtained by instantiating the source
proof's graph embedding isometry `z ↦ (z, g z)`. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicGraphCqState_le_cqState
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (E.deterministicGraphCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicGraphCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) :=
  le_of_eq
    (E.subnormalizedSmoothConditionalMinEntropy_deterministicGraphCqState_eq_cqState
      g hε0 hε1)

/-- Two-step smooth deterministic-postprocessing endpoint: a postprocessed
witness lift to the graph state plus a graph-to-source candidate lift implies
the desired smooth deterministic-function data-processing inequality. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_graph_and_source_candidate_lifts
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hgraph : ∀ ρSE',
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall ε ρSE' →
        ∃ τ : SubnormalizedState (Prod (Prod Z S) e),
          (E.deterministicGraphCqState g).toSubnormalized.purifiedBall ε τ ∧
          ρSE'.conditionalMinEntropyRaw ≤ τ.conditionalMinEntropyRaw)
    (hsource : ∀ h,
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := Prod Z S)
        (E.deterministicGraphCqState g).toSubnormalized ε h →
        ∃ h',
          SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := Z)
            E.cqState.toSubnormalized ε h' ∧ h ≤ h') :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) :=
  (E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_deterministicGraphCqState_of_witness_lift
    g hε0 hε1 hgraph).trans
    (E.subnormalizedSmoothConditionalMinEntropy_deterministicGraphCqState_le_cqState_of_candidate_lift
      g hε0 hε1 hsource)

omit [DecidableEq Z] in
/-- Every smooth candidate around a deterministic postprocessed cq center can
be replaced by its source-coordinate pinching without decreasing the candidate
entropy. -/
theorem deterministicPostprocessCqState_smoothCandidate_sourceCoordinatePinch
    (E : Ensemble Z e) (g : Z → S) {ε h : ℝ}
    (hε1 : ε < 1)
    (hcand :
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := S)
        (E.deterministicPostprocessCqState g).toSubnormalized ε h) :
    ∃ h',
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := S)
        (E.deterministicPostprocessCqState g).toSubnormalized ε h' ∧ h ≤ h' := by
  classical
  have hpost_prod : Nonempty (Prod S e) :=
    (E.deterministicPostprocessCqState g).nonempty
  letI : Nonempty S := ⟨(Classical.choice hpost_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hpost_prod).2⟩
  have hεpost :
      ε < Real.sqrt
        (E.deterministicPostprocessCqState g).toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt (E.deterministicPostprocessCqState g).matrix.trace.re
    have htrace :
        (E.deterministicPostprocessCqState g).matrix.trace.re = 1 := by
      rw [(E.deterministicPostprocessCqState g).trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  exact
    SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw.sourceCoordinatePinch_of_fixed
      (E.deterministicPostprocessCqState_toSubnormalized_sourceCoordinatePinch g)
      hεpost hcand

/-- Deterministic postprocessing smooth min-entropy follows from a candidate
lift from every smoothed postprocessed witness back to the original cq center.
This packages the supremum/boundedness endpoint separately from the concrete
purified-distance witness lift. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_candidate_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ h,
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := S)
        (E.deterministicPostprocessCqState g).toSubnormalized ε h →
        ∃ h',
          SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := Z)
            E.cqState.toSubnormalized ε h' ∧ h ≤ h') :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hεsource : ε < Real.sqrt E.cqState.toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt E.cqState.matrix.trace.re
    have htrace : E.cqState.matrix.trace.re = 1 := by
      rw [E.cqState.trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  exact
    SubnormalizedState.smoothConditionalMinEntropyRaw_le_of_candidate_lift_of_lt_sqrt_trace
      (a := S) (source := Z)
      (E.deterministicPostprocessCqState g).toSubnormalized E.cqState.toSubnormalized
      hε0 hεsource hlift

/-- Deterministic postprocessing smooth min-entropy follows from a witness-level
lift from each nearby postprocessed state to a nearby original cq state whose
ordinary conditional min-entropy is no smaller. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_witness_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE',
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall ε ρSE' →
        ∃ ρZE',
          E.cqState.toSubnormalized.purifiedBall ε ρZE' ∧
          ρSE'.conditionalMinEntropyRaw ≤ ρZE'.conditionalMinEntropyRaw) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hεsource : ε < Real.sqrt E.cqState.toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt E.cqState.matrix.trace.re
    have htrace : E.cqState.matrix.trace.re = 1 := by
      rw [E.cqState.trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  exact
    SubnormalizedState.smoothConditionalMinEntropyRaw_le_of_witness_lift_of_lt_sqrt_trace
      (a := S) (source := Z)
      (E.deterministicPostprocessCqState g).toSubnormalized E.cqState.toSubnormalized
      hε0 hεsource hlift

/-- It suffices to lift source-coordinate-pinched smoothed witnesses of the
deterministically postprocessed center.  Arbitrary witnesses are first pinched;
the postprocessed cq center is fixed by this pinching, the purified ball is
preserved, and subnormalized conditional min-entropy can only increase. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceCoordinatePinch_witness_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE' : SubnormalizedState (Prod S e),
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
        ε ρSE'.sourceCoordinatePinch →
        ∃ ρZE',
          E.cqState.toSubnormalized.purifiedBall ε ρZE' ∧
          ρSE'.sourceCoordinatePinch.conditionalMinEntropyRaw ≤
            ρZE'.conditionalMinEntropyRaw) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hpost_prod : Nonempty (Prod S e) :=
    (E.deterministicPostprocessCqState g).nonempty
  letI : Nonempty S := ⟨(Classical.choice hpost_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hpost_prod).2⟩
  have hεpost :
      ε < Real.sqrt
        (E.deterministicPostprocessCqState g).toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt (E.deterministicPostprocessCqState g).matrix.trace.re
    have htrace :
        (E.deterministicPostprocessCqState g).matrix.trace.re = 1 := by
      rw [(E.deterministicPostprocessCqState g).trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  refine
    E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_witness_lift
      g hε0 hε1 ?_
  intro ρSE' hball
  have hρSE'_pos : 0 < ρSE'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (E.deterministicPostprocessCqState g).toSubnormalized ρSE' hεpost hball
  have hball_pinch :
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
        ε ρSE'.sourceCoordinatePinch :=
    (E.deterministicPostprocessCqState g).toSubnormalized
      |>.purifiedBall_sourceCoordinatePinch_of_fixed
        (E.deterministicPostprocessCqState_toSubnormalized_sourceCoordinatePinch g)
        hball
  rcases hlift ρSE' hball_pinch with ⟨ρZE', hρZE', hle_pinch⟩
  exact ⟨ρZE', hρZE',
    (ρSE'.conditionalMinEntropy_le_sourceCoordinatePinch_of_trace_pos
      (a := S) hρSE'_pos).trans hle_pinch⟩

/-- Exact source-witness endpoint for the smooth deterministic postprocessing
lift.  If every source-coordinate-pinched postprocessed witness has an exact
`Z × E` fiber refinement in the source purified ball, then the smooth
data-processing inequality follows from source pinching plus the generic
deterministic source coarse-graining API. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceCoordinatePinch_exact_source_witness_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE' : SubnormalizedState (Prod S e),
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
        ε ρSE'.sourceCoordinatePinch →
        ∃ ρZE' : SubnormalizedState (Prod Z e),
          E.cqState.toSubnormalized.purifiedBall ε ρZE' ∧
          ρZE'.sourceDeterministicPostprocess g =
            ρSE'.sourceCoordinatePinch) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hεsource : ε < Real.sqrt E.cqState.toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt E.cqState.matrix.trace.re
    have htrace : E.cqState.matrix.trace.re = 1 := by
      rw [E.cqState.trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  refine
    E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceCoordinatePinch_witness_lift
      g hε0 hε1 ?_
  intro ρSE' hρSE'
  rcases hlift ρSE' hρSE' with ⟨ρZE', hρZE', hcoarse⟩
  have hρZE_pinch :
      E.cqState.toSubnormalized.purifiedBall ε ρZE'.sourceCoordinatePinch :=
    E.cqState.toSubnormalized
      |>.purifiedBall_sourceCoordinatePinch_of_fixed
        (Ensemble.cqState_toSubnormalized_sourceCoordinatePinch E)
        hρZE'
  have hρZE_pinch_pos : 0 < ρZE'.sourceCoordinatePinch.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      E.cqState.toSubnormalized ρZE'.sourceCoordinatePinch hεsource hρZE_pinch
  have hentropy_raw :
      (ρZE'.sourceCoordinatePinch.sourceDeterministicPostprocess g).conditionalMinEntropyRaw ≤
        ρZE'.sourceCoordinatePinch.sourceCoordinatePinch.conditionalMinEntropyRaw :=
    ρZE'.sourceCoordinatePinch
      |>.conditionalMinEntropy_sourceDeterministicPostprocess_le_sourceCoordinatePinch_of_trace_pos
        g hρZE_pinch_pos
  have hentropy :
      (ρZE'.sourceCoordinatePinch.sourceDeterministicPostprocess g).conditionalMinEntropyRaw ≤
        ρZE'.sourceCoordinatePinch.conditionalMinEntropyRaw :=
    by simpa using hentropy_raw
  exact ⟨ρZE'.sourceCoordinatePinch, hρZE_pinch, by
    simpa [hcoarse] using hentropy⟩

/-- Exact source-witness endpoint after first filtering postprocessed witnesses
to the image of `g`.  This is the non-surjective-safe form: arbitrary
postprocessed witnesses are source-coordinate pinched and then restricted to
reachable output labels before an exact `Z × E` fiber refinement is requested. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceImageFilter_exact_source_witness_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE' : SubnormalizedState (Prod S e),
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
        ε
        (ρSE'.sourceCoordinatePinch.sourceBlockFilter
          (fun s : S => ∃ z : Z, g z = s)) →
        ∃ ρZE' : SubnormalizedState (Prod Z e),
          E.cqState.toSubnormalized.purifiedBall ε ρZE' ∧
          ρZE'.sourceDeterministicPostprocess g =
            ρSE'.sourceCoordinatePinch.sourceBlockFilter
              (fun s : S => ∃ z : Z, g z = s)) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hpost_prod : Nonempty (Prod S e) :=
    (E.deterministicPostprocessCqState g).nonempty
  letI : Nonempty S := ⟨(Classical.choice hpost_prod).1⟩
  have hεpost :
      ε < Real.sqrt
        (E.deterministicPostprocessCqState g).toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt (E.deterministicPostprocessCqState g).matrix.trace.re
    have htrace :
        (E.deterministicPostprocessCqState g).matrix.trace.re = 1 := by
      rw [(E.deterministicPostprocessCqState g).trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  have hεsource : ε < Real.sqrt E.cqState.toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt E.cqState.matrix.trace.re
    have htrace : E.cqState.matrix.trace.re = 1 := by
      rw [E.cqState.trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  refine
    E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_witness_lift
      g hε0 hε1 ?_
  intro ρSE' hball
  let imagePred : S → Prop := fun s => ∃ z : Z, g z = s
  let σSE : SubnormalizedState (Prod S e) :=
    ρSE'.sourceCoordinatePinch.sourceBlockFilter imagePred
  have hρSE'_pos : 0 < ρSE'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (E.deterministicPostprocessCqState g).toSubnormalized ρSE' hεpost hball
  have hball_pinch :
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
        ε ρSE'.sourceCoordinatePinch :=
    (E.deterministicPostprocessCqState g).toSubnormalized
      |>.purifiedBall_sourceCoordinatePinch_of_fixed
        (E.deterministicPostprocessCqState_toSubnormalized_sourceCoordinatePinch g)
        hball
  have hball_filter :
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall ε σSE := by
    simpa [σSE, imagePred] using
      ((E.deterministicPostprocessCqState g).toSubnormalized
        |>.purifiedBall_sourceBlockFilter_of_fixed imagePred
          (by
            simpa [imagePred] using
              E.deterministicPostprocessCqState_toSubnormalized_sourceBlockFilter_image g)
          hball_pinch)
  have hσSE_pos : 0 < σSE.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      (E.deterministicPostprocessCqState g).toSubnormalized σSE hεpost hball_filter
  have hpinch_pos : 0 < ρSE'.sourceCoordinatePinch.matrix.trace.re := by
    rw [SubnormalizedState.sourceCoordinatePinch_trace_re]
    exact hρSE'_pos
  have hpost_le_pinch :
      ρSE'.conditionalMinEntropyRaw ≤
        ρSE'.sourceCoordinatePinch.conditionalMinEntropyRaw :=
    ρSE'.conditionalMinEntropy_le_sourceCoordinatePinch_of_trace_pos
      (a := S) hρSE'_pos
  have hpinch_le_filter :
      ρSE'.sourceCoordinatePinch.conditionalMinEntropyRaw ≤ σSE.conditionalMinEntropyRaw := by
    simpa [σSE, imagePred] using
      (ρSE'.sourceCoordinatePinch
        |>.conditionalMinEntropy_le_sourceBlockFilter_of_trace_pos
          (a := S) imagePred hpinch_pos hσSE_pos)
  rcases hlift ρSE' (by simpa [σSE, imagePred] using hball_filter) with
    ⟨ρZE', hρZE', hcoarse⟩
  have hρZE_pinch :
      E.cqState.toSubnormalized.purifiedBall ε ρZE'.sourceCoordinatePinch :=
    E.cqState.toSubnormalized
      |>.purifiedBall_sourceCoordinatePinch_of_fixed
        (Ensemble.cqState_toSubnormalized_sourceCoordinatePinch E)
        hρZE'
  have hρZE_pinch_pos : 0 < ρZE'.sourceCoordinatePinch.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      E.cqState.toSubnormalized ρZE'.sourceCoordinatePinch hεsource hρZE_pinch
  have hcoarse_pinch :
      ρZE'.sourceCoordinatePinch.sourceDeterministicPostprocess g = σSE := by
    simp [σSE, imagePred, hcoarse]
  have hentropy_raw :
      (ρZE'.sourceCoordinatePinch.sourceDeterministicPostprocess g).conditionalMinEntropyRaw ≤
        ρZE'.sourceCoordinatePinch.sourceCoordinatePinch.conditionalMinEntropyRaw :=
    ρZE'.sourceCoordinatePinch
      |>.conditionalMinEntropy_sourceDeterministicPostprocess_le_sourceCoordinatePinch_of_trace_pos
        g hρZE_pinch_pos
  have hentropy_source :
      σSE.conditionalMinEntropyRaw ≤ ρZE'.sourceCoordinatePinch.conditionalMinEntropyRaw := by
    simpa [hcoarse_pinch] using hentropy_raw
  exact ⟨ρZE'.sourceCoordinatePinch, hρZE_pinch,
    (hpost_le_pinch.trans hpinch_le_filter).trans hentropy_source⟩

/-- Exact source-witness endpoint where the lift supplies the generalized
fidelity comparison instead of directly supplying the source purified-ball
witness.  The purified-distance bookkeeping is discharged by the reusable
`SubnormalizedState.purifiedBall_of_generalizedFidelity_le` API, so the
remaining concrete task is the fiberwise fidelity construction. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceImageFilter_exact_source_fidelity_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE' : SubnormalizedState (Prod S e),
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
        ε
        (ρSE'.sourceCoordinatePinch.sourceBlockFilter
          (fun s : S => ∃ z : Z, g z = s)) →
        ∃ ρZE' : SubnormalizedState (Prod Z e),
          (E.deterministicPostprocessCqState g).toSubnormalized.generalizedFidelity
              (ρSE'.sourceCoordinatePinch.sourceBlockFilter
                (fun s : S => ∃ z : Z, g z = s)) ≤
            E.cqState.toSubnormalized.generalizedFidelity ρZE' ∧
          ρZE'.sourceDeterministicPostprocess g =
            ρSE'.sourceCoordinatePinch.sourceBlockFilter
              (fun s : S => ∃ z : Z, g z = s)) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  refine
    E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceImageFilter_exact_source_witness_lift
      g hε0 hε1 ?_
  intro ρSE' hball
  rcases hlift ρSE' hball with ⟨ρZE', hfid, hcoarse⟩
  refine ⟨ρZE', ?_, hcoarse⟩
  exact
    SubnormalizedState.purifiedBall_of_generalizedFidelity_le
      (ρ := (E.deterministicPostprocessCqState g).toSubnormalized)
      (σ := ρSE'.sourceCoordinatePinch.sourceBlockFilter
        (fun s : S => ∃ z : Z, g z = s))
      (τ := E.cqState.toSubnormalized)
      (υ := ρZE') hfid hball

/-- Smooth deterministic postprocessing endpoint reduced to blockwise fiber
splits of each source-image-filtered witness.  The only remaining concrete
work for the unconditional theorem is to construct such `blocks` with the
blockwise fidelity bounds. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceImageFilter_block_bounds
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE' : SubnormalizedState (Prod S e),
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
        ε
        (ρSE'.sourceCoordinatePinch.sourceBlockFilter
          (fun s : S => ∃ z : Z, g z = s)) →
        ∃ blocks : Z → CMatrix e,
          (∀ z, (blocks z).PosSemidef) ∧
          (∑ z, (blocks z).trace).re ≤ 1 ∧
          SubnormalizedState.sourceDeterministicPostprocessMap
              (a := Z) (b := e) g (Classical.blockDiagonal blocks) =
            (ρSE'.sourceCoordinatePinch.sourceBlockFilter
              (fun s : S => ∃ z : Z, g z = s)).matrix ∧
          ∀ s : S,
            traceNorm
                (psdSqrt
                    (Classical.block
                      (E.deterministicPostprocessCqState g).toSubnormalized.matrix s s) *
                  psdSqrt
                    (Classical.block
                      (ρSE'.sourceCoordinatePinch.sourceBlockFilter
                        (fun s : S => ∃ z : Z, g z = s)).matrix s s)) ≤
              ∑ z : Z,
                if g z = s then
                  traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z))
                else 0) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  refine
    E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceImageFilter_exact_source_fidelity_lift
      g hε0 hε1 ?_
  intro ρSE' hball
  rcases hlift ρSE' hball with ⟨blocks, hblocks, htrace, hcoarse, hblock⟩
  exact
    E.sourceImageFilteredWitness_exactSourceFidelityLift_of_block_bounds
      g ρSE' blocks hblocks htrace hcoarse hblock

/-- Smooth conditional min-entropy cannot increase when the classical source
register is deterministically postprocessed.  The proof refines each reachable
postprocessed witness block along the corresponding source fiber and then uses
the blockwise fidelity lift above. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  refine
    E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceImageFilter_block_bounds
      g hε0 hε1 ?_
  intro ρSE' _hball
  let imagePred : S → Prop := fun s : S => ∃ z : Z, g z = s
  let σSE : SubnormalizedState (Prod S e) :=
    ρSE'.sourceCoordinatePinch.sourceBlockFilter imagePred
  have hσ_matrix :
      σSE.matrix =
        Classical.blockDiagonal
          (fun s : S =>
            if imagePred s then
              Classical.block ρSE'.sourceCoordinatePinch.matrix s s
            else 0) := by
    simpa [σSE, imagePred] using
      (SubnormalizedState.sourceBlockFilter_matrix_eq_blockDiagonal
        (ρSE'.sourceCoordinatePinch) imagePred)
  have hσ_blockDiagonal :
      Classical.blockDiagonal (fun s : S => Classical.block σSE.matrix s s) =
        σSE.matrix := by
    rw [hσ_matrix]
    apply congrArg Classical.blockDiagonal
    funext s
    exact Classical.blockDiagonal_block_self
      (fun s : S =>
        if imagePred s then Classical.block ρSE'.sourceCoordinatePinch.matrix s s else 0) s
  have hpost_block :
      ∀ s : S,
        Classical.block (E.deterministicPostprocessCqState g).toSubnormalized.matrix s s =
          ∑ zf : {z : Z // g z = s}, E.cqBlock zf.1 := by
    intro s
    rw [State.toSubnormalized_matrix, deterministicPostprocessCqState_block]
    simpa using
      (sum_fiber_subtype_eq_if g s
        (fun zf : {z : Z // g z = s} => E.cqBlock zf.1))
  have hsplit :
      ∀ s : S,
        ∃ fiberBlocks : {z : Z // g z = s} → CMatrix e,
          (∀ zf, (fiberBlocks zf).PosSemidef) ∧
          (∑ zf : {z : Z // g z = s}, fiberBlocks zf) =
            Classical.block σSE.matrix s s ∧
          traceNorm
              (psdSqrt (∑ zf : {z : Z // g z = s}, E.cqBlock zf.1) *
                psdSqrt (Classical.block σSE.matrix s s)) ≤
            ∑ zf : {z : Z // g z = s},
              traceNorm (psdSqrt (E.cqBlock zf.1) * psdSqrt (fiberBlocks zf)) := by
    intro s
    by_cases hs : imagePred s
    · letI : Nonempty {z : Z // g z = s} :=
        ⟨⟨Classical.choose hs, Classical.choose_spec hs⟩⟩
      exact
        exists_fiber_psd_split_traceNorm_bound
          (A := fun zf : {z : Z // g z = s} => E.cqBlock zf.1)
          (fun zf => E.cqBlock_posSemidef zf.1)
          (Classical.block σSE.matrix s s)
          (σSE.pos.submatrix (fun i : e => (s, i)))
    · letI : IsEmpty {z : Z // g z = s} :=
        ⟨fun zf => hs ⟨zf.1, zf.2⟩⟩
      have hBzero : Classical.block σSE.matrix s s = 0 := by
        rw [hσ_matrix, Classical.blockDiagonal_block_self, if_neg hs]
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · intro zf
        exact Matrix.PosSemidef.zero
      · simp [hBzero]
      · simp [hBzero]
  let fiberBlocks : (s : S) → {z : Z // g z = s} → CMatrix e :=
    fun s => Classical.choose (hsplit s)
  let blocks : Z → CMatrix e := fun z => fiberBlocks (g z) ⟨z, rfl⟩
  have hblocks : ∀ z, (blocks z).PosSemidef := by
    intro z
    exact (Classical.choose_spec (hsplit (g z))).1 ⟨z, rfl⟩
  have hsum_blocks :
      ∀ s : S,
        (∑ z : Z, if g z = s then blocks z else 0) =
          Classical.block σSE.matrix s s := by
    intro s
    have hcongr :
        (∑ z : Z, if g z = s then blocks z else 0) =
          ∑ z : Z, if h : g z = s then fiberBlocks s ⟨z, h⟩ else 0 := by
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : g z = s
      · subst s
        simp [blocks, fiberBlocks]
      · simp [hz]
    calc
      (∑ z : Z, if g z = s then blocks z else 0) =
          ∑ z : Z, if h : g z = s then fiberBlocks s ⟨z, h⟩ else 0 := hcongr
      _ = ∑ zf : {z : Z // g z = s}, fiberBlocks s zf :=
          sum_fiber_subtype_eq_if g s (fiberBlocks s)
      _ = Classical.block σSE.matrix s s :=
          (Classical.choose_spec (hsplit s)).2.1
  have hcoarse_matrix :
      SubnormalizedState.sourceDeterministicPostprocessMap
          (a := Z) (b := e) g (Classical.blockDiagonal blocks) =
        σSE.matrix := by
    rw [SubnormalizedState.sourceDeterministicPostprocessMap_apply_eq_blockDiagonal]
    have hfun :
        (fun s : S =>
            ∑ z : Z,
              if g z = s then
                Classical.block (Classical.blockDiagonal blocks) z z
              else 0) =
          (fun s : S => Classical.block σSE.matrix s s) := by
      funext s
      calc
        (∑ z : Z,
            if g z = s then
              Classical.block (Classical.blockDiagonal blocks) z z
            else 0) =
            ∑ z : Z, if g z = s then blocks z else 0 := by
              refine Finset.sum_congr rfl fun z _ => ?_
              by_cases hz : g z = s
              · simp [hz, Classical.blockDiagonal_block_self]
              · simp [hz]
        _ = Classical.block σSE.matrix s s := hsum_blocks s
    rw [hfun, hσ_blockDiagonal]
  have htrace : (∑ z, (blocks z).trace).re ≤ 1 := by
    have htrace_eq :
        (∑ z : Z, (blocks z).trace) = σSE.matrix.trace := by
      have htp :=
        SubnormalizedState.sourceDeterministicPostprocessMap_tracePreserving
          (a := Z) (b := e) g (Classical.blockDiagonal blocks)
      rw [hcoarse_matrix] at htp
      rw [← Classical.blockDiagonal_trace blocks]
      exact htp.symm
    rw [htrace_eq]
    exact σSE.trace_le_one
  have hsum_trace_terms :
      ∀ s : S,
        (∑ zf : {z : Z // g z = s},
            traceNorm (psdSqrt (E.cqBlock zf.1) *
              psdSqrt (fiberBlocks s zf))) =
          ∑ z : Z,
            if g z = s then
              traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z))
            else 0 := by
    intro s
    have hsub :=
      (sum_fiber_subtype_eq_if g s
        (fun zf : {z : Z // g z = s} =>
          traceNorm (psdSqrt (E.cqBlock zf.1) *
            psdSqrt (fiberBlocks s zf)))).symm
    calc
      (∑ zf : {z : Z // g z = s},
          traceNorm (psdSqrt (E.cqBlock zf.1) *
            psdSqrt (fiberBlocks s zf))) =
          ∑ z : Z,
            if h : g z = s then
              traceNorm (psdSqrt (E.cqBlock z) *
                psdSqrt (fiberBlocks s ⟨z, h⟩))
            else 0 := hsub
      _ = ∑ z : Z,
            if g z = s then
              traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z))
            else 0 := by
              refine Finset.sum_congr rfl fun z _ => ?_
              by_cases hz : g z = s
              · subst s
                simp [blocks, fiberBlocks]
              · simp [hz]
  have hblock :
      ∀ s : S,
        traceNorm
            (psdSqrt
                (Classical.block
                  (E.deterministicPostprocessCqState g).toSubnormalized.matrix s s) *
              psdSqrt (Classical.block σSE.matrix s s)) ≤
          ∑ z : Z,
            if g z = s then
              traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z))
            else 0 := by
    intro s
    have hbound := (Classical.choose_spec (hsplit s)).2.2
    calc
      traceNorm
          (psdSqrt
              (Classical.block
                (E.deterministicPostprocessCqState g).toSubnormalized.matrix s s) *
            psdSqrt (Classical.block σSE.matrix s s)) =
          traceNorm
            (psdSqrt (∑ zf : {z : Z // g z = s}, E.cqBlock zf.1) *
              psdSqrt (Classical.block σSE.matrix s s)) := by
            rw [hpost_block s]
      _ ≤ ∑ zf : {z : Z // g z = s},
            traceNorm (psdSqrt (E.cqBlock zf.1) *
              psdSqrt (fiberBlocks s zf)) := hbound
      _ = ∑ z : Z,
            if g z = s then
              traceNorm (psdSqrt (E.cqBlock z) * psdSqrt (blocks z))
            else 0 := hsum_trace_terms s
  exact ⟨blocks, hblocks, htrace, by
    simpa [σSE, imagePred] using hcoarse_matrix, by
    intro s
    simpa [σSE, imagePred] using hblock s⟩

/-- A graph witness lift only has to be supplied for the source-coordinate
pinched smoothed postprocessed witnesses.  The graph witness is then projected
to the original source-side witness using the existing graph/source marginal
API. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceCoordinatePinch_graph_witness_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE' : SubnormalizedState (Prod S e),
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
        ε ρSE'.sourceCoordinatePinch →
        ∃ τ : SubnormalizedState (Prod S (Prod Z e)),
          ((E.deterministicGraphCqState g).reindex
            (deterministicGraphSourceMarginalEquiv Z S e)).toSubnormalized.purifiedBall ε τ ∧
          ρSE'.sourceCoordinatePinch.conditionalMinEntropyRaw ≤
            τ.marginalB.conditionalMinEntropyRaw) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) :=
  E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceCoordinatePinch_witness_lift
    g hε0 hε1 fun ρSE' hρSE' => by
      rcases hlift ρSE' hρSE' with ⟨τ, hτball, hle⟩
      exact ⟨τ.marginalB,
        E.deterministicGraphCqState_purifiedBall_marginalZE_of_purifiedBall g hτball,
        hle⟩

/-- Exact graph-witness endpoint for the remaining smooth deterministic
postprocessing lift.  If every source-coordinate-pinched postprocessed witness
has a graph-ball lift whose `Z × E` marginal is already coordinate-pinched and
coarse-grains exactly back to that witness, the entropy comparison follows
from the generic deterministic source coarse-graining API. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceCoordinatePinch_exact_graph_witness_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE' : SubnormalizedState (Prod S e),
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall
        ε ρSE'.sourceCoordinatePinch →
        ∃ τ : SubnormalizedState (Prod S (Prod Z e)),
          ((E.deterministicGraphCqState g).reindex
            (deterministicGraphSourceMarginalEquiv Z S e)).toSubnormalized.purifiedBall ε τ ∧
          τ.marginalB.sourceDeterministicPostprocess g =
            ρSE'.sourceCoordinatePinch ∧
          τ.marginalB.sourceCoordinatePinch = τ.marginalB) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hεgraph : ε < Real.sqrt
      ((E.deterministicGraphCqState g).reindex
        (deterministicGraphSourceMarginalEquiv Z S e)).toSubnormalized.matrix.trace.re := by
    change ε < Real.sqrt
      ((E.deterministicGraphCqState g).reindex
        (deterministicGraphSourceMarginalEquiv Z S e)).matrix.trace.re
    have htrace :
        ((E.deterministicGraphCqState g).reindex
          (deterministicGraphSourceMarginalEquiv Z S e)).matrix.trace.re = 1 := by
      rw [((E.deterministicGraphCqState g).reindex
        (deterministicGraphSourceMarginalEquiv Z S e)).trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  refine
    E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_sourceCoordinatePinch_graph_witness_lift
      g hε0 hε1 ?_
  intro ρSE' hρSE'
  rcases hlift ρSE' hρSE' with ⟨τ, hτball, hcoarse, hpinched⟩
  have hτpos : 0 < τ.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      ((E.deterministicGraphCqState g).reindex
        (deterministicGraphSourceMarginalEquiv Z S e)).toSubnormalized τ
      hεgraph hτball
  have hτmarg_pos : 0 < τ.marginalB.matrix.trace.re := by
    rw [SubnormalizedState.marginalB_matrix, partialTraceA_trace]
    exact hτpos
  have hentropy :
      (τ.marginalB.sourceDeterministicPostprocess g).conditionalMinEntropyRaw ≤
        τ.marginalB.sourceCoordinatePinch.conditionalMinEntropyRaw :=
    τ.marginalB
      |>.conditionalMinEntropy_sourceDeterministicPostprocess_le_sourceCoordinatePinch_of_trace_pos
        g hτmarg_pos
  exact ⟨τ, hτball, by
    simpa [hcoarse, hpinched] using hentropy⟩

/-- A graph-ball lift of each nearby postprocessed state is sufficient for the
smooth deterministic postprocessing inequality. The source witness is obtained
by tracing out the deterministic output register of the graph witness. -/
theorem subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_graph_witness_lift
    (E : Ensemble Z e) (g : Z → S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hlift : ∀ ρSE',
      (E.deterministicPostprocessCqState g).toSubnormalized.purifiedBall ε ρSE' →
        ∃ τ : SubnormalizedState (Prod S (Prod Z e)),
          ((E.deterministicGraphCqState g).reindex
            (deterministicGraphSourceMarginalEquiv Z S e)).toSubnormalized.purifiedBall ε τ ∧
          ρSE'.conditionalMinEntropyRaw ≤ τ.marginalB.conditionalMinEntropyRaw) :
    (E.deterministicPostprocessCqState g).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((E.deterministicPostprocessCqState g).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) :=
  E.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le_of_witness_lift
    g hε0 hε1 fun ρSE' hρSE' => by
      rcases hlift ρSE' hρSE' with ⟨τ, hτball, hle⟩
      exact ⟨τ.marginalB,
        E.deterministicGraphCqState_purifiedBall_marginalZE_of_purifiedBall g hτball, hle⟩

end Ensemble

namespace Security

/-- The trace-distance converse radius stays inside the normalized smoothing domain. -/
theorem sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Real.sqrt (2 * ε - ε ^ 2) < 1 := by
  have hinside_nonneg : 0 ≤ 2 * ε - ε ^ 2 := by
    nlinarith [hε0, hε1.le]
  have hsq_pos : 0 < (1 - ε) ^ 2 := by
    exact sq_pos_of_ne_zero (by linarith)
  have hinside_lt_one : 2 * ε - ε ^ 2 < 1 := by
    nlinarith
  have hsqrt_lt : Real.sqrt (2 * ε - ε ^ 2) < Real.sqrt 1 :=
    Real.sqrt_lt_sqrt hinside_nonneg hinside_lt_one
  simpa using hsqrt_lt

variable {F : Type uF} {Z : Type uZ} {S : Type uS} {e : Type ue}
variable [Fintype F] [DecidableEq F]
variable [Fintype Z] [DecidableEq Z]
variable [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype e] [DecidableEq e]

/-- The extractor uniform-output state is the existing maximally mixed state on
the output alphabet. -/
theorem uniformExtractorOutputState_eq_maximallyMixed :
    QIT.Security.uniformExtractorOutputState (S := S) = State.maximallyMixed S := by
  ext s t
  by_cases hst : s = t
  · subst t
    simp [QIT.Security.uniformExtractorOutputState_matrix,
      QIT.Security.uniformExtractorOutputProb, State.maximallyMixed_matrix]
  · simp [QIT.Security.uniformExtractorOutputState_matrix,
      QIT.Security.uniformExtractorOutputProb, State.maximallyMixed_matrix, hst]

/-- The ideal uniform extractor output tensor arbitrary side information has
conditional min-entropy `log₂ |S|`. -/
theorem conditionalMinEntropy_uniformExtractorOutputState_prod
    (σ : State e) :
    ((QIT.Security.uniformExtractorOutputState (S := S)).prod σ).conditionalMinEntropy =
      log2 (Fintype.card S : ℝ) := by
  rw [uniformExtractorOutputState_eq_maximallyMixed (S := S)]
  exact State.conditionalMinEntropy_maximallyMixed_prod (a := S) σ

/-- The idealized extractor output state has conditional min-entropy
`log₂ |S|` on the extractor-output register. -/
theorem idealExtractorOutputState_conditionalMinEntropy
    (ρ : State (Prod S (Prod F e))) :
    (QIT.Security.idealExtractorOutputState ρ).conditionalMinEntropy =
      log2 (Fintype.card S : ℝ) := by
  rw [QIT.Security.idealExtractorOutputState]
  exact conditionalMinEntropy_uniformExtractorOutputState_prod
    (S := S) ρ.marginalB

namespace HashFamily

variable {Z : Type uZ} [Fintype Z] [DecidableEq Z]
variable [Nonempty F]

/-- Source-shaped ensemble with the public seed copied into the conditioning
system.  The classical source label is `(z, f)` and the side information is
`(f, e)`. -/
def seededSourceEnsemble
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) :
    Ensemble (Prod Z F) (Prod F e) where
  probs := fun zf => E.probs zf.1 * H.prob zf.2
  weights_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ z : Z, ∑ f : F, E.probs z * H.prob f) =
          ∑ z : Z, E.probs z * (∑ f : F, H.prob f) := by
        simp [Finset.mul_sum]
      _ = ∑ z : Z, E.probs z * 1 := by rw [H.prob_sum]
      _ = ∑ z : Z, E.probs z := by simp
      _ = 1 := E.weights_sum
  states := fun zf => (Classical.basisState zf.2).prod (E.states zf.1)

omit [Fintype S] [DecidableEq S] [Nonempty S] [DecidableEq Z] [Nonempty F] in
@[simp]
theorem seededSourceEnsemble_probs
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) (z : Z) (f : F) :
    (H.seededSourceEnsemble E).probs (z, f) = E.probs z * H.prob f :=
  rfl

omit [Fintype S] [DecidableEq S] [Nonempty S] [DecidableEq Z] [Nonempty F] in
@[simp]
theorem seededSourceEnsemble_states
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) (z : Z) (f : F) :
    (H.seededSourceEnsemble E).states (z, f) =
      (Classical.basisState f).prod (E.states z) :=
  rfl

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty F] in
/-- The `(z,f)` source block of the seeded source, restricted to the copied
seed value `f` in the conditioning system, is the original `z` cq block scaled
by the seed probability. -/
theorem seededSourceEnsemble_cqBlock_seedBlock
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) (z : Z) (f : F) :
    Classical.block
        (Classical.block (H.seededSourceEnsemble E).cqState.matrix (z, f) (z, f)) f f =
      (((E.probs z * H.prob f : ℝ≥0) : ℂ) • (E.states z).matrix) := by
  rw [Classical.cqState_block_self]
  ext i j
  simp [Classical.block, Matrix.smul_apply]

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty F] in
/-- Summing over the copied seed blocks recovers the original source cq block. -/
theorem seededSourceEnsemble_cqBlock_seedBlock_sum
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) (z : Z) :
    (∑ f : F,
        Classical.block
          (Classical.block (H.seededSourceEnsemble E).cqState.matrix (z, f) (z, f)) f f) =
      E.cqBlock z := by
  simp_rw [H.seededSourceEnsemble_cqBlock_seedBlock E z]
  have hsum_prob :
      (∑ f : F, (((E.probs z * H.prob f : ℝ≥0) : ℂ))) =
        (E.probs z : ℂ) := by
    calc
      (∑ f : F, (((E.probs z * H.prob f : ℝ≥0) : ℂ))) =
          (((∑ f : F, E.probs z * H.prob f : ℝ≥0)) : ℂ) := by
            simp
      _ = ((E.probs z * ∑ f : F, H.prob f : ℝ≥0) : ℂ) := by
            rw [Finset.mul_sum]
      _ = (E.probs z : ℂ) := by
            rw [H.prob_sum]
            simp
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Ensemble.cqBlock_eq]
  rw [← Finset.sum_smul, hsum_prob]

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty F] in
/-- A feasible conditional-min-entropy witness for the seeded source pushes
back to a feasible witness for the original source by tracing out the public
seed from the conditioning system. -/
theorem conditionalMinEntropyFeasible_of_seededSourceEnsemble
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e)
    (σ : State (Prod F e)) {lam : ℝ}
    (hseed : State.ConditionalMinEntropyFeasible (a := Prod Z F)
      (H.seededSourceEnsemble E).cqState σ lam) :
    State.ConditionalMinEntropyFeasible (a := Z) E.cqState σ.marginalB lam := by
  classical
  refine Ensemble.conditionalMinEntropyFeasible_of_cqBlock_le E σ.marginalB lam ?_
  intro z
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  have hsum_left :
      E.cqBlock z =
        ∑ f : F,
          Classical.block
            (Classical.block (H.seededSourceEnsemble E).cqState.matrix (z, f) (z, f)) f f :=
    (H.seededSourceEnsemble_cqBlock_seedBlock_sum E z).symm
  rw [hsum_left]
  have hsum_le :
      (∑ f : F,
          Classical.block
            (Classical.block (H.seededSourceEnsemble E).cqState.matrix (z, f) (z, f)) f f) ≤
        ∑ f : F, c • Classical.block σ.matrix f f := by
    refine Finset.sum_le_sum fun f _ => ?_
    have houter :
        Classical.block (H.seededSourceEnsemble E).cqState.matrix (z, f) (z, f) ≤
          c • σ.matrix := by
      simpa [c] using
        State.block_le_of_conditionalMinEntropyFeasible
          (H.seededSourceEnsemble E).cqState σ (z, f) hseed
    have hblock := Classical.block_le_block_of_le houter f
    simpa [Classical.block, Matrix.smul_apply] using hblock
  refine hsum_le.trans_eq ?_
  rw [State.marginalB_matrix]
  rw [Classical.partialTraceA_eq_sum_blocks]
  simpa [c] using
    (Finset.smul_sum.symm :
      (∑ f : F, c • Classical.block σ.matrix f f) =
        c • ∑ f : F, Classical.block σ.matrix f f)

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty F] in
/-- Copying an independent public seed into both the source label and the
conditioning system does not increase normalized cq conditional min-entropy. -/
theorem conditionalMinEntropy_seededSourceEnsemble_le_source
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) :
    (H.seededSourceEnsemble E).cqState.conditionalMinEntropy ≤
      E.cqState.conditionalMinEntropy := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hseed_prod : Nonempty (Prod (Prod Z F) (Prod F e)) :=
    (H.seededSourceEnsemble E).cqState.nonempty
  letI : Nonempty (Prod Z F) := ⟨(Classical.choice hseed_prod).1⟩
  letI : Nonempty (Prod F e) := ⟨(Classical.choice hseed_prod).2⟩
  let sseed : Set ℝ :=
    (H.seededSourceEnsemble E).cqState.conditionalMinEntropyFeasibleExponentValueSet
      (a := Prod Z F)
  let ssource : Set ℝ := E.cqState.conditionalMinEntropyFeasibleExponentValueSet (a := Z)
  have hseed_nonempty : sseed.Nonempty := by
    simpa [sseed] using
      (H.seededSourceEnsemble E).cqState.conditionalMinEntropyFeasibleExponentValueSet_nonempty
        (a := Prod Z F)
  have hsource_bdd : BddAbove ssource := by
    simpa [ssource] using
      State.conditionalMinEntropyFeasibleExponentValueSet_bddAbove (a := Z) E.cqState
  have hseed_eq :
      (H.seededSourceEnsemble E).cqState.conditionalMinEntropy = sSup sseed := by
    simp [sseed, State.conditionalMinEntropy_eq,
      State.conditionalMinEntropyFeasibleExponentValueSet]
  have hsource_eq :
      E.cqState.conditionalMinEntropy = sSup ssource := by
    simp [ssource, State.conditionalMinEntropy_eq,
      State.conditionalMinEntropyFeasibleExponentValueSet]
  rw [hseed_eq, hsource_eq]
  refine csSup_le hseed_nonempty ?_
  intro lam hlam
  rcases hlam with ⟨σ, hσ⟩
  exact le_csSup hsource_bdd
    ⟨σ.marginalB, H.conditionalMinEntropyFeasible_of_seededSourceEnsemble E σ hσ⟩

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty F] in
/-- A subnormalized feasible conditional-min-entropy witness for the seeded
source pushes back to the original source by tracing out the public seed from
the conditioning system. -/
theorem subnormalizedConditionalMinEntropyFeasible_of_seededSourceEnsemble
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e)
    (σ : SubnormalizedState (Prod F e)) {lam : ℝ}
    (hseed : SubnormalizedState.ConditionalMinEntropyFeasible (a := Prod Z F)
      (H.seededSourceEnsemble E).cqState.toSubnormalized σ lam) :
    SubnormalizedState.ConditionalMinEntropyFeasible (a := Z)
      E.cqState.toSubnormalized σ.marginalB lam := by
  classical
  refine Ensemble.subnormalizedConditionalMinEntropyFeasible_of_cqBlock_le E σ.marginalB lam ?_
  intro z
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  have hsum_left :
      E.cqBlock z =
        ∑ f : F,
          Classical.block
            (Classical.block (H.seededSourceEnsemble E).cqState.matrix (z, f) (z, f)) f f :=
    (H.seededSourceEnsemble_cqBlock_seedBlock_sum E z).symm
  rw [hsum_left]
  have hsum_le :
      (∑ f : F,
          Classical.block
            (Classical.block (H.seededSourceEnsemble E).cqState.matrix (z, f) (z, f)) f f) ≤
        ∑ f : F, c • Classical.block σ.matrix f f := by
    refine Finset.sum_le_sum fun f _ => ?_
    have houter :
        Classical.block (H.seededSourceEnsemble E).cqState.toSubnormalized.matrix
            (z, f) (z, f) ≤
          c • σ.matrix := by
      simpa [c] using
        Ensemble.subnormalizedBlock_le_of_conditionalMinEntropyFeasible
          (H.seededSourceEnsemble E).cqState.toSubnormalized σ (z, f) hseed
    have hblock := Classical.block_le_block_of_le houter f
    simpa [Classical.block, Matrix.smul_apply, State.toSubnormalized_matrix] using hblock
  refine hsum_le.trans_eq ?_
  rw [SubnormalizedState.marginalB_matrix]
  rw [Classical.partialTraceA_eq_sum_blocks]
  simpa [c] using
    (Finset.smul_sum.symm :
      (∑ f : F, c • Classical.block σ.matrix f f) =
        c • ∑ f : F, Classical.block σ.matrix f f)

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty F] in
/-- Copying an independent public seed into both the source label and the
conditioning system does not increase subnormalized cq conditional min-entropy
after embedding the normalized cq states. -/
theorem subnormalizedConditionalMinEntropy_seededSourceEnsemble_le_source
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) :
    (H.seededSourceEnsemble E).cqState.toSubnormalized.conditionalMinEntropyRaw ≤
      E.cqState.toSubnormalized.conditionalMinEntropyRaw := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  have hseed_prod : Nonempty (Prod (Prod Z F) (Prod F e)) :=
    (H.seededSourceEnsemble E).cqState.nonempty
  letI : Nonempty (Prod Z F) := ⟨(Classical.choice hseed_prod).1⟩
  letI : Nonempty (Prod F e) := ⟨(Classical.choice hseed_prod).2⟩
  let sseed : Set ℝ :=
    (H.seededSourceEnsemble E).cqState.toSubnormalized
      |>.conditionalMinEntropyFeasibleExponentValueSet (a := Prod Z F)
  let ssource : Set ℝ :=
    E.cqState.toSubnormalized.conditionalMinEntropyFeasibleExponentValueSet (a := Z)
  have hseed_nonempty : sseed.Nonempty := by
    obtain ⟨lam, σ, hσ⟩ :=
      (H.seededSourceEnsemble E).cqState.conditionalMinEntropyFeasibleExponentValueSet_nonempty
        (a := Prod Z F)
    refine ⟨lam, ?_⟩
    exact ⟨σ.toSubnormalized,
      (State.toSubnormalized_ConditionalMinEntropyFeasible_iff
        (a := Prod Z F) (H.seededSourceEnsemble E).cqState σ lam).2 hσ⟩
  have hsource_bdd : BddAbove ssource := by
    simpa [ssource] using
      Ensemble.subnormalizedConditionalMinEntropyFeasibleExponentValueSet_toSubnormalized_bddAbove
        (a := Z) E.cqState
  have hseed_eq :
      (H.seededSourceEnsemble E).cqState.toSubnormalized.conditionalMinEntropyRaw =
        sSup sseed := by
    simp [sseed, SubnormalizedState.conditionalMinEntropyRaw_eq]
  have hsource_eq :
      E.cqState.toSubnormalized.conditionalMinEntropyRaw = sSup ssource := by
    simp [ssource, SubnormalizedState.conditionalMinEntropyRaw_eq]
  rw [hseed_eq, hsource_eq]
  refine csSup_le hseed_nonempty ?_
  intro lam hlam
  rcases hlam with ⟨σ, hσ⟩
  exact le_csSup hsource_bdd
    ⟨σ.marginalB, H.subnormalizedConditionalMinEntropyFeasible_of_seededSourceEnsemble E σ hσ⟩

private def matchedSeedSourceEquiv (Z : Type uZ) (F : Type uF) (e : Type ue) :
    Prod (Prod Z F) (Prod F e) ≃ Prod (Prod (Prod Z F) F) e where
  toFun x := (((x.1.1, x.1.2), x.2.1), x.2.2)
  invFun y := ((y.1.1.1, y.1.1.2), (y.1.2, y.2))
  left_inv := by
    intro x
    rcases x with ⟨⟨z, fs⟩, ⟨ft, i⟩⟩
    rfl
  right_inv := by
    intro y
    rcases y with ⟨⟨⟨z, fs⟩, ft⟩, i⟩
    rfl

private def matchedSeedReindexedState
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e))) :
    SubnormalizedState (Prod (Prod (Prod Z F) F) e) :=
  τ.applyTraceNonincreasingCP
    (Channel.reindex (matchedSeedSourceEquiv Z F e)).map
    (MatrixMap.traceNonincreasingCP_of_tracePreserving
      (Channel.reindex (matchedSeedSourceEquiv Z F e)).completelyPositive
      (Channel.reindex (matchedSeedSourceEquiv Z F e)).tracePreserving)

private def matchedSeedFilteredState
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e))) :
    SubnormalizedState (Prod (Prod (Prod Z F) F) e) :=
  (matchedSeedReindexedState (Z := Z) (F := F) (e := e) τ).sourceBlockFilter
    (fun x : Prod (Prod Z F) F => x.1.2 = x.2)

private def matchedSeedSourceState
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e))) :
    SubnormalizedState (Prod Z e) :=
  (matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ).sourceDeterministicPostprocess
    (fun x : Prod (Prod Z F) F => x.1.1)

omit [Nonempty F] in
private theorem matchedSeedReindexedState_matrix_apply
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e)))
    (z z' : Z) (fs fs' ft ft' : F) (i j : e) :
    (matchedSeedReindexedState (Z := Z) (F := F) (e := e) τ).matrix
        (((z, fs), ft), i) (((z', fs'), ft'), j) =
      τ.matrix ((z, fs), (ft, i)) ((z', fs'), (ft', j)) := by
  simp [matchedSeedReindexedState, matchedSeedSourceEquiv, Channel.reindex,
    MatrixMap.ofReferenceIsometry_apply, ReferenceIsometry.ofEquiv, Matrix.mul_apply]
  rw [Finset.sum_eq_single (((z', fs'), (ft', j)) : Prod (Prod Z F) (Prod F e))]
  · simp only [and_self, ↓reduceIte]
    rw [Finset.sum_eq_single (((z, fs), (ft, i)) : Prod (Prod Z F) (Prod F e))]
    · simp
    · intro x _ hx
      rcases x with ⟨⟨zx, fsx⟩, ⟨ftx, ix⟩⟩
      by_cases hcond : (((z, fs) = (zx, fsx) ∧ ft = ftx) ∧ i = ix)
      · rcases hcond with ⟨⟨hzf, hft⟩, hi⟩
        cases hzf
        cases hft
        cases hi
        exact (hx rfl).elim
      · rw [if_neg hcond]
    · simp
  · intro x _ hx
    rcases x with ⟨⟨zx, fsx⟩, ⟨ftx, ix⟩⟩
    by_cases hcond : (((z', fs') = (zx, fsx) ∧ ft' = ftx) ∧ j = ix)
    · rcases hcond with ⟨⟨hzf, hft⟩, hi⟩
      cases hzf
      cases hft
      cases hi
      exact (hx rfl).elim
    · rw [if_neg hcond]
  · simp

omit [Nonempty F] in
private theorem matchedSeedFilteredState_block
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e)))
    (z : Z) (fs ft : F) :
    Classical.block (matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ).matrix
        ((z, fs), ft) ((z, fs), ft) =
      if fs = ft then
        Classical.block (Classical.block τ.matrix (z, fs) (z, fs)) ft ft
      else 0 := by
  classical
  ext i j
  rw [matchedSeedFilteredState, SubnormalizedState.sourceBlockFilter_matrix_eq_blockDiagonal]
  have hblock :=
    congrFun (congrFun
      (Classical.blockDiagonal_block_self
        (fun x : Prod (Prod Z F) F =>
          if x.1.2 = x.2 then
            Classical.block (matchedSeedReindexedState (Z := Z) (F := F) (e := e) τ).matrix x x
          else 0)
        ((z, fs), ft)) i) j
  rw [hblock]
  by_cases hfs : fs = ft
  · subst ft
    simp [Classical.block, matchedSeedReindexedState_matrix_apply]
  · simp [hfs]

omit [Nonempty F] in
private theorem matchedSeedSourceState_block
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e))) (z : Z) :
    Classical.block (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ).matrix z z =
      ∑ f : F, Classical.block (Classical.block τ.matrix (z, f) (z, f)) f f := by
  classical
  ext i j
  simp only [matchedSeedSourceState, SubnormalizedState.sourceDeterministicPostprocess_block,
    Matrix.sum_apply]
  rw [Fintype.sum_prod_type]
  simp only [Classical.block]
  let matchedSum : ℂ :=
    ∑ f : F, τ.matrix ((z, f), (f, i)) ((z, f), (f, j))
  have hleft :
      (∑ zf : Prod Z F,
          ∑ ft : F,
            (if (fun x : Prod (Prod Z F) F => x.1.1) (zf, ft) = z then
                Classical.block
                  (matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ).matrix
                  (zf, ft) (zf, ft)
              else 0) i j) = matchedSum := by
    calc
      (∑ zf : Prod Z F,
          ∑ ft : F,
            (if (fun x : Prod (Prod Z F) F => x.1.1) (zf, ft) = z then
                Classical.block
                  (matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ).matrix
                  (zf, ft) (zf, ft)
              else 0) i j) =
          ∑ zf : Prod Z F,
            ∑ ft : F,
              if zf.1 = z ∧ zf.2 = ft then
                τ.matrix ((zf.1, zf.2), (ft, i)) ((zf.1, zf.2), (ft, j))
              else 0 := by
            refine Finset.sum_congr rfl fun zf _ => ?_
            refine Finset.sum_congr rfl fun ft _ => ?_
            by_cases hz : zf.1 = z
            · subst z
              by_cases hf : zf.2 = ft
              · subst ft
                have hblock :=
                  congrFun (congrFun
                    (matchedSeedFilteredState_block
                      (Z := Z) (F := F) (e := e) τ zf.1 zf.2 zf.2) i) j
                simpa [Classical.block] using hblock
              · have hblock :=
                  congrFun (congrFun
                    (matchedSeedFilteredState_block
                      (Z := Z) (F := F) (e := e) τ zf.1 zf.2 ft) i) j
                simpa [hf, Classical.block] using hblock
            · simp [hz]
      _ = matchedSum := by
            dsimp [matchedSum]
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_eq_single z]
            · simp
            · intro z' _ hz'
              simp [hz']
            · simp
  simpa [matchedSum] using hleft

omit [Nonempty F] in
private theorem matchedSeedSourceState_matrix_eq_blockDiagonal
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e))) :
    (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ).matrix =
      Classical.blockDiagonal
        (fun z : Z =>
          ∑ f : F, Classical.block (Classical.block τ.matrix (z, f) (z, f)) f f) := by
  classical
  ext zi zj
  rcases zi with ⟨z, i⟩
  rcases zj with ⟨z', j⟩
  by_cases hzz : z = z'
  · subst z'
    have hblock :=
      congrFun (congrFun
        (matchedSeedSourceState_block (Z := Z) (F := F) (e := e) τ z) i) j
    have hdiag :=
      congrFun (congrFun
        (Classical.blockDiagonal_block_self
          (fun z : Z =>
            ∑ f : F, Classical.block (Classical.block τ.matrix (z, f) (z, f)) f f)
          z) i) j
    simpa [Classical.block] using hblock.trans hdiag.symm
  · have hleft : (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ).matrix
        (z, i) (z', j) = 0 := by
      rw [matchedSeedSourceState, SubnormalizedState.sourceDeterministicPostprocess_matrix]
      have hblock :=
        congrFun (congrFun
          (Classical.blockDiagonal_block_ne
            (fun y : Z =>
              ∑ x : Prod (Prod Z F) F,
                if (fun x : Prod (Prod Z F) F => x.1.1) x = y then
                  Classical.block
                    (matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ).matrix x x
                else 0)
            hzz) i) j
      simpa [Classical.block] using hblock
    have hright :
        Classical.blockDiagonal
          (fun z : Z =>
            ∑ f : F, Classical.block (Classical.block τ.matrix (z, f) (z, f)) f f)
          (z, i) (z', j) = 0 := by
      have hblock :=
        congrFun (congrFun
          (Classical.blockDiagonal_block_ne
            (fun z : Z =>
              ∑ f : F, Classical.block (Classical.block τ.matrix (z, f) (z, f)) f f)
            hzz) i) j
      simpa [Classical.block] using hblock
    rw [hleft, hright]

omit [Nonempty F] in
private theorem matchedSeedSourceState_ConditionalMinEntropyScaleFeasible
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e)))
    (T : CMatrix (Prod F e))
    (hT : SubnormalizedState.ConditionalMinEntropyScaleFeasible
      (a := Prod Z F) τ T) :
    SubnormalizedState.ConditionalMinEntropyScaleFeasible (a := Z)
      (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ)
      (partialTraceA (a := F) (b := e) T) := by
  classical
  constructor
  · exact partialTraceA_posSemidef hT.1
  · rw [Matrix.le_iff]
    let blocks : Z → CMatrix e :=
      fun z : Z =>
        ∑ f : F, Classical.block (Classical.block τ.matrix (z, f) (z, f)) f f
    have hblocks : ∀ z : Z,
        (partialTraceA (a := F) (b := e) T - blocks z).PosSemidef := by
      intro z
      rw [← Matrix.le_iff]
      have hsum_le :
          blocks z ≤ ∑ f : F, Classical.block T f f := by
        dsimp [blocks]
        refine Finset.sum_le_sum fun f _ => ?_
        have houter :
            Classical.block τ.matrix (z, f) (z, f) ≤ T :=
          SubnormalizedState.block_le_of_conditionalMinEntropyScaleFeasible
            τ T (z, f) hT
        have hblock := Classical.block_le_block_of_le houter f
        simpa [Classical.block] using hblock
      exact hsum_le.trans_eq
        (Classical.partialTraceA_eq_sum_blocks (ι := F) (a := e) T).symm
    have hmatrix :
        Matrix.kronecker (1 : CMatrix Z) (partialTraceA (a := F) (b := e) T) -
            (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ).matrix =
          Classical.blockDiagonal
            (fun z : Z => partialTraceA (a := F) (b := e) T - blocks z) := by
      calc
        Matrix.kronecker (1 : CMatrix Z) (partialTraceA (a := F) (b := e) T) -
            (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ).matrix =
            Classical.blockDiagonal
                (fun _ : Z => partialTraceA (a := F) (b := e) T) -
              Classical.blockDiagonal blocks := by
              rw [Classical.identityTensor_eq_blockDiagonal,
                matchedSeedSourceState_matrix_eq_blockDiagonal
                  (Z := Z) (F := F) (e := e) τ]
        _ = Classical.blockDiagonal
            (fun z : Z => partialTraceA (a := F) (b := e) T - blocks z) := by
              rw [← Classical.blockDiagonal_sub]
    rw [hmatrix]
    exact Classical.blockDiagonal_posSemidef
      (fun z : Z => partialTraceA (a := F) (b := e) T - blocks z) hblocks

omit [Nonempty F] in
private theorem matchedSeedSourceState_conditionalMinEntropyScale_le
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e))) :
    (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ).conditionalMinEntropyScale
        (a := Z) ≤
      τ.conditionalMinEntropyScale (a := Prod Z F) := by
  classical
  rw [SubnormalizedState.conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    SubnormalizedState.conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (τ.conditionalMinEntropyScaleValueSet_nonempty (a := Prod Z F)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbdd :
      BddBelow
        ((matchedSeedSourceState (Z := Z) (F := F) (e := e) τ)
          |>.conditionalMinEntropyScaleValueSet (a := Z)) :=
    (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ)
      |>.conditionalMinEntropyScaleValueSet_bddBelow (a := Z)
  refine csInf_le hbdd ?_
  refine ⟨partialTraceA (a := F) (b := e) T,
    matchedSeedSourceState_ConditionalMinEntropyScaleFeasible
      (Z := Z) (F := F) (e := e) τ T hT, ?_⟩
  rw [partialTraceA_trace]

private theorem conditionalMinEntropy_le_matchedSeedSourceState_of_trace_pos
    [Nonempty Z] [Nonempty e]
    (τ : SubnormalizedState (Prod (Prod Z F) (Prod F e)))
    (hτ : 0 < τ.matrix.trace.re)
    (hmatched :
      0 < (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ).matrix.trace.re) :
    τ.conditionalMinEntropyRaw ≤
      (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ).conditionalMinEntropyRaw := by
  classical
  have hseed_source_nonempty : Nonempty (Prod Z F) := ⟨(Classical.choice inferInstance, Classical.choice inferInstance)⟩
  have hseed_side_nonempty : Nonempty (Prod F e) := ⟨(Classical.choice inferInstance, Classical.choice inferInstance)⟩
  letI : Nonempty (Prod Z F) := hseed_source_nonempty
  letI : Nonempty (Prod F e) := hseed_side_nonempty
  rw [τ.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos
      (a := Prod Z F) hτ,
    (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ)
      |>.conditionalMinEntropy_eq_neg_log2_scale_of_trace_pos (a := Z) hmatched]
  have hscale :=
    matchedSeedSourceState_conditionalMinEntropyScale_le
      (Z := Z) (F := F) (e := e) τ
  have hmatched_scale_pos :
      0 <
        ((matchedSeedSourceState (Z := Z) (F := F) (e := e) τ)
          |>.conditionalMinEntropyScale (a := Z)) :=
    ((matchedSeedSourceState (Z := Z) (F := F) (e := e) τ)
      |>.conditionalMinEntropyScale_pos_of_trace_pos (a := Z)) hmatched
  have hlog :
      log2
          (((matchedSeedSourceState (Z := Z) (F := F) (e := e) τ)
            |>.conditionalMinEntropyScale (a := Z))) ≤
        log2 (τ.conditionalMinEntropyScale (a := Prod Z F)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hmatched_scale_pos hscale)
      (le_of_lt (Real.log_pos one_lt_two))
  exact neg_le_neg hlog

omit [Nonempty F] in
/-- Applying the deterministic source-coarse-graining matrix map to a
subnormalized state is the same state as `sourceDeterministicPostprocess`. -/
private theorem apply_sourceDeterministicPostprocessMap_eq
    (ρ : SubnormalizedState (Prod (Prod (Prod Z F) F) e)) :
    ρ.applyTraceNonincreasingCP
        (SubnormalizedState.sourceDeterministicPostprocessMap
          (a := Prod (Prod Z F) F) (b := e)
          (fun x : Prod (Prod Z F) F => x.1.1))
        (SubnormalizedState.sourceDeterministicPostprocessMap_traceNonincreasingCP
          (a := Prod (Prod Z F) F) (b := e)
          (fun x : Prod (Prod Z F) F => x.1.1)) =
      ρ.sourceDeterministicPostprocess
        (fun x : Prod (Prod Z F) F => x.1.1) := by
  apply SubnormalizedState.ext
  rw [SubnormalizedState.applyTraceNonincreasingCP_matrix]
  exact SubnormalizedState.sourceDeterministicPostprocessMap_apply_matrix
    (a := Prod (Prod Z F) F) (b := e) ρ
    (fun x : Prod (Prod Z F) F => x.1.1)

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty F] in
private theorem matchedSeedSourceState_seededSourceEnsemble
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) :
    matchedSeedSourceState (Z := Z) (F := F) (e := e)
        (H.seededSourceEnsemble E).cqState.toSubnormalized =
      E.cqState.toSubnormalized := by
  classical
  apply SubnormalizedState.ext
  ext zi zj
  rcases zi with ⟨z, i⟩
  rcases zj with ⟨z', j⟩
  rw [matchedSeedSourceState_matrix_eq_blockDiagonal]
  rw [State.toSubnormalized_matrix, State.toSubnormalized_matrix]
  let blocks : Z → CMatrix e :=
    fun z : Z =>
      ∑ f : F,
        Classical.block
          (Classical.block (H.seededSourceEnsemble E).cqState.matrix
            (z, f) (z, f)) f f
  change Classical.blockDiagonal blocks (z, i) (z', j) =
    E.cqState.matrix (z, i) (z', j)
  rw [Classical.cqState_eq_blockDiagonal E]
  by_cases hzz : z = z'
  · subst z'
    have hleft :=
      congrFun (congrFun (Classical.blockDiagonal_block_self blocks z) i) j
    have hright :=
      congrFun (congrFun
        (Classical.blockDiagonal_block_self
          (fun z : Z => (E.probs z : ℂ) • (E.states z).matrix) z) i) j
    have hsum :=
      congrFun (congrFun
        (H.seededSourceEnsemble_cqBlock_seedBlock_sum E z) i) j
    calc
      Classical.blockDiagonal blocks (z, i) (z, j) = blocks z i j := hleft
      _ = ((E.probs z : ℂ) • (E.states z).matrix) i j := by
            simpa [blocks, Ensemble.cqBlock_eq] using hsum
      _ = Classical.blockDiagonal
            (fun z : Z => (E.probs z : ℂ) • (E.states z).matrix) (z, i) (z, j) :=
            hright.symm
  · have hleft :=
      congrFun (congrFun (Classical.blockDiagonal_block_ne blocks hzz) i) j
    have hright :=
      congrFun (congrFun
        (Classical.blockDiagonal_block_ne
          (fun z : Z => (E.probs z : ℂ) • (E.states z).matrix) hzz) i) j
    have hleft' : Classical.blockDiagonal blocks (z, i) (z', j) = 0 := by
      simpa [Classical.block] using hleft
    have hright' :
        Classical.blockDiagonal (fun z : Z => (E.probs z : ℂ) • (E.states z).matrix)
          (z, i) (z', j) = 0 := by
      simpa [Classical.block] using hright
    rw [hleft', hright']

omit [Fintype S] [DecidableEq S] [Nonempty S] [Nonempty F] in
private theorem matchedSeedSourceState_purifiedBall
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e)
    {τ : SubnormalizedState (Prod (Prod Z F) (Prod F e))} {ε : ℝ}
    (hτ :
      (H.seededSourceEnsemble E).cqState.toSubnormalized.purifiedBall ε τ) :
    E.cqState.toSubnormalized.purifiedBall ε
      (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ) := by
  classical
  let center : SubnormalizedState (Prod (Prod Z F) (Prod F e)) :=
    (H.seededSourceEnsemble E).cqState.toSubnormalized
  let Φreindex : MatrixMap (Prod (Prod Z F) (Prod F e))
      (Prod (Prod (Prod Z F) F) e) :=
    (Channel.reindex (matchedSeedSourceEquiv Z F e)).map
  let hΦreindex : MatrixMap.TraceNonincreasingCP Φreindex :=
    MatrixMap.traceNonincreasingCP_of_tracePreserving
      (Channel.reindex (matchedSeedSourceEquiv Z F e)).completelyPositive
      (Channel.reindex (matchedSeedSourceEquiv Z F e)).tracePreserving
  have hreindex :
      (matchedSeedReindexedState (Z := Z) (F := F) (e := e) center).purifiedBall
        ε (matchedSeedReindexedState (Z := Z) (F := F) (e := e) τ) := by
    simpa [matchedSeedReindexedState, center, Φreindex, hΦreindex] using
      (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
        (ρ := center) (σ := τ) (ε := ε) Φreindex hΦreindex
        (by simpa [center] using hτ))
  let p : Prod (Prod Z F) F → Prop := fun x => x.1.2 = x.2
  have hfilter :
      (matchedSeedFilteredState (Z := Z) (F := F) (e := e) center).purifiedBall
        ε (matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ) := by
    simpa [matchedSeedFilteredState, p] using
      (SubnormalizedState.purifiedBall_of_traceNonincreasingCP
        (ρ := matchedSeedReindexedState (Z := Z) (F := F) (e := e) center)
        (σ := matchedSeedReindexedState (Z := Z) (F := F) (e := e) τ)
        (ε := ε)
        (SubnormalizedState.sourceBlockFilterMap
          (a := Prod (Prod Z F) F) (b := e) p)
        (SubnormalizedState.sourceBlockFilterMap_traceNonincreasingCP
          (a := Prod (Prod Z F) F) (b := e) p)
        hreindex)
  let g : Prod (Prod Z F) F → Z := fun x => x.1.1
  let Φpost : MatrixMap (Prod (Prod (Prod Z F) F) e) (Prod Z e) :=
    SubnormalizedState.sourceDeterministicPostprocessMap
      (a := Prod (Prod Z F) F) (b := e) g
  let hΦpost : MatrixMap.TraceNonincreasingCP Φpost :=
    SubnormalizedState.sourceDeterministicPostprocessMap_traceNonincreasingCP
      (a := Prod (Prod Z F) F) (b := e) g
  have hpost :
      ((matchedSeedFilteredState (Z := Z) (F := F) (e := e) center).applyTraceNonincreasingCP
          Φpost hΦpost).purifiedBall ε
        ((matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ).applyTraceNonincreasingCP
          Φpost hΦpost) := by
    exact SubnormalizedState.purifiedBall_of_traceNonincreasingCP
      (ρ := matchedSeedFilteredState (Z := Z) (F := F) (e := e) center)
      (σ := matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ)
      (ε := ε) Φpost hΦpost hfilter
  have hpost' :
      (matchedSeedSourceState (Z := Z) (F := F) (e := e) center).purifiedBall ε
        (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ) := by
    have hleft :
        (matchedSeedFilteredState (Z := Z) (F := F) (e := e) center).applyTraceNonincreasingCP
            Φpost hΦpost =
          SubnormalizedState.sourceDeterministicPostprocess
            (matchedSeedFilteredState (Z := Z) (F := F) (e := e) center) g := by
      dsimp [Φpost, hΦpost, g]
      exact apply_sourceDeterministicPostprocessMap_eq
        (Z := Z) (F := F) (e := e)
        (matchedSeedFilteredState (Z := Z) (F := F) (e := e) center)
    have hright :
        (matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ).applyTraceNonincreasingCP
            Φpost hΦpost =
          SubnormalizedState.sourceDeterministicPostprocess
            (matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ) g := by
      dsimp [Φpost, hΦpost, g]
      exact apply_sourceDeterministicPostprocessMap_eq
        (Z := Z) (F := F) (e := e)
        (matchedSeedFilteredState (Z := Z) (F := F) (e := e) τ)
    rw [hleft, hright] at hpost
    simpa [matchedSeedSourceState, g] using hpost
  have hcenter :
      matchedSeedSourceState (Z := Z) (F := F) (e := e) center =
        E.cqState.toSubnormalized := by
    simpa [center] using
      matchedSeedSourceState_seededSourceEnsemble
        (Z := Z) (F := F) (S := S) (e := e) H E
  rwa [hcenter] at hpost'

omit [Fintype S] [DecidableEq S] [Nonempty S] in
/-- Copying an independent public seed into both the source label and the
conditioning system does not increase subnormalized smooth cq conditional
min-entropy after embedding the normalized cq states. -/
theorem seededSourceEnsemble_toSubnormalized_smoothConditionalMinEntropy_le_source
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (H.seededSourceEnsemble E).cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((H.seededSourceEnsemble E).cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  classical
  have hsource_prod : Nonempty (Prod Z e) := E.cqState.nonempty
  letI : Nonempty Z := ⟨(Classical.choice hsource_prod).1⟩
  letI : Nonempty e := ⟨(Classical.choice hsource_prod).2⟩
  let center : SubnormalizedState (Prod (Prod Z F) (Prod F e)) :=
    (H.seededSourceEnsemble E).cqState.toSubnormalized
  let source : SubnormalizedState (Prod Z e) := E.cqState.toSubnormalized
  have hεsource : ε < Real.sqrt source.matrix.trace.re := by
    change ε < Real.sqrt E.cqState.matrix.trace.re
    have htrace : E.cqState.matrix.trace.re = 1 := by
      rw [E.cqState.trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  have hεcenter : ε < Real.sqrt center.matrix.trace.re := by
    change ε < Real.sqrt (H.seededSourceEnsemble E).cqState.matrix.trace.re
    have htrace : (H.seededSourceEnsemble E).cqState.matrix.trace.re = 1 := by
      rw [(H.seededSourceEnsemble E).cqState.trace_eq_one]
      norm_num
    rw [htrace]
    simpa using hε1
  exact
    SubnormalizedState.smoothConditionalMinEntropyRaw_le_of_witness_lift_diff_side_of_lt_sqrt_trace
      (a := Prod Z F) (b := Prod F e) (source := Z) (c := e)
      center source hε0 hεsource
      (fun τ hτball => by
        refine ⟨matchedSeedSourceState (Z := Z) (F := F) (e := e) τ, ?_, ?_⟩
        · exact matchedSeedSourceState_purifiedBall
            (Z := Z) (F := F) (S := S) (e := e) H E
            (by simpa [center] using hτball)
        · have hτpos :
              0 < τ.matrix.trace.re :=
            SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
              center τ hεcenter hτball
          have hmatched_ball :
              source.purifiedBall ε
                (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ) :=
            matchedSeedSourceState_purifiedBall
              (Z := Z) (F := F) (S := S) (e := e) H E
              (by simpa [center] using hτball)
          have hmatched_pos :
              0 <
                (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ).matrix.trace.re :=
            SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
              source
              (matchedSeedSourceState (Z := Z) (F := F) (e := e) τ)
              hεsource hmatched_ball
          exact conditionalMinEntropy_le_matchedSeedSourceState_of_trace_pos
            (Z := Z) (F := F) (e := e) τ hτpos hmatched_pos)

omit [Nonempty S] [DecidableEq Z] [Nonempty F] in
/-- The real public-seed extractor output is the deterministic postprocessing
of the seeded source ensemble by `(z, f) ↦ H f z`. -/
theorem extractorOutputState_eq_seededSourceEnsemble_deterministicPostprocessCqState
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) :
    QIT.Security.extractorOutputState H E =
      (H.seededSourceEnsemble E).deterministicPostprocessCqState
        (fun zf : Prod Z F => H.hash zf.2 zf.1) := by
  apply State.ext
  ext x y
  rcases x with ⟨s, fi⟩
  rcases fi with ⟨f, i⟩
  rcases y with ⟨s', fj⟩
  rcases fj with ⟨f', j⟩
  simp only [QIT.Security.extractorOutputState_matrix,
    QIT.Security.extractorOutputMatrix_eq_sum,
    Ensemble.deterministicPostprocessCqState_matrix, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type]
  simp [mul_left_comm]

omit [Nonempty S] [Nonempty F] in
/-- Deterministic-postprocessing DPI applied to the seeded source
representation of a public-seed extractor output. -/
theorem extractorOutputState_toSubnormalized_smoothConditionalMinEntropy_le_seededSource
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    (QIT.Security.extractorOutputState H E).toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((QIT.Security.extractorOutputState H E).epsilon_lt_sqrt_toSubnormalized_trace hε1) ≤
      (H.seededSourceEnsemble E).cqState.toSubnormalized.smoothConditionalMinEntropy ε hε0
        ((H.seededSourceEnsemble E).cqState.epsilon_lt_sqrt_toSubnormalized_trace hε1) := by
  rw [H.extractorOutputState_eq_seededSourceEnsemble_deterministicPostprocessCqState E]
  exact (H.seededSourceEnsemble E)
    |>.subnormalizedSmoothConditionalMinEntropy_deterministicPostprocessCqState_le
      (fun zf : Prod Z F => H.hash zf.2 zf.1)
      hε0 hε1

omit [DecidableEq Z] [Nonempty F] in
/-- If an extractor is `ε`-secret, the ideal uniform output is a smooth
min-entropy candidate at the converse smoothing radius `sqrt (2ε - ε^2)`. -/
theorem idealExtractorOutputState_smoothConditionalMinEntropyCandidate_of_isEpsilonSecretExtractor
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) {ε : ℝ}
    (hε1 : ε ≤ 1) (hsecret : H.IsEpsilonSecretExtractor ε E) :
    State.SmoothConditionalMinEntropyCandidate (a := S)
      (QIT.Security.extractorOutputState H E) (Real.sqrt (2 * ε - ε ^ 2))
      (log2 (Fintype.card S : ℝ)) := by
  refine ⟨QIT.Security.idealExtractorOutputState (QIT.Security.extractorOutputState H E), ?_, ?_⟩
  · rw [State.purifiedBall_eq]
    have hD :
        (QIT.Security.extractorOutputState H E).normalizedTraceDistance
            (QIT.Security.idealExtractorOutputState
              (QIT.Security.extractorOutputState H E)) ≤ ε := by
      simpa [QIT.Security.extractorSecrecyDistance_eq_normalizedTraceDistance] using hsecret
    exact State.purifiedDistance_le_sqrt_two_mul_sub_sq_of_normalizedTraceDistance_le
      (QIT.Security.extractorOutputState H E)
      (QIT.Security.idealExtractorOutputState (QIT.Security.extractorOutputState H E))
      hε1 hD
  · exact (idealExtractorOutputState_conditionalMinEntropy
      (ρ := QIT.Security.extractorOutputState H E)).symm

omit [DecidableEq Z] [Nonempty F] in
/-- Per-extractor subnormalized output endpoint: an `ε`-secret extractor's
output length is bounded by the subnormalized smooth conditional min-entropy of
its actual output state at the converse smoothing radius. -/
theorem log2_outputLength_le_toSubnormalized_smoothConditionalMinEntropy_of_isEpsilonSecretExtractor
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hsecret : H.IsEpsilonSecretExtractor ε E) :
    log2 (H.outputLength : ℝ) ≤
      (QIT.Security.extractorOutputState H E).toSubnormalized.smoothConditionalMinEntropy
        (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
        ((QIT.Security.extractorOutputState H E).epsilon_lt_sqrt_toSubnormalized_trace
          (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) := by
  classical
  let ρout : State (Prod S (Prod F e)) := QIT.Security.extractorOutputState H E
  let ρideal : State (Prod S (Prod F e)) := QIT.Security.idealExtractorOutputState ρout
  have hside_nonempty : Nonempty (Prod F e) := ⟨(Classical.choice ρout.nonempty).2⟩
  letI : Nonempty (Prod F e) := hside_nonempty
  have hball : ρout.purifiedBall (Real.sqrt (2 * ε - ε ^ 2)) ρideal := by
    rw [State.purifiedBall_eq]
    have hD :
        ρout.normalizedTraceDistance ρideal ≤ ε := by
      simpa [ρout, ρideal, QIT.Security.extractorSecrecyDistance_eq_normalizedTraceDistance]
        using hsecret
    exact State.purifiedDistance_le_sqrt_two_mul_sub_sq_of_normalizedTraceDistance_le
      ρout ρideal hε1.le hD
  have hideal_sub_entropy :
      log2 (Fintype.card S : ℝ) = ρideal.toSubnormalized.conditionalMinEntropyRaw := by
    have hscale :
        ρideal.toSubnormalized =
          SubnormalizedState.ofStateScale ρideal 1 (by norm_num) (by norm_num) := by
      apply SubnormalizedState.ext
      simp [SubnormalizedState.ofStateScale_matrix, State.toSubnormalized_matrix]
    rw [hscale]
    rw [SubnormalizedState.conditionalMinEntropy_ofStateScale
      (a := S) (b := Prod F e) ρideal (by norm_num) (by norm_num)]
    rw [idealExtractorOutputState_conditionalMinEntropy
      (S := S) (F := F) (e := e) (ρ := ρout)]
    simp [log2]
  have hsubcand :
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := S)
        ρout.toSubnormalized (Real.sqrt (2 * ε - ε ^ 2))
        (log2 (Fintype.card S : ℝ)) := by
    exact State.toSubnormalized_SmoothConditionalMinEntropyCandidate_of
      (a := S) (ρ := ρout) (ρ' := ρideal) hball hideal_sub_entropy
  have hdelta_lt_one : Real.sqrt (2 * ε - ε ^ 2) < 1 :=
    sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1
  have htrace_out :
      ρout.matrix.trace.re = 1 := by
    rw [ρout.trace_eq_one]
    norm_num
  have hdelta_lt_trace :
      Real.sqrt (2 * ε - ε ^ 2) <
        Real.sqrt ρout.toSubnormalized.matrix.trace.re := by
    simpa [State.toSubnormalized_matrix, htrace_out] using hdelta_lt_one
  have hle :
      log2 (Fintype.card S : ℝ) ≤
        ρout.toSubnormalized.smoothConditionalMinEntropy
          (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _) hdelta_lt_trace :=
    SubnormalizedState.le_smoothConditionalMinEntropy_of_candidate_of_lt_sqrt_trace
      (a := S) (ρ := ρout.toSubnormalized) (Real.sqrt_nonneg _)
      hdelta_lt_trace hsubcand
  simpa [ρout, QIT.Security.HashFamily.outputLength_eq_card H] using hle

omit [Nonempty F] in
/-- Per-extractor seeded-source endpoint: secrecy bounds the output length by
the smooth conditional min-entropy of the source-shaped ensemble that includes
the public seed in both the source label and side information. -/
theorem log2_outputLength_le_seededSource_toSubnormalized_smoothConditionalMinEntropy_of_isEpsilonSecretExtractor
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hsecret : H.IsEpsilonSecretExtractor ε E) :
    log2 (H.outputLength : ℝ) ≤
      (H.seededSourceEnsemble E).cqState.toSubnormalized.smoothConditionalMinEntropy
        (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
        ((H.seededSourceEnsemble E).cqState.epsilon_lt_sqrt_toSubnormalized_trace
          (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) := by
  have houtput :
      log2 (H.outputLength : ℝ) ≤
        (QIT.Security.extractorOutputState H E).toSubnormalized.smoothConditionalMinEntropy
          (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
          ((QIT.Security.extractorOutputState H E).epsilon_lt_sqrt_toSubnormalized_trace
            (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) :=
    H.log2_outputLength_le_toSubnormalized_smoothConditionalMinEntropy_of_isEpsilonSecretExtractor
      E hε0 hε1 hsecret
  have hdelta0 : 0 ≤ Real.sqrt (2 * ε - ε ^ 2) :=
    Real.sqrt_nonneg _
  have hdelta1 : Real.sqrt (2 * ε - ε ^ 2) < 1 :=
    sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1
  exact houtput.trans
    (H.extractorOutputState_toSubnormalized_smoothConditionalMinEntropy_le_seededSource
      E hdelta0 hdelta1)

/-- Source-strength converse endpoint: an `ε`-secret extractor's output length
is bounded by the subnormalized smooth conditional min-entropy of the original
source cq state, at the converse smoothing radius. -/
theorem log2_outputLength_le_source_toSubnormalized_smoothConditionalMinEntropy_of_isEpsilonSecretExtractor
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hsecret : H.IsEpsilonSecretExtractor ε E) :
    log2 (H.outputLength : ℝ) ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy
        (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
          (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) := by
  have hseed :
      log2 (H.outputLength : ℝ) ≤
        (H.seededSourceEnsemble E).cqState.toSubnormalized.smoothConditionalMinEntropy
          (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
          ((H.seededSourceEnsemble E).cqState.epsilon_lt_sqrt_toSubnormalized_trace
            (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) :=
    H.log2_outputLength_le_seededSource_toSubnormalized_smoothConditionalMinEntropy_of_isEpsilonSecretExtractor
      E hε0 hε1 hsecret
  have hdelta0 : 0 ≤ Real.sqrt (2 * ε - ε ^ 2) :=
    Real.sqrt_nonneg _
  have hdelta1 : Real.sqrt (2 * ε - ε ^ 2) < 1 :=
    sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1
  exact hseed.trans
    (H.seededSourceEnsemble_toSubnormalized_smoothConditionalMinEntropy_le_source
      E hdelta0 hdelta1)

omit [DecidableEq Z] [Nonempty F] in
/-- Per-extractor converse endpoint: an `ε`-secret extractor's output length is
bounded by the smooth conditional min-entropy of its actual output state. -/
theorem log2_outputLength_le_smoothConditionalMinEntropyNormalizedCandidates_of_isEpsilonSecretExtractor
    (H : QIT.Security.HashFamily F Z S) (E : Ensemble Z e) {ε : ℝ}
    (hε1 : ε ≤ 1) (hsecret : H.IsEpsilonSecretExtractor ε E) :
    log2 (H.outputLength : ℝ) ≤
      (QIT.Security.extractorOutputState H E).smoothConditionalMinEntropyNormalizedCandidates
        (Real.sqrt (2 * ε - ε ^ 2)) := by
  have hcand :
      State.SmoothConditionalMinEntropyCandidate (a := S)
        (QIT.Security.extractorOutputState H E) (Real.sqrt (2 * ε - ε ^ 2))
        (log2 (Fintype.card S : ℝ)) :=
    idealExtractorOutputState_smoothConditionalMinEntropyCandidate_of_isEpsilonSecretExtractor
      H
      E hε1 hsecret
  have hle :
      log2 (Fintype.card S : ℝ) ≤
        (QIT.Security.extractorOutputState H E).smoothConditionalMinEntropyNormalizedCandidates
          (Real.sqrt (2 * ε - ε ^ 2)) :=
    State.le_smoothConditionalMinEntropyNormalizedCandidates_of_candidate (a := S) hcand
  simpa [QIT.Security.HashFamily.outputLength_eq_card H] using hle

end HashFamily

/-- Every achievable extractor log-length satisfies the source-strength smooth
conditional min-entropy converse bound. -/
theorem extractableRandomnessLogValueSet_le_source_toSubnormalized_smoothConditionalMinEntropy
    (E : Ensemble Z e) {ε r : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hr : r ∈ ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε) :
    r ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy
        (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
          (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) := by
  rcases hr with ⟨ell, hach, rfl⟩
  rcases hach with
    ⟨S', instS, decS, nonS, hcard, F', instF, decF, nonF, H, hsecret⟩
  letI : Fintype S' := instS
  letI : DecidableEq S' := decS
  letI : Nonempty S' := nonS
  letI : Fintype F' := instF
  letI : DecidableEq F' := decF
  letI : Nonempty F' := nonF
  have hle :
      log2 (H.outputLength : ℝ) ≤
        E.cqState.toSubnormalized.smoothConditionalMinEntropy
          (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
          (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
            (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) :=
    H.log2_outputLength_le_source_toSubnormalized_smoothConditionalMinEntropy_of_isEpsilonSecretExtractor
      E hε0 hε1 hsecret
  simpa [QIT.Security.HashFamily.outputLength_eq_card H, hcard] using hle

/-- Every achievable log-output value lies below the extractable-randomness
supremum, in the source range where the converse gives boundedness. -/
theorem extractableRandomnessLogValueSet_member_le_extractableRandomnessLog
    (E : Ensemble Z e) {ε r : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hr : r ∈ ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε) :
    r ≤ extractableRandomnessLog.{uF, uZ, uS, ue} E ε := by
  rw [extractableRandomnessLog]
  refine le_csSup ?_ hr
  refine
    ⟨E.cqState.toSubnormalized.smoothConditionalMinEntropy
        (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
          (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)), ?_⟩
  intro x hx
  exact
    extractableRandomnessLogValueSet_le_source_toSubnormalized_smoothConditionalMinEntropy
      (E := E) hε0 hε1 hx

/-- Source-strength converse bound lifted from each extractor to the
extractable-randomness supremum, assuming the achievable-value set is nonempty. -/
theorem extractableRandomnessLog_le_source_toSubnormalized_smoothConditionalMinEntropy_of_valueSet_nonempty
    (E : Ensemble Z e) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hne : (ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε).Nonempty) :
    extractableRandomnessLog.{uF, uZ, uS, ue} E ε ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy
        (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
          (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) := by
  rw [extractableRandomnessLog]
  refine csSup_le hne ?_
  intro r hr
  exact
    extractableRandomnessLogValueSet_le_source_toSubnormalized_smoothConditionalMinEntropy
      (E := E) hε0 hε1 hr

/-- Source-strength converse bound lifted from each extractor to the
extractable-randomness supremum. -/
theorem extractableRandomnessLog_le_source_toSubnormalized_smoothConditionalMinEntropy
    (E : Ensemble Z e) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    extractableRandomnessLog.{uF, uZ, uS, ue} E ε ≤
      E.cqState.toSubnormalized.smoothConditionalMinEntropy
        (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
        (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
          (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) :=
  extractableRandomnessLog_le_source_toSubnormalized_smoothConditionalMinEntropy_of_valueSet_nonempty
    (E := E) hε0 hε1 (extractableRandomnessLogValueSet_nonempty_of_nonneg E hε0)

/-- Finite-alphabet lower endpoint associated to a real bit lower bound. -/
def roundedOutputLengthLower (l : Real) : Nat :=
  max 1 (Nat.floor (Real.rpow 2 l))

private theorem roundedOutputLengthLower_pos (l : Real) :
    0 < roundedOutputLengthLower l := by
  unfold roundedOutputLengthLower
  exact Nat.lt_of_lt_of_le (by norm_num : 0 < (1 : Nat))
    (le_max_left 1 (Nat.floor (Real.rpow 2 l)))

private theorem roundedOutputLengthLower_eq_one_of_neg {l : Real} (hl : l < 0) :
    roundedOutputLengthLower l = 1 := by
  unfold roundedOutputLengthLower
  have hpow_nonneg : 0 ≤ Real.rpow 2 l :=
    Real.rpow_nonneg (by norm_num : (0 : Real) ≤ 2) l
  have hpow_lt_one : Real.rpow 2 l < 1 := by
    have hpow_lt : Real.rpow 2 l < Real.rpow 2 (0 : Real) :=
      Real.rpow_lt_rpow_of_exponent_lt one_lt_two hl
    simpa [Real.rpow_zero] using hpow_lt
  have hfloor_lt : Nat.floor (Real.rpow 2 l) < 1 :=
    (Nat.floor_lt hpow_nonneg).mpr (by simpa using hpow_lt_one)
  have hfloor_eq0 : Nat.floor (Real.rpow 2 l) = 0 := Nat.lt_one_iff.mp hfloor_lt
  rw [hfloor_eq0]
  norm_num

private theorem roundedOutputLengthLower_log2_le_self_of_nonneg {l : Real} (hl : 0 ≤ l) :
    log2 (roundedOutputLengthLower l : Real) ≤ l := by
  unfold roundedOutputLengthLower
  have hpow_nonneg : 0 ≤ Real.rpow 2 l :=
    Real.rpow_nonneg (by norm_num : (0 : Real) ≤ 2) l
  have hpow_one_le : 1 ≤ Real.rpow 2 l :=
    Real.one_le_rpow (by norm_num : (1 : Real) ≤ 2) hl
  have hfloor_pos : 0 < Nat.floor (Real.rpow 2 l) :=
    (Nat.floor_pos).mpr hpow_one_le
  have hmax : max 1 (Nat.floor (Real.rpow 2 l)) = Nat.floor (Real.rpow 2 l) := by
    exact max_eq_right hfloor_pos
  rw [hmax]
  have hfloor_le : (Nat.floor (Real.rpow 2 l) : Real) ≤ Real.rpow 2 l :=
    Nat.floor_le hpow_nonneg
  have hfloor_pos_real : 0 < (Nat.floor (Real.rpow 2 l) : Real) := by
    exact_mod_cast hfloor_pos
  exact (log2_mono_of_pos hfloor_pos_real hfloor_le).trans_eq (log2_rpow_two l)

/-- Every achievable output length is bounded by the source-converse ceiling
bound when `0 ≤ ε < 1`. -/
private theorem extractorOutputLengthAchievable_le_extractableRandomnessLengthBound
    (E : Ensemble Z e) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {ell : Nat}
    (hach : ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε ell) :
    ell ≤
      Nat.ceil
        (Real.rpow 2
          (E.cqState.toSubnormalized.smoothConditionalMinEntropy
            (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
            (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
              (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)))) := by
  let M :=
    E.cqState.toSubnormalized.smoothConditionalMinEntropy
      (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
      (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
        (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1))
  have hlog :
      log2 (ell : ℝ) ≤ M :=
    extractableRandomnessLogValueSet_le_source_toSubnormalized_smoothConditionalMinEntropy
      (E := E) hε0 hε1 ⟨ell, hach, rfl⟩
  have hell_pos_nat : 0 < ell := extractorOutputLengthAchievable_pos hach
  have hell_pos_real : 0 < (ell : ℝ) := by exact_mod_cast hell_pos_nat
  have hpow :
      Real.rpow 2 (log2 (ell : ℝ)) ≤ Real.rpow 2 M :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlog
  have hreal : (ell : ℝ) ≤ Real.rpow 2 M := by
    rw [QIT.rpow_two_log2_pos hell_pos_real] at hpow
    exact hpow
  have hceil :
      (ell : ℝ) ≤
        (Nat.ceil
          (Real.rpow 2
            (E.cqState.toSubnormalized.smoothConditionalMinEntropy
              (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
              (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
                (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1))) : ℝ) : ℝ) := by
    simpa [M] using
      hreal.trans (Nat.le_ceil (Real.rpow 2 M))
  exact_mod_cast hceil

/-- Nat-valued version of Tomamichel's `ell^epsilon`: the maximum achievable
output length for `0 ≤ ε < 1`. -/
noncomputable def extractableRandomnessLength
    (E : Ensemble Z e) (ε : ℝ) (_hε0 : 0 ≤ ε) (_hε1 : ε < 1) : Nat := by
  classical
  exact
    Nat.findGreatest
      (fun ell => ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε ell)
      (Nat.ceil
        (Real.rpow 2
          (E.cqState.toSubnormalized.smoothConditionalMinEntropy
            (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
            (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
              (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one _hε0 _hε1)))))

/-- The Nat-valued extractable-randomness length is itself achievable. -/
theorem extractableRandomnessLength_achievable
    (E : Ensemble Z e) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε
      (extractableRandomnessLength.{uF, uZ, uS, ue} E ε hε0 hε1) := by
  classical
  unfold extractableRandomnessLength
  have hone :
      ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε 1 :=
    extractorOutputLengthAchievable_one_of_nonneg E hε0
  have hone_bound :
      1 ≤
        Nat.ceil
          (Real.rpow 2
            (E.cqState.toSubnormalized.smoothConditionalMinEntropy
              (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
              (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
                (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)))) :=
    extractorOutputLengthAchievable_le_extractableRandomnessLengthBound
      (E := E) hε0 hε1 hone
  exact Nat.findGreatest_spec hone_bound hone

/-- The Nat-valued extractable-randomness length dominates every achievable
output length. -/
theorem extractableRandomnessLength_greatest
    (E : Ensemble Z e) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {ell : Nat}
    (hach : ExtractorOutputLengthAchievable.{uF, uZ, uS, ue} E ε ell) :
    ell ≤ extractableRandomnessLength.{uF, uZ, uS, ue} E ε hε0 hε1 := by
  classical
  unfold extractableRandomnessLength
  exact
    Nat.le_findGreatest
      (extractorOutputLengthAchievable_le_extractableRandomnessLengthBound
        (E := E) hε0 hε1 hach)
      hach

/-- The Nat-valued extractable-randomness length is positive. -/
theorem extractableRandomnessLength_pos
    (E : Ensemble Z e) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    0 < extractableRandomnessLength.{uF, uZ, uS, ue} E ε hε0 hε1 :=
  extractorOutputLengthAchievable_pos
    (extractableRandomnessLength_achievable (E := E) hε0 hε1)

/-- The supremum-based formal endpoint equals the logarithm of the Nat-valued
maximum output length.  This closes the formal convention bridge for
Tomamichel's `log ell^epsilon`. -/
theorem extractableRandomnessLog_eq_log2_extractableRandomnessLength
    (E : Ensemble Z e) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    extractableRandomnessLog.{uF, uZ, uS, ue} E ε =
      log2
        (extractableRandomnessLength.{uF, uZ, uS, ue} E ε hε0 hε1 : ℝ) := by
  let M :=
    E.cqState.toSubnormalized.smoothConditionalMinEntropy
      (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
      (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
        (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1))
  have hne :
      (ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε).Nonempty :=
    extractableRandomnessLogValueSet_nonempty_of_nonneg E hε0
  have hbdd :
      BddAbove (ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε) := by
    refine ⟨M, ?_⟩
    intro r hr
    exact
      extractableRandomnessLogValueSet_le_source_toSubnormalized_smoothConditionalMinEntropy
        (E := E) hε0 hε1 hr
  have hmax_mem :
      log2
          (extractableRandomnessLength.{uF, uZ, uS, ue} E ε hε0 hε1 : ℝ) ∈
        ExtractableRandomnessLogValueSet.{uF, uZ, uS, ue} E ε :=
    ⟨extractableRandomnessLength.{uF, uZ, uS, ue} E ε hε0 hε1,
      extractableRandomnessLength_achievable (E := E) hε0 hε1, rfl⟩
  rw [extractableRandomnessLog]
  apply le_antisymm
  · refine csSup_le hne ?_
    intro r hr
    rcases hr with ⟨ell, hach, rfl⟩
    have hle_nat :
        ell ≤ extractableRandomnessLength.{uF, uZ, uS, ue} E ε hε0 hε1 :=
      extractableRandomnessLength_greatest (E := E) hε0 hε1 hach
    have hell_pos_nat : 0 < ell := extractorOutputLengthAchievable_pos hach
    have hell_pos_real : 0 < (ell : ℝ) := by exact_mod_cast hell_pos_nat
    exact log2_mono_of_pos hell_pos_real (by exact_mod_cast hle_nat)
  · exact le_csSup hbdd hmax_mem

omit [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S] [Nonempty S] in
/-- The full-function direct value-set witness gives a concrete lower bound on
the extractable-randomness supremum. -/
theorem finFullFunctionHashFamily_log2_le_extractableRandomnessLog_of_cqSmoothConditionalMinEntropyCandidate_log_le
    {ell : Nat} (hell : 0 < ell) (E : Ensemble Z e) {ε₁ ε₂ h : ℝ}
    (hε₂ : 0 < ε₂)
    (hεdir0 : 0 ≤ 2 * ε₁ + ε₂)
    (hεdir1 : 2 * ε₁ + ε₂ < 1)
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ε₁ h)
    (hlog : log2 (ell : ℝ) ≤ h - 2 * log2 (1 / ε₂)) :
    log2 (ell : ℝ) ≤
      extractableRandomnessLog.{uZ, uZ, 0, ue} E (2 * ε₁ + ε₂) := by
  have hmem :
      log2 (ell : ℝ) ∈
        ExtractableRandomnessLogValueSet.{uZ, uZ, 0, ue}
          E (2 * ε₁ + ε₂) :=
    finFullFunctionHashFamily_extractableRandomnessLogValue_mem_of_cqSmoothConditionalMinEntropyCandidate_log_le
      (Z := Z) hell E hε₂ hcq hlog
  exact
    extractableRandomnessLogValueSet_member_le_extractableRandomnessLog
      (E := E) hεdir0 hεdir1 hmem

omit [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S] [Nonempty S] in
/--
Rounded finite-alphabet version of Tomamichel's randomness-extraction theorem.

The source statement writes the lower bound in continuous-bit convention.  This
entrypoint exposes the strict finite-alphabet theorem obtained by replacing the
real lower endpoint `L` by `log₂ max(1, floor(2^L))`.

[Tomamichel2015FiniteResources, apps.tex:404-449]
-/
theorem extractableRandomnessLog_tomamichel_rounded_source_theorem_of_cqSmoothConditionalMinEntropyCandidate
    (E : Ensemble Z e) {ε δ h : Real}
    (hδ0 : 0 < δ) (hδε : δ < ε) (hε1 : ε < 1)
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ((ε - δ) / 2) h) :
    let l := h - 2 * log2 (1 / δ)
    And
      (log2 (roundedOutputLengthLower l : Real) ≤
        extractableRandomnessLog.{uZ, uZ, 0, ue} E ε)
      (extractableRandomnessLog.{uZ, uZ, 0, ue} E ε ≤
        E.cqState.toSubnormalized.smoothConditionalMinEntropy
          (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
          (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
            (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one
              (le_of_lt (hδ0.trans hδε)) hε1))) := by
  dsimp only
  let l : Real := h - 2 * log2 (1 / δ)
  have hε0 : 0 ≤ ε := le_of_lt (hδ0.trans hδε)
  have hsplit : 2 * ((ε - δ) / 2) + δ = ε := by ring
  have hdir0 : 0 ≤ 2 * ((ε - δ) / 2) + δ := by
    rw [hsplit]
    exact hε0
  have hdir1 : 2 * ((ε - δ) / 2) + δ < 1 := by
    rw [hsplit]
    exact hε1
  apply And.intro
  · change
      log2 (roundedOutputLengthLower l : Real) ≤
        extractableRandomnessLog.{uZ, uZ, 0, ue} E ε
    by_cases hlneg : l < 0
    · have hrounded : roundedOutputLengthLower l = 1 :=
        roundedOutputLengthLower_eq_one_of_neg hlneg
      have hmem :
          log2 (1 : Real) ∈
            ExtractableRandomnessLogValueSet.{uZ, uZ, 0, ue} E ε :=
        ⟨1, extractorOutputLengthAchievable_one_of_nonneg E hε0, by norm_num⟩
      have hzero_le :=
        extractableRandomnessLogValueSet_member_le_extractableRandomnessLog
          (E := E) hε0 hε1 hmem
      simpa [hrounded, log2] using hzero_le
    · have hlnonneg : 0 ≤ l := le_of_not_gt hlneg
      have hrounded_log : log2 (roundedOutputLengthLower l : Real) ≤ l :=
        roundedOutputLengthLower_log2_le_self_of_nonneg hlnonneg
      have hrounded_pos : 0 < roundedOutputLengthLower l :=
        roundedOutputLengthLower_pos l
      have hlower :=
        finFullFunctionHashFamily_log2_le_extractableRandomnessLog_of_cqSmoothConditionalMinEntropyCandidate_log_le
          (Z := Z) hrounded_pos E hδ0 hdir0 hdir1 hcq
          (by simpa [l] using hrounded_log)
      simpa [hsplit] using hlower
  · exact
      extractableRandomnessLog_le_source_toSubnormalized_smoothConditionalMinEntropy
        (E := E) hε0 hε1

omit [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S] [Nonempty S] in
/--
Rounded finite-alphabet normalized-cq wrapper for Tomamichel's
randomness-extraction theorem.

This public entrypoint uses the normalized finite cq ensemble surface available
in the library.  The supporting candidate theorem remains available separately
as `extractableRandomnessLog_tomamichel_rounded_source_theorem_of_cqSmoothConditionalMinEntropyCandidate`.

[Tomamichel2015FiniteResources, apps.tex:404-449]
-/
theorem extractableRandomnessLog_tomamichel_rounded_source_theorem
    (E : Ensemble Z e) {ε δ : Real}
    (hδ0 : 0 < δ) (hδε : δ < ε) (hε1 : ε < 1) :
    let l :=
      E.cqState.smoothConditionalMinEntropyNormalizedCandidates ((ε - δ) / 2) -
        2 * log2 (1 / δ)
    And
      (log2 (roundedOutputLengthLower l : Real) ≤
        extractableRandomnessLog.{uZ, uZ, 0, ue} E ε)
      (extractableRandomnessLog.{uZ, uZ, 0, ue} E ε ≤
        E.cqState.toSubnormalized.smoothConditionalMinEntropy
          (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
          (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
            (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one
              (le_of_lt (hδ0.trans hδε)) hε1))) := by
  have hεsmooth_nonneg : 0 ≤ (ε - δ) / 2 := by
    linarith
  exact
    extractableRandomnessLog_tomamichel_rounded_source_theorem_of_cqSmoothConditionalMinEntropyCandidate
      E hδ0 hδε hε1
      (E.CqSmoothConditionalMinEntropyCandidate_of_smoothConditionalMinEntropyNormalizedCandidates
        hεsmooth_nonneg)

/--
Registered source-strength randomness-extraction endpoint.

This packages the two source-facing formal endpoints used for
Tomamichel's randomness-extraction theorem: the constructive smooth direct
achievability witness for a concrete full-function hash output length, the
corresponding concrete lower bound on extractable randomness as a supremum, the
source-strength converse bound for extractable randomness as a supremum, and
the underlying per-extractor converse endpoint.

[Tomamichel2015FiniteResources, apps.tex:404-449]
-/
theorem extractableRandomnessLog_source_bounds_of_cqSmoothConditionalMinEntropyCandidate
    [Nonempty F]
    {ell : Nat} (hell : 0 < ell) (E : Ensemble Z e)
    (H : QIT.Security.HashFamily F Z S) {ε ε₁ ε₂ h : ℝ}
    (hε₂ : 0 < ε₂)
    (hεdir0 : 0 ≤ 2 * ε₁ + ε₂)
    (hεdir1 : 2 * ε₁ + ε₂ < 1)
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ε₁ h)
    (hlog : log2 (ell : ℝ) ≤ h - 2 * log2 (1 / ε₂))
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    log2 (ell : ℝ) ∈
        ExtractableRandomnessLogValueSet.{uZ, uZ, 0, ue} E (2 * ε₁ + ε₂) ∧
      log2 (ell : ℝ) ≤
        extractableRandomnessLog.{uZ, uZ, 0, ue} E (2 * ε₁ + ε₂) ∧
      extractableRandomnessLog.{uZ, uZ, 0, ue} E ε ≤
        E.cqState.toSubnormalized.smoothConditionalMinEntropy
          (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
          (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
            (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1)) ∧
      (H.IsEpsilonSecretExtractor ε E →
        log2 (H.outputLength : ℝ) ≤
          E.cqState.toSubnormalized.smoothConditionalMinEntropy
            (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
            (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
              (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one hε0 hε1))) := by
  constructor
  · exact
      finFullFunctionHashFamily_extractableRandomnessLogValue_mem_of_cqSmoothConditionalMinEntropyCandidate_log_le
        (Z := Z) hell E hε₂ hcq hlog
  · constructor
    · exact
        finFullFunctionHashFamily_log2_le_extractableRandomnessLog_of_cqSmoothConditionalMinEntropyCandidate_log_le
          (Z := Z) hell E hε₂ hεdir0 hεdir1 hcq hlog
    · constructor
      · exact
          extractableRandomnessLog_le_source_toSubnormalized_smoothConditionalMinEntropy
            (E := E) hε0 hε1
      · intro hsecret
        exact
          H.log2_outputLength_le_source_toSubnormalized_smoothConditionalMinEntropy_of_isEpsilonSecretExtractor
            E hε0 hε1 hsecret

/--
Tomamichel-parameter source-strength randomness-extraction endpoint.

This is the registered endpoint with the source theorem's error split
`ε' = (ε - δ) / 2` and direct error `2 * ε' + δ = ε` already discharged.
It keeps the direct side as a concrete output-length witness and corresponding
lower bound on the `extractableRandomnessLog` supremum; the separate
Nat-valued maximum-attainment convention for `ell^epsilon` is supplied by
`extractableRandomnessLog_eq_log2_extractableRandomnessLength`.

[Tomamichel2015FiniteResources, apps.tex:404-449]
-/
theorem extractableRandomnessLog_tomamichel_source_bounds_of_cqSmoothConditionalMinEntropyCandidate
    [Nonempty F]
    {ell : Nat} (hell : 0 < ell) (E : Ensemble Z e)
    (H : QIT.Security.HashFamily F Z S) {ε δ h : ℝ}
    (hδ0 : 0 < δ) (hδε : δ < ε) (hε1 : ε < 1)
    (hcq : E.CqSmoothConditionalMinEntropyCandidate ((ε - δ) / 2) h)
    (hlog : log2 (ell : ℝ) ≤ h - 2 * log2 (1 / δ)) :
    log2 (ell : ℝ) ∈
        ExtractableRandomnessLogValueSet.{uZ, uZ, 0, ue} E ε ∧
      log2 (ell : ℝ) ≤
        extractableRandomnessLog.{uZ, uZ, 0, ue} E ε ∧
      extractableRandomnessLog.{uZ, uZ, 0, ue} E ε ≤
        E.cqState.toSubnormalized.smoothConditionalMinEntropy
          (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
          (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
            (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one
              (le_of_lt (hδ0.trans hδε)) hε1)) ∧
      (H.IsEpsilonSecretExtractor ε E →
        log2 (H.outputLength : ℝ) ≤
          E.cqState.toSubnormalized.smoothConditionalMinEntropy
            (Real.sqrt (2 * ε - ε ^ 2)) (Real.sqrt_nonneg _)
            (E.cqState.epsilon_lt_sqrt_toSubnormalized_trace
              (sqrt_two_mul_sub_sq_lt_one_of_nonneg_lt_one
                (le_of_lt (hδ0.trans hδε)) hε1))) := by
  have hε0 : 0 ≤ ε := le_of_lt (hδ0.trans hδε)
  have hsplit : 2 * ((ε - δ) / 2) + δ = ε := by ring
  have hεdir0 : 0 ≤ 2 * ((ε - δ) / 2) + δ := by
    rw [hsplit]
    exact hε0
  have hεdir1 : 2 * ((ε - δ) / 2) + δ < 1 := by
    rw [hsplit]
    exact hε1
  simpa [hsplit] using
    extractableRandomnessLog_source_bounds_of_cqSmoothConditionalMinEntropyCandidate
      (F := F) (Z := Z) (S := S) (e := e)
      hell E H hδ0 hεdir0 hεdir1 hcq hlog hε0 hε1

end Security

end

end QIT
