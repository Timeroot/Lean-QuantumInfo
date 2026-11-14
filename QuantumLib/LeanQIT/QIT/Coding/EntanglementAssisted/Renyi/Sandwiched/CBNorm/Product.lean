/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Collapse.RightIdentity
public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.ComplementBridge

/-!
# Product bounds for the positive `alpha -> alpha` and CB `1 -> alpha` norms

This module formalizes the registered multiplicativity claim
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2152-2240]: its
product-input lower bound appears in source lines 2174-2190, the
identity-extension/complement upper bound in source lines 2208-2238, and the
final CB `1 -> alpha` multiplicativity conclusion at source line 2240.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z

noncomputable section

namespace MatrixMap

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]
variable [Fintype d] [DecidableEq d]

private theorem psdSchattenPNorm_le_trace_re_of_one_le
    {A : CMatrix a} (hA : A.PosSemidef) {p : SchattenOrder}
    (hp : 1 ≤ (p : ℝ)) :
    psdSchattenPNorm A hA p ≤ A.trace.re := by
  classical
  let p : Real := (p : Real)
  let S : ℝ := ∑ i, hA.isHermitian.eigenvalues i
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i
  have htrace : A.trace.re = S := by
    have h := congrArg Complex.re hA.isHermitian.trace_eq_sum_eigenvalues
    simpa [S] using h
  have hpoint_le_sum : ∀ i, hA.isHermitian.eigenvalues i ≤ S := by
    intro i
    calc
      hA.isHermitian.eigenvalues i
          ≤ hA.isHermitian.eigenvalues i +
              ∑ j ∈ Finset.univ.erase i, hA.isHermitian.eigenvalues j :=
            le_add_of_nonneg_right
              (Finset.sum_nonneg fun j _ => hA.eigenvalues_nonneg j)
      _ = S := by
            rw [add_comm]
            exact Finset.sum_erase_add (s := Finset.univ)
              (f := fun j => hA.isHermitian.eigenvalues j) (Finset.mem_univ i)
  by_cases hS_zero : S = 0
  · have heig_zero : ∀ i, hA.isHermitian.eigenvalues i = 0 := by
      intro i
      exact le_antisymm (by simpa [hS_zero] using hpoint_le_sum i)
        (hA.eigenvalues_nonneg i)
    have hpower_zero :
        ∑ i, hA.isHermitian.eigenvalues i ^ p = 0 := by
      simp [heig_zero, Real.zero_rpow (ne_of_gt hp_pos)]
    rw [psdSchattenPNorm, Internal.psdSchattenExpression,
      psdTracePower_eq_sum_eigenvalues_rpow, hpower_zero, htrace, hS_zero]
    exact le_of_eq (by
      simpa using (Real.zero_rpow (one_div_ne_zero (ne_of_gt hp_pos)) :
        (0 : ℝ) ^ (1 / p) = 0))
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_zero)
    have hpower_le :
        ∑ i, hA.isHermitian.eigenvalues i ^ p ≤ S ^ p := by
      calc
        ∑ i, hA.isHermitian.eigenvalues i ^ p
            ≤ ∑ i, hA.isHermitian.eigenvalues i * S ^ (p - 1) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have hi_nonneg : 0 ≤ hA.isHermitian.eigenvalues i :=
                hA.eigenvalues_nonneg i
              by_cases hi_zero : hA.isHermitian.eigenvalues i = 0
              · simp [hi_zero, Real.zero_rpow (ne_of_gt hp_pos)]
              · have hi_pos : 0 < hA.isHermitian.eigenvalues i :=
                  lt_of_le_of_ne hi_nonneg (Ne.symm hi_zero)
                have hpow_le :
                    hA.isHermitian.eigenvalues i ^ (p - 1) ≤ S ^ (p - 1) := by
                  exact Real.rpow_le_rpow hi_nonneg (hpoint_le_sum i)
                    (sub_nonneg.mpr hp)
                calc
                  hA.isHermitian.eigenvalues i ^ p =
                      hA.isHermitian.eigenvalues i ^ (1 + (p - 1)) := by
                        congr 1
                        ring
                  _ = hA.isHermitian.eigenvalues i *
                      hA.isHermitian.eigenvalues i ^ (p - 1) := by
                        rw [Real.rpow_add hi_pos 1 (p - 1)]
                        rw [Real.rpow_one]
                  _ ≤ hA.isHermitian.eigenvalues i * S ^ (p - 1) :=
                        mul_le_mul_of_nonneg_left hpow_le hi_nonneg
        _ = S * S ^ (p - 1) := by
              rw [← Finset.sum_mul]
        _ = S ^ (1 + (p - 1)) := by
              rw [Real.rpow_add hS_pos 1 (p - 1)]
              rw [Real.rpow_one]
        _ = S ^ p := by
              congr 1
              ring
    rw [psdSchattenPNorm, Internal.psdSchattenExpression,
      psdTracePower_eq_sum_eigenvalues_rpow, htrace]
    have hleft_nonneg :
        0 ≤ ∑ i, hA.isHermitian.eigenvalues i ^ p := by
      exact Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (hA.eigenvalues_nonneg i) p
    calc
      (∑ i, hA.isHermitian.eigenvalues i ^ p) ^ (1 / p)
          ≤ (S ^ p) ^ (1 / p) :=
            Real.rpow_le_rpow hleft_nonneg hpower_le
              (one_div_nonneg.mpr (le_of_lt hp_pos))
      _ = S := by
            rw [← Real.rpow_mul hS_nonneg]
            have hp_ne : p ≠ 0 := ne_of_gt hp_pos
            rw [show p * (1 / p) = (1 : ℝ) by field_simp [hp_ne]]
            rw [Real.rpow_one]

private theorem psdTracePower_le_one_of_psdSchattenPNorm_le_one
    {A : CMatrix a} (hA : A.PosSemidef) {p : SchattenOrder}
    (hnorm : psdSchattenPNorm A hA p ≤ 1) :
    psdTracePower A hA (p : ℝ) ≤ 1 := by
  have hp : 0 < (p : ℝ) := p.property
  have htrace_nonneg : 0 ≤ psdTracePower A hA p :=
    psdTracePower_nonneg A hA p
  have hnorm_nonneg : 0 ≤ psdSchattenPNorm A hA p :=
    psdSchattenPNorm_nonneg A hA p
  have hpow :
      (psdSchattenPNorm A hA p) ^ (p : Real) ≤
        (1 : ℝ) ^ (p : Real) :=
    Real.rpow_le_rpow hnorm_nonneg hnorm (le_of_lt hp)
  rw [psdSchattenPNorm, Internal.psdSchattenExpression] at hpow
  change (Real.rpow (psdTracePower A hA p) (1 / (p : Real))) ^
      (p : Real) ≤ 1 ^ (p : Real) at hpow
  calc
    psdTracePower A hA p =
        (Real.rpow (psdTracePower A hA p) (1 / (p : Real))) ^
          (p : Real) := by
          simpa [one_div] using
            (Real.rpow_inv_rpow htrace_nonneg (ne_of_gt hp)).symm
    _ ≤ 1 ^ (p : Real) := hpow
    _ = 1 := Real.one_rpow (p : Real)

omit [DecidableEq a] in
private theorem trace_re_le_of_le {X Y : CMatrix a} (hXY : X ≤ Y) :
    X.trace.re ≤ Y.trace.re := by
  have hdiff : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
  have htrace_complex := Matrix.PosSemidef.trace_nonneg hdiff
  have htrace_re : 0 ≤ (Y.trace - X.trace).re := by
    have hle_re : X.trace.re ≤ Y.trace.re := by
      have h :
          X.trace.re ≤ Y.trace.re ∧ X.trace.im = Y.trace.im := by
        simpa [Matrix.trace_sub, Complex.le_def, Complex.sub_re, Complex.sub_im]
          using htrace_complex
      exact h.1
    simpa [Complex.sub_re] using sub_nonneg.mpr hle_re
  rw [Complex.sub_re] at htrace_re
  linarith

private theorem isCompletelyPositive_monotone
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {X Y : CMatrix a} (hXY : X ≤ Y) :
    Phi X ≤ Phi Y := by
  rw [Matrix.le_iff]
  have hdiff : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
  have hmap :
      (Phi (Y - X)).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi (Y - X) hdiff
  simpa [map_sub] using hmap

private theorem alphaToAlphaPositiveValue_le_trace_map_one
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha)
    (Z : AlphaToAlphaPositiveDomain a (SchattenOrder.ofOneLt halpha)) :
    alphaToAlphaPositiveValue Phi hPhi Z ≤ (Phi (1 : CMatrix a)).trace.re := by
  let normZ : ℝ :=
    psdSchattenPNorm Z.matrix Z.pos (SchattenOrder.ofOneLt halpha)
  let X : CMatrix a := (normZ⁻¹ : ℝ) • Z.matrix
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hnormZ_pos : 0 < normZ := by
    simpa [normZ] using Z.norm_pos
  have hnormZ_nonneg : 0 ≤ normZ := le_of_lt hnormZ_pos
  have hinv_nonneg : 0 ≤ normZ⁻¹ := inv_nonneg.mpr hnormZ_nonneg
  have hX : X.PosSemidef :=
    Matrix.PosSemidef.smul Z.pos hinv_nonneg
  have hPhiX : (Phi X).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi X hX
  have hPhiZ : (Phi Z.matrix).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Z.matrix Z.pos
  have hscaledPhiZ : ((normZ⁻¹ : ℝ) • Phi Z.matrix).PosSemidef :=
    Matrix.PosSemidef.smul hPhiZ hinv_nonneg
  have hPhiX_eq : Phi X = (normZ⁻¹ : ℝ) • Phi Z.matrix := by
    simp [X]
  have hvalue_eq :
      alphaToAlphaPositiveValue Phi hPhi Z =
        psdSchattenPNorm (Phi X) hPhiX (SchattenOrder.ofOneLt halpha) := by
    unfold alphaToAlphaPositiveValue
    calc
      psdSchattenPNorm (Phi Z.matrix) hPhiZ (SchattenOrder.ofOneLt halpha) /
          psdSchattenPNorm Z.matrix Z.pos (SchattenOrder.ofOneLt halpha) =
        normZ⁻¹ * psdSchattenPNorm (Phi Z.matrix) hPhiZ
          (SchattenOrder.ofOneLt halpha) := by
          simp [normZ, div_eq_mul_inv, mul_comm]
      _ =
        psdSchattenPNorm ((normZ⁻¹ : ℝ) • Phi Z.matrix)
          hscaledPhiZ (SchattenOrder.ofOneLt halpha) := by
          rw [psdSchattenPNorm_real_smul hPhiZ hinv_nonneg
            (SchattenOrder.ofOneLt halpha)]
      _ =
        psdSchattenPNorm (Phi X) hPhiX (SchattenOrder.ofOneLt halpha) := by
          exact (psdSchattenPNorm_congr hPhiX_eq hPhiX hscaledPhiZ
            (SchattenOrder.ofOneLt halpha)).symm
  have hnormX_le_one :
      psdSchattenPNorm X hX (SchattenOrder.ofOneLt halpha) ≤ 1 := by
    calc
      psdSchattenPNorm X hX (SchattenOrder.ofOneLt halpha) =
          normZ⁻¹ * psdSchattenPNorm Z.matrix Z.pos
            (SchattenOrder.ofOneLt halpha) := by
          simpa [X, normZ] using
            psdSchattenPNorm_real_smul Z.pos hinv_nonneg
              (SchattenOrder.ofOneLt halpha)
      _ = normZ⁻¹ * normZ := by
          rfl
      _ ≤ 1 := by
          rw [inv_mul_cancel₀ (ne_of_gt hnormZ_pos)]
  have htracePowerX_le_one :
      psdTracePower X hX alpha ≤ 1 :=
    psdTracePower_le_one_of_psdSchattenPNorm_le_one hX hnormX_le_one
  have hX_le_one : X ≤ (1 : CMatrix a) :=
    posSemidef_le_one_of_psdTracePower_le_one hX halpha_pos htracePowerX_le_one
  have hPhiX_le_one :
      Phi X ≤ Phi (1 : CMatrix a) :=
    isCompletelyPositive_monotone Phi hPhi hX_le_one
  have hPhiOne : (Phi (1 : CMatrix a)).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi (1 : CMatrix a)
      Matrix.PosSemidef.one
  calc
    alphaToAlphaPositiveValue Phi hPhi Z =
        psdSchattenPNorm (Phi X) hPhiX
          (SchattenOrder.ofOneLt halpha) := hvalue_eq
    _ ≤ (Phi X).trace.re :=
        psdSchattenPNorm_le_trace_re_of_one_le hPhiX (le_of_lt halpha)
    _ ≤ (Phi (1 : CMatrix a)).trace.re :=
        trace_re_le_of_le hPhiX_le_one

private theorem alphaToAlphaPositiveValueSet_bddAbove_of_one_lt
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (alphaToAlphaPositiveValueSet Phi hPhi
      (SchattenOrder.ofOneLt halpha)) := by
  refine ⟨(Phi (1 : CMatrix a)).trace.re, ?_⟩
  rintro x ⟨Z, rfl⟩
  exact alphaToAlphaPositiveValue_le_trace_map_one Phi hPhi halpha Z

theorem alphaToAlphaPositiveValue_le_alphaToAlphaNorm_of_one_lt
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha)
    (Z : AlphaToAlphaPositiveDomain a (SchattenOrder.ofOneLt halpha)) :
    alphaToAlphaPositiveValue Phi hPhi Z ≤
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
  unfold alphaToAlphaNorm
  exact le_csSup (alphaToAlphaPositiveValueSet_bddAbove_of_one_lt Phi hPhi halpha)
    ⟨Z, rfl⟩

private theorem alphaToAlphaNorm_nonneg_of_one_lt
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (_halpha : 1 < alpha) :
    0 ≤ alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt _halpha) := by
  unfold alphaToAlphaNorm
  exact Real.sSup_nonneg (by
    rintro x ⟨Z, rfl⟩
    exact alphaToAlphaPositiveValue_nonneg Phi hPhi Z)

/-- Trace-normalized candidates are bounded by the positive-input induced
`alpha -> alpha` norm. -/
theorem alphaToAlphaTraceValue_le_alphaToAlphaNorm_of_one_lt
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha)
    (Y : AlphaToAlphaTraceDomain a (SchattenOrder.ofOneLt halpha)) :
    alphaToAlphaTraceValue Phi hPhi Y ≤
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
  let Z : CMatrix a := CFC.rpow Y.matrix (1 / alpha)
  let hZ : Z.PosSemidef :=
    cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / alpha) Y.pos
  let normZ : ℝ := psdSchattenPNorm Z hZ (SchattenOrder.ofOneLt halpha)
  have hnormZ_nonneg : 0 ≤ normZ :=
    psdSchattenPNorm_nonneg Z hZ (SchattenOrder.ofOneLt halpha)
  by_cases hnormZ_zero : normZ = 0
  · rw [alphaToAlphaTraceValue_eq_zero_of_rpow_norm_eq_zero Phi hPhi halpha Y
      (by simpa [Z, hZ, normZ] using hnormZ_zero)]
    exact alphaToAlphaNorm_nonneg_of_one_lt Phi hPhi halpha
  · have hnormZ_pos : 0 < normZ :=
      lt_of_le_of_ne hnormZ_nonneg (Ne.symm hnormZ_zero)
    let X : AlphaToAlphaPositiveDomain a (SchattenOrder.ofOneLt halpha) :=
      { matrix := Z, pos := hZ, norm_pos := hnormZ_pos }
    exact (alphaToAlphaTraceValue_le_positiveValue_of_rpow_norm_pos Phi hPhi
      halpha Y (by simpa [Z, hZ, normZ] using hnormZ_pos)).trans
        (alphaToAlphaPositiveValue_le_alphaToAlphaNorm_of_one_lt Phi hPhi halpha X)

/-- Original CB `1 -> alpha` candidates are bounded by the CB norm. -/
theorem cbOneToAlphaOriginalValue_le_cbOneToAlphaNorm_of_one_lt
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha) (Y : CBOneToAlphaOriginalDomain a) :
    cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofOneLt halpha) ≤
      cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
  have hvalue :
      cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofOneLt halpha) =
        alphaToAlphaTraceValue
          (MatrixMap.cpComplement Phi hPhi)
          (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
          (Y.toTransposeTraceDomain (alpha := alpha)
            (lt_trans zero_lt_one halpha)) := by
    simpa [SchattenOrder.ofOneLt, SchattenOrder.ofPositive] using
      (cbOneToAlphaOriginalValue_eq_cpComplement_alphaToAlphaTraceValue_transpose
        Phi hPhi (lt_trans zero_lt_one halpha) Y)
  rw [hvalue]
  rw [cbOneToAlphaNorm_eq_cpComplement_alphaToAlphaNorm Phi hPhi halpha]
  exact alphaToAlphaTraceValue_le_alphaToAlphaNorm_of_one_lt
    (MatrixMap.cpComplement Phi hPhi)
    (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
    halpha
    (Y.toTransposeTraceDomain (alpha := alpha) (lt_trans zero_lt_one halpha))

private theorem alphaToAlphaPositiveDomain_nonempty [Nonempty a]
    (alpha : SchattenOrder) :
    Nonempty (AlphaToAlphaPositiveDomain a alpha) :=
  ⟨{ matrix := 1,
      pos := Matrix.PosSemidef.one,
      norm_pos := by
        simpa using
          (psdSchattenPNorm_pos_of_posDef
            (a := a) (A := (1 : CMatrix a)) Matrix.PosDef.one
            (p := alpha)) }⟩

private theorem alphaToAlphaPositiveValue_comp_le_mul
    (Psi : MatrixMap b c) (hPsi : MatrixMap.IsCompletelyPositive Psi)
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha)
    (Z : AlphaToAlphaPositiveDomain a (SchattenOrder.ofOneLt halpha)) :
    alphaToAlphaPositiveValue (Psi.comp Phi)
        (MatrixMap.isCompletelyPositive_comp Psi Phi hPsi hPhi) Z ≤
      alphaToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) *
        alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
  let W : CMatrix b := Phi Z.matrix
  let hW : W.PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Z.matrix Z.pos
  let normW : ℝ := psdSchattenPNorm W hW (SchattenOrder.ofOneLt halpha)
  have hnormW_nonneg : 0 ≤ normW := by
    exact psdSchattenPNorm_nonneg W hW (SchattenOrder.ofOneLt halpha)
  by_cases hnormW_zero : normW = 0
  · have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
    let hCompZ : (Psi (Phi Z.matrix)).PosSemidef :=
      MatrixMap.isCompletelyPositive_mapsPositive (Psi.comp Phi)
        (MatrixMap.isCompletelyPositive_comp Psi Phi hPsi hPhi)
        Z.matrix Z.pos
    have hWzero : W = 0 := by
      by_contra hne
      have hpos : 0 < normW :=
        psdSchattenPNorm_pos_of_ne_zero W hW hne
      exact (ne_of_gt hpos) hnormW_zero
    have hPsiWzero : Psi W = 0 := by
      rw [hWzero]
      exact map_zero Psi
    have hcomp_zero :
        alphaToAlphaPositiveValue (Psi.comp Phi)
            (MatrixMap.isCompletelyPositive_comp Psi Phi hPsi hPhi) Z = 0 := by
      unfold alphaToAlphaPositiveValue
      change psdSchattenPNorm (Psi (Phi Z.matrix)) hCompZ
          (SchattenOrder.ofOneLt halpha) /
          psdSchattenPNorm Z.matrix Z.pos (SchattenOrder.ofOneLt halpha) = 0
      have hPsiPhi_zero : Psi (Phi Z.matrix) = 0 := by
        simpa [W] using hPsiWzero
      have hzero_norm :
          psdSchattenPNorm (Psi (Phi Z.matrix)) hCompZ
            (SchattenOrder.ofOneLt halpha) = 0 := by
        calc
          psdSchattenPNorm (Psi (Phi Z.matrix)) hCompZ
              (SchattenOrder.ofOneLt halpha) =
            psdSchattenPNorm (0 : CMatrix c) Matrix.PosSemidef.zero
              (SchattenOrder.ofOneLt halpha) :=
              psdSchattenPNorm_congr hPsiPhi_zero hCompZ
                Matrix.PosSemidef.zero (SchattenOrder.ofOneLt halpha)
          _ = 0 := psdSchattenPNorm_zero (SchattenOrder.ofOneLt halpha)
      rw [hzero_norm, zero_div]
    rw [hcomp_zero]
    exact mul_nonneg
      (alphaToAlphaNorm_nonneg_of_one_lt Psi hPsi halpha)
      (alphaToAlphaNorm_nonneg_of_one_lt Phi hPhi halpha)
  · have hnormW_pos : 0 < normW :=
      lt_of_le_of_ne hnormW_nonneg (Ne.symm hnormW_zero)
    let Wdom : AlphaToAlphaPositiveDomain b (SchattenOrder.ofOneLt halpha) :=
      { matrix := W, pos := hW, norm_pos := hnormW_pos }
    have hcomp_eq :
        alphaToAlphaPositiveValue (Psi.comp Phi)
            (MatrixMap.isCompletelyPositive_comp Psi Phi hPsi hPhi) Z =
          alphaToAlphaPositiveValue Psi hPsi Wdom *
            alphaToAlphaPositiveValue Phi hPhi Z := by
      unfold alphaToAlphaPositiveValue
      change
        psdSchattenPNorm (Psi W) _ (SchattenOrder.ofOneLt halpha) /
            psdSchattenPNorm Z.matrix Z.pos (SchattenOrder.ofOneLt halpha) =
          (psdSchattenPNorm (Psi W) _ (SchattenOrder.ofOneLt halpha) /
              psdSchattenPNorm W hW (SchattenOrder.ofOneLt halpha)) *
            (psdSchattenPNorm W hW (SchattenOrder.ofOneLt halpha) /
              psdSchattenPNorm Z.matrix Z.pos (SchattenOrder.ofOneLt halpha))
      field_simp [normW, ne_of_gt hnormW_pos, ne_of_gt Z.norm_pos]
    rw [hcomp_eq]
    have hPsiVal_le :
        alphaToAlphaPositiveValue Psi hPsi Wdom ≤
          alphaToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) :=
      alphaToAlphaPositiveValue_le_alphaToAlphaNorm_of_one_lt Psi hPsi halpha Wdom
    have hPhiVal_le :
        alphaToAlphaPositiveValue Phi hPhi Z ≤
          alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) :=
      alphaToAlphaPositiveValue_le_alphaToAlphaNorm_of_one_lt Phi hPhi halpha Z
    exact mul_le_mul hPsiVal_le hPhiVal_le
      (alphaToAlphaPositiveValue_nonneg Phi hPhi Z)
      (alphaToAlphaNorm_nonneg_of_one_lt Psi hPsi halpha)

/-- The positive induced `alpha -> alpha` norm is submultiplicative under
composition for completely positive maps. -/
theorem alphaToAlphaNorm_comp_le_mul
    (Psi : MatrixMap b c) (hPsi : MatrixMap.IsCompletelyPositive Psi)
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alphaToAlphaNorm (Psi.comp Phi)
        (MatrixMap.isCompletelyPositive_comp Psi Phi hPsi hPhi)
        (SchattenOrder.ofOneLt halpha) ≤
      alphaToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) *
        alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
  unfold alphaToAlphaNorm
  by_cases hne :
      (alphaToAlphaPositiveValueSet (Psi.comp Phi)
        (MatrixMap.isCompletelyPositive_comp Psi Phi hPsi hPhi)
        (SchattenOrder.ofOneLt halpha)).Nonempty
  · refine csSup_le hne ?_
    rintro x ⟨Z, rfl⟩
    exact alphaToAlphaPositiveValue_comp_le_mul Psi hPsi Phi hPhi halpha Z
  · have hempty :
        alphaToAlphaPositiveValueSet (Psi.comp Phi)
          (MatrixMap.isCompletelyPositive_comp Psi Phi hPsi hPhi)
          (SchattenOrder.ofOneLt halpha) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Real.sSup_empty]
    exact mul_nonneg
      (alphaToAlphaNorm_nonneg_of_one_lt Psi hPsi halpha)
      (alphaToAlphaNorm_nonneg_of_one_lt Phi hPhi halpha)

private theorem alphaToAlphaNorm_congr_map
    {Phi Psi : MatrixMap a b}
    (hmap : Phi = Psi)
    (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (hPsi : MatrixMap.IsCompletelyPositive Psi)
    (alpha : SchattenOrder) :
    alphaToAlphaNorm Phi hPhi alpha =
      alphaToAlphaNorm Psi hPsi alpha := by
  subst hmap
  rfl

private theorem cbOneToAlphaNorm_congr_map
    {Phi Psi : MatrixMap a b}
    (hmap : Phi = Psi)
    (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (hPsi : MatrixMap.IsCompletelyPositive Psi)
    (alpha : SchattenOrder) :
    cbOneToAlphaNorm Phi hPhi alpha =
      cbOneToAlphaNorm Psi hPsi alpha := by
  subst hmap
  rfl

private theorem kron_eq_comp_identity_extensions
    (Phi : MatrixMap a b) (Psi : MatrixMap c d) :
    MatrixMap.kron Phi Psi =
      (MatrixMap.kron Phi (Channel.idChannel d).map).comp
        (MatrixMap.kron (Channel.idChannel a).map Psi) := by
  ext X bd bd'
  have hmat :
      MatrixMap.kron Phi Psi X =
        MatrixMap.kron Phi (Channel.idChannel d).map
          (MatrixMap.kron (Channel.idChannel a).map Psi X) := by
    calc
      MatrixMap.kron Phi Psi X =
        MatrixMap.kron
          (Phi.comp (Channel.idChannel a).map)
          ((Channel.idChannel d).map.comp Psi) X := by
          have hid_left : Phi.comp (Channel.idChannel a).map = Phi := by
            ext Y i j
            simp [LinearMap.comp_apply, Channel.idChannel_map]
          have hid_right : (Channel.idChannel d).map.comp Psi = Psi := by
            ext Y i j
            simp [LinearMap.comp_apply, Channel.idChannel_map]
          rw [hid_left, hid_right]
      _ =
        MatrixMap.kron Phi (Channel.idChannel d).map
          (MatrixMap.kron (Channel.idChannel a).map Psi X) := by
          exact (kron_comp_apply_general
            (Φ₁ := Phi)
            (Ψ₁ := (Channel.idChannel d).map)
            (Φ₂ := (Channel.idChannel a).map)
            (Ψ₂ := Psi)
            X).symm
  exact congrFun (congrFun hmat bd) bd'

/-- Source product upper bound for the positive induced `alpha -> alpha` norm:
the product map factors through the two identity-reference extensions, and the
collapse lemmas identify their norms with the one-system norms. -/
theorem alphaToAlphaNorm_kron_le_mul
    [Nonempty a] [Nonempty d]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Psi : MatrixMap c d) (hPsi : MatrixMap.IsCompletelyPositive Psi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alphaToAlphaNorm (MatrixMap.kron Phi Psi)
        (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
        (SchattenOrder.ofOneLt halpha) ≤
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) *
        alphaToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) := by
  let K₁ : MatrixMap (Prod a c) (Prod a d) :=
    MatrixMap.kron (Channel.idChannel a).map Psi
  let K₂ : MatrixMap (Prod a d) (Prod b d) :=
    MatrixMap.kron Phi (Channel.idChannel d).map
  let hK₁ : MatrixMap.IsCompletelyPositive K₁ :=
    MatrixMap.isCompletelyPositive_kron
      (Channel.idChannel a).map Psi (Channel.idChannel a).completelyPositive hPsi
  let hK₂ : MatrixMap.IsCompletelyPositive K₂ :=
    MatrixMap.isCompletelyPositive_kron
      Phi (Channel.idChannel d).map hPhi (Channel.idChannel d).completelyPositive
  have hmap :
      MatrixMap.kron Phi Psi = K₂.comp K₁ := by
    simpa [K₁, K₂] using kron_eq_comp_identity_extensions Phi Psi
  have hnorm_eq :
      alphaToAlphaNorm (MatrixMap.kron Phi Psi)
          (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
          (SchattenOrder.ofOneLt halpha) =
        alphaToAlphaNorm (K₂.comp K₁)
          (MatrixMap.isCompletelyPositive_comp K₂ K₁ hK₂ hK₁)
          (SchattenOrder.ofOneLt halpha) := by
    exact alphaToAlphaNorm_congr_map hmap
      (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
      (MatrixMap.isCompletelyPositive_comp K₂ K₁ hK₂ hK₁)
      (SchattenOrder.ofOneLt halpha)
  calc
    alphaToAlphaNorm (MatrixMap.kron Phi Psi)
        (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
        (SchattenOrder.ofOneLt halpha) =
      alphaToAlphaNorm (K₂.comp K₁)
        (MatrixMap.isCompletelyPositive_comp K₂ K₁ hK₂ hK₁)
        (SchattenOrder.ofOneLt halpha) := hnorm_eq
    _ ≤ alphaToAlphaNorm K₂ hK₂ (SchattenOrder.ofOneLt halpha) *
        alphaToAlphaNorm K₁ hK₁ (SchattenOrder.ofOneLt halpha) :=
        alphaToAlphaNorm_comp_le_mul K₂ hK₂ K₁ hK₁ halpha
    _ =
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) *
        alphaToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) := by
        rw [MatrixMap.alphaToAlphaNorm_kron_id_eq (r := d) Phi hPhi halpha]
        rw [MatrixMap.alphaToAlphaNorm_id_kron_eq (r := a) Psi hPsi halpha]

private theorem alphaToAlphaPositiveValue_kron_product_eq_mul
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Psi : MatrixMap c d) (hPsi : MatrixMap.IsCompletelyPositive Psi)
    {alpha : ℝ} (halpha : 1 < alpha)
    (X : AlphaToAlphaPositiveDomain a (SchattenOrder.ofOneLt halpha))
    (Y : AlphaToAlphaPositiveDomain c (SchattenOrder.ofOneLt halpha)) :
    alphaToAlphaPositiveValue (MatrixMap.kron Phi Psi)
        (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
        { matrix := Matrix.kronecker X.matrix Y.matrix,
          pos := X.pos.kronecker Y.pos,
          norm_pos := by
            rw [psdSchattenPNorm_kronecker X.pos Y.pos
              (SchattenOrder.ofOneLt halpha)]
            exact mul_pos X.norm_pos Y.norm_pos } =
      alphaToAlphaPositiveValue Phi hPhi X *
        alphaToAlphaPositiveValue Psi hPsi Y := by
  let hKron : MatrixMap.IsCompletelyPositive (MatrixMap.kron Phi Psi) :=
    MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi
  let hPhiX : (Phi X.matrix).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi X.matrix X.pos
  let hPsiY : (Psi Y.matrix).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Psi hPsi Y.matrix Y.pos
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hnum :
      psdSchattenPNorm
          (MatrixMap.kron Phi Psi (Matrix.kronecker X.matrix Y.matrix))
          (MatrixMap.isCompletelyPositive_mapsPositive (MatrixMap.kron Phi Psi)
            hKron (Matrix.kronecker X.matrix Y.matrix)
            (X.pos.kronecker Y.pos))
          (SchattenOrder.ofOneLt halpha) =
        psdSchattenPNorm
          (Matrix.kronecker (Phi X.matrix) (Psi Y.matrix))
          (hPhiX.kronecker hPsiY)
          (SchattenOrder.ofOneLt halpha) := by
    exact psdSchattenPNorm_congr
      (MatrixMap.kron_apply_kronecker Phi Psi X.matrix Y.matrix)
      (MatrixMap.isCompletelyPositive_mapsPositive (MatrixMap.kron Phi Psi)
        hKron (Matrix.kronecker X.matrix Y.matrix) (X.pos.kronecker Y.pos))
      (hPhiX.kronecker hPsiY)
      (SchattenOrder.ofOneLt halpha)
  unfold alphaToAlphaPositiveValue
  rw [hnum]
  rw [psdSchattenPNorm_kronecker hPhiX hPsiY (SchattenOrder.ofOneLt halpha)]
  rw [psdSchattenPNorm_kronecker X.pos Y.pos (SchattenOrder.ofOneLt halpha)]
  field_simp [ne_of_gt X.norm_pos, ne_of_gt Y.norm_pos]

private theorem alphaToAlphaNorm_mul_le_kron
    [Nonempty a] [Nonempty c]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Psi : MatrixMap c d) (hPsi : MatrixMap.IsCompletelyPositive Psi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) *
        alphaToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) ≤
      alphaToAlphaNorm (MatrixMap.kron Phi Psi)
        (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
        (SchattenOrder.ofOneLt halpha) := by
  have hsup_product :
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) *
          alphaToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) =
        ⨆ X : AlphaToAlphaPositiveDomain a (SchattenOrder.ofOneLt halpha),
          ⨆ Y : AlphaToAlphaPositiveDomain c (SchattenOrder.ofOneLt halpha),
            alphaToAlphaPositiveValue Phi hPhi X *
              alphaToAlphaPositiveValue Psi hPsi Y := by
    rw [alphaToAlphaNorm, alphaToAlphaNorm]
    unfold alphaToAlphaPositiveValueSet
    rw [sSup_range, sSup_range]
    rw [Real.iSup_mul_of_nonneg]
    · congr
      ext X
      rw [Real.mul_iSup_of_nonneg]
      exact alphaToAlphaPositiveValue_nonneg Phi hPhi X
    · exact Real.iSup_nonneg fun Y =>
        alphaToAlphaPositiveValue_nonneg Psi hPsi Y
  rw [hsup_product]
  change
    (⨆ X : AlphaToAlphaPositiveDomain a (SchattenOrder.ofOneLt halpha),
      ⨆ Y : AlphaToAlphaPositiveDomain c (SchattenOrder.ofOneLt halpha),
        alphaToAlphaPositiveValue Phi hPhi X *
          alphaToAlphaPositiveValue Psi hPsi Y) ≤
      alphaToAlphaNorm (MatrixMap.kron Phi Psi)
        (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
        (SchattenOrder.ofOneLt halpha)
  haveI : Nonempty
      (AlphaToAlphaPositiveDomain a (SchattenOrder.ofOneLt halpha)) :=
    alphaToAlphaPositiveDomain_nonempty (a := a) (SchattenOrder.ofOneLt halpha)
  haveI : Nonempty
      (AlphaToAlphaPositiveDomain c (SchattenOrder.ofOneLt halpha)) :=
    alphaToAlphaPositiveDomain_nonempty (a := c) (SchattenOrder.ofOneLt halpha)
  refine ciSup_le ?_
  intro X
  refine ciSup_le ?_
  intro Y
  let Z : AlphaToAlphaPositiveDomain (Prod a c)
      (SchattenOrder.ofOneLt halpha) :=
    { matrix := Matrix.kronecker X.matrix Y.matrix,
      pos := X.pos.kronecker Y.pos,
      norm_pos := by
        rw [psdSchattenPNorm_kronecker X.pos Y.pos
          (SchattenOrder.ofOneLt halpha)]
        exact mul_pos X.norm_pos Y.norm_pos }
  have hvalue :
      alphaToAlphaPositiveValue (MatrixMap.kron Phi Psi)
          (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
          Z =
        alphaToAlphaPositiveValue Phi hPhi X *
          alphaToAlphaPositiveValue Psi hPsi Y := by
    simpa [Z] using
      alphaToAlphaPositiveValue_kron_product_eq_mul
        Phi hPhi Psi hPsi halpha X Y
  rw [← hvalue]
  exact alphaToAlphaPositiveValue_le_alphaToAlphaNorm_of_one_lt
    (MatrixMap.kron Phi Psi)
    (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
    halpha Z

/-- Source-backed product equality for the positive induced `alpha -> alpha`
norm.  The lower bound is the product-input restriction from
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2152-2240], source lines
2174-2190, and the upper bound is the complement/alpha route formalized by
`alphaToAlphaNorm_kron_le_mul` from source lines 2208-2238 of the same claim. -/
theorem alphaToAlphaNorm_kron_eq_mul
    [Nonempty a] [Nonempty c] [Nonempty d]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Psi : MatrixMap c d) (hPsi : MatrixMap.IsCompletelyPositive Psi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alphaToAlphaNorm (MatrixMap.kron Phi Psi)
        (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
        (SchattenOrder.ofOneLt halpha) =
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) *
        alphaToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) := by
  exact le_antisymm
    (alphaToAlphaNorm_kron_le_mul Phi hPhi Psi hPsi halpha)
    (alphaToAlphaNorm_mul_le_kron Phi hPhi Psi hPsi halpha)

/-- Final source-backed multiplicativity of the completely bounded
`1 -> alpha` norm for tensor products of completely positive maps, matching
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2152-2240], specifically
source line 2240. -/
theorem cbOneToAlphaNorm_kron_eq_mul
    [Nonempty a] [Nonempty c] [Nonempty d]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Psi : MatrixMap c d) (hPsi : MatrixMap.IsCompletelyPositive Psi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    cbOneToAlphaNorm (MatrixMap.kron Phi Psi)
        (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
        (SchattenOrder.ofOneLt halpha) =
      cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) *
        cbOneToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) := by
  let K₁ : (a × b) → Matrix b a ℂ := MatrixMap.cpKraus Phi hPhi
  let K₂ : (c × d) → Matrix d c ℂ := MatrixMap.cpKraus Psi hPsi
  have hkron_kraus :
      MatrixMap.kron Phi Psi =
        MatrixMap.ofKraus (MatrixMap.krausProduct K₁ K₂) := by
    rw [MatrixMap.cpKraus_spec Phi hPhi, MatrixMap.cpKraus_spec Psi hPsi]
    exact MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct K₁ K₂
  have hPhi_kraus :
      cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) =
        cbOneToAlphaNorm
          (MatrixMap.ofKraus K₁)
          (MatrixMap.ofKraus_completelyPositive K₁)
          (SchattenOrder.ofOneLt halpha) := by
    exact cbOneToAlphaNorm_congr_map
      (MatrixMap.cpKraus_spec Phi hPhi)
      hPhi
      (MatrixMap.ofKraus_completelyPositive K₁)
      (SchattenOrder.ofOneLt halpha)
  have hPsi_kraus :
      cbOneToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) =
        cbOneToAlphaNorm
          (MatrixMap.ofKraus K₂)
          (MatrixMap.ofKraus_completelyPositive K₂)
          (SchattenOrder.ofOneLt halpha) := by
    exact cbOneToAlphaNorm_congr_map
      (MatrixMap.cpKraus_spec Psi hPsi)
      hPsi
      (MatrixMap.ofKraus_completelyPositive K₂)
      (SchattenOrder.ofOneLt halpha)
  calc
    cbOneToAlphaNorm (MatrixMap.kron Phi Psi)
        (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
        (SchattenOrder.ofOneLt halpha) =
      cbOneToAlphaNorm
        (MatrixMap.ofKraus (MatrixMap.krausProduct K₁ K₂))
        (MatrixMap.ofKraus_completelyPositive (MatrixMap.krausProduct K₁ K₂))
        (SchattenOrder.ofOneLt halpha) := by
          exact cbOneToAlphaNorm_congr_map hkron_kraus
            (MatrixMap.isCompletelyPositive_kron Phi Psi hPhi hPsi)
            (MatrixMap.ofKraus_completelyPositive (MatrixMap.krausProduct K₁ K₂))
            (SchattenOrder.ofOneLt halpha)
    _ =
      alphaToAlphaNorm
        (MatrixMap.krausComplement (MatrixMap.krausProduct K₁ K₂))
        (MatrixMap.krausComplement_isCompletelyPositive
          (MatrixMap.krausProduct K₁ K₂))
        (SchattenOrder.ofOneLt halpha) :=
        MatrixMap.cbOneToAlphaNorm_eq_krausComplement_alphaToAlphaNorm
          (MatrixMap.krausProduct K₁ K₂) halpha
    _ =
      alphaToAlphaNorm
        (MatrixMap.kron
          (MatrixMap.krausComplement K₁)
          (MatrixMap.krausComplement K₂))
        (MatrixMap.isCompletelyPositive_kron
          (MatrixMap.krausComplement K₁)
          (MatrixMap.krausComplement K₂)
          (MatrixMap.krausComplement_isCompletelyPositive K₁)
          (MatrixMap.krausComplement_isCompletelyPositive K₂))
        (SchattenOrder.ofOneLt halpha) := by
          exact alphaToAlphaNorm_congr_map
            (MatrixMap.krausComplement_krausProduct_eq_kron K₁ K₂)
            (MatrixMap.krausComplement_isCompletelyPositive
              (MatrixMap.krausProduct K₁ K₂))
            (MatrixMap.isCompletelyPositive_kron
              (MatrixMap.krausComplement K₁)
              (MatrixMap.krausComplement K₂)
              (MatrixMap.krausComplement_isCompletelyPositive K₁)
              (MatrixMap.krausComplement_isCompletelyPositive K₂))
            (SchattenOrder.ofOneLt halpha)
    _ =
      alphaToAlphaNorm
          (MatrixMap.krausComplement K₁)
          (MatrixMap.krausComplement_isCompletelyPositive K₁)
          (SchattenOrder.ofOneLt halpha) *
        alphaToAlphaNorm
          (MatrixMap.krausComplement K₂)
          (MatrixMap.krausComplement_isCompletelyPositive K₂)
          (SchattenOrder.ofOneLt halpha) := by
          exact alphaToAlphaNorm_kron_eq_mul
            (MatrixMap.krausComplement K₁)
            (MatrixMap.krausComplement_isCompletelyPositive K₁)
            (MatrixMap.krausComplement K₂)
            (MatrixMap.krausComplement_isCompletelyPositive K₂)
            halpha
    _ =
      cbOneToAlphaNorm
          (MatrixMap.ofKraus K₁)
          (MatrixMap.ofKraus_completelyPositive K₁)
          (SchattenOrder.ofOneLt halpha) *
        cbOneToAlphaNorm
          (MatrixMap.ofKraus K₂)
          (MatrixMap.ofKraus_completelyPositive K₂)
          (SchattenOrder.ofOneLt halpha) := by
          rw [← MatrixMap.cbOneToAlphaNorm_eq_krausComplement_alphaToAlphaNorm
            K₁ halpha]
          rw [← MatrixMap.cbOneToAlphaNorm_eq_krausComplement_alphaToAlphaNorm
            K₂ halpha]
    _ =
      cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) *
        cbOneToAlphaNorm Psi hPsi (SchattenOrder.ofOneLt halpha) := by
          rw [← hPhi_kraus, ← hPsi_kraus]

end MatrixMap

end

end QIT
