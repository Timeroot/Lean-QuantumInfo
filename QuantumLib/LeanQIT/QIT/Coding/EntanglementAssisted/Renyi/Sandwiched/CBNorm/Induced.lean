/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Basic

/-!
# Positive-input `alpha -> alpha` induced norm API

This module records the source-shaped positive-input induced norm surface used
in the Khatri--Wilde entanglement-assisted CB-norm multiplicativity route.

Source alignment:
* KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2162-2172 define
  `||P||_{alpha -> alpha}` as a supremum over positive inputs and record the
  trace-normalized power-substitution surface `Y = Z^alpha`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace MatrixMap

/-- Positive-input domain for the source induced `alpha -> alpha` norm.

The source writes strict positive inputs `Z_C > 0`.  This finite-dimensional
API works over the PSD closure and keeps the strict positive Schatten norm
side condition exactly where the source divides by `||Z||_alpha`. -/
structure AlphaToAlphaPositiveDomain (a : Type u) [Fintype a] [DecidableEq a]
    (alpha : SchattenOrder) where
  matrix : CMatrix a
  pos : matrix.PosSemidef
  norm_pos : 0 < psdSchattenPNorm matrix pos alpha

/-- One source ratio value `||P(Z)||_alpha / ||Z||_alpha` for a positive
admissible input. -/
def alphaToAlphaPositiveValue
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (Z : AlphaToAlphaPositiveDomain a alpha) : Real :=
  psdSchattenPNorm (Phi Z.matrix)
      (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Z.matrix Z.pos)
      alpha /
    psdSchattenPNorm Z.matrix Z.pos alpha

/-- Value set for the positive-input induced `alpha -> alpha` norm. -/
def alphaToAlphaPositiveValueSet
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) : Set Real :=
  Set.range fun Z : AlphaToAlphaPositiveDomain a alpha =>
    alphaToAlphaPositiveValue Phi hPhi Z

/-- Source positive-input induced `alpha -> alpha` norm. -/
def alphaToAlphaNorm
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) : Real :=
  sSup (alphaToAlphaPositiveValueSet Phi hPhi alpha)

/-- Trace-normalized domain for the source power-substitution surface
`Y = Z^alpha`, `Tr[Y] <= 1`.

The source writes strict positive `Y_C > 0`; this API uses the PSD closure,
which also includes the zero-boundary case needed by the supremum surface. -/
structure AlphaToAlphaTraceDomain (a : Type u) [Fintype a] [DecidableEq a]
    (alpha : SchattenOrder) where
  matrix : CMatrix a
  pos : matrix.PosSemidef
  trace_le_one : matrix.trace.re <= 1

/-- One source trace-normalized value `||P(Y^(1/alpha))||_alpha`. -/
def alphaToAlphaTraceValue
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (Y : AlphaToAlphaTraceDomain a alpha) : Real :=
  psdSchattenPNorm
    (Phi (CFC.rpow Y.matrix (1 / (alpha : Real))))
    (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
      (CFC.rpow Y.matrix (1 / (alpha : Real)))
      (cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos))
    alpha

/-- Value set for the trace-normalized power-substitution surface. -/
def alphaToAlphaTraceValueSet
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) : Set Real :=
  Set.range fun Y : AlphaToAlphaTraceDomain a alpha =>
    alphaToAlphaTraceValue Phi hPhi Y

/-- The source substitution `Y = Z^alpha / Tr[Z^alpha]` sends a positive-domain
input to the trace-normalized power domain. -/
def AlphaToAlphaPositiveDomain.toTraceDomain
    {alpha : SchattenOrder} (Y : AlphaToAlphaPositiveDomain a alpha)
    (halpha : 1 < (alpha : Real)) :
    AlphaToAlphaTraceDomain a alpha := by
  let R : Real := psdTracePower Y.matrix Y.pos alpha
  have hRpos : 0 < R :=
    psdTracePower_pos_of_psdSchattenPNorm_pos_of_one_lt Y.pos halpha Y.norm_pos
  have hRinv_nonneg : 0 <= R⁻¹ := inv_nonneg.mpr (le_of_lt hRpos)
  refine ⟨(R⁻¹ : Real) • (CFC.rpow Y.matrix alpha), ?_, ?_⟩
  · exact Matrix.PosSemidef.smul
      (cMatrix_rpow_posSemidef (A := Y.matrix) (s := alpha) Y.pos)
      hRinv_nonneg
  ·
      have htrace :
          ((R⁻¹ : Real) • (CFC.rpow Y.matrix alpha) : CMatrix a).trace.re = 1 := by
        rw [Matrix.trace_smul, Complex.smul_re]
        change R⁻¹ * (CFC.rpow Y.matrix alpha).trace.re = 1
        rw [← psdTracePower_eq Y.matrix Y.pos alpha]
        change R⁻¹ * R = 1
        exact inv_mul_cancel₀ (ne_of_gt hRpos)
      exact le_of_eq htrace

/-- The source trace condition `Tr[Y] <= 1` implies
`||Y^(1/alpha)||_alpha <= 1`. -/
theorem AlphaToAlphaTraceDomain.rpow_schatten_norm_le_one
    {alpha : SchattenOrder} (Y : AlphaToAlphaTraceDomain a alpha)
    (halpha : 1 < (alpha : Real)) :
    psdSchattenPNorm (CFC.rpow Y.matrix (1 / (alpha : Real)))
        (cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos)
        alpha <= 1 := by
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have halpha_nonneg : 0 <= (alpha : Real) := le_of_lt halpha_pos
  have hinv_alpha_nonneg : 0 <= 1 / (alpha : Real) := one_div_nonneg.mpr halpha_nonneg
  have hpower :
      psdTracePower (CFC.rpow Y.matrix (1 / (alpha : Real)))
          (cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos)
          alpha =
        Y.matrix.trace.re := by
    rw [psdTracePower_eq]
    have hpow :
        CFC.rpow (CFC.rpow Y.matrix (1 / (alpha : Real))) alpha =
          CFC.rpow Y.matrix 1 := by
      exact cMatrix_rpow_rpow_of_nonneg Y.pos hinv_alpha_nonneg halpha_nonneg (by
        field_simp [ne_of_gt halpha_pos])
    rw [hpow]
    exact congrArg (fun M : CMatrix a => M.trace.re)
      (CFC.rpow_one Y.matrix (ha := Matrix.nonneg_iff_posSemidef.mpr Y.pos))
  rw [psdSchattenPNorm, Internal.psdSchattenExpression, hpower]
  exact Real.rpow_le_one (Matrix.PosSemidef.trace_nonneg Y.pos).1
    Y.trace_le_one hinv_alpha_nonneg

theorem alphaToAlphaTraceValue_toTraceDomain_eq_positiveValue
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (Y : AlphaToAlphaPositiveDomain a alpha) :
    alphaToAlphaTraceValue Phi hPhi (Y.toTraceDomain halpha) =
      alphaToAlphaPositiveValue Phi hPhi Y := by
  let R : Real := psdTracePower Y.matrix Y.pos alpha
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have halpha_nonneg : 0 <= (alpha : Real) := le_of_lt halpha_pos
  have hinv_alpha_nonneg : 0 <= 1 / (alpha : Real) := one_div_nonneg.mpr halpha_nonneg
  have hRpos : 0 < R :=
    psdTracePower_pos_of_psdSchattenPNorm_pos_of_one_lt Y.pos halpha Y.norm_pos
  have hR_nonneg : 0 <= R := le_of_lt hRpos
  have hRinv_nonneg : 0 <= R⁻¹ := inv_nonneg.mpr hR_nonneg
  have hpow_power :
      CFC.rpow (CFC.rpow Y.matrix alpha) (1 / (alpha : Real)) =
        CFC.rpow Y.matrix 1 := by
    exact cMatrix_rpow_rpow_of_nonneg Y.pos halpha_nonneg hinv_alpha_nonneg (by
      field_simp [ne_of_gt halpha_pos])
  have hpow_one :
      CFC.rpow Y.matrix 1 = Y.matrix := by
    exact CFC.rpow_one Y.matrix (ha := Matrix.nonneg_iff_posSemidef.mpr Y.pos)
  have hscale_eq :
      (R⁻¹) ^ (1 / (alpha : Real)) =
        (psdSchattenPNorm Y.matrix Y.pos alpha)⁻¹ := by
    simpa [psdSchattenPNorm, Internal.psdSchattenExpression, R] using
      Real.inv_rpow hR_nonneg (1 / (alpha : Real))
  have hinput :
      CFC.rpow ((R⁻¹ : Real) • (CFC.rpow Y.matrix alpha) : CMatrix a)
          (1 / (alpha : Real)) =
        ((psdSchattenPNorm Y.matrix Y.pos alpha)⁻¹ : Real) • Y.matrix := by
    rw [cMatrix_rpow_real_smul_posSemidef_schatten
      (cMatrix_rpow_posSemidef (A := Y.matrix) (s := alpha) Y.pos)
      hRinv_nonneg]
    rw [hpow_power, hpow_one, hscale_eq]
  have hactualNormedPos :
      ((R⁻¹ : Real) • (CFC.rpow Y.matrix alpha) : CMatrix a).PosSemidef :=
    Matrix.PosSemidef.smul
      (cMatrix_rpow_posSemidef (A := Y.matrix) (s := alpha) Y.pos)
      hRinv_nonneg
  have hactualPowerPos :
      (CFC.rpow ((R⁻¹ : Real) • (CFC.rpow Y.matrix alpha) : CMatrix a)
        (1 / (alpha : Real))).PosSemidef :=
    cMatrix_rpow_posSemidef (A := ((R⁻¹ : Real) • (CFC.rpow Y.matrix alpha) :
      CMatrix a)) (s := 1 / (alpha : Real)) hactualNormedPos
  have hactualPhiPos :
      (Phi (CFC.rpow ((R⁻¹ : Real) • (CFC.rpow Y.matrix alpha) : CMatrix a)
        (1 / (alpha : Real)))).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
      (CFC.rpow ((R⁻¹ : Real) • (CFC.rpow Y.matrix alpha) : CMatrix a)
        (1 / (alpha : Real))) hactualPowerPos
  have hPhiYpos :
      (Phi Y.matrix).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Y.matrix Y.pos
  have hnorm_inv_nonneg :
      0 <= (psdSchattenPNorm Y.matrix Y.pos alpha)⁻¹ :=
    inv_nonneg.mpr (le_of_lt Y.norm_pos)
  have hscaledPhiPos :
      (((psdSchattenPNorm Y.matrix Y.pos alpha)⁻¹ : Real) •
        Phi Y.matrix).PosSemidef :=
    Matrix.PosSemidef.smul hPhiYpos hnorm_inv_nonneg
  have hscaledInputPos :
      (Phi (((psdSchattenPNorm Y.matrix Y.pos alpha)⁻¹ : Real) •
        Y.matrix)).PosSemidef := by
    rw [LinearMap.map_smul_of_tower]
    exact hscaledPhiPos
  unfold alphaToAlphaTraceValue alphaToAlphaPositiveValue
  change
    psdSchattenPNorm
        (Phi (CFC.rpow ((R⁻¹ : Real) • (CFC.rpow Y.matrix alpha) : CMatrix a)
          (1 / (alpha : Real))))
        _ alpha =
      psdSchattenPNorm (Phi Y.matrix)
          (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Y.matrix Y.pos)
          alpha /
        psdSchattenPNorm Y.matrix Y.pos alpha
  calc
    psdSchattenPNorm
        (Phi (CFC.rpow ((R⁻¹ : Real) • (CFC.rpow Y.matrix alpha) : CMatrix a)
          (1 / (alpha : Real))))
        _ alpha
        =
      psdSchattenPNorm
        (Phi (((psdSchattenPNorm Y.matrix Y.pos alpha)⁻¹ : Real) • Y.matrix))
        hscaledInputPos alpha := by
          exact psdSchattenPNorm_congr (congrArg Phi hinput)
            hactualPhiPos hscaledInputPos alpha
    _ =
      psdSchattenPNorm
        (((psdSchattenPNorm Y.matrix Y.pos alpha)⁻¹ : Real) • Phi Y.matrix)
        hscaledPhiPos alpha := by
          exact psdSchattenPNorm_congr
            (LinearMap.map_smul_of_tower Phi
              ((psdSchattenPNorm Y.matrix Y.pos alpha)⁻¹ : Real) Y.matrix)
            hscaledInputPos hscaledPhiPos alpha
    _ =
      (psdSchattenPNorm Y.matrix Y.pos alpha)⁻¹ *
        psdSchattenPNorm (Phi Y.matrix)
          (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Y.matrix Y.pos)
          alpha := by
          simpa using
            (psdSchattenPNorm_real_smul
              (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Y.matrix Y.pos)
              (inv_nonneg.mpr (le_of_lt Y.norm_pos)) alpha)
    _ =
      psdSchattenPNorm (Phi Y.matrix)
          (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Y.matrix Y.pos)
          alpha /
        psdSchattenPNorm Y.matrix Y.pos alpha := by
          rw [div_eq_mul_inv, mul_comm]

theorem alphaToAlphaNorm_eq_sSup_positive
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) :
    alphaToAlphaNorm Phi hPhi alpha =
      sSup (alphaToAlphaPositiveValueSet Phi hPhi alpha) := by
  rfl

theorem alphaToAlphaTraceValue_nonneg
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (Y : AlphaToAlphaTraceDomain a alpha) :
    0 <= alphaToAlphaTraceValue Phi hPhi Y :=
  psdSchattenPNorm_nonneg
    (Phi (CFC.rpow Y.matrix (1 / (alpha : Real))))
    (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
      (CFC.rpow Y.matrix (1 / (alpha : Real)))
      (cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos))
    alpha

theorem alphaToAlphaPositiveValue_nonneg
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (Y : AlphaToAlphaPositiveDomain a alpha) :
    0 <= alphaToAlphaPositiveValue Phi hPhi Y := by
  exact div_nonneg
    (psdSchattenPNorm_nonneg (Phi Y.matrix)
      (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Y.matrix Y.pos)
      alpha)
    (le_of_lt Y.norm_pos)

theorem alphaToAlphaTraceValue_le_positiveValue_of_rpow_norm_pos
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (Y : AlphaToAlphaTraceDomain a alpha)
    (hnorm_pos :
      0 < psdSchattenPNorm (CFC.rpow Y.matrix (1 / (alpha : Real)))
        (cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos)
        alpha) :
    alphaToAlphaTraceValue Phi hPhi Y <=
      alphaToAlphaPositiveValue Phi hPhi
        { matrix := CFC.rpow Y.matrix (1 / (alpha : Real)),
          pos := cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos,
          norm_pos := hnorm_pos } := by
  let Z : CMatrix a := CFC.rpow Y.matrix (1 / (alpha : Real))
  let hZ : Z.PosSemidef :=
    cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos
  let normZ : Real := psdSchattenPNorm Z hZ alpha
  have hnormZ_pos : 0 < normZ := by
    simpa [Z, hZ, normZ] using hnorm_pos
  let X : AlphaToAlphaPositiveDomain a alpha :=
    { matrix := Z, pos := hZ, norm_pos := hnormZ_pos }
  have hnorm_le_one : normZ <= 1 := by
    simpa [Z, hZ, normZ] using Y.rpow_schatten_norm_le_one halpha
  have hratio_nonneg : 0 <= alphaToAlphaPositiveValue Phi hPhi X :=
    alphaToAlphaPositiveValue_nonneg Phi hPhi X
  have htrace_eq_mul :
      alphaToAlphaTraceValue Phi hPhi Y =
        normZ * alphaToAlphaPositiveValue Phi hPhi X := by
    unfold alphaToAlphaTraceValue alphaToAlphaPositiveValue
    change psdSchattenPNorm (Phi Z) _ alpha =
      normZ * (psdSchattenPNorm (Phi Z) _ alpha / normZ)
    rw [mul_div_cancel₀ _ (ne_of_gt hnormZ_pos)]
  calc
    alphaToAlphaTraceValue Phi hPhi Y
        = normZ * alphaToAlphaPositiveValue Phi hPhi X := htrace_eq_mul
    _ <= alphaToAlphaPositiveValue Phi hPhi X :=
        mul_le_of_le_one_left hratio_nonneg hnorm_le_one

theorem alphaToAlphaTraceValue_eq_zero_of_rpow_norm_eq_zero
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (Y : AlphaToAlphaTraceDomain a alpha)
    (hnorm_zero :
      psdSchattenPNorm (CFC.rpow Y.matrix (1 / (alpha : Real)))
        (cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos)
        alpha = 0) :
    alphaToAlphaTraceValue Phi hPhi Y = 0 := by
  let Z : CMatrix a := CFC.rpow Y.matrix (1 / (alpha : Real))
  let hZ : Z.PosSemidef :=
    cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have hnormZ_zero : psdSchattenPNorm Z hZ alpha = 0 := by
    simpa [Z, hZ] using hnorm_zero
  have hZzero : Z = 0 := by
    by_contra hZne
    have hZnorm_pos : 0 < psdSchattenPNorm Z hZ alpha :=
      psdSchattenPNorm_pos_of_ne_zero Z hZ hZne
    exact (ne_of_gt hZnorm_pos) hnormZ_zero
  have hPhiZpos : (Phi Z).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Z hZ
  have hPhiZzero : Phi Z = 0 := by
    rw [hZzero]
    exact map_zero Phi
  unfold alphaToAlphaTraceValue
  change psdSchattenPNorm (Phi Z) _ alpha = 0
  calc
    psdSchattenPNorm (Phi Z) _ alpha =
        psdSchattenPNorm (0 : CMatrix b) Matrix.PosSemidef.zero alpha := by
          exact psdSchattenPNorm_congr hPhiZzero hPhiZpos Matrix.PosSemidef.zero alpha
    _ = 0 := psdSchattenPNorm_zero alpha

theorem alphaToAlphaNorm_eq_tracePower_sSup_of_one_lt
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real)) :
    alphaToAlphaNorm Phi hPhi alpha =
      sSup (alphaToAlphaTraceValueSet Phi hPhi alpha) := by
  let P : Set Real := alphaToAlphaPositiveValueSet Phi hPhi alpha
  let T : Set Real := alphaToAlphaTraceValueSet Phi hPhi alpha
  have hP_nonneg : ∀ x ∈ P, 0 <= x := by
    rintro x ⟨Y, rfl⟩
    exact alphaToAlphaPositiveValue_nonneg Phi hPhi Y
  have hT_nonneg : ∀ x ∈ T, 0 <= x := by
    rintro x ⟨Y, rfl⟩
    exact alphaToAlphaTraceValue_nonneg Phi hPhi Y
  have hP_subset_T : P ⊆ T := by
    rintro x ⟨Y, rfl⟩
    exact ⟨Y.toTraceDomain halpha,
      alphaToAlphaTraceValue_toTraceDomain_eq_positiveValue Phi hPhi halpha Y⟩
  have hT_le_zero_or_positive :
      ∀ x ∈ T, x = 0 ∨ ∃ p ∈ P, x <= p := by
    rintro x ⟨Y, rfl⟩
    let Z : CMatrix a := CFC.rpow Y.matrix (1 / (alpha : Real))
    let hZ : Z.PosSemidef :=
      cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos
    let normZ : Real := psdSchattenPNorm Z hZ alpha
    have hnormZ_nonneg : 0 <= normZ := by
      exact psdSchattenPNorm_nonneg Z hZ alpha
    by_cases hnormZ_zero : normZ = 0
    · left
      exact alphaToAlphaTraceValue_eq_zero_of_rpow_norm_eq_zero Phi hPhi halpha Y
        (by simpa [Z, hZ, normZ] using hnormZ_zero)
    · right
      have hnormZ_pos : 0 < normZ :=
        lt_of_le_of_ne hnormZ_nonneg (Ne.symm hnormZ_zero)
      let X : AlphaToAlphaPositiveDomain a alpha :=
        { matrix := Z, pos := hZ, norm_pos := hnormZ_pos }
      refine ⟨alphaToAlphaPositiveValue Phi hPhi X, ⟨X, rfl⟩, ?_⟩
      exact alphaToAlphaTraceValue_le_positiveValue_of_rpow_norm_pos Phi hPhi
        halpha Y (by simpa [Z, hZ, normZ] using hnormZ_pos)
  have hTbdd_of_hPbdd : BddAbove P → BddAbove T := by
    rintro ⟨M, hM⟩
    refine ⟨max M 0, ?_⟩
    intro x hx
    rcases hT_le_zero_or_positive x hx with hzero | ⟨p, hp, hxp⟩
    · rw [hzero]
      exact le_max_right M 0
    · exact hxp.trans ((hM hp).trans (le_max_left M 0))
  have hPbdd_of_hTbdd : BddAbove T → BddAbove P := by
    rintro ⟨M, hM⟩
    exact ⟨M, fun x hx => hM (hP_subset_T hx)⟩
  unfold alphaToAlphaNorm
  change sSup P = sSup T
  by_cases hPbdd : BddAbove P
  · have hTbdd : BddAbove T := hTbdd_of_hPbdd hPbdd
    refine le_antisymm ?_ ?_
    · refine Real.sSup_le ?_ (Real.sSup_nonneg hT_nonneg)
      intro x hx
      exact le_csSup hTbdd (hP_subset_T hx)
    · refine Real.sSup_le ?_ (Real.sSup_nonneg hP_nonneg)
      intro x hx
      rcases hT_le_zero_or_positive x hx with hzero | ⟨p, hp, hxp⟩
      · rw [hzero]
        exact Real.sSup_nonneg hP_nonneg
      · exact hxp.trans (le_csSup hPbdd hp)
  · have hTnotbdd : ¬ BddAbove T := by
      intro hTbdd
      exact hPbdd (hPbdd_of_hTbdd hTbdd)
    rw [Real.sSup_of_not_bddAbove hPbdd, Real.sSup_of_not_bddAbove hTnotbdd]

end MatrixMap

end

end QIT
