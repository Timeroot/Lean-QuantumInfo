/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Induced
public import QIT.Information.Renyi.FrankLieb.Variational

/-!
# Concavity and reference twirl support for EA CB norms

This module collects no-placeholder support for the Khatri--Wilde
entanglement-assisted completely bounded norm collapse route.

Source alignment:
* KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2254-2265 average
  over a finite depolarizing twirl on the reference system and identify the
  average with `π_R ⊗ Tr_R[X]`.
* KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2283-2399 use
  concavity of `X ↦ ||M(X^(1/alpha))||_alpha` for CP maps and `alpha > 1`.

The full concavity theorem requires a Holder/Lieb bridge that is intentionally
not assumed here.  The proved CP/Schatten helpers below package the exact
positive endpoints needed by that bridge.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

open State

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Source value `X ↦ ||Phi(X^(1/alpha))||_alpha` on PSD inputs.

This is the function whose concavity is invoked in
KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2283-2399. -/
def cpPsdSchattenRpowValue
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) (X : CMatrix a) (hX : X.PosSemidef) : ℝ :=
  psdSchattenPNorm
    (Phi (CFC.rpow X (1 / (alpha : ℝ))))
    (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
      (CFC.rpow X (1 / (alpha : ℝ)))
      (cMatrix_rpow_posSemidef (A := X) (s := 1 / (alpha : ℝ)) hX))
    alpha

/-- The CP/Schatten rpow value is nonnegative. -/
theorem cpPsdSchattenRpowValue_nonneg
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) (X : CMatrix a) (hX : X.PosSemidef) :
    0 ≤ cpPsdSchattenRpowValue Phi hPhi alpha X hX :=
  psdSchattenPNorm_nonneg
    (Phi (CFC.rpow X (1 / (alpha : ℝ))))
    (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
      (CFC.rpow X (1 / (alpha : ℝ)))
      (cMatrix_rpow_posSemidef (A := X) (s := 1 / (alpha : ℝ)) hX))
    alpha

omit [Fintype a] [DecidableEq a] in
/-- The convex input appearing in the source concavity lemma is PSD. -/
theorem cp_psdSchatten_rpow_convexInput_posSemidef
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {X0 X1 : CMatrix a} (hX0 : X0.PosSemidef) (hX1 : X1.PosSemidef) :
    (lambda • X0 + (1 - lambda) • X1).PosSemidef :=
  Matrix.PosSemidef.add
    (Matrix.PosSemidef.smul hX0 hlambda0)
    (Matrix.PosSemidef.smul hX1 (sub_nonneg.mpr hlambda1))

/-- Completely positive maps send the PSD `1 / alpha` powers from the source
concavity lemma to PSD outputs. -/
theorem cp_map_rpow_posSemidef
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : ℝ) {X : CMatrix a} (hX : X.PosSemidef) :
    (Phi (CFC.rpow X (1 / alpha))).PosSemidef :=
  MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
    (CFC.rpow X (1 / alpha))
    (cMatrix_rpow_posSemidef (A := X) (s := 1 / alpha) hX)

/-- Rank-one PSD tensor weight obtained by vectorizing a rectangular Kraus
operator `K : a -> b` as a vector on `a × b`. -/
def rectangularKrausVecWeight (K : Matrix b a ℂ) : CMatrix (a × b) :=
  rankOneMatrix (fun p : a × b => star (K p.2 p.1))

omit [DecidableEq a] [DecidableEq b] in
/-- The rectangular Kraus vectorized weight is positive semidefinite. -/
theorem rectangularKrausVecWeight_posSemidef (K : Matrix b a ℂ) :
    (rectangularKrausVecWeight K).PosSemidef := by
  simpa [rectangularKrausVecWeight] using
    rankOneMatrix_pos (fun p : a × b => star (K p.2 p.1))

omit [DecidableEq a] [DecidableEq b] in
/-- Rectangular vectorized trace identity for a single Kraus operator.

With the convention `|K>` indexed by `(input, output)` and conjugated to match
`rankOneMatrix`, this is the identity
`Tr[K A K† B] = Tr[|K><K| (A ⊗ Bᵀ)]`. -/
theorem rectangular_kraus_trace_tensor_trace_transpose
    (K : Matrix b a ℂ) (A : CMatrix a) (B : CMatrix b) :
    (((K * A * Matrix.conjTranspose K) * B).trace) =
      ((rectangularKrausVecWeight K * Matrix.kronecker A B.transpose).trace) := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    rectangularKrausVecWeight, rankOneMatrix_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply]
  simp only [Finset.sum_mul]
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  let e : (((b × b) × a) × a) ≃ (a × b) × (a × b) := {
    toFun x := ((x.1.2, x.1.1.2), (x.2, x.1.1.1))
    invFun y := (((y.2.2, y.1.2), y.1.1), y.2.1)
    left_inv := by
      intro x
      rcases x with ⟨⟨⟨x, x_1⟩, x_2⟩, x_3⟩
      rfl
    right_inv := by
      intro y
      rcases y with ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩
      rfl
  }
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  simp [e, mul_assoc, mul_left_comm, mul_comm]

omit [DecidableEq a] [DecidableEq b] in
/-- Real-part form of `rectangular_kraus_trace_tensor_trace_transpose`. -/
theorem rectangular_kraus_trace_tensor_trace_transpose_re
    (K : Matrix b a ℂ) (A : CMatrix a) (B : CMatrix b) :
    ((((K * A * Matrix.conjTranspose K) * B).trace).re) =
      (((rectangularKrausVecWeight K *
        Matrix.kronecker A B.transpose).trace).re) := by
  exact congrArg Complex.re (rectangular_kraus_trace_tensor_trace_transpose K A B)

/-- Single-rectangular-Kraus Lieb trace concavity.

This is the source term
`(X,Y) ↦ Tr[K X^p K† Y^(1-p)]`, proved by vectorizing `K` and applying the
finite-dimensional Lieb--Ando tensor weighted trace concavity theorem. -/
theorem rectangular_kraus_lieb_trace_concave
    (K : Matrix b a ℂ)
    {X0 X1 : CMatrix a} {Y0 Y1 : CMatrix b}
    (hX0 : X0.PosSemidef) (hX1 : X1.PosSemidef)
    (hY0 : Y0.PosSemidef) (hY1 : Y1.PosSemidef)
    {p lambda : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    lambda * ((((K * CFC.rpow X0 p * Matrix.conjTranspose K) *
        CFC.rpow Y0 (1 - p)).trace).re) +
      (1 - lambda) * ((((K * CFC.rpow X1 p * Matrix.conjTranspose K) *
        CFC.rpow Y1 (1 - p)).trace).re) ≤
    ((((K * CFC.rpow (lambda • X0 + (1 - lambda) • X1) p *
        Matrix.conjTranspose K) *
        CFC.rpow (lambda • Y0 + (1 - lambda) • Y1) (1 - p)).trace).re) := by
  let pNN : NNReal := ⟨p, hp0.le⟩
  have hpNN : pNN ∈ Set.Ioo (0 : NNReal) 1 := by
    constructor
    · exact_mod_cast hp0
    · exact_mod_cast hp1
  have hY0T : Y0.transpose.PosSemidef := hY0.transpose
  have hY1T : Y1.transpose.PosSemidef := hY1.transpose
  have hW : (rectangularKrausVecWeight K).PosSemidef :=
    rectangularKrausVecWeight_posSemidef K
  have htensor :=
    liebAndo_tensorWeightedTraceConcavity_posSemidef
      (a := a) (b := b) (p := pNN) hpNN
      (A₁ := X0) (A₂ := X1)
      (B₁ := Y0.transpose) (B₂ := Y1.transpose)
      (W := rectangularKrausVecWeight K)
      hX0 hX1 hY0T hY1T hW hlambda0 hlambda1
  have h1p_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
  have hY0powT :
      CFC.rpow Y0.transpose (1 - (pNN : ℝ)) =
        (CFC.rpow Y0 (1 - p)).transpose := by
    simpa [pNN] using cMatrix_rpow_transpose_nonneg (A := Y0) hY0 h1p_nonneg
  have hY1powT :
      CFC.rpow Y1.transpose (1 - (pNN : ℝ)) =
        (CFC.rpow Y1 (1 - p)).transpose := by
    simpa [pNN] using cMatrix_rpow_transpose_nonneg (A := Y1) hY1 h1p_nonneg
  have hYmix : (lambda • Y0 + (1 - lambda) • Y1).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hY0 hlambda0)
      (Matrix.PosSemidef.smul hY1 (sub_nonneg.mpr hlambda1))
  have hYmixT :
      lambda • Y0.transpose + (1 - lambda) • Y1.transpose =
        (lambda • Y0 + (1 - lambda) • Y1).transpose := by
    ext i j
    simp
  have hYmixpowT :
      CFC.rpow (lambda • Y0.transpose + (1 - lambda) • Y1.transpose)
          (1 - (pNN : ℝ)) =
        (CFC.rpow (lambda • Y0 + (1 - lambda) • Y1) (1 - p)).transpose := by
    rw [hYmixT]
    simpa [pNN] using
      cMatrix_rpow_transpose_nonneg
        (A := lambda • Y0 + (1 - lambda) • Y1) hYmix h1p_nonneg
  have htrace0 :=
    rectangular_kraus_trace_tensor_trace_transpose_re K
      (CFC.rpow X0 p) (CFC.rpow Y0 (1 - p))
  have htrace1 :=
    rectangular_kraus_trace_tensor_trace_transpose_re K
      (CFC.rpow X1 p) (CFC.rpow Y1 (1 - p))
  have htracet :=
    rectangular_kraus_trace_tensor_trace_transpose_re K
      (CFC.rpow (lambda • X0 + (1 - lambda) • X1) p)
      (CFC.rpow (lambda • Y0 + (1 - lambda) • Y1) (1 - p))
  have htensor' := htensor
  rw [hY0powT, hY1powT, hYmixpowT] at htensor'
  have hpcoe : (pNN : ℝ) = p := rfl
  rw [hpcoe] at htensor'
  rw [htrace0, htrace1, htracet]
  exact htensor'

/-- Trace pairing against a Kraus-form map expands as the finite sum of
single-Kraus trace pairings. -/
theorem ofKraus_trace_mul_eq_sum
    {κ : Type w} [Fintype κ] (K : κ → Matrix b a ℂ)
    (X : CMatrix a) (Y : CMatrix b) :
    ((((MatrixMap.ofKraus K) X) * Y).trace).re =
      ∑ k : κ, ((((K k * X * Matrix.conjTranspose (K k)) * Y).trace).re) := by
  simp [MatrixMap.ofKraus, Matrix.sum_mul, Matrix.trace_sum]

/-- Finite-Kraus Lieb trace concavity for `MatrixMap.ofKraus`. -/
theorem ofKraus_psd_trace_rpow_value_concave
    {κ : Type w} [Fintype κ] (K : κ → Matrix b a ℂ)
    {X0 X1 : CMatrix a} {Y0 Y1 : CMatrix b}
    (hX0 : X0.PosSemidef) (hX1 : X1.PosSemidef)
    (hY0 : Y0.PosSemidef) (hY1 : Y1.PosSemidef)
    {p lambda : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    lambda * ((((MatrixMap.ofKraus K (CFC.rpow X0 p)) *
        CFC.rpow Y0 (1 - p)).trace).re) +
      (1 - lambda) * ((((MatrixMap.ofKraus K (CFC.rpow X1 p)) *
        CFC.rpow Y1 (1 - p)).trace).re) ≤
    ((((MatrixMap.ofKraus K
        (CFC.rpow (lambda • X0 + (1 - lambda) • X1) p)) *
        CFC.rpow (lambda • Y0 + (1 - lambda) • Y1) (1 - p)).trace).re) := by
  have htrace0 :=
    ofKraus_trace_mul_eq_sum K (CFC.rpow X0 p) (CFC.rpow Y0 (1 - p))
  have htrace1 :=
    ofKraus_trace_mul_eq_sum K (CFC.rpow X1 p) (CFC.rpow Y1 (1 - p))
  have htracet :=
    ofKraus_trace_mul_eq_sum K
      (CFC.rpow (lambda • X0 + (1 - lambda) • X1) p)
      (CFC.rpow (lambda • Y0 + (1 - lambda) • Y1) (1 - p))
  rw [htrace0, htrace1, htracet]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ =>
    rectangular_kraus_lieb_trace_concave (K k)
      hX0 hX1 hY0 hY1 hp0 hp1 hlambda0 hlambda1

/-- Completely positive map version of the Kraus/Lieb trace concavity bridge. -/
theorem cp_map_psd_trace_rpow_value_concave
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {X0 X1 : CMatrix a} {Y0 Y1 : CMatrix b}
    (hX0 : X0.PosSemidef) (hX1 : X1.PosSemidef)
    (hY0 : Y0.PosSemidef) (hY1 : Y1.PosSemidef)
    {p lambda : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    lambda * ((((Phi (CFC.rpow X0 p)) *
        CFC.rpow Y0 (1 - p)).trace).re) +
      (1 - lambda) * ((((Phi (CFC.rpow X1 p)) *
        CFC.rpow Y1 (1 - p)).trace).re) ≤
    ((((Phi (CFC.rpow (lambda • X0 + (1 - lambda) • X1) p)) *
        CFC.rpow (lambda • Y0 + (1 - lambda) • Y1) (1 - p)).trace).re) := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd Phi hPhi
  rw [hK]
  exact ofKraus_psd_trace_rpow_value_concave K
    hX0 hX1 hY0 hY1 hp0 hp1 hlambda0 hlambda1

/-- Source concavity theorem for the CP-map Schatten value
`X ↦ ||Phi(X^(1/alpha))||_alpha`, for `alpha > 1`.

This is the no-placeholder Lean form of
KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2283-2399. -/
theorem cp_psdSchatten_rpow_value_concave
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha lambda : Real} (halpha : 1 < alpha)
    (hlambda0 : 0 <= lambda) (hlambda1 : lambda <= 1)
    {X0 X1 : CMatrix a} (hX0 : X0.PosSemidef) (hX1 : X1.PosSemidef) :
    lambda *
        psdSchattenPNorm
          (Phi (CFC.rpow X0 (1 / alpha)))
          (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
            (CFC.rpow X0 (1 / alpha))
            (cMatrix_rpow_posSemidef hX0))
          (SchattenOrder.ofOneLt halpha) +
      (1 - lambda) *
        psdSchattenPNorm
          (Phi (CFC.rpow X1 (1 / alpha)))
          (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
            (CFC.rpow X1 (1 / alpha))
            (cMatrix_rpow_posSemidef hX1))
          (SchattenOrder.ofOneLt halpha) <=
    psdSchattenPNorm
      (Phi (CFC.rpow (lambda • X0 + (1 - lambda) • X1) (1 / alpha)))
      (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
        (CFC.rpow (lambda • X0 + (1 - lambda) • X1) (1 / alpha))
        (cMatrix_rpow_posSemidef
          (Matrix.PosSemidef.add
            (Matrix.PosSemidef.smul hX0 hlambda0)
            (Matrix.PosSemidef.smul hX1 (sub_nonneg.mpr hlambda1)))))
      (SchattenOrder.ofOneLt halpha) := by
  let p : ℝ := 1 / alpha
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hp0 : 0 < p := by
    dsimp [p]
    exact one_div_pos.mpr halpha_pos
  have hp1 : p < 1 := by
    dsimp [p]
    calc
      1 / alpha < alpha / alpha := div_lt_div_of_pos_right halpha halpha_pos
      _ = 1 := by field_simp [ne_of_gt halpha_pos]
  let q : ℝ := (1 - p)⁻¹
  have h1p_pos : 0 < 1 - p := sub_pos.mpr hp1
  have h1p_nonneg : 0 ≤ 1 - p := le_of_lt h1p_pos
  have hq_pos : 0 < q := by
    dsimp [q]
    exact inv_pos.mpr h1p_pos
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hp_inv : p⁻¹ = alpha := by
    dsimp [p]
    field_simp [ne_of_gt halpha_pos]
  have hpq_inv : p⁻¹.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.inv_one_sub_inv hp0 hp1
  have hpq : alpha.HolderConjugate q := by
    simpa [hp_inv] using hpq_inv
  have hq_ge_one : 1 ≤ q := le_of_lt hpq.symm.lt
  have hXmix : (lambda • X0 + (1 - lambda) • X1).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hX0 hlambda0)
      (Matrix.PosSemidef.smul hX1 (sub_nonneg.mpr hlambda1))
  let N0 : CMatrix b := Phi (CFC.rpow X0 p)
  let N1 : CMatrix b := Phi (CFC.rpow X1 p)
  let Nt : CMatrix b := Phi (CFC.rpow (lambda • X0 + (1 - lambda) • X1) p)
  have hN0 : N0.PosSemidef := by
    simpa [N0, p] using
      MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
        (CFC.rpow X0 (1 / alpha))
        (cMatrix_rpow_posSemidef (A := X0) (s := 1 / alpha) hX0)
  have hN1 : N1.PosSemidef := by
    simpa [N1, p] using
      MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
        (CFC.rpow X1 (1 / alpha))
        (cMatrix_rpow_posSemidef (A := X1) (s := 1 / alpha) hX1)
  have hNt : Nt.PosSemidef := by
    simpa [Nt, p] using
      MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi
        (CFC.rpow (lambda • X0 + (1 - lambda) • X1) (1 / alpha))
        (cMatrix_rpow_posSemidef
          (A := lambda • X0 + (1 - lambda) • X1) (s := 1 / alpha) hXmix)
  rcases (psdTraceHolderUnitBall_isGreatest (M := N0) hN0 (p := alpha) (q := q) hpq).1
    with ⟨B0, hB0, hB0q, hval0⟩
  rcases (psdTraceHolderUnitBall_isGreatest (M := N1) hN1 (p := alpha) (q := q) hpq).1
    with ⟨B1, hB1, hB1q, hval1⟩
  let Y0 : CMatrix b := CFC.rpow B0 q
  let Y1 : CMatrix b := CFC.rpow B1 q
  have hY0 : Y0.PosSemidef := by
    simpa [Y0] using cMatrix_rpow_posSemidef (A := B0) (s := q) hB0
  have hY1 : Y1.PosSemidef := by
    simpa [Y1] using cMatrix_rpow_posSemidef (A := B1) (s := q) hB1
  have hY0_trace_le_one : Y0.trace.re ≤ 1 := by
    simpa [Y0, psdTracePower_eq] using hB0q
  have hY1_trace_le_one : Y1.trace.re ≤ 1 := by
    simpa [Y1, psdTracePower_eq] using hB1q
  have hq_mul : q * (1 - p) = 1 := by
    dsimp [q]
    field_simp [ne_of_gt h1p_pos]
  have h1p_mul : (1 - p) * q = 1 := by
    rw [mul_comm]
    exact hq_mul
  have hY0pow : CFC.rpow Y0 (1 - p) = B0 := by
    calc
      CFC.rpow Y0 (1 - p) =
          CFC.rpow B0 1 := by
            simpa [Y0] using
              cMatrix_rpow_rpow_of_nonneg hB0 hq_nonneg h1p_nonneg hq_mul
      _ = B0 := by
            exact CFC.rpow_one B0 (ha := Matrix.nonneg_iff_posSemidef.mpr hB0)
  have hY1pow : CFC.rpow Y1 (1 - p) = B1 := by
    calc
      CFC.rpow Y1 (1 - p) =
          CFC.rpow B1 1 := by
            simpa [Y1] using
              cMatrix_rpow_rpow_of_nonneg hB1 hq_nonneg h1p_nonneg hq_mul
      _ = B1 := by
            exact CFC.rpow_one B1 (ha := Matrix.nonneg_iff_posSemidef.mpr hB1)
  let Yt : CMatrix b := lambda • Y0 + (1 - lambda) • Y1
  have hYt : Yt.PosSemidef := by
    simpa [Yt] using
      Matrix.PosSemidef.add
        (Matrix.PosSemidef.smul hY0 hlambda0)
        (Matrix.PosSemidef.smul hY1 (sub_nonneg.mpr hlambda1))
  have hYt_trace :
      Yt.trace.re = lambda * Y0.trace.re + (1 - lambda) * Y1.trace.re := by
    have hY0im : Y0.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hY0).2.symm
    have hY1im : Y1.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hY1).2.symm
    simp [Yt, Matrix.trace_add, Matrix.trace_smul, Complex.mul_re, hY0im, hY1im]
  have hYt_trace_le_one : Yt.trace.re ≤ 1 := by
    rw [hYt_trace]
    have hright_nonneg : 0 ≤ 1 - lambda := sub_nonneg.mpr hlambda1
    nlinarith [hY0_trace_le_one, hY1_trace_le_one, hlambda0, hright_nonneg]
  let Bt : CMatrix b := CFC.rpow Yt (1 - p)
  have hBt : Bt.PosSemidef := by
    simpa [Bt] using cMatrix_rpow_posSemidef (A := Yt) (s := 1 - p) hYt
  have hBtq_eq_trace : psdTracePower Bt hBt q = Yt.trace.re := by
    rw [psdTracePower_eq]
    have hpow :
        CFC.rpow Bt q = CFC.rpow Yt 1 := by
      simpa [Bt] using
        cMatrix_rpow_rpow_of_nonneg hYt h1p_nonneg hq_nonneg h1p_mul
    rw [hpow]
    exact congrArg (fun M : CMatrix b => M.trace.re)
      (CFC.rpow_one Yt (ha := Matrix.nonneg_iff_posSemidef.mpr hYt))
  have hBtq : psdTracePower Bt hBt q ≤ 1 := by
    rw [hBtq_eq_trace]
    exact hYt_trace_le_one
  have htrace_concave :
      lambda * (((N0 * B0).trace).re) +
          (1 - lambda) * (((N1 * B1).trace).re) ≤
        (((Nt * Bt).trace).re) := by
    have htrace :=
      cp_map_psd_trace_rpow_value_concave Phi hPhi
        hX0 hX1 hY0 hY1 hp0 hp1 hlambda0 hlambda1
    have htrace' := htrace
    rw [hY0pow, hY1pow] at htrace'
    simpa [N0, N1, Nt, Bt, Yt] using htrace'
  have hholder_t : (((Nt * Bt).trace).re) ≤
      psdSchattenPNorm Nt hNt (SchattenOrder.ofOneLt halpha) :=
    posSemidef_trace_mul_le_psdSchattenPNorm_of_tracePower_le_one
      hNt hBt hpq hq_ge_one hBtq
  have hleft :
      lambda * psdSchattenPNorm N0 hN0 (SchattenOrder.ofOneLt halpha) +
          (1 - lambda) * psdSchattenPNorm N1 hN1 (SchattenOrder.ofOneLt halpha) =
        lambda * (((N0 * B0).trace).re) +
          (1 - lambda) * (((N1 * B1).trace).re) := by
    have hval0' :
        psdSchattenPNorm N0 hN0 (SchattenOrder.ofOneLt halpha) =
          ((N0 * B0).trace).re := by
      simpa [SchattenOrder.ofOneLt] using hval0
    have hval1' :
        psdSchattenPNorm N1 hN1 (SchattenOrder.ofOneLt halpha) =
          ((N1 * B1).trace).re := by
      simpa [SchattenOrder.ofOneLt] using hval1
    rw [hval0', hval1']
  have hmain :
      lambda * psdSchattenPNorm N0 hN0 (SchattenOrder.ofOneLt halpha) +
          (1 - lambda) * psdSchattenPNorm N1 hN1 (SchattenOrder.ofOneLt halpha) ≤
        psdSchattenPNorm Nt hNt (SchattenOrder.ofOneLt halpha) := by
    rw [hleft]
    exact le_trans htrace_concave hholder_t
  simpa [N0, N1, Nt, p] using hmain

variable {r : Type u}
variable [Fintype r] [DecidableEq r]

/-- The unitary acting on the left/reference tensor factor as `U` and as the
identity on the right/application tensor factor. -/
def localReferenceUnitary (U : Matrix.unitaryGroup r ℂ) :
    Matrix.unitaryGroup (Prod r a) ℂ :=
  ⟨Matrix.kronecker (U : CMatrix r) (1 : CMatrix a), by
    let I : Matrix.unitaryGroup a ℂ := ⟨1, by simp⟩
    simpa using Matrix.kronecker_mem_unitary U.2 I.2⟩

@[simp] theorem localReferenceUnitary_coe (U : Matrix.unitaryGroup r ℂ) :
    (localReferenceUnitary (a := a) U : CMatrix (Prod r a)) =
      Matrix.kronecker (U : CMatrix r) (1 : CMatrix a) := rfl

theorem diagonalSignReferenceUnitary_conj_apply
    (ε : r → Bool) (X : CMatrix (Prod r a)) (i i' : r) (j j' : a) :
    (((localReferenceUnitary (a := a) (diagonalSignUnitary ε) :
          CMatrix (Prod r a)) *
        X * star (localReferenceUnitary (a := a) (diagonalSignUnitary ε) :
          CMatrix (Prod r a))) (i, j) (i', j')) =
      boolSignComplex (ε i) * X (i, j) (i', j') * boolSignComplex (ε i') := by
  simp only [localReferenceUnitary_coe, diagonalSignUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal, Matrix.of_apply,
    Matrix.conjTranspose_apply]
  have hinner : ∀ x : Prod r a,
      (∑ y : Prod r a,
        (((if i = y.1 then boolSignComplex (ε i) else 0) *
            if j = y.2 then 1 else 0) * X y x)) =
        boolSignComplex (ε i) * X (i, j) x := by
    intro x
    refine (Finset.sum_eq_single (i, j) ?_ ?_).trans ?_
    · intro y _ hy
      rcases y with ⟨y₁, y₂⟩
      by_cases hiy : i = y₁
      · by_cases hjy : j = y₂
        · exfalso
          apply hy
          exact Prod.ext hiy.symm hjy.symm
        · simp [hiy, hjy]
      · simp [hiy]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
    · simp
  simp_rw [hinner]
  refine (Finset.sum_eq_single (i', j') ?_ ?_).trans ?_
  · intro x _ hx
    rcases x with ⟨x₁, x₂⟩
    by_cases hjx : x₂ = j'
    · by_cases hix : x₁ = i'
      · exfalso
        apply hx
        exact Prod.ext hix hjx
      · have hix' : i' ≠ x₁ := fun h => hix h.symm
        simp [hix', hjx]
    · simp [hjx]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))
  · simp [mul_assoc]

theorem permutationReferenceUnitary_conj_apply
    (π : Equiv.Perm r) (X : CMatrix (Prod r a)) (i i' : r) (j j' : a) :
    (((localReferenceUnitary (a := a) (permutationUnitary π) :
          CMatrix (Prod r a)) *
        X * star (localReferenceUnitary (a := a) (permutationUnitary π) :
          CMatrix (Prod r a))) (i, j) (i', j')) =
      X (π i, j) (π i', j') := by
  simp only [localReferenceUnitary_coe, permutationUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply]
  have hinner : ∀ x : Prod r a,
      (∑ y : Prod r a,
        (((if π i = y.1 then 1 else 0) * if j = y.2 then 1 else 0) * X y x)) =
        X (π i, j) x := by
    intro x
    refine (Finset.sum_eq_single (π i, j) ?_ ?_).trans ?_
    · intro y _ hy
      rcases y with ⟨y₁, y₂⟩
      by_cases hiy : π i = y₁
      · by_cases hjy : j = y₂
        · exfalso
          apply hy
          exact Prod.ext hiy.symm hjy.symm
        · simp [hiy, hjy]
      · simp [hiy]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
    · simp
  simp_rw [hinner]
  refine (Finset.sum_eq_single (π i', j') ?_ ?_).trans ?_
  · intro x _ hx
    rcases x with ⟨x₁, x₂⟩
    by_cases hjx : x₂ = j'
    · by_cases hix : x₁ = π i'
      · exfalso
        apply hx
        exact Prod.ext hix hjx
      · have hix' : π i' ≠ x₁ := fun h => hix h.symm
        simp [hix', hjx]
    · simp [hjx]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))
  · simp

/-- Local-reference unitaries respect multiplication. -/
theorem localReferenceUnitary_mul (U V : Matrix.unitaryGroup r ℂ) :
    (localReferenceUnitary (a := a) (U * V) : CMatrix (Prod r a)) =
      (localReferenceUnitary (a := a) U : CMatrix (Prod r a)) *
        (localReferenceUnitary (a := a) V : CMatrix (Prod r a)) := by
  rw [localReferenceUnitary_coe, localReferenceUnitary_coe, localReferenceUnitary_coe]
  simpa using
    (Matrix.mul_kronecker_mul (U : CMatrix r) (V : CMatrix r)
      (1 : CMatrix a) (1 : CMatrix a))

/-- Entrywise formula for the finite reference-unitary family obtained by
first dephasing with a diagonal sign and then permuting the reference factor. -/
theorem localReferenceSignPermutationUnitary_conj_apply
    (ε : r → Bool) (π : Equiv.Perm r) (X : CMatrix (Prod r a))
    (i i' : r) (j j' : a) :
    (((localReferenceUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a)) *
        X *
        star (localReferenceUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a))) (i, j) (i', j')) =
      boolSignComplex (ε (π i)) * X (π i, j) (π i', j') *
        boolSignComplex (ε (π i')) := by
  classical
  let P : CMatrix (Prod r a) := localReferenceUnitary (a := a) (permutationUnitary π)
  let D : CMatrix (Prod r a) := localReferenceUnitary (a := a) (diagonalSignUnitary ε)
  have hmul :
      (localReferenceUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a)) = P * D := by
    simpa [P, D] using
      localReferenceUnitary_mul (a := a) (U := permutationUnitary π)
        (V := diagonalSignUnitary ε)
  calc
    (((localReferenceUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a)) *
        X *
        star (localReferenceUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a))) (i, j) (i', j')) =
        (P * (D * X * star D) * star P) (i, j) (i', j') := by
          rw [hmul, star_mul]
          simp [P, D, mul_assoc]
    _ = (D * X * star D) (π i, j) (π i', j') := by
          simpa [P] using
            permutationReferenceUnitary_conj_apply (a := a) π
              (D * X * star D) i i' j j'
    _ = boolSignComplex (ε (π i)) * X (π i, j) (π i', j') *
          boolSignComplex (ε (π i')) := by
          simpa [D] using
            diagonalSignReferenceUnitary_conj_apply (a := a) ε X
              (π i) (π i') j j'

/-- Finite sign-permutation depolarizing twirl on the left/reference tensor
factor. -/
def referenceDepolarizingTwirl [Nonempty r] (X : CMatrix (Prod r a)) :
    CMatrix (Prod r a) :=
  ∑ idx : (r → Bool) × Equiv.Perm r,
    ((Fintype.card ((r → Bool) × Equiv.Perm r) : ℂ)⁻¹) •
      ((Matrix.kronecker
          ((permutationUnitary idx.2 * diagonalSignUnitary idx.1 :
            Matrix.unitaryGroup r ℂ) : CMatrix r)
          (1 : CMatrix a)) *
        X *
        star (Matrix.kronecker
          ((permutationUnitary idx.2 * diagonalSignUnitary idx.1 :
            Matrix.unitaryGroup r ℂ) : CMatrix r)
          (1 : CMatrix a)))

/-- The finite local-reference sign-permutation twirl realizes the source
identity `π_R ⊗ Tr_R[X]`.

For `X : CMatrix (Prod r a)`, the reference system is the left tensor factor,
so `Tr_R[X]` is `partialTraceA (a := r) (b := a) X`; using `partialTraceB`
would trace out the application system and leave the wrong type.  This is the
finite sign-permutation version of the depolarizing twirl used in
KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2254-2265. -/
theorem localReferenceTwirl_eq_maximallyMixed_tensor_partialTrace
    [Nonempty r] (X : CMatrix (Prod r a)) :
    referenceDepolarizingTwirl (r := r) (a := a) X =
      Matrix.kronecker (maximallyMixed r).matrix
        (partialTraceA (a := r) (b := a) X) := by
  classical
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  unfold referenceDepolarizingTwirl
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp_rw [← localReferenceUnitary_coe (a := a)]
  simp_rw [localReferenceSignPermutationUnitary_conj_apply]
  simp only [smul_eq_mul]
  rw [← Finset.mul_sum]
  have hS : (Fintype.card (r → Bool) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (r → Bool) ≠ 0)
  have hP : (Fintype.card (Equiv.Perm r) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm r) ≠ 0)
  have hcard :
      ((Fintype.card ((r → Bool) × Equiv.Perm r) : ℂ)⁻¹) =
        (Fintype.card (r → Bool) : ℂ)⁻¹ *
          (Fintype.card (Equiv.Perm r) : ℂ)⁻¹ := by
    rw [Fintype.card_prod]
    rw [Nat.cast_mul]
    field_simp [hS, hP]
  have hcastR :
      ((((Fintype.card r : ℝ)⁻¹ : ℝ) : ℂ)) =
        (Fintype.card r : ℂ)⁻¹ := by
    have hcardR : (Fintype.card r : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card r ≠ 0)
    norm_num [hcardR]
  by_cases hii' : i = i'
  · subst i'
    have hsum :
        (∑ idx : (r → Bool) × Equiv.Perm r,
          boolSignComplex (idx.1 (idx.2 i)) *
              X (idx.2 i, j) (idx.2 i, j') *
            boolSignComplex (idx.1 (idx.2 i))) =
          (Fintype.card (r → Bool) : ℂ) *
            ∑ π : Equiv.Perm r, X (π i, j) (π i, j') := by
      rw [Fintype.sum_prod_type]
      simp [Finset.mul_sum, mul_left_comm, mul_comm]
    rw [hsum, hcard]
    calc
      ((Fintype.card (r → Bool) : ℂ)⁻¹ *
          (Fintype.card (Equiv.Perm r) : ℂ)⁻¹) *
          ((Fintype.card (r → Bool) : ℂ) *
            ∑ π : Equiv.Perm r, X (π i, j) (π i, j')) =
          (Fintype.card (Equiv.Perm r) : ℂ)⁻¹ *
            ∑ π : Equiv.Perm r, X (π i, j) (π i, j') := by
        field_simp [hS, hP]
      _ = (Fintype.card r : ℂ)⁻¹ * ∑ k : r, X (k, j) (k, j') := by
        exact perm_orbit_average_eq_uniform (fun k : r => X (k, j) (k, j')) i
      _ = (Matrix.kronecker (maximallyMixed r).matrix
            (partialTraceA (a := r) (b := a) X)) (i, j) (i, j') := by
        simp [partialTraceA, maximallyMixed_matrix, Matrix.kronecker,
          Matrix.kroneckerMap_apply, hcastR]
  · have hsum :
        (∑ idx : (r → Bool) × Equiv.Perm r,
          boolSignComplex (idx.1 (idx.2 i)) *
              X (idx.2 i, j) (idx.2 i', j') *
            boolSignComplex (idx.1 (idx.2 i'))) = 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_eq_zero ?_
      intro π _
      have hne : π i ≠ π i' := fun h => hii' (π.injective h)
      calc
        (∑ ε : r → Bool,
          boolSignComplex (ε (π i)) *
              X (π i, j) (π i', j') *
            boolSignComplex (ε (π i'))) =
            X (π i, j) (π i', j') *
              (∑ ε : r → Bool,
                boolSignComplex (ε (π i)) * boolSignComplex (ε (π i'))) := by
          simp [Finset.mul_sum, mul_assoc, mul_comm]
        _ = 0 := by
          rw [boolSignComplex_sum_mul_eq_zero_of_ne hne, mul_zero]
    rw [hsum, mul_zero]
    simp [partialTraceA, maximallyMixed_matrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
      hii']

end

end QIT
