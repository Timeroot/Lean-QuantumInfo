/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.StateProduct
import QuantumLib.QIT.States.Purification.Uhlmann
public import QuantumLib.QIT.Information.Entropy.Log2Lemmas

/-!
# Channel alternate expression for sandwiched EA additivity

This module is part of the Khatri--Wilde sandwiched-Renyi additivity proof
spine for entanglement-assisted classical communication.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Pointwise

universe u1 v1 u2 v2

namespace QIT

noncomputable section

private instance fullRankStateSubtypeNonempty
    {a : Type u1} [Fintype a] [DecidableEq a] [Nonempty a] :
    Nonempty {sigma : MState a // sigma.m.PosDef} :=
  ⟨⟨(MState.uniform : MState a), MState.uniform_posDef⟩⟩

namespace MatrixMap

variable {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
variable [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
variable [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]

/-- The output-side weighting map `S_sigma^(alpha)` from the KW CB-norm
expression for sandwiched entanglement-assisted mutual information. -/
def sandwichedSideWeightMap (sigma : MState b1) (alpha : ℝ) : MatrixMap b1 b1 :=
  MatrixMap.ofKraus
    (fun _ : Unit => CFC.rpow sigma.m ((1 - alpha) / (2 * alpha)))

/-- The weighting map acts by conjugation with the sandwiched reference power. -/
theorem sandwichedSideWeightMap_apply
    (sigma : MState b1) (alpha : ℝ) (X : CMatrix b1) :
    sandwichedSideWeightMap sigma alpha X =
      CFC.rpow sigma.m ((1 - alpha) / (2 * alpha)) *
        X *
        (CFC.rpow sigma.m ((1 - alpha) / (2 * alpha))).conjTranspose := by
  simp [sandwichedSideWeightMap, MatrixMap.ofKraus]

/-- Source form of the KW weighting map:
`S_sigma^(alpha)(X) = sigma^s X sigma^s`.  The right-hand Kraus adjoint in
`sandwichedSideWeightMap_apply` is the same matrix because PSD functional
calculus powers are Hermitian. -/
theorem sandwichedSideWeightMap_apply_source
    (sigma : MState b1) (alpha : ℝ) (X : CMatrix b1) :
    sandwichedSideWeightMap sigma alpha X =
      CFC.rpow sigma.m ((1 - alpha) / (2 * alpha)) *
        X *
        CFC.rpow sigma.m ((1 - alpha) / (2 * alpha)) := by
  rw [sandwichedSideWeightMap_apply]
  have hHerm :
      (CFC.rpow sigma.m ((1 - alpha) / (2 * alpha))).IsHermitian :=
    (cMatrix_rpow_posSemidef
      (A := sigma.m) (s := (1 - alpha) / (2 * alpha)) sigma.psd).isHermitian
  rw [hHerm.eq]

/-- The output-side weighting map is completely positive. -/
theorem sandwichedSideWeightMap_completelyPositive
    (sigma : MState b1) (alpha : ℝ) :
    MatrixMap.IsCompletelyPositive (sandwichedSideWeightMap sigma alpha) :=
  MatrixMap.ofKraus_completelyPositive _

/-- The KW output-side weighting map preserves positive semidefinite inputs. -/
theorem sandwichedSideWeightMap_mapsPositive
    (sigma : MState b1) (alpha : ℝ)
    {X : CMatrix b1} (hX : X.PosSemidef) :
    (sandwichedSideWeightMap sigma alpha X).PosSemidef :=
  MatrixMap.isCompletelyPositive_mapsPositive (sandwichedSideWeightMap sigma alpha)
    (sandwichedSideWeightMap_completelyPositive sigma alpha) X hX

/-- Full-rank KW side weighting is injective on matrices.  This is the local
nonzero-preservation fact behind the strict positivity side condition needed
when the source proof takes `log ||S_sigma^(alpha) o N||`. -/
theorem sandwichedSideWeightMap_apply_ne_zero_of_posDef
    (sigma : MState b1) (hsigma : sigma.m.PosDef) (alpha : ℝ)
    {X : CMatrix b1} (hXne : X ≠ 0) :
    sandwichedSideWeightMap sigma alpha X ≠ 0 := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let C : CMatrix b1 := CFC.rpow sigma.m s
  have hC : C.PosDef := by
    simpa [C, s] using cMatrix_rpow_posDef_of_posDef hsigma s
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have hleft : C⁻¹ * C = (1 : CMatrix b1) := Matrix.nonsing_inv_mul C hCdet
  have hright : C * C⁻¹ = (1 : CMatrix b1) := Matrix.mul_nonsing_inv C hCdet
  intro hzero
  have hzeroC : C * X * C = 0 := by
    have h := hzero
    rw [sandwichedSideWeightMap_apply] at h
    change C * X * C.conjTranspose = 0 at h
    rwa [hC.isHermitian.eq] at h
  have hzero' : C⁻¹ * (C * X * C) * C⁻¹ = 0 := by
    rw [hzeroC]
    simp
  have hXzero : X = 0 := by
    calc
      X = (1 : CMatrix b1) * X * (1 : CMatrix b1) := by simp
      _ = (C⁻¹ * C) * X * (C * C⁻¹) := by rw [hleft, hright]
      _ = C⁻¹ * (C * X * C) * C⁻¹ := by noncomm_ring
      _ = 0 := hzero'
  exact hXne hXzero

/-- Reference-tensored KW side weighting is conjugation by
`I_R ⊗ sigma^((1-alpha)/(2 alpha))`. -/
theorem referenceKron_sandwichedSideWeightMap_apply
    (sigma : MState b1) (alpha : ℝ) (X : CMatrix (a1 × b1)) :
    MatrixMap.kron (CPTPOp.id (dIn := a1)).map (sandwichedSideWeightMap sigma alpha) X =
      Matrix.kronecker (1 : CMatrix a1)
          (CFC.rpow sigma.m ((1 - alpha) / (2 * alpha))) *
        X *
        (Matrix.kronecker (1 : CMatrix a1)
          (CFC.rpow sigma.m ((1 - alpha) / (2 * alpha)))).conjTranspose := by
  have hid : (CPTPOp.id (dIn := a1)).map =
      MatrixMap.ofKraus (fun _ : Unit => (1 : CMatrix a1)) := by
    ext Y i j
    simp [MatrixMap.ofKraus]
  rw [hid, sandwichedSideWeightMap,
    MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct]
  simp [MatrixMap.ofKraus, MatrixMap.krausProduct]

/-- Full-rank reference-tensored KW side weighting preserves nonzero matrices. -/
theorem referenceKron_sandwichedSideWeightMap_apply_ne_zero_of_posDef
    (sigma : MState b1) (hsigma : sigma.m.PosDef) (alpha : ℝ)
    {X : CMatrix (a1 × b1)} (hXne : X ≠ 0) :
    MatrixMap.kron (CPTPOp.id (dIn := a1)).map
        (sandwichedSideWeightMap sigma alpha) X ≠ 0 := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let C : CMatrix b1 := CFC.rpow sigma.m s
  let D : CMatrix (a1 × b1) := Matrix.kronecker (1 : CMatrix a1) C
  have hC : C.PosDef := by
    simpa [C, s] using cMatrix_rpow_posDef_of_posDef hsigma s
  have hD : D.PosDef := by
    simpa [D] using Matrix.PosDef.one.kronecker hC
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hleft : D⁻¹ * D = (1 : CMatrix (a1 × b1)) :=
    Matrix.nonsing_inv_mul D hDdet
  have hright : D * D⁻¹ = (1 : CMatrix (a1 × b1)) :=
    Matrix.mul_nonsing_inv D hDdet
  intro hzero
  have hzeroD : D * X * D = 0 := by
    have h := hzero
    rw [referenceKron_sandwichedSideWeightMap_apply] at h
    change D * X * D.conjTranspose = 0 at h
    rwa [hD.isHermitian.eq] at h
  have hzero' : D⁻¹ * (D * X * D) * D⁻¹ = 0 := by
    rw [hzeroD]
    simp
  have hXzero : X = 0 := by
    calc
      X = (1 : CMatrix (a1 × b1)) * X * (1 : CMatrix (a1 × b1)) := by simp
      _ = (D⁻¹ * D) * X * (D * D⁻¹) := by rw [hleft, hright]
      _ = D⁻¹ * (D * X * D) * D⁻¹ := by noncomm_ring
      _ = 0 := hzero'
  exact hXne hXzero

/-- The source CB `1 → alpha` norm is nonnegative because it is the supremum
of nonnegative admissible values. -/
theorem cbOneToAlphaNorm_nonneg
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) :
    0 ≤ MatrixMap.cbOneToAlphaNorm Phi hPhi alpha := by
  unfold MatrixMap.cbOneToAlphaNorm MatrixMap.cbOneToAlphaOriginalValueSet
  exact Real.sSup_nonneg (by
    rintro x ⟨Y, rfl⟩
    exact MatrixMap.cbOneToAlphaOriginalValue_nonneg Phi hPhi Y alpha)

/-- Reference lifting preserves trace when the underlying matrix map does.
This is the trace-preserving half of the source `id_R ⊗ Phi` construction. -/
theorem referenceLift_isTracePreserving
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsTracePreserving Phi) :
    MatrixMap.IsTracePreserving Phi.referenceLift :=
  MatrixMap.IsTracePreserving.kron (CPTPOp.id (dIn := a1)).map_TP hPhi

/-- A trace-preserving map cannot send a nonzero positive semidefinite input
to zero, because that would force the input trace to vanish. -/
theorem isTracePreserving_apply_ne_zero_of_posSemidef
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsTracePreserving Phi)
    {X : CMatrix a1} (hX : X.PosSemidef) (hXne : X ≠ 0) :
    Phi X ≠ 0 := by
  intro hzero
  have htrace_zero : X.trace = 0 := by
    have htrace := hPhi X
    rw [hzero] at htrace
    simpa using htrace.symm
  have hXzero : X = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hX).mp htrace_zero
  exact hXne hXzero

/-- Reference-lifted trace-preserving maps preserve nonzero PSD inputs. -/
theorem referenceLift_apply_ne_zero_of_tracePreserving
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsTracePreserving Phi)
    {X : CMatrix (a1 × a1)} (hX : X.PosSemidef) (hXne : X ≠ 0) :
    Phi.referenceLift X ≠ 0 :=
  isTracePreserving_apply_ne_zero_of_posSemidef Phi.referenceLift
    (referenceLift_isTracePreserving Phi hPhi) hX hXne

omit [DecidableEq a1] in
/-- A positive-definite finite matrix on a nonempty system is nonzero. -/
theorem cMatrix_ne_zero_of_posDef [Nonempty a1]
    {X : CMatrix a1} (hX : X.PosDef) :
    X ≠ 0 := by
  intro hzero
  have htrace : (0 : ℂ) < X.trace := Matrix.PosDef.trace_pos hX
  rw [hzero] at htrace
  norm_num at htrace

/-- The source Choi/Gamma CB input is nonzero for full-rank reference-side
weights. -/
theorem cbOneToAlphaOriginalInput_ne_zero_of_posDef
    [Nonempty a1] {Y : CMatrix a1} (hY : Y.PosDef)
    {alpha : ℝ} (halpha : 0 < alpha) :
    cbOneToAlphaOriginalInput Y alpha ≠ 0 := by
  intro hzero
  have hpartial_zero :
      Matrix.traceRight (cbOneToAlphaOriginalInput Y alpha) = 0 := by
    rw [hzero]
    ext i j
    change (∑ k : a1, (0 : CMatrix (a1 × a1)) (i, k) (j, k)) = 0
    simp
  have hrpow_zero : CFC.rpow Y (1 / alpha) = 0 := by
    rw [← traceRight_cbOneToAlphaOriginalInput_eq_rpow
      (a := a1) hY.posSemidef halpha]
    exact hpartial_zero
  exact cMatrix_ne_zero_of_posDef
    (cMatrix_rpow_posDef_of_posDef hY (1 / alpha)) hrpow_zero

/-- The source Choi/Gamma CB input is nonzero for every normalized state.

This is the trace-one endpoint needed in KW `EA_capacity.tex:2090-2093` after
the `Tr[Y_R] = 1` reduction: positive definiteness of the state is not needed,
only normalization. -/
theorem cbOneToAlphaOriginalInput_ne_zero_of_state
    (tau : MState a1) {alpha : ℝ} (halpha : 0 < alpha) :
    cbOneToAlphaOriginalInput tau.m alpha ≠ 0 := by
  intro hzero
  have hpartial_zero :
      Matrix.traceRight
          (cbOneToAlphaOriginalInput tau.m alpha) = 0 := by
    rw [hzero]
    ext i j
    change (∑ k : a1, (0 : CMatrix (a1 × a1)) (i, k) (j, k)) = 0
    simp
  have hrpow_zero : CFC.rpow tau.m (1 / alpha) = 0 := by
    rw [← traceRight_cbOneToAlphaOriginalInput_eq_rpow
      (a := a1) tau.psd halpha]
    exact hpartial_zero
  have hnorm_zero :
      psdSchattenPNorm (CFC.rpow tau.m (1 / alpha))
          (tau.rpowMatrix_posSemidef (1 / alpha))
          (SchattenOrder.ofPositive halpha) = 0 := by
    calc
      psdSchattenPNorm (CFC.rpow tau.m (1 / alpha))
          (tau.rpowMatrix_posSemidef (1 / alpha))
          (SchattenOrder.ofPositive halpha) =
        psdSchattenPNorm (0 : CMatrix a1) Matrix.PosSemidef.zero
          (SchattenOrder.ofPositive halpha) := by
          exact psdSchattenPNorm_congr hrpow_zero _ Matrix.PosSemidef.zero
            (SchattenOrder.ofPositive halpha)
      _ = 0 := psdSchattenPNorm_zero (SchattenOrder.ofPositive halpha)
  have hone :=
    MState.state_rpow_one_div_psdSchattenPNorm_eq_one_psd tau halpha
  rw [hone] at hnorm_zero
  norm_num at hnorm_zero

/-- The maximally mixed reference gives a nonzero source Choi/Gamma CB input. -/
theorem cbOneToAlphaOriginalInput_uniform_ne_zero
    [Nonempty a1] {alpha : ℝ} (halpha : 0 < alpha) :
    cbOneToAlphaOriginalInput (MState.uniform : MState a1).m alpha ≠ 0 :=
  cbOneToAlphaOriginalInput_ne_zero_of_posDef
    (MState.uniform_posDef (d := a1)) halpha

/-- The maximally mixed source-side CB candidate has strictly positive value
for any trace-preserving completely positive map. -/
theorem cbOneToAlphaOriginalValue_uniform_pos_of_tracePreserving
    [Nonempty a1] (Phi : MatrixMap a1 b1)
    (hPhiCP : MatrixMap.IsCompletelyPositive Phi)
    (hPhiTP : MatrixMap.IsTracePreserving Phi)
    {alpha : ℝ} (halpha : 0 < alpha) :
    0 <
      cbOneToAlphaOriginalValue Phi hPhiCP
        { matrix := (MState.uniform : MState a1).m,
          pos := (MState.uniform : MState a1).psd,
          trace_le_one := by
            rw [(MState.uniform : MState a1).tr']
            norm_num }
        (SchattenOrder.ofPositive halpha) := by
  let Y0 : CBOneToAlphaOriginalDomain a1 :=
    { matrix := (MState.uniform : MState a1).m,
      pos := (MState.uniform : MState a1).psd,
      trace_le_one := by
        rw [(MState.uniform : MState a1).tr']
        norm_num }
  let X : CMatrix (a1 × a1) := cbOneToAlphaOriginalInput Y0.matrix alpha
  let hX : X.PosSemidef := cbOneToAlphaOriginalInput_posSemidef Y0.pos alpha
  have hXne : X ≠ 0 := by
    simpa [X, Y0] using cbOneToAlphaOriginalInput_uniform_ne_zero
      (a1 := a1) halpha
  have hPhiXne : Phi.referenceLift X ≠ 0 :=
    referenceLift_apply_ne_zero_of_tracePreserving Phi hPhiTP hX hXne
  unfold cbOneToAlphaOriginalValue
  change 0 < psdSchattenPNorm (Phi.referenceLift X) _
    (SchattenOrder.ofPositive halpha)
  exact psdSchattenPNorm_pos_of_ne_zero (Phi.referenceLift X) _ hPhiXne

/-- A zero-trace PSD source-side input gives the zero Choi/Gamma CB input.

This is the zero-boundary branch of KW `EA_capacity.tex:2088-2093`: when the
trace-normalized source variable has zero trace, it contributes zero to the
CB `1 → alpha` supremum before the trace-one normalization step. -/
theorem cbOneToAlphaOriginalInput_eq_zero_of_trace_zero
    {Y : CMatrix a1} (hY : Y.PosSemidef)
    {alpha : ℝ} (halpha : 0 < alpha)
    (htrace : Y.trace.re = 0) :
    cbOneToAlphaOriginalInput Y alpha = 0 := by
  have hYtrace : Y.trace = 0 := by
    apply Complex.ext
    · simpa using htrace
    · simpa using (Matrix.PosSemidef.trace_nonneg hY).2.symm
  have hYzero : Y = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hY).mp hYtrace
  have hexp_ne : 1 / (2 * alpha) ≠ 0 :=
    one_div_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt halpha))
  unfold cbOneToAlphaOriginalInput cbOneToAlphaReferenceWeight
  rw [hYzero, CFC.zero_rpow (A := CMatrix a1) hexp_ne]
  simp [Matrix.kronecker]

/-- Zero-trace source-side inputs contribute zero to the source Choi/Gamma
CB-norm value.

This is the scalar-value form of
`cbOneToAlphaOriginalInput_eq_zero_of_trace_zero`, used before replacing a
nonzero subnormalized source variable by its normalized trace-one state. -/
theorem cbOneToAlphaOriginalValue_eq_zero_of_trace_zero
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Y : CBOneToAlphaOriginalDomain a1)
    {alpha : ℝ} (halpha : 0 < alpha)
    (htrace : Y.matrix.trace.re = 0) :
    cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofPositive halpha) = 0 := by
  let X : CMatrix (a1 × a1) := cbOneToAlphaOriginalInput Y.matrix alpha
  let hX : X.PosSemidef := cbOneToAlphaOriginalInput_posSemidef Y.pos alpha
  have hXzero : X = 0 := by
    simpa [X] using
      cbOneToAlphaOriginalInput_eq_zero_of_trace_zero Y.pos halpha htrace
  have hPhiXpos : (Phi.referenceLift X).PosSemidef :=
    Phi.referenceLift_mapsPositive hPhi hX
  have hPhiXzero : Phi.referenceLift X = 0 := by
    rw [hXzero]
    exact map_zero Phi.referenceLift
  unfold cbOneToAlphaOriginalValue
  change psdSchattenPNorm (Phi.referenceLift X) _
    (SchattenOrder.ofPositive halpha) = 0
  calc
    psdSchattenPNorm (Phi.referenceLift X) _ (SchattenOrder.ofPositive halpha) =
        psdSchattenPNorm (0 : CMatrix (a1 × b1))
          Matrix.PosSemidef.zero (SchattenOrder.ofPositive halpha) := by
          exact psdSchattenPNorm_congr hPhiXzero hPhiXpos
            Matrix.PosSemidef.zero (SchattenOrder.ofPositive halpha)
    _ = 0 := psdSchattenPNorm_zero (SchattenOrder.ofPositive halpha)

/-- A trace-one state as a source-side CB original-domain point. -/
def CBOneToAlphaOriginalDomain.ofState (tau : MState a1) :
    CBOneToAlphaOriginalDomain a1 where
  matrix := tau.m
  pos := tau.psd
  trace_le_one := by
    rw [tau.tr']
    norm_num

/-- A nonzero source CB original-domain point is its normalized state times
its trace.

This is the matrix normalization step in KW `EA_capacity.tex:2088-2093`,
before proving that the source CB supremum can be restricted to `Tr[Y] = 1`. -/
theorem cbOneToAlphaOriginalDomain_matrix_eq_trace_smul_normalize
    (Y : CBOneToAlphaOriginalDomain a1)
    (htrace : Y.matrix.trace.re ≠ 0) :
    let ρ : SubnormalizedState a1 :=
      { matrix := Y.matrix, pos := Y.pos, trace_le_one := Y.trace_le_one }
    Y.matrix = Y.matrix.trace.re • (ρ.normalize htrace).m := by
  intro ρ
  have hscale : Y.matrix.trace.re * (Y.matrix.trace.re)⁻¹ = 1 := by
    exact mul_inv_cancel₀ htrace
  rw [SubnormalizedState.normalize_matrix]
  change Y.matrix = Y.matrix.trace.re • ((Y.matrix.trace.re)⁻¹ • Y.matrix)
  rw [smul_smul, hscale, one_smul]

/-- Positive real scaling pulls through the source-side CB reference weight.

This is the homogeneous part of the KW trace-normalization step
`EA_capacity.tex:2088-2093`. -/
theorem cbOneToAlphaReferenceWeight_pos_real_smul
    {Y : CMatrix a1} (hY : Y.PosSemidef)
    {t alpha : ℝ} (ht : 0 < t) (_halpha : 0 < alpha) :
    cbOneToAlphaReferenceWeight (t • Y : CMatrix a1) alpha =
      (t ^ (1 / (2 * alpha)) : ℝ) • cbOneToAlphaReferenceWeight Y alpha := by
  unfold cbOneToAlphaReferenceWeight
  rw [cMatrix_rpow_real_smul_posSemidef_schatten hY (le_of_lt ht)]
  ext p q
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, mul_assoc]

/-- Positive real scaling of the source-side CB original input.

If `Y = t tau` with `t > 0`, then the weighted Choi/Gamma input scales by
`t^(1/alpha)`.  This is the algebraic heart of KW
`EA_capacity.tex:2088-2093`. -/
theorem cbOneToAlphaOriginalInput_pos_real_smul
    {Y : CMatrix a1} (hY : Y.PosSemidef)
    {t alpha : ℝ} (ht : 0 < t) (halpha : 0 < alpha) :
    cbOneToAlphaOriginalInput (t • Y : CMatrix a1) alpha =
      (t ^ (1 / alpha) : ℝ) • cbOneToAlphaOriginalInput Y alpha := by
  let c : ℝ := t ^ (1 / (2 * alpha))
  have hW :
      cbOneToAlphaReferenceWeight (t • Y : CMatrix a1) alpha =
        c • cbOneToAlphaReferenceWeight Y alpha := by
    simpa [c] using cbOneToAlphaReferenceWeight_pos_real_smul
      (a1 := a1) hY ht halpha
  have hc_mul : c * c = t ^ (1 / alpha) := by
    have hexp : 1 / alpha = 1 / (2 * alpha) + 1 / (2 * alpha) := by
      field_simp [ne_of_gt halpha]
      ring
    rw [hexp, Real.rpow_add ht]
  unfold cbOneToAlphaOriginalInput
  rw [hW]
  simp [hc_mul, smul_smul, mul_assoc]

/-- Positive real scaling of the source-side CB original value.

This is the value-level homogeneous step in KW `EA_capacity.tex:2088-2093`:
once a subnormalized source variable is written as `t • tau`, the corresponding
CB value is multiplied by `t^(1/alpha)`. -/
theorem cbOneToAlphaOriginalValue_eq_rpow_mul_of_matrix_eq_pos_real_smul
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Y : CBOneToAlphaOriginalDomain a1) (tau : MState a1)
    {t alpha : ℝ} (ht : 0 < t) (halpha : 0 < alpha)
    (hY : Y.matrix = t • tau.m) :
    cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofPositive halpha) =
      t ^ (1 / alpha) *
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau)
          (SchattenOrder.ofPositive halpha) := by
  let lambda : ℝ := t ^ (1 / alpha)
  let Xtau : CMatrix (a1 × a1) := cbOneToAlphaOriginalInput tau.m alpha
  let hXtau : Xtau.PosSemidef := cbOneToAlphaOriginalInput_posSemidef tau.psd alpha
  let XY : CMatrix (a1 × a1) := cbOneToAlphaOriginalInput Y.matrix alpha
  let hXY : XY.PosSemidef := cbOneToAlphaOriginalInput_posSemidef Y.pos alpha
  have hlambda_nonneg : 0 ≤ lambda := Real.rpow_nonneg (le_of_lt ht) (1 / alpha)
  have hinput :
      XY = lambda • Xtau := by
    dsimp [XY, Xtau, lambda]
    rw [hY]
    exact cbOneToAlphaOriginalInput_pos_real_smul tau.psd ht halpha
  have hPhiXtau :
      (Phi.referenceLift Xtau).PosSemidef :=
    Phi.referenceLift_mapsPositive hPhi hXtau
  have hPhiScaled :
      (lambda • Phi.referenceLift Xtau : CMatrix (a1 × b1)).PosSemidef :=
    Matrix.PosSemidef.smul hPhiXtau hlambda_nonneg
  have hPhiXY :
      Phi.referenceLift XY = lambda • Phi.referenceLift Xtau := by
    rw [hinput]
    exact LinearMap.map_smul_of_tower Phi.referenceLift lambda Xtau
  unfold cbOneToAlphaOriginalValue
  calc
    psdSchattenPNorm (Phi.referenceLift XY) _ (SchattenOrder.ofPositive halpha) =
        psdSchattenPNorm (lambda • Phi.referenceLift Xtau) hPhiScaled
          (SchattenOrder.ofPositive halpha) := by
          exact psdSchattenPNorm_congr hPhiXY _ hPhiScaled
            (SchattenOrder.ofPositive halpha)
    _ =
        lambda * psdSchattenPNorm (Phi.referenceLift Xtau) hPhiXtau
          (SchattenOrder.ofPositive halpha) := by
          rw [psdSchattenPNorm_real_smul hPhiXtau hlambda_nonneg
            (SchattenOrder.ofPositive halpha)]
    _ =
        t ^ (1 / alpha) *
          psdSchattenPNorm
            (Phi.referenceLift
              (cbOneToAlphaOriginalInput
                (CBOneToAlphaOriginalDomain.ofState tau).matrix alpha))
            _ (SchattenOrder.ofPositive halpha) := by
          simp [lambda, Xtau, CBOneToAlphaOriginalDomain.ofState]

/-- Source concavity for the trace-normalized induced `alpha → alpha` value.

This is the `Y ↦ ||Phi(Y^(1/alpha))||_alpha` form of KW
`EA_capacity.tex:2080-2084`, specialized to the trace-normalized domain used
by the CB complement bridge.  The theorem is the finite-dimensional
bookkeeping wrapper around
`cp_psdSchatten_rpow_value_concave`. -/
theorem alphaToAlphaTraceValue_mix_le
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha lambda : ℝ} (halpha : 1 < alpha)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (Y0 Y1 : AlphaToAlphaTraceDomain a1 (SchattenOrder.ofOneLt halpha)) :
    lambda * alphaToAlphaTraceValue Phi hPhi Y0 +
        (1 - lambda) * alphaToAlphaTraceValue Phi hPhi Y1 ≤
      alphaToAlphaTraceValue (alpha := SchattenOrder.ofOneLt halpha) Phi hPhi
        { matrix := lambda • Y0.matrix + (1 - lambda) • Y1.matrix,
          pos :=
            Matrix.PosSemidef.add
              (Matrix.PosSemidef.smul Y0.pos hlambda0)
              (Matrix.PosSemidef.smul Y1.pos (sub_nonneg.mpr hlambda1)),
          trace_le_one := by
            calc
              ((lambda • Y0.matrix + (1 - lambda) • Y1.matrix).trace).re =
                  lambda * Y0.matrix.trace.re + (1 - lambda) * Y1.matrix.trace.re := by
                    simp [Matrix.trace_add, Matrix.trace_smul]
              _ ≤ lambda * 1 + (1 - lambda) * 1 := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left Y0.trace_le_one hlambda0)
                      (mul_le_mul_of_nonneg_left Y1.trace_le_one
                        (sub_nonneg.mpr hlambda1))
              _ = 1 := by ring } := by
  exact cp_psdSchatten_rpow_value_concave
    Phi hPhi halpha hlambda0 hlambda1 Y0.pos Y1.pos

/-- Concavity of the KW source-side CB original value in the normalized
source input.

This is the `tau_R`-side mathematical condition used in the channel Sion step
KW `EA_capacity.tex:2080-2084`: for fixed weighted channel map, the function
`tau ↦ ||(id ⊗ Phi)(Γ_tau)||_alpha` is concave on normalized source states.
The proof follows the source route already formalized locally: pass through the
complement trace-domain representation and apply
`alphaToAlphaTraceValue_mix_le`. -/
theorem cbOneToAlphaOriginalValue_ofState_mix_le
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha lambda : ℝ} (halpha : 1 < alpha)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (tau0 tau1 : MState a1) :
    lambda *
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau0)
          (SchattenOrder.ofOneLt halpha) +
      (1 - lambda) *
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau1)
          (SchattenOrder.ofOneLt halpha) ≤
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState
            (MState.ofMatrix (matrix := lambda • tau0.m + (1 - lambda) • tau1.m)
              (pos :=
                Matrix.PosSemidef.add
                  (Matrix.PosSemidef.smul tau0.psd hlambda0)
                  (Matrix.PosSemidef.smul tau1.psd (sub_nonneg.mpr hlambda1)))
              (trace_eq_one := by
                rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                  tau0.tr', tau1.tr']
                norm_num))) (SchattenOrder.ofOneLt halpha) := by
  let tauMix : MState a1 :=
    .ofMatrix (matrix := lambda • tau0.m + (1 - lambda) • tau1.m)
      (pos :=
        Matrix.PosSemidef.add
          (Matrix.PosSemidef.smul tau0.psd hlambda0)
          (Matrix.PosSemidef.smul tau1.psd (sub_nonneg.mpr hlambda1)))
      (trace_eq_one := by
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
          tau0.tr', tau1.tr']
        norm_num)
  let PhiC : MatrixMap a1 (a1 × b1) := MatrixMap.cpComplement Phi hPhi
  let hPhiC : MatrixMap.IsCompletelyPositive PhiC :=
    MatrixMap.cpComplement_isCompletelyPositive Phi hPhi
  let Y0 : AlphaToAlphaTraceDomain a1 (SchattenOrder.ofOneLt halpha) :=
    (CBOneToAlphaOriginalDomain.ofState tau0).toTransposeTraceDomain
      (alpha := alpha) (lt_trans zero_lt_one halpha)
  let Y1 : AlphaToAlphaTraceDomain a1 (SchattenOrder.ofOneLt halpha) :=
    (CBOneToAlphaOriginalDomain.ofState tau1).toTransposeTraceDomain
      (alpha := alpha) (lt_trans zero_lt_one halpha)
  have hconc := alphaToAlphaTraceValue_mix_le
    PhiC hPhiC halpha hlambda0 hlambda1 Y0 Y1
  have h0 :
      cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau0)
          (SchattenOrder.ofOneLt halpha) =
        alphaToAlphaTraceValue PhiC hPhiC Y0 := by
    exact cbOneToAlphaOriginalValue_eq_cpComplement_alphaToAlphaTraceValue_transpose
      Phi hPhi (lt_trans zero_lt_one halpha)
      (CBOneToAlphaOriginalDomain.ofState tau0)
  have h1 :
      cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau1)
          (SchattenOrder.ofOneLt halpha) =
        alphaToAlphaTraceValue PhiC hPhiC Y1 := by
    exact cbOneToAlphaOriginalValue_eq_cpComplement_alphaToAlphaTraceValue_transpose
      Phi hPhi (lt_trans zero_lt_one halpha)
      (CBOneToAlphaOriginalDomain.ofState tau1)
  have hmix :
      cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tauMix)
          (SchattenOrder.ofOneLt halpha) =
        alphaToAlphaTraceValue (alpha := SchattenOrder.ofOneLt halpha) PhiC hPhiC
          { matrix := lambda • Y0.matrix + (1 - lambda) • Y1.matrix,
            pos :=
              Matrix.PosSemidef.add
                (Matrix.PosSemidef.smul Y0.pos hlambda0)
                (Matrix.PosSemidef.smul Y1.pos (sub_nonneg.mpr hlambda1)),
            trace_le_one := by
              calc
                ((lambda • Y0.matrix + (1 - lambda) • Y1.matrix).trace).re =
                    lambda * Y0.matrix.trace.re +
                      (1 - lambda) * Y1.matrix.trace.re := by
                    simp [Matrix.trace_add, Matrix.trace_smul]
                _ ≤ lambda * 1 + (1 - lambda) * 1 := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left Y0.trace_le_one hlambda0)
                      (mul_le_mul_of_nonneg_left Y1.trace_le_one
                        (sub_nonneg.mpr hlambda1))
                _ = 1 := by ring } := by
    refine Eq.trans
      (cbOneToAlphaOriginalValue_eq_cpComplement_alphaToAlphaTraceValue_transpose
        Phi hPhi (lt_trans zero_lt_one halpha)
        (CBOneToAlphaOriginalDomain.ofState tauMix))
      (alphaToAlphaTraceValue_congr _ _ ?_)
    simp only [tauMix, Y0, Y1, CBOneToAlphaOriginalDomain.toTransposeTraceDomain,
      CBOneToAlphaOriginalDomain.ofState, MState.matrix_ofMatrix,
      Matrix.transpose_add, Matrix.transpose_smul]
  have hgoal :
      lambda *
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau0)
            (SchattenOrder.ofOneLt halpha) +
        (1 - lambda) *
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau1)
            (SchattenOrder.ofOneLt halpha) ≤
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tauMix)
            (SchattenOrder.ofOneLt halpha) := by
    rw [h0, h1, hmix]
    exact hconc
  simpa [tauMix] using hgoal

/-- Quasiconcavity-style two-point consequence of the KW source-side
concavity theorem.

This is the scalar `min ≤ mixed value` form needed by Sion's
`QuasiconcaveOn` hypothesis for the source variable in
KW `EA_capacity.tex:2080-2084`. -/
theorem cbOneToAlphaOriginalValue_ofState_min_le_mix
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha lambda : ℝ} (halpha : 1 < alpha)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (tau0 tau1 : MState a1) :
    min
        (cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau0) (SchattenOrder.ofOneLt halpha))
        (cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau1) (SchattenOrder.ofOneLt halpha)) ≤
      cbOneToAlphaOriginalValue Phi hPhi
        (CBOneToAlphaOriginalDomain.ofState
          (MState.ofMatrix (matrix := lambda • tau0.m + (1 - lambda) • tau1.m)
            (pos :=
              Matrix.PosSemidef.add
                (Matrix.PosSemidef.smul tau0.psd hlambda0)
                (Matrix.PosSemidef.smul tau1.psd (sub_nonneg.mpr hlambda1)))
            (trace_eq_one := by
              rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                tau0.tr', tau1.tr']
              norm_num))) (SchattenOrder.ofOneLt halpha) := by
  let v0 : ℝ :=
    cbOneToAlphaOriginalValue Phi hPhi
      (CBOneToAlphaOriginalDomain.ofState tau0) (SchattenOrder.ofOneLt halpha)
  let v1 : ℝ :=
    cbOneToAlphaOriginalValue Phi hPhi
      (CBOneToAlphaOriginalDomain.ofState tau1) (SchattenOrder.ofOneLt halpha)
  let tauMix : MState a1 :=
    .ofMatrix (matrix := lambda • tau0.m + (1 - lambda) • tau1.m)
      (pos :=
        Matrix.PosSemidef.add
          (Matrix.PosSemidef.smul tau0.psd hlambda0)
          (Matrix.PosSemidef.smul tau1.psd (sub_nonneg.mpr hlambda1)))
      (trace_eq_one := by
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
          tau0.tr', tau1.tr']
        norm_num)
  have hmix :=
    cbOneToAlphaOriginalValue_ofState_mix_le
      Phi hPhi halpha hlambda0 hlambda1 tau0 tau1
  have hweighted :
      min v0 v1 ≤ lambda * v0 + (1 - lambda) * v1 := by
    calc
      min v0 v1 =
          lambda * min v0 v1 + (1 - lambda) * min v0 v1 := by ring
      _ ≤ lambda * v0 + (1 - lambda) * v1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (min_le_left v0 v1) hlambda0)
            (mul_le_mul_of_nonneg_left (min_le_right v0 v1)
              (sub_nonneg.mpr hlambda1))
  exact hweighted.trans (by simpa [v0, v1, tauMix] using hmix)

/-- Every source original-domain CB candidate is bounded by a trace-one state
candidate.

This formalizes KW `EA_capacity.tex:2090`: after splitting off the trace of
`Y_R`, a nonzero subnormalized candidate is a positive scalar multiple of its
normalized state, and the scalar factor is at most one. -/
theorem exists_state_cbOneToAlphaOriginalValue_ge
    [Nonempty a1]
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 0 < alpha) (Y : CBOneToAlphaOriginalDomain a1) :
    ∃ tau : MState a1,
      cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofPositive halpha) ≤
        cbOneToAlphaOriginalValue Phi hPhi
          (CBOneToAlphaOriginalDomain.ofState tau)
          (SchattenOrder.ofPositive halpha) := by
  by_cases htrace : Y.matrix.trace.re = 0
  · refine ⟨(MState.uniform : MState a1), ?_⟩
    rw [cbOneToAlphaOriginalValue_eq_zero_of_trace_zero Phi hPhi Y halpha htrace]
    exact cbOneToAlphaOriginalValue_nonneg Phi hPhi
      (CBOneToAlphaOriginalDomain.ofState (MState.uniform : MState a1))
      (SchattenOrder.ofPositive halpha)
  · let ρ : SubnormalizedState a1 :=
      { matrix := Y.matrix, pos := Y.pos, trace_le_one := Y.trace_le_one }
    let tau : MState a1 := ρ.normalize htrace
    refine ⟨tau, ?_⟩
    have ht : 0 < Y.matrix.trace.re := by
      simpa [ρ] using ρ.trace_pos_of_trace_ne_zero htrace
    have hY :
        Y.matrix = Y.matrix.trace.re • tau.m := by
      simpa [ρ, tau] using
        cbOneToAlphaOriginalDomain_matrix_eq_trace_smul_normalize Y htrace
    have hvalue :
        cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofPositive halpha) =
          Y.matrix.trace.re ^ (1 / alpha) *
            cbOneToAlphaOriginalValue Phi hPhi
              (CBOneToAlphaOriginalDomain.ofState tau)
              (SchattenOrder.ofPositive halpha) := by
      exact cbOneToAlphaOriginalValue_eq_rpow_mul_of_matrix_eq_pos_real_smul
        Phi hPhi Y tau ht halpha hY
    have hscale :
        Y.matrix.trace.re ^ (1 / alpha) ≤ 1 := by
      have htrace_nonneg : 0 ≤ Y.matrix.trace.re :=
        (Matrix.PosSemidef.trace_nonneg Y.pos).1
      have hinv_nonneg : 0 ≤ 1 / alpha :=
        one_div_nonneg.mpr (le_of_lt halpha)
      exact Real.rpow_le_one htrace_nonneg Y.trace_le_one hinv_nonneg
    have hstate_nonneg :
        0 ≤
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofPositive halpha) :=
      cbOneToAlphaOriginalValue_nonneg Phi hPhi
        (CBOneToAlphaOriginalDomain.ofState tau) (SchattenOrder.ofPositive halpha)
    rw [hvalue]
    calc
      Y.matrix.trace.re ^ (1 / alpha) *
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofPositive halpha) ≤
        1 *
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofPositive halpha) := by
          exact mul_le_mul_of_nonneg_right hscale hstate_nonneg
      _ =
          cbOneToAlphaOriginalValue Phi hPhi
            (CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofPositive halpha) := by
          rw [one_mul]

/-- Source CB original values restricted to trace-one state candidates. -/
def cbOneToAlphaStateOriginalValueSet
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) : Set ℝ :=
  Set.range fun tau : MState a1 =>
    cbOneToAlphaOriginalValue Phi hPhi
      (CBOneToAlphaOriginalDomain.ofState tau) alpha

/-- The source CB norm supremum is unchanged after restricting the source
variable to trace-one state candidates.

This is the formal Lean interface for the final sentence of KW
`EA_capacity.tex:2090-2093`. -/
theorem cbOneToAlphaNorm_eq_sSup_stateOriginalValueSet_of_one_lt
    [Nonempty a1]
    (Phi : MatrixMap a1 b1) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) =
      sSup (cbOneToAlphaStateOriginalValueSet Phi hPhi
        (SchattenOrder.ofOneLt halpha)) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hbddState :
      BddAbove (cbOneToAlphaStateOriginalValueSet Phi hPhi
        (SchattenOrder.ofOneLt halpha)) := by
    refine ⟨cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha), ?_⟩
    rintro y ⟨tau, rfl⟩
    exact cbOneToAlphaOriginalValue_le_cbOneToAlphaNorm_of_one_lt
      Phi hPhi halpha (CBOneToAlphaOriginalDomain.ofState tau)
  have : Nonempty (MState a1) := ⟨(MState.uniform : MState a1)⟩
  have : Nonempty (CBOneToAlphaOriginalDomain a1) :=
    ⟨CBOneToAlphaOriginalDomain.ofState (MState.uniform : MState a1)⟩
  refine le_antisymm ?_ ?_
  · unfold cbOneToAlphaNorm cbOneToAlphaOriginalValueSet
    refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨Y, rfl⟩
    rcases exists_state_cbOneToAlphaOriginalValue_ge
        Phi hPhi halpha_pos Y with ⟨tau, hleTau⟩
    exact hleTau.trans
      (le_csSup hbddState
        ⟨tau, rfl⟩)
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro y ⟨tau, rfl⟩
    exact cbOneToAlphaOriginalValue_le_cbOneToAlphaNorm_of_one_lt
      Phi hPhi halpha (CBOneToAlphaOriginalDomain.ofState tau)

/-- For full-rank product references, the KW output-side weighting map
factorizes as a tensor product.  This is the `S_{sigma_1 ⊗ sigma_2}` identity
used in `EA_capacity.tex:1242-1254`. -/
theorem sandwichedSideWeightMap_prod_posDef
    (sigma1 : MState b1) (sigma2 : MState b2)
    (hsigma1 : sigma1.m.PosDef) (hsigma2 : sigma2.m.PosDef)
    (alpha : ℝ) :
    sandwichedSideWeightMap (sigma1.prod sigma2) alpha =
      MatrixMap.kron (sandwichedSideWeightMap sigma1 alpha)
        (sandwichedSideWeightMap sigma2 alpha) := by
  unfold sandwichedSideWeightMap
  rw [MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct]
  ext X bd bd'
  simp [MatrixMap.ofKraus, MatrixMap.krausProduct]
  change
    (CFC.rpow (Matrix.kronecker sigma1.m sigma2.m)
          ((1 - alpha) / (2 * alpha)) *
        X *
        (CFC.rpow (Matrix.kronecker sigma1.m sigma2.m)
          ((1 - alpha) / (2 * alpha))).conjTranspose)
        bd bd' =
      (Matrix.kronecker
          (CFC.rpow sigma1.m ((1 - alpha) / (2 * alpha)))
          (CFC.rpow sigma2.m ((1 - alpha) / (2 * alpha))) *
        X *
        (Matrix.kronecker
          (CFC.rpow sigma1.m ((1 - alpha) / (2 * alpha)))
          (CFC.rpow sigma2.m ((1 - alpha) / (2 * alpha)))).conjTranspose)
        bd bd'
  rw [cMatrix_rpow_kronecker hsigma1.posSemidef hsigma2.posSemidef ((1 - alpha) / (2 * alpha))]

/-- Reference lifting commutes with composition in the expected
`id_R ⊗ (Psi o Phi)` form. -/
theorem referenceLift_comp_apply
    (Psi : MatrixMap b1 b2) (Phi : MatrixMap a1 b1)
    (X : CMatrix (a1 × a1)) :
    MatrixMap.referenceLift (Psi.comp Phi) X =
      MatrixMap.kron (CPTPOp.id (dIn := a1)).map Psi (MatrixMap.referenceLift Phi X) := by
  symm
  change MatrixMap.kron (CPTPOp.id (dIn := a1)).map Psi
      (MatrixMap.kron (CPTPOp.id (dIn := a1)).map Phi X) =
    MatrixMap.kron (CPTPOp.id (dIn := a1)).map (Psi.comp Phi) X
  rw [kron_comp_apply_general
    (CPTPOp.id (dIn := a1)).map Psi (CPTPOp.id (dIn := a1)).map Phi X]
  have hid :
      ((CPTPOp.id (dIn := a1)).map.comp (CPTPOp.id (dIn := a1)).map) =
        (CPTPOp.id (dIn := a1)).map := by
    ext Y i j
    simp
  rw [hid]

/-- A reference lift commutes with sandwiching by a matrix acting only on the
reference register.

This is the matrix-map form of the KW polar-decomposition step where the
reference factor `tau_R^s` is absorbed into the Choi/Gamma input before the
channel acts on the second tensor factor. -/
theorem referenceLift_referenceSandwich
    (Phi : MatrixMap a1 b1) (W : CMatrix a1) (X : CMatrix (a1 × a1)) :
    MatrixMap.referenceLift Phi
        (Matrix.kronecker W (1 : CMatrix a1) *
          X *
          Matrix.kronecker W (1 : CMatrix a1)) =
      Matrix.kronecker W (1 : CMatrix b1) *
        MatrixMap.referenceLift Phi X *
        Matrix.kronecker W (1 : CMatrix b1) := by
  classical
  ext rb rb'
  rcases rb with ⟨r, b⟩
  rcases rb' with ⟨r', b'⟩
  simp only [MatrixMap.referenceLift, MatrixMap.kron_idChannel_left_apply_slice,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  simp only [eq_comm]
  have hleft :
      (fun j j' =>
          ∑ x, ∑ y,
            (∑ u, ∑ v, (W r u * if j = v then 1 else 0) * X (u, v) (x, y)) *
              (W x r' * if j' = y then 1 else 0)) =
        (fun j j' => ∑ u, ∑ x, W r u * (W x r' * X (u, j) (x, j'))) := by
    ext j j'
    calc
      (∑ x, ∑ y,
          (∑ u, ∑ v, (W r u * if j = v then 1 else 0) * X (u, v) (x, y)) *
            (W x r' * if j' = y then 1 else 0)) =
          ∑ x, W x r' * ∑ u, W r u * X (u, j) (x, j') := by
            simp [mul_comm]
      _ =
          ∑ x, ∑ u, W x r' * (W r u * X (u, j) (x, j')) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
      _ = ∑ u, ∑ x, W x r' * (W r u * X (u, j) (x, j')) := by
            rw [Finset.sum_comm]
      _ = ∑ u, ∑ x, W r u * (W x r' * X (u, j) (x, j')) := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro x _
            ring
  have hright :
      (∑ x, ∑ y,
          (∑ u, ∑ v, (W r u * if b = v then 1 else 0) *
            Phi (Matrix.of fun j j' => X (u, j) (x, j')) v y) *
            (W x r' * if b' = y then 1 else 0)) =
        ∑ u, ∑ x, W r u * (W x r' * Phi (Matrix.of fun j j' => X (u, j) (x, j')) b b') := by
    calc
      (∑ x, ∑ y,
          (∑ u, ∑ v, (W r u * if b = v then 1 else 0) *
            Phi (Matrix.of fun j j' => X (u, j) (x, j')) v y) *
            (W x r' * if b' = y then 1 else 0)) =
          ∑ x, W x r' * ∑ u, W r u *
            Phi (Matrix.of fun j j' => X (u, j) (x, j')) b b' := by
            simp [mul_comm]
      _ =
          ∑ x, W x r' * ∑ u, W r u *
            Phi (Matrix.of fun j j' => X (u, j) (x, j')) b b' :=
        rfl
      _ =
          ∑ x, ∑ u, W x r' *
            (W r u * Phi (Matrix.of fun j j' => X (u, j) (x, j')) b b') := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
      _ = ∑ u, ∑ x, W x r' *
            (W r u * Phi (Matrix.of fun j j' => X (u, j) (x, j')) b b') := by
            rw [Finset.sum_comm]
      _ = ∑ u, ∑ x, W r u *
            (W x r' * Phi (Matrix.of fun j j' => X (u, j) (x, j')) b b') := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro x _
            ring
  rw [hleft, hright]
  have hslice :
      (Matrix.of fun j j' => ∑ x, ∑ y, W r x * (W y r' * X (x, j) (y, j'))) =
        ∑ x, ∑ y, (W r x * W y r') • (Matrix.of fun j j' => X (x, j) (y, j')) := by
    ext j j'
    simp [Matrix.sum_apply, Matrix.of_apply, Pi.smul_apply, mul_assoc]
  rw [hslice]
  have hmap1 :
      Phi (∑ x, ∑ y, (W r x * W y r') • (Matrix.of fun j j' => X (x, j) (y, j'))) =
        ∑ x, Phi (∑ y, (W r x * W y r') •
          (Matrix.of fun j j' => X (x, j) (y, j'))) := by
    exact (map_sum Phi (fun x =>
      ∑ y, (W r x * W y r') • (Matrix.of fun j j' => X (x, j) (y, j'))) Finset.univ)
  calc
    Phi (∑ x, ∑ y, (W r x * W y r') • (Matrix.of fun j j' => X (x, j) (y, j'))) b b' =
        (∑ x, Phi (∑ y, (W r x * W y r') •
          (Matrix.of fun j j' => X (x, j) (y, j')))) b b' := by
          exact congrFun (congrFun hmap1 b) b'
    _ = ∑ x, (Phi (∑ y, (W r x * W y r') •
          (Matrix.of fun j j' => X (x, j) (y, j')))) b b' := by
          simp [Matrix.sum_apply]
    _ = ∑ x, ∑ y, W r x *
          (W y r' * Phi (Matrix.of fun j j' => X (x, j) (y, j')) b b') := by
          refine Finset.sum_congr rfl fun x _ => ?_
          have hmap2 :
              Phi (∑ y, (W r x * W y r') • (Matrix.of fun j j' => X (x, j) (y, j'))) =
                ∑ y, Phi ((W r x * W y r') • (Matrix.of fun j j' => X (x, j) (y, j'))) := by
            exact (map_sum Phi (fun y =>
              (W r x * W y r') • (Matrix.of fun j j' => X (x, j) (y, j')))) Finset.univ
          calc
            (Phi (∑ y, (W r x * W y r') •
                (Matrix.of fun j j' => X (x, j) (y, j')))) b b' =
                (∑ y, Phi ((W r x * W y r') •
                  (Matrix.of fun j j' => X (x, j) (y, j')))) b b' := by
                  exact congrFun (congrFun hmap2 b) b'
            _ = ∑ y, (Phi ((W r x * W y r') •
                  (Matrix.of fun j j' => X (x, j) (y, j')))) b b' := by
                  simp [Matrix.sum_apply]
            _ = ∑ y, W r x *
                  (W y r' * Phi (Matrix.of fun j j' => X (x, j) (y, j')) b b') := by
                  refine Finset.sum_congr rfl fun y _ => ?_
                  have hmap3 :
                      Phi ((W r x * W y r') • (Matrix.of fun j j' => X (x, j) (y, j'))) =
                        (W r x * W y r') • Phi (Matrix.of fun j j' => X (x, j) (y, j')) := by
                    exact map_smul Phi (W r x * W y r') (Matrix.of fun j j' => X (x, j) (y, j'))
                  calc
                    (Phi ((W r x * W y r') •
                        (Matrix.of fun j j' => X (x, j) (y, j')))) b b' =
                        ((W r x * W y r') •
                          Phi (Matrix.of fun j j' => X (x, j) (y, j'))) b b' := by
                          exact congrFun (congrFun hmap3 b) b'
                    _ = W r x *
                        (W y r' * Phi (Matrix.of fun j j' => X (x, j) (y, j')) b b') := by
                        rw [Matrix.smul_apply]
                        ring
    _ = ∑ u, ∑ x, W r u *
          (W x r' * Phi (Matrix.of fun j j' => X (u, j) (x, j')) b b') := by
          rfl

theorem canonicalPurification_referenceSandwich_state_eq_cbOneToAlphaOriginalInput
    (tau : MState a1) {alpha : ℝ} (halpha : 1 < alpha) :
    Matrix.kronecker
        (CFC.rpow tau.m ((1 - alpha) / (2 * alpha))) (1 : CMatrix a1) *
          (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)).state.m *
        Matrix.kronecker
          (CFC.rpow tau.m ((1 - alpha) / (2 * alpha))) (1 : CMatrix a1) =
      MatrixMap.cbOneToAlphaOriginalInput tau.m alpha := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let R : CMatrix a1 := CFC.rpow tau.m (1 / (2 * alpha))
  let W : CMatrix a1 := CFC.rpow tau.m s
  have hs_den : (1 - alpha) / (alpha * 2) = s := by
    dsimp [s]
    ring
  have hsqrt_left :
      CFC.rpow tau.m s * tau.sqrtMatrix = R := by
    rw [MState.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
    change tau.m ^ s * tau.m ^ (1 / 2 : ℝ) = R
    simpa [s, R] using cMatrix_sandwiched_left_rpow_mul_sqrt tau.psd halpha
  have hsqrt_right :
      tau.sqrtMatrix * CFC.rpow tau.m s = R := by
    rw [MState.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow]
    change tau.m ^ (1 / 2 : ℝ) * tau.m ^ s = R
    simpa [s, R] using cMatrix_sqrt_mul_sandwiched_left_rpow tau.psd halpha
  have hleftEntry (i j : a1) :
      (∑ x : a1, W i x * tau.sqrtMatrix x j) =
        R i j := by
    have happ := congrFun (congrFun hsqrt_left i) j
    simpa [Matrix.mul_apply, W, R] using happ
  have hrightEntry (i j : a1) :
      (∑ x : a1, tau.sqrtMatrix i x * W x j) =
        R i j := by
    have happ := congrFun (congrFun hsqrt_right i) j
    simpa [Matrix.mul_apply, W, R] using happ
  have hcanon :
      (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)).state.m =
        rankOneMatrix (fun ra : a1 × a1 => tau.sqrtMatrix ra.1 ra.2) := by
    ext ra ra'
    rcases ra with ⟨r, x⟩
    rcases ra' with ⟨r', x'⟩
    simp [Ket.reindex_state, Ket.state_matrix,
      rankOneMatrix_apply, MState.canonicalPurification, MState.canonicalPurificationAmp]
  have hrightEntryStar (i j : a1) :
      (∑ x : a1, star (tau.sqrtMatrix x i) * W x j) =
        R i j := by
    calc
      (∑ x : a1, star (tau.sqrtMatrix x i) * W x j) =
          ∑ x : a1, tau.sqrtMatrix i x * W x j := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [← tau.sqrtMatrix_isHermitian.apply i x]
      _ = R i j := hrightEntry i j
  have hinput :
      MatrixMap.cbOneToAlphaOriginalInput tau.m alpha =
        rankOneMatrix (fun ra : a1 × a1 => R ra.1 ra.2) := by
    simpa [R] using
      MatrixMap.cbOneToAlphaOriginalInput_eq_rankOne_rpow tau.psd alpha
  rw [hinput]
  rw [hcanon]
  ext ra ra'
  rcases ra with ⟨r, x⟩
  rcases ra' with ⟨r', x'⟩
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, rankOneMatrix_apply]
  calc
    (∑ y : a1 × a1,
        (∑ z : a1 × a1,
          (CFC.rpow tau.m ((1 - alpha) / (2 * alpha)) r z.1 *
              (if x = z.2 then 1 else 0)) *
            (tau.sqrtMatrix z.1 z.2 * star (tau.sqrtMatrix y.1 y.2))) *
          (CFC.rpow tau.m ((1 - alpha) / (2 * alpha)) y.1 r' *
              (if y.2 = x' then 1 else 0))) =
        (∑ u : a1, W r u * tau.sqrtMatrix u x) *
          (∑ v : a1, star (tau.sqrtMatrix v x') * W v r') := by
          simp [W, Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm,
            Finset.mul_sum, hs_den]
          rw [Finset.sum_comm]
    _ = R r x * R x' r' := by
          rw [hleftEntry r x, hrightEntryStar x' r']
    _ = R r x * star (R r' x') := by
          have hRherm :
              R.IsHermitian :=
            (cMatrix_rpow_posSemidef (A := tau.m)
              (s := 1 / (2 * alpha)) tau.psd).isHermitian
          rw [hRherm.apply]

/-- The full-rank KW weighting map for a product reference composes with a
product channel map as the product of the individually weighted channel maps. -/
theorem sandwichedSideWeightMap_prod_comp_kron_posDef
    (sigma1 : MState b1) (sigma2 : MState b2)
    (Phi1 : MatrixMap a1 b1) (Phi2 : MatrixMap a2 b2)
    (hsigma1 : sigma1.m.PosDef) (hsigma2 : sigma2.m.PosDef)
    (alpha : ℝ) :
    (sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
        (MatrixMap.kron Phi1 Phi2) =
      MatrixMap.kron ((sandwichedSideWeightMap sigma1 alpha).comp Phi1)
        ((sandwichedSideWeightMap sigma2 alpha).comp Phi2) := by
  rw [sandwichedSideWeightMap_prod_posDef sigma1 sigma2 hsigma1 hsigma2 alpha]
  ext X bd bd'
  exact congrFun (congrFun
    (kron_comp_apply_general
      (sandwichedSideWeightMap sigma1 alpha)
      (sandwichedSideWeightMap sigma2 alpha)
      Phi1 Phi2 X) bd) bd'

/-- Full-rank product-reference instance of the KW CB-norm multiplicativity
step for the weighted channel maps. -/
theorem cbOneToAlphaNorm_sandwichedSideWeightMap_prod_comp_kron_eq_mul_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (sigma1 : MState b1) (sigma2 : MState b2)
    (Phi1 : MatrixMap a1 b1) (hPhi1 : MatrixMap.IsCompletelyPositive Phi1)
    (Phi2 : MatrixMap a2 b2) (hPhi2 : MatrixMap.IsCompletelyPositive Phi2)
    (hsigma1 : sigma1.m.PosDef) (hsigma2 : sigma2.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaNorm
        ((sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
          (MatrixMap.kron Phi1 Phi2))
        (MatrixMap.isCompletelyPositive_comp _ _
          (sandwichedSideWeightMap_completelyPositive (sigma1.prod sigma2) alpha)
          (MatrixMap.IsCompletelyPositive.kron hPhi1 hPhi2))
        (SchattenOrder.ofOneLt halpha) =
      MatrixMap.cbOneToAlphaNorm
          ((sandwichedSideWeightMap sigma1 alpha).comp Phi1)
          (MatrixMap.isCompletelyPositive_comp _ _
            (sandwichedSideWeightMap_completelyPositive sigma1 alpha) hPhi1)
          (SchattenOrder.ofOneLt halpha) *
        MatrixMap.cbOneToAlphaNorm
          ((sandwichedSideWeightMap sigma2 alpha).comp Phi2)
          (MatrixMap.isCompletelyPositive_comp _ _
            (sandwichedSideWeightMap_completelyPositive sigma2 alpha) hPhi2)
          (SchattenOrder.ofOneLt halpha) := by
  let Tprod : MatrixMap (a1 × a2) (b1 × b2) :=
    (sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
      (MatrixMap.kron Phi1 Phi2)
  let T1 : MatrixMap a1 b1 := (sandwichedSideWeightMap sigma1 alpha).comp Phi1
  let T2 : MatrixMap a2 b2 := (sandwichedSideWeightMap sigma2 alpha).comp Phi2
  let hTprod : MatrixMap.IsCompletelyPositive Tprod :=
    MatrixMap.isCompletelyPositive_comp _ _
      (sandwichedSideWeightMap_completelyPositive (sigma1.prod sigma2) alpha)
      (MatrixMap.IsCompletelyPositive.kron hPhi1 hPhi2)
  let hT1 : MatrixMap.IsCompletelyPositive T1 :=
    MatrixMap.isCompletelyPositive_comp _ _
      (sandwichedSideWeightMap_completelyPositive sigma1 alpha) hPhi1
  let hT2 : MatrixMap.IsCompletelyPositive T2 :=
    MatrixMap.isCompletelyPositive_comp _ _
      (sandwichedSideWeightMap_completelyPositive sigma2 alpha) hPhi2
  have hTprod_eq : Tprod = MatrixMap.kron T1 T2 := by
    dsimp [Tprod, T1, T2]
    exact sandwichedSideWeightMap_prod_comp_kron_posDef
      sigma1 sigma2 Phi1 Phi2 hsigma1 hsigma2 alpha
  change MatrixMap.cbOneToAlphaNorm Tprod hTprod (SchattenOrder.ofOneLt halpha) =
    MatrixMap.cbOneToAlphaNorm T1 hT1 (SchattenOrder.ofOneLt halpha) *
      MatrixMap.cbOneToAlphaNorm T2 hT2 (SchattenOrder.ofOneLt halpha)
  calc
    MatrixMap.cbOneToAlphaNorm Tprod hTprod (SchattenOrder.ofOneLt halpha) =
      MatrixMap.cbOneToAlphaNorm (MatrixMap.kron T1 T2)
        (MatrixMap.IsCompletelyPositive.kron hT1 hT2)
        (SchattenOrder.ofOneLt halpha) := by
          exact MatrixMap.cbOneToAlphaNorm_congr_map hTprod_eq hTprod
            (MatrixMap.IsCompletelyPositive.kron hT1 hT2)
            (SchattenOrder.ofOneLt halpha)
    _ = MatrixMap.cbOneToAlphaNorm T1 hT1 (SchattenOrder.ofOneLt halpha) *
        MatrixMap.cbOneToAlphaNorm T2 hT2 (SchattenOrder.ofOneLt halpha) := by
          exact MatrixMap.cbOneToAlphaNorm_kron_eq_mul T1 hT1 T2 hT2 halpha

end MatrixMap

end
end QIT

noncomputable section

namespace CPTPOp

open QIT

variable {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
variable [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
variable [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]

/-- Matrix form of a pure input-reference output, matching the `referenceLift`
input used by the KW CB-norm quotient. -/
theorem hypothesisTestingOutputState_matrix_referenceLift
    (N : CPTPMap a1 b1) (ψ : Ket (a1 × a1)) :
    (N.hypothesisTestingOutputState ψ).m =
      MatrixMap.referenceLift N.map ψ.state.m :=
  N.hypothesisTestingOutputState_matrix ψ

/-- The reference marginal is untouched by the channel output state
`(id_R ⊗ N)(|ψ⟩⟨ψ|)`. -/
theorem hypothesisTestingOutputState_traceRight
    (N : CPTPMap a1 b1) (ψ : Ket (a1 × a1)) :
    (N.hypothesisTestingOutputState ψ).traceRight = ψ.state.traceRight := by
  unfold CPTPOp.hypothesisTestingOutputState
  exact MState.traceRight_applyState_id_prod ψ.state N

/-- Sandwiched mutual information of a channel output is monotone under
reference-side isometries.

This is the channel-output form of the KW purification-equivalence step:
`N` commutes with the reference isometry, and the resulting reference-side
post-processing is handled by the optimized state sandwiched-Renyi DPI. -/
theorem hypothesisTestingOutputState_applyReferenceIsometry_sandwichedRenyiMutualInformationE_le
    {r1 : Type u1} {r2 : Type u2}
    [Fintype r1] [DecidableEq r1] [Fintype r2] [DecidableEq r2]
    (N : CPTPMap a1 b1) (V : ReferenceIsometry r1 r2)
    (ψ : Ket (r1 × a1)) {alpha : ℝ} (halpha : 1 < alpha) :
    (N.hypothesisTestingOutputState (V.applyKet ψ)).sandwichedRenyiMutualInformationE
        alpha ≤
      (N.hypothesisTestingOutputState ψ).sandwichedRenyiMutualInformationE alpha := by
  rw [N.hypothesisTestingOutputState_applyReferenceIsometry V ψ]
  exact MState.sandwichedRenyiMutualInformationE_dataProcessing_left
    (N.hypothesisTestingOutputState ψ) (CPTPOp.ofReferenceIsometry V) halpha

/-- Arbitrary-reference pure inputs whose reference system contains an
input-copy reference are bounded by the optimized channel sandwiched-Renyi
mutual information.

This is the sandwiched-Renyi analogue of the hypothesis-testing purification
bridge: replace an arbitrary purification by the canonical purification of its
input marginal, then use reference-side data processing. -/
theorem hypothesisTestingOutputState_sandwichedRenyiMutualInformationE_le_channel_of_card_le
    (N : CPTPMap a1 b1) {r : Type u2} [Fintype r] [DecidableEq r]
    (ψ : Ket (r × a1)) {alpha : ℝ} (halpha : 1 < alpha)
    (hcard : Fintype.card a1 ≤ Fintype.card r) :
    (N.hypothesisTestingOutputState ψ).sandwichedRenyiMutualInformationE alpha ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  let φ : Ket (a1 × a1) := ψ.state.traceLeft.canonicalPurification
  have hφ : φ.Purifies ψ.state.traceLeft := by
    exact ψ.state.traceLeft.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.traceLeft :=
    ψ.purifies_traceLeft
  rcases Ket.exists_referenceIsometry_applyKet_eq_of_purifies_same_state
      hφ hψ hcard with ⟨V, hV⟩
  have hout :
      N.hypothesisTestingOutputState ψ =
        ((CPTPOp.ofReferenceIsometry V).prod (CPTPOp.id (dIn := b1)))
          (N.hypothesisTestingOutputState φ) := by
    rw [hV]
    exact N.hypothesisTestingOutputState_applyReferenceIsometry V φ
  rw [hout]
  exact (MState.sandwichedRenyiMutualInformationE_dataProcessing_left
      (N.hypothesisTestingOutputState φ) (CPTPOp.ofReferenceIsometry V) halpha).trans
    (N.inputSandwichedRenyiMutualInformationE_le_channel φ alpha)

omit [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2] in
/-- Pure inputs with an input-copy reference are bounded by the canonical
purification of their input marginal.

This is the KW purification-equivalence step before the support/full-rank
analysis of the input marginal: every input-copy purification is a
reference-side isometric image of the canonical purification of the same input
state, and optimized sandwiched mutual information is monotone under that
reference-side post-processing. -/
theorem hypothesisTestingOutputState_sandwichedRenyiMutualInformationE_le_canonical_traceLeft
    (N : CPTPMap a1 b1) (ψ : Ket (a1 × a1))
    {alpha : ℝ} (halpha : 1 < alpha) :
    (N.hypothesisTestingOutputState ψ).sandwichedRenyiMutualInformationE alpha ≤
      (N.hypothesisTestingOutputState
        ψ.state.traceLeft.canonicalPurification).sandwichedRenyiMutualInformationE
          alpha := by
  let φ : Ket (a1 × a1) := ψ.state.traceLeft.canonicalPurification
  change (N.hypothesisTestingOutputState ψ).sandwichedRenyiMutualInformationE alpha ≤
    (N.hypothesisTestingOutputState φ).sandwichedRenyiMutualInformationE alpha
  have hφ : φ.Purifies ψ.state.traceLeft := by
    exact ψ.state.traceLeft.canonicalPurification_purifies
  have hψ : ψ.Purifies ψ.state.traceLeft :=
    ψ.purifies_traceLeft
  rcases Ket.exists_referenceIsometry_applyKet_eq_of_purifies_same_state
      hφ hψ (Nat.le_refl (Fintype.card a1)) with ⟨V, hV⟩
  rw [hV]
  exact
    N.hypothesisTestingOutputState_applyReferenceIsometry_sandwichedRenyiMutualInformationE_le
      V φ halpha

/-- The KW weighted channel map `S_sigma^(alpha) ∘ N` from
`EA_capacity.tex:1242-1254`. -/
def sandwichedSideWeightedMap (N : CPTPMap a1 b1) (sigma : MState b1) (alpha : ℝ) :
    MatrixMap a1 b1 :=
  (MatrixMap.sandwichedSideWeightMap sigma alpha).comp N.map

/-- Source form of the KW weighted channel map:
`(S_sigma^(alpha) o N)(X) = sigma^s N(X) sigma^s`. -/
theorem sandwichedSideWeightedMap_apply_source
    (N : CPTPMap a1 b1) (sigma : MState b1) (alpha : ℝ) (X : CMatrix a1) :
    sandwichedSideWeightedMap N sigma alpha X =
      CFC.rpow sigma.m ((1 - alpha) / (2 * alpha)) *
        (N.map X) *
        CFC.rpow sigma.m ((1 - alpha) / (2 * alpha)) := by
  rw [sandwichedSideWeightedMap]
  change MatrixMap.sandwichedSideWeightMap sigma alpha (N.map X) = _
  exact MatrixMap.sandwichedSideWeightMap_apply_source sigma alpha (N.map X)

/-- Complete positivity of the KW weighted channel map. -/
theorem sandwichedSideWeightedMap_completelyPositive
    (N : CPTPMap a1 b1) (sigma : MState b1) (alpha : ℝ) :
    MatrixMap.IsCompletelyPositive (sandwichedSideWeightedMap N sigma alpha) :=
  MatrixMap.isCompletelyPositive_comp _ _
    (MatrixMap.sandwichedSideWeightMap_completelyPositive sigma alpha)
    N.map_cp

/-- The KW weighted channel map preserves positive semidefinite inputs. -/
theorem sandwichedSideWeightedMap_mapsPositive
    (N : CPTPMap a1 b1) (sigma : MState b1) (alpha : ℝ)
    {X : CMatrix a1} (hX : X.PosSemidef) :
    (sandwichedSideWeightedMap N sigma alpha X).PosSemidef :=
  MatrixMap.isCompletelyPositive_mapsPositive (sandwichedSideWeightedMap N sigma alpha)
    (sandwichedSideWeightedMap_completelyPositive N sigma alpha) X hX

theorem swappedCanonical_referenceInner_eq_referenceLift_cbOneToAlphaOriginalInput
    (N : CPTPMap a1 b1) (sigma : MState b1) (tau : MState a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    let psi := tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
    MState.sandwichedRenyiReferenceInner (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).traceRight.prod sigma).m alpha =
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (MatrixMap.cbOneToAlphaOriginalInput tau.m alpha) := by
  intro psi
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let Wtau : CMatrix a1 := CFC.rpow tau.m s
  let Wsigma : CMatrix b1 := CFC.rpow sigma.m s
  have hmarg : (N.hypothesisTestingOutputState psi).traceRight = tau := by
    calc
      (N.hypothesisTestingOutputState psi).traceRight = psi.state.traceRight :=
        CPTPOp.hypothesisTestingOutputState_traceRight N psi
      _ = tau := by
        simpa [psi] using MState.canonicalPurification_reindex_prodComm_traceRight tau
  have hstateSandwich :
      Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.m *
          Matrix.kronecker Wtau (1 : CMatrix a1) =
        MatrixMap.cbOneToAlphaOriginalInput tau.m alpha := by
    simpa [psi, Wtau, s] using
      MatrixMap.canonicalPurification_referenceSandwich_state_eq_cbOneToAlphaOriginalInput
        tau halpha
  have hreferenceSandwich :
      MatrixMap.referenceLift N.map
          (Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.m *
            Matrix.kronecker Wtau (1 : CMatrix a1)) =
        Matrix.kronecker Wtau (1 : CMatrix b1) *
          MatrixMap.referenceLift N.map psi.state.m *
          Matrix.kronecker Wtau (1 : CMatrix b1) := by
    exact MatrixMap.referenceLift_referenceSandwich N.map Wtau psi.state.m
  have hBA :
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
          Matrix.kronecker Wtau (1 : CMatrix b1) =
        Matrix.kronecker Wtau Wsigma := by
    calc
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
          Matrix.kronecker Wtau (1 : CMatrix b1) =
        Matrix.kronecker ((1 : CMatrix a1) * Wtau)
          (Wsigma * (1 : CMatrix b1)) := by
            exact (Matrix.mul_kronecker_mul
              (1 : CMatrix a1) Wtau Wsigma (1 : CMatrix b1)).symm
      _ = Matrix.kronecker Wtau Wsigma := by simp
  have hAB :
      Matrix.kronecker Wtau (1 : CMatrix b1) *
          Matrix.kronecker (1 : CMatrix a1) Wsigma =
        Matrix.kronecker Wtau Wsigma := by
    calc
      Matrix.kronecker Wtau (1 : CMatrix b1) *
          Matrix.kronecker (1 : CMatrix a1) Wsigma =
        Matrix.kronecker (Wtau * (1 : CMatrix a1))
          ((1 : CMatrix b1) * Wsigma) := by
            exact (Matrix.mul_kronecker_mul
              Wtau (1 : CMatrix a1) (1 : CMatrix b1) Wsigma).symm
      _ = Matrix.kronecker Wtau Wsigma := by simp
  have hpow :
      CFC.rpow (Matrix.kronecker tau.m sigma.m) s =
        Matrix.kronecker Wtau Wsigma := by
    simpa [Wtau, Wsigma] using
      cMatrix_rpow_kronecker tau.psd sigma.psd s
  calc
    MState.sandwichedRenyiReferenceInner (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).traceRight.prod sigma).m alpha
        =
      Matrix.kronecker Wtau Wsigma *
        MatrixMap.referenceLift N.map psi.state.m *
        Matrix.kronecker Wtau Wsigma := by
          unfold MState.sandwichedRenyiReferenceInner
          change
            CFC.rpow ((N.hypothesisTestingOutputState psi).traceRight.prod sigma).m s *
                (N.hypothesisTestingOutputState psi).m *
              CFC.rpow ((N.hypothesisTestingOutputState psi).traceRight.prod sigma).m s =
            Matrix.kronecker Wtau Wsigma *
                MatrixMap.referenceLift N.map psi.state.m *
              Matrix.kronecker Wtau Wsigma
          rw [hmarg, MState.prod_m, ← Matrix.kronecker, hpow]
          rw [CPTPOp.hypothesisTestingOutputState_matrix_referenceLift]
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        (Matrix.kronecker Wtau (1 : CMatrix b1) *
          MatrixMap.referenceLift N.map psi.state.m *
          Matrix.kronecker Wtau (1 : CMatrix b1)) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          calc
            Matrix.kronecker Wtau Wsigma *
                MatrixMap.referenceLift N.map psi.state.m *
              Matrix.kronecker Wtau Wsigma =
              (Matrix.kronecker (1 : CMatrix a1) Wsigma *
                  Matrix.kronecker Wtau (1 : CMatrix b1)) *
                MatrixMap.referenceLift N.map psi.state.m *
                (Matrix.kronecker Wtau (1 : CMatrix b1) *
                  Matrix.kronecker (1 : CMatrix a1) Wsigma) := by
                  rw [hBA, hAB]
            _ =
              Matrix.kronecker (1 : CMatrix a1) Wsigma *
                (Matrix.kronecker Wtau (1 : CMatrix b1) *
                  MatrixMap.referenceLift N.map psi.state.m *
                  Matrix.kronecker Wtau (1 : CMatrix b1)) *
                Matrix.kronecker (1 : CMatrix a1) Wsigma := by
                  noncomm_ring
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        MatrixMap.referenceLift N.map
          (Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.m *
            Matrix.kronecker Wtau (1 : CMatrix a1)) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          rw [hreferenceSandwich]
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        MatrixMap.referenceLift N.map
          (MatrixMap.cbOneToAlphaOriginalInput tau.m alpha) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          rw [hstateSandwich]
    _ =
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (MatrixMap.cbOneToAlphaOriginalInput tau.m alpha) := by
          rw [sandwichedSideWeightedMap]
          rw [MatrixMap.referenceLift_comp_apply]
          rw [MatrixMap.referenceKron_sandwichedSideWeightMap_apply]
          have hWherm : Wsigma.conjTranspose = Wsigma := by
            exact (cMatrix_rpow_posSemidef (A := sigma.m) (s := s) sigma.psd).isHermitian.eq
          have hDherm :
              (Matrix.kronecker (1 : CMatrix a1) Wsigma).conjTranspose =
                Matrix.kronecker (1 : CMatrix a1) Wsigma := by
            exact (Matrix.PosSemidef.one.kronecker
              (cMatrix_rpow_posSemidef (A := sigma.m) (s := s) sigma.psd)).isHermitian.eq
          rw [hDherm]

/-- KW weighted rank-one alternate expression for an arbitrary pure input.

This is the channel-side version of the polar-decomposition step in
`EA_capacity.tex:2054-2093`: sandwiching the channel output by
`rho_R^s \otimes sigma_B^s` is the same as first sandwiching the pure input on
the reference register by `rho_R^s`, then applying the weighted channel map
`S_sigma^(alpha) o N`. -/
theorem referenceInner_eq_referenceLift_weightedRankOne
    (N : CPTPMap a1 b1) (sigma : MState b1) (psi : Ket (a1 × a1))
    (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (_halpha : 1 < alpha) :
    let s : ℝ := (1 - alpha) / (2 * alpha)
    let weighted : a1 × a1 → ℂ :=
      Matrix.mulVec
        (Matrix.kronecker (CFC.rpow psi.state.traceRight.m s) (1 : CMatrix a1))
        psi.vec
    MState.sandwichedRenyiReferenceInner (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).traceRight.prod sigma).m alpha =
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (rankOneMatrix weighted) := by
  intro s weighted
  let Wtau : CMatrix a1 := CFC.rpow psi.state.traceRight.m s
  let Wsigma : CMatrix b1 := CFC.rpow sigma.m s
  let M : CMatrix (a1 × a1) := Matrix.kronecker Wtau (1 : CMatrix a1)
  have hmarg :
      (N.hypothesisTestingOutputState psi).traceRight = psi.state.traceRight :=
    CPTPOp.hypothesisTestingOutputState_traceRight N psi
  have hMherm : M.conjTranspose = M := by
    exact (Matrix.PosSemidef.kronecker
      (cMatrix_rpow_posSemidef (A := psi.state.traceRight.m) (s := s)
        psi.state.traceRight.psd)
      Matrix.PosSemidef.one).isHermitian.eq
  have hrank :
      rankOneMatrix (M.mulVec psi.vec) =
        M * rankOneMatrix psi.vec * Matrix.conjTranspose M := by
    rw [rankOneMatrix, rankOneMatrix]
    rw [Matrix.mul_vecMulVec]
    rw [Matrix.vecMulVec_mul]
    congr
    ext i
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose, mul_comm]
  have hstateSandwich :
      Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.m *
          Matrix.kronecker Wtau (1 : CMatrix a1) =
        rankOneMatrix weighted := by
    calc
      Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.m *
          Matrix.kronecker Wtau (1 : CMatrix a1) =
        M * rankOneMatrix psi.vec * Matrix.conjTranspose M := by
          rw [Ket.state_matrix]
          change M * rankOneMatrix psi.vec * M =
            M * rankOneMatrix psi.vec * Matrix.conjTranspose M
          rw [hMherm]
      _ = rankOneMatrix (M.mulVec psi.vec) := hrank.symm
      _ = rankOneMatrix weighted := by
          rfl
  have hreferenceSandwich :
      MatrixMap.referenceLift N.map
          (Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.m *
            Matrix.kronecker Wtau (1 : CMatrix a1)) =
        Matrix.kronecker Wtau (1 : CMatrix b1) *
          MatrixMap.referenceLift N.map psi.state.m *
          Matrix.kronecker Wtau (1 : CMatrix b1) := by
    exact MatrixMap.referenceLift_referenceSandwich N.map Wtau psi.state.m
  have hBA :
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
          Matrix.kronecker Wtau (1 : CMatrix b1) =
        Matrix.kronecker Wtau Wsigma := by
    calc
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
          Matrix.kronecker Wtau (1 : CMatrix b1) =
        Matrix.kronecker ((1 : CMatrix a1) * Wtau)
          (Wsigma * (1 : CMatrix b1)) := by
            exact (Matrix.mul_kronecker_mul
              (1 : CMatrix a1) Wtau Wsigma (1 : CMatrix b1)).symm
      _ = Matrix.kronecker Wtau Wsigma := by simp
  have hAB :
      Matrix.kronecker Wtau (1 : CMatrix b1) *
          Matrix.kronecker (1 : CMatrix a1) Wsigma =
        Matrix.kronecker Wtau Wsigma := by
    calc
      Matrix.kronecker Wtau (1 : CMatrix b1) *
          Matrix.kronecker (1 : CMatrix a1) Wsigma =
        Matrix.kronecker (Wtau * (1 : CMatrix a1))
          ((1 : CMatrix b1) * Wsigma) := by
            exact (Matrix.mul_kronecker_mul
              Wtau (1 : CMatrix a1) (1 : CMatrix b1) Wsigma).symm
      _ = Matrix.kronecker Wtau Wsigma := by simp
  have hpow :
      CFC.rpow (Matrix.kronecker psi.state.traceRight.m sigma.m) s =
        Matrix.kronecker Wtau Wsigma := by
    simpa [Wtau, Wsigma] using
      cMatrix_rpow_kronecker psi.state.traceRight.psd hsigma.posSemidef s
  calc
    MState.sandwichedRenyiReferenceInner (N.hypothesisTestingOutputState psi)
        ((N.hypothesisTestingOutputState psi).traceRight.prod sigma).m alpha
        =
      Matrix.kronecker Wtau Wsigma *
        MatrixMap.referenceLift N.map psi.state.m *
        Matrix.kronecker Wtau Wsigma := by
          unfold MState.sandwichedRenyiReferenceInner
          change
            CFC.rpow ((N.hypothesisTestingOutputState psi).traceRight.prod sigma).m s *
                (N.hypothesisTestingOutputState psi).m *
              CFC.rpow ((N.hypothesisTestingOutputState psi).traceRight.prod sigma).m s =
            Matrix.kronecker Wtau Wsigma *
                MatrixMap.referenceLift N.map psi.state.m *
              Matrix.kronecker Wtau Wsigma
          rw [hmarg, MState.prod_m, ← Matrix.kronecker, hpow]
          rw [CPTPOp.hypothesisTestingOutputState_matrix_referenceLift]
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        (Matrix.kronecker Wtau (1 : CMatrix b1) *
          MatrixMap.referenceLift N.map psi.state.m *
          Matrix.kronecker Wtau (1 : CMatrix b1)) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          calc
            Matrix.kronecker Wtau Wsigma *
                MatrixMap.referenceLift N.map psi.state.m *
              Matrix.kronecker Wtau Wsigma =
              (Matrix.kronecker (1 : CMatrix a1) Wsigma *
                  Matrix.kronecker Wtau (1 : CMatrix b1)) *
                MatrixMap.referenceLift N.map psi.state.m *
                (Matrix.kronecker Wtau (1 : CMatrix b1) *
                  Matrix.kronecker (1 : CMatrix a1) Wsigma) := by
                  rw [hBA, hAB]
            _ =
              Matrix.kronecker (1 : CMatrix a1) Wsigma *
                (Matrix.kronecker Wtau (1 : CMatrix b1) *
                  MatrixMap.referenceLift N.map psi.state.m *
                  Matrix.kronecker Wtau (1 : CMatrix b1)) *
                Matrix.kronecker (1 : CMatrix a1) Wsigma := by
                  noncomm_ring
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        MatrixMap.referenceLift N.map
          (Matrix.kronecker Wtau (1 : CMatrix a1) * psi.state.m *
            Matrix.kronecker Wtau (1 : CMatrix a1)) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          rw [hreferenceSandwich]
    _ =
      Matrix.kronecker (1 : CMatrix a1) Wsigma *
        MatrixMap.referenceLift N.map (rankOneMatrix weighted) *
        Matrix.kronecker (1 : CMatrix a1) Wsigma := by
          rw [hstateSandwich]
    _ =
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (rankOneMatrix weighted) := by
          rw [sandwichedSideWeightedMap]
          rw [MatrixMap.referenceLift_comp_apply]
          rw [MatrixMap.referenceKron_sandwichedSideWeightMap_apply]
          have hDherm :
              (Matrix.kronecker (1 : CMatrix a1) Wsigma).conjTranspose =
                Matrix.kronecker (1 : CMatrix a1) Wsigma := by
            exact (Matrix.PosSemidef.one.kronecker
              (cMatrix_rpow_posSemidef (A := sigma.m) (s := s) sigma.psd)).isHermitian.eq
          rw [hDherm]

/-- The KW weighted rank-one input has normalized Schatten-`alpha`
denominator.

For `tau_R = psi_R`, applying the reference weight
`tau_R^((1-alpha)/(2 alpha))` to `|psi><psi|` leaves reference marginal
`tau_R^(1/alpha)`, whose Schatten-`alpha` norm is one.  This is exactly the
normalization step used in `EA_capacity.tex:2052-2058`. -/
theorem weightedRankOne_denominator_eq_one
    (psi : Ket (a1 × a1)) (hA : psi.state.traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 0 < alpha) :
    let s : ℝ := (1 - alpha) / (2 * alpha)
    let weighted : a1 × a1 → ℂ :=
      Matrix.mulVec
        (Matrix.kronecker (CFC.rpow psi.state.traceRight.m s) (1 : CMatrix a1))
        psi.vec
    psdSchattenPNorm
        (Matrix.traceRight (rankOneMatrix weighted))
        (traceRight_posSemidef (rankOneMatrix_pos weighted))
        (SchattenOrder.ofPositive halpha) =
      1 := by
  intro s weighted
  let tau : MState a1 := psi.state.traceRight
  let W : CMatrix a1 := CFC.rpow tau.m s
  have hWherm : Matrix.conjTranspose W = W :=
    (cMatrix_rpow_posSemidef (A := tau.m) (s := s) tau.psd).isHermitian.eq
  have hnonneg : 0 ≤ tau.m :=
    Matrix.nonneg_iff_posSemidef.mpr tau.psd
  have hpow_one : CFC.rpow tau.m (1 : ℝ) = tau.m :=
    CFC.rpow_one tau.m (ha := hnonneg)
  have hs_left :
      CFC.rpow tau.m s * tau.m = CFC.rpow tau.m (s + 1) := by
    calc
      CFC.rpow tau.m s * tau.m =
          CFC.rpow tau.m s * CFC.rpow tau.m (1 : ℝ) := by
            rw [hpow_one]
      _ = CFC.rpow tau.m (s + 1) := by
            exact (CFC.rpow_add (a := tau.m) (x := s) (y := 1) hA.isUnit).symm
  have hs_total :
      CFC.rpow tau.m (s + 1) * CFC.rpow tau.m s =
        CFC.rpow tau.m ((s + 1) + s) := by
    exact (CFC.rpow_add (a := tau.m) (x := s + 1) (y := s) hA.isUnit).symm
  have hexp : (s + 1) + s = 1 / alpha := by
    dsimp [s]
    field_simp [ne_of_gt halpha]
    ring
  have hsand :
      W * tau.m * Matrix.conjTranspose W = CFC.rpow tau.m (1 / alpha) := by
    calc
      W * tau.m * Matrix.conjTranspose W =
          CFC.rpow tau.m s * tau.m * CFC.rpow tau.m s := by
            rw [hWherm]
      _ = (CFC.rpow tau.m s * tau.m) * CFC.rpow tau.m s := by
            rw [Matrix.mul_assoc]
      _ = CFC.rpow tau.m (s + 1) * CFC.rpow tau.m s := by
            rw [hs_left]
      _ = CFC.rpow tau.m ((s + 1) + s) := hs_total
      _ = CFC.rpow tau.m (1 / alpha) := by rw [hexp]
  have hmatrix :
      Matrix.traceRight (rankOneMatrix weighted) =
        CFC.rpow tau.m (1 / alpha) := by
    calc
      Matrix.traceRight (rankOneMatrix weighted) =
          W * Matrix.traceRight (rankOneMatrix psi.vec) *
            Matrix.conjTranspose W := by
            simpa [weighted, W, tau] using
              QIT.traceRight_rankOne_kron_left_mulVec_eq
                (a := a1) (c := a1) W psi.vec
      _ = W * tau.m * Matrix.conjTranspose W := by
            simp [tau, Ket.state_matrix]
      _ = CFC.rpow tau.m (1 / alpha) := hsand
  calc
    psdSchattenPNorm
        (Matrix.traceRight (rankOneMatrix weighted))
        (traceRight_posSemidef (rankOneMatrix_pos weighted))
        (SchattenOrder.ofPositive halpha) =
      psdSchattenPNorm
        (CFC.rpow tau.m (1 / alpha))
        (tau.rpowMatrix_posSemidef (1 / alpha))
        (SchattenOrder.ofPositive halpha) := by
          exact psdSchattenPNorm_congr hmatrix _ _ (SchattenOrder.ofPositive halpha)
    _ = 1 := MState.state_rpow_one_div_psdSchattenPNorm_eq_one tau hA alpha halpha

/-- Support-convention version of
`weightedRankOne_denominator_eq_one`.

For `alpha > 1`, the same KW weighted rank-one input is normalized without
assuming that the input/reference marginal is full rank.  The only new
ingredient is the PSD support algebra
`MState.rpow_sandwich_self_eq_rpow_one_div`. -/
theorem weightedRankOne_denominator_eq_one_psd
    (psi : Ket (a1 × a1)) {alpha : ℝ} (halpha : 1 < alpha) :
    let s : ℝ := (1 - alpha) / (2 * alpha)
    let weighted : a1 × a1 → ℂ :=
      Matrix.mulVec
        (Matrix.kronecker (CFC.rpow psi.state.traceRight.m s) (1 : CMatrix a1))
        psi.vec
    psdSchattenPNorm
        (Matrix.traceRight (rankOneMatrix weighted))
        (traceRight_posSemidef (rankOneMatrix_pos weighted))
        (SchattenOrder.ofOneLt halpha) =
      1 := by
  intro s weighted
  let tau : MState a1 := psi.state.traceRight
  let W : CMatrix a1 := CFC.rpow tau.m s
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hWherm : Matrix.conjTranspose W = W :=
    (cMatrix_rpow_posSemidef (A := tau.m) (s := s) tau.psd).isHermitian.eq
  have hsand :
      W * tau.m * Matrix.conjTranspose W = CFC.rpow tau.m (1 / alpha) := by
    calc
      W * tau.m * Matrix.conjTranspose W = W * tau.m * W := by
        rw [hWherm]
      _ = CFC.rpow tau.m (1 / alpha) := by
        simpa [s, W] using
          (MState.rpow_sandwich_self_eq_rpow_one_div tau halpha)
  have hmatrix :
      Matrix.traceRight (rankOneMatrix weighted) =
        CFC.rpow tau.m (1 / alpha) := by
    calc
      Matrix.traceRight (rankOneMatrix weighted) =
          W * Matrix.traceRight (rankOneMatrix psi.vec) *
            Matrix.conjTranspose W := by
            simpa [weighted, W, tau] using
              QIT.traceRight_rankOne_kron_left_mulVec_eq
                (a := a1) (c := a1) W psi.vec
      _ = W * tau.m * Matrix.conjTranspose W := by
            simp [tau, Ket.state_matrix]
      _ = CFC.rpow tau.m (1 / alpha) := hsand
  calc
    psdSchattenPNorm
        (Matrix.traceRight (rankOneMatrix weighted))
        (traceRight_posSemidef (rankOneMatrix_pos weighted))
        (SchattenOrder.ofOneLt halpha) =
      psdSchattenPNorm
        (CFC.rpow tau.m (1 / alpha))
        (tau.rpowMatrix_posSemidef (1 / alpha))
        (SchattenOrder.ofOneLt halpha) := by
          exact psdSchattenPNorm_congr hmatrix _ _ (SchattenOrder.ofOneLt halpha)
    _ = 1 := MState.state_rpow_one_div_psdSchattenPNorm_eq_one_psd tau halpha_pos

/-- The reference lift of a full-rank KW weighted channel map preserves
nonzero PSD inputs. -/
theorem sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
    (N : CPTPMap a1 b1) (sigma : MState b1) (hsigma : sigma.m.PosDef)
    (alpha : ℝ) {X : CMatrix (a1 × a1)}
    (hX : X.PosSemidef) (hXne : X ≠ 0) :
    MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X ≠ 0 := by
  rw [sandwichedSideWeightedMap]
  rw [MatrixMap.referenceLift_comp_apply]
  have hNXne : MatrixMap.referenceLift N.map X ≠ 0 :=
    MatrixMap.referenceLift_apply_ne_zero_of_tracePreserving
      N.map N.map_TP hX hXne
  exact MatrixMap.referenceKron_sandwichedSideWeightMap_apply_ne_zero_of_posDef
    sigma hsigma alpha hNXne

/-- Real-valued CB-norm expression from the KW alternate expression before
identifying it with optimized sandwiched EA mutual information. -/
def sandwichedRenyiCBNormExpression
    (N : CPTPMap a1 b1) (sigma : MState b1) (alpha : SchattenOrder) : ℝ :=
  alpha / (alpha - 1) *
    log2 (MatrixMap.cbOneToAlphaNorm
      (sandwichedSideWeightedMap N sigma alpha)
      (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
      alpha)

/-- KW alternate-expression form of the weighted-channel logarithmic integrand.

This is the direct specialization of
`MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression` to the
side-weighted channel map used in the EA sandwiched mutual information proof. -/
theorem sandwichedRenyiCBNormExpression_eq_cbAlternateExpression
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha) =
      alpha / (alpha - 1) *
        log2 (MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          (SchattenOrder.ofOneLt halpha)) := by
  unfold sandwichedRenyiCBNormExpression
  simp only [SchattenOrder.coe_ofOneLt]
  rw [MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap N sigma alpha)
    (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
    halpha]

/-- Order bridge from a pointwise fixed-input CB upper bound to the optimized
channel alternate-expression upper bound.

This is the `sup_psi`/`inf_sigma` bookkeeping in KW
`EA_capacity.tex:2039-2093`.  The hypothesis is the remaining pointwise
matrix-analytic step: for every pure input and every full-rank side state, the
input sandwiched-Renyi objective is bounded by the corresponding weighted
CB expression. -/
theorem sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_of_input_le
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) (alpha : SchattenOrder)
    (hBelow :
      BddBelow (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha))
    (hinput :
      ∀ psi : Ket (a1 × a1),
        ∀ sigma : {sigma : MState b1 // sigma.m.PosDef},
          N.inputSandwichedRenyiMutualInformationE psi alpha ≤
            ((sandwichedRenyiCBNormExpression N sigma.1 alpha : ℝ) : EReal)) :
    N.sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 alpha) : ℝ) : EReal) := by
  let S := {sigma : MState b1 // sigma.m.PosDef}
  have : Nonempty S := ⟨(MState.uniform : MState b1), MState.uniform_posDef⟩
  let f : S → ℝ := fun sigma =>
    sandwichedRenyiCBNormExpression N sigma.1 alpha
  have hInf :
      sInf (Set.range fun sigma : S => ((f sigma : ℝ) : EReal)) =
        ((sInf (Set.range f) : ℝ) : EReal) :=
    ereal_sInf_range_coe_eq_coe_real_sInf f (by simpa [S, f] using hBelow)
  rw [N.sandwichedRenyiMutualInformationE_eq_sSup]
  refine csSup_le (N.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  rintro y ⟨psi, rfl⟩
  have hleInf :
      N.inputSandwichedRenyiMutualInformationE psi alpha ≤
        sInf (Set.range fun sigma : S => ((f sigma : ℝ) : EReal)) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro z ⟨sigma, rfl⟩
    simpa [S, f] using hinput psi sigma
  simpa [S, f, hInf] using hleInf

/-- Logarithmic CB-norm bound for a fixed rank-one input.

This is the scalar/logarithmic form of the pure-rank-one quotient bound from
the CB-norm alternate-expression proof.  It supplies the final `log` step used
after KW rewrites a fixed channel input into a weighted `|Γ⟩⟨Γ|` candidate in
`EA_capacity.tex:2054-2093`. -/
theorem sandwichedPureRankOneLogQuotient_le_CBNormExpression
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    {alpha : ℝ} (halpha : 1 < alpha) (psi : a1 × a1 → ℂ)
    (hden :
      0 <
        psdSchattenPNorm
          (Matrix.traceRight (rankOneMatrix psi))
          (traceRight_posSemidef (rankOneMatrix_pos psi))
          (SchattenOrder.ofOneLt halpha))
    (hnum :
      0 <
        psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix psi))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos psi))
          (SchattenOrder.ofOneLt halpha)) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
              (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                (rankOneMatrix psi))
              (MatrixMap.referenceLift_mapsPositive
                (sandwichedSideWeightedMap N sigma alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                (rankOneMatrix_pos psi))
              (SchattenOrder.ofOneLt halpha) /
            psdSchattenPNorm
              (Matrix.traceRight (rankOneMatrix psi))
              (traceRight_posSemidef (rankOneMatrix_pos psi))
              (SchattenOrder.ofOneLt halpha)) ≤
      sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha) := by
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let num : ℝ :=
    psdSchattenPNorm
      (MatrixMap.referenceLift Phi (rankOneMatrix psi))
      (MatrixMap.referenceLift_mapsPositive Phi hPhi (rankOneMatrix_pos psi))
      (SchattenOrder.ofOneLt halpha)
  let den : ℝ :=
    psdSchattenPNorm
      (Matrix.traceRight (rankOneMatrix psi))
      (traceRight_posSemidef (rankOneMatrix_pos psi))
      (SchattenOrder.ofOneLt halpha)
  have hquot_le :
      num / den ≤ MatrixMap.cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
    simpa [Phi, hPhi, num, den] using
      MatrixMap.cbOneToAlphaPureRankOneValue_le_cbOneToAlphaNorm
        Phi hPhi halpha psi hden
  have hnum' : 0 < num := by
    simpa [Phi, hPhi, num] using hnum
  have hquot_pos : 0 < num / den := div_pos hnum' hden
  have hlog_le :
      log2 (num / den) ≤
        log2 (MatrixMap.cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha)) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hquot_pos hquot_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact mul_le_mul_of_nonneg_left hlog_le (le_of_lt (highAlpha_conjExponent_pos halpha))

/-- The denominator of the source CB original input is normalized to one for a
state reference.

This is the Lean form of the normalization used in KW
`EA_capacity.tex:2052-2058` and before `eq-operator_CB_alpha_norm`: for a
state `tau_R`, the reference marginal of
`tau_R^(1/(2 alpha)) |Γ⟩⟨Γ| tau_R^(1/(2 alpha))` is `tau_R^(1/alpha)`,
whose Schatten-`alpha` norm is one. -/
theorem cbOneToAlphaOriginalInput_state_denominator_eq_one
    (tau : MState a1) {alpha : ℝ} (halpha : 0 < alpha) :
    psdSchattenPNorm
        (Matrix.traceRight
          (MatrixMap.cbOneToAlphaOriginalInput tau.m alpha))
        (traceRight_posSemidef
          (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.psd alpha))
        (SchattenOrder.ofPositive halpha) =
      1 := by
  have htrace :
      Matrix.traceRight
          (MatrixMap.cbOneToAlphaOriginalInput tau.m alpha) =
        CFC.rpow tau.m (1 / alpha) :=
    MatrixMap.traceRight_cbOneToAlphaOriginalInput_eq_rpow tau.psd halpha
  calc
    psdSchattenPNorm
        (Matrix.traceRight
          (MatrixMap.cbOneToAlphaOriginalInput tau.m alpha))
        (traceRight_posSemidef
          (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.psd alpha))
        (SchattenOrder.ofPositive halpha) =
      psdSchattenPNorm
        (CFC.rpow tau.m (1 / alpha))
        (tau.rpowMatrix_posSemidef (1 / alpha))
        (SchattenOrder.ofPositive halpha) := by
          exact psdSchattenPNorm_congr htrace _ _ (SchattenOrder.ofPositive halpha)
    _ = 1 := MState.state_rpow_one_div_psdSchattenPNorm_eq_one_psd tau halpha

/-- Full-rank original CB candidates have strictly positive weighted-channel
value under a full-rank side reference.

This is the positivity side condition needed before taking logarithms of the
rank-one candidates that arise from the KW polar-decomposition route. -/
theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_posDef
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    (hsigma : sigma.m.PosDef) (Y : MatrixMap.CBOneToAlphaOriginalDomain a1)
    (hY : Y.matrix.PosDef) {alpha : ℝ} (halpha : 0 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        Y
        (SchattenOrder.ofPositive halpha) := by
  let X : CMatrix (a1 × a1) := MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha
  let hX : X.PosSemidef := MatrixMap.cbOneToAlphaOriginalInput_posSemidef Y.pos alpha
  have hXne : X ≠ 0 := by
    simpa [X] using MatrixMap.cbOneToAlphaOriginalInput_ne_zero_of_posDef
      (a1 := a1) hY halpha
  have hPhiXne :
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X ≠ 0 :=
    sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
      N sigma hsigma alpha hX hXne
  unfold MatrixMap.cbOneToAlphaOriginalValue
  change 0 <
    psdSchattenPNorm
      (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _
      (SchattenOrder.ofPositive halpha)
  exact psdSchattenPNorm_pos_of_ne_zero
    (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _ hPhiXne

/-- Trace-one state candidates have strictly positive weighted-channel CB
value under a full-rank side reference.

This removes the unnecessary full-rank hypothesis from the source-side
candidate in the `Tr[Y_R] = 1` branch of KW `EA_capacity.tex:2090-2093`. -/
theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    (hsigma : sigma.m.PosDef) (tau : MState a1)
    {alpha : ℝ} (halpha : 0 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
        (SchattenOrder.ofPositive halpha) := by
  let X : CMatrix (a1 × a1) := MatrixMap.cbOneToAlphaOriginalInput tau.m alpha
  let hX : X.PosSemidef := MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.psd alpha
  have hXne : X ≠ 0 := by
    simpa [X] using MatrixMap.cbOneToAlphaOriginalInput_ne_zero_of_state
      (a1 := a1) tau halpha
  have hPhiXne :
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X ≠ 0 :=
    sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
      N sigma hsigma alpha hX hXne
  unfold MatrixMap.cbOneToAlphaOriginalValue
  change 0 <
    psdSchattenPNorm
      (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _
      (SchattenOrder.ofPositive halpha)
  exact psdSchattenPNorm_pos_of_ne_zero
    (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _ hPhiXne

/-- Logarithmic two-point quasiconcavity input for the channel Sion exchange.

This is the `tau_R`-side Sion hypothesis from KW
`EA_capacity.tex:2080-2084`, in the exact scalar form used by the channel
alternate-expression surface: for a fixed full-rank `sigma_B`, the
weighted-channel CB objective at a convex mixture of normalized source states
dominates the smaller endpoint value after applying `log2` and the positive
Renyi prefactor. -/
theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_log_mix_min_le
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    (hsigma : sigma.m.PosDef)
    {alpha lambda : ℝ} (halpha : 1 < alpha)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (tau0 tau1 : MState a1) :
    min
        (alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau0)
              (SchattenOrder.ofOneLt halpha)))
        (alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau1)
              (SchattenOrder.ofOneLt halpha))) ≤
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState
              (MState.ofMatrix (matrix := lambda • tau0.m + (1 - lambda) • tau1.m)
                (pos :=
                  Matrix.PosSemidef.add
                    (Matrix.PosSemidef.smul tau0.psd hlambda0)
                    (Matrix.PosSemidef.smul tau1.psd (sub_nonneg.mpr hlambda1)))
                (trace_eq_one := by
                  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
                    tau0.tr', tau1.tr']
                  norm_num)))
            (SchattenOrder.ofOneLt halpha)) := by
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let tauMix : MState a1 :=
    .ofMatrix (matrix := lambda • tau0.m + (1 - lambda) • tau1.m)
      (pos :=
        Matrix.PosSemidef.add
          (Matrix.PosSemidef.smul tau0.psd hlambda0)
          (Matrix.PosSemidef.smul tau1.psd (sub_nonneg.mpr hlambda1)))
      (trace_eq_one := by
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
          tau0.tr', tau1.tr']
        norm_num)
  let v0 : ℝ :=
    MatrixMap.cbOneToAlphaOriginalValue Phi hPhi
      (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau0)
      (SchattenOrder.ofOneLt halpha)
  let v1 : ℝ :=
    MatrixMap.cbOneToAlphaOriginalValue Phi hPhi
      (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau1)
      (SchattenOrder.ofOneLt halpha)
  let vmix : ℝ :=
    MatrixMap.cbOneToAlphaOriginalValue Phi hPhi
      (MatrixMap.CBOneToAlphaOriginalDomain.ofState tauMix)
      (SchattenOrder.ofOneLt halpha)
  have hraw : min v0 v1 ≤ vmix := by
    simpa [Phi, hPhi, tauMix, v0, v1, vmix] using
      MatrixMap.cbOneToAlphaOriginalValue_ofState_min_le_mix
        Phi hPhi halpha hlambda0 hlambda1 tau0 tau1
  have hv0_pos : 0 < v0 := by
    exact cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
      N sigma hsigma tau0 (lt_trans zero_lt_one halpha)
  have hv1_pos : 0 < v1 := by
    exact cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
      N sigma hsigma tau1 (lt_trans zero_lt_one halpha)
  have hvmix_pos : 0 < vmix := by
    exact cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
      N sigma hsigma tauMix (lt_trans zero_lt_one halpha)
  have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
    simpa [coeff] using highAlpha_conjExponent_pos halpha)
  by_cases h01 : v0 ≤ v1
  · have hlog01 : log2 v0 ≤ log2 v1 := log2_mono_of_pos hv0_pos h01
    have hv0_le_mix : v0 ≤ vmix := by
      simpa [min_eq_left h01] using hraw
    have hlog0_mix : log2 v0 ≤ log2 vmix :=
      log2_mono_of_pos hv0_pos hv0_le_mix
    calc
      min (coeff * log2 v0) (coeff * log2 v1) =
          coeff * log2 v0 := by
            rw [min_eq_left (mul_le_mul_of_nonneg_left hlog01 hcoeff_nonneg)]
      _ ≤ coeff * log2 vmix := by
            exact mul_le_mul_of_nonneg_left hlog0_mix hcoeff_nonneg
  · have h10 : v1 ≤ v0 := le_of_lt (lt_of_not_ge h01)
    have hlog10 : log2 v1 ≤ log2 v0 := log2_mono_of_pos hv1_pos h10
    have hv1_le_mix : v1 ≤ vmix := by
      simpa [min_eq_right h10] using hraw
    have hlog1_mix : log2 v1 ≤ log2 vmix :=
      log2_mono_of_pos hv1_pos hv1_le_mix
    calc
      min (coeff * log2 v0) (coeff * log2 v1) =
          coeff * log2 v1 := by
            rw [min_eq_right (mul_le_mul_of_nonneg_left hlog10 hcoeff_nonneg)]
      _ ≤ coeff * log2 vmix := by
            exact mul_le_mul_of_nonneg_left hlog1_mix hcoeff_nonneg

/-- Matrix-domain wrapper for the source-side logarithmic objective in the KW
channel Sion step.

The surrounding channel API optimizes over `MState a`, while mathlib's Sion
theorem works over compact convex matrix domains.  This wrapper is equal to
the state expression on `MState.densityMatrixSet a`; outside that domain its
value is irrelevant. -/
def sandwichedChannelOriginalValueLogDensity
    (N : CPTPMap a1 b1) (sigma : MState b1) (alpha : SchattenOrder)
    (M : CMatrix a1) : ℝ := by
  classical
  exact
    if hM : M ∈ MState.densityMatrixSet a1 then
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState
              (MState.densityMatrixSetState M hM))
            alpha)
    else
      0

@[simp]
theorem sandwichedChannelOriginalValueLogDensity_of_mem
    (N : CPTPMap a1 b1) (sigma : MState b1) {alpha : ℝ} (halpha : 1 < alpha)
    {M : CMatrix a1} (hM : M ∈ MState.densityMatrixSet a1) :
    sandwichedChannelOriginalValueLogDensity N sigma
        (SchattenOrder.ofOneLt halpha) M =
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState
              (MState.densityMatrixSetState M hM))
            (SchattenOrder.ofOneLt halpha)) := by
  classical
  simp [sandwichedChannelOriginalValueLogDensity, hM]

private theorem cbOneToAlphaReferenceWeight_continuousOn_posSemidef
    {alpha : ℝ} (halpha : 0 < alpha) :
    ContinuousOn
      (fun M : CMatrix a1 => MatrixMap.cbOneToAlphaReferenceWeight M alpha)
      ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) := by
  have hexp : 0 < (1 / (2 * alpha) : ℝ) := by
    positivity
  have hpow := MState.cMatrix_rpow_continuousOn_posSemidef_of_pos (a := a1) hexp
  have hkr :
      Continuous fun T : CMatrix a1 => Matrix.kronecker T (1 : CMatrix a1) := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply, Pi.mul_def] using
        (continuous_id.matrix_elem x.1 y.1).mul continuous_const
  simpa [MatrixMap.cbOneToAlphaReferenceWeight, Function.comp_def] using
    hkr.comp_continuousOn hpow

private theorem cbOneToAlphaOriginalInput_continuousOn_posSemidef
    {alpha : ℝ} (halpha : 0 < alpha) :
    ContinuousOn
      (fun M : CMatrix a1 => MatrixMap.cbOneToAlphaOriginalInput M alpha)
      ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) := by
  let W : CMatrix a1 → CMatrix (a1 × a1) := fun M =>
    MatrixMap.cbOneToAlphaReferenceWeight M alpha
  have hW : ContinuousOn W ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) :=
    cbOneToAlphaReferenceWeight_continuousOn_posSemidef (a1 := a1) halpha
  have hleft :
      ContinuousOn
        (fun M : CMatrix a1 =>
          W M * MatrixMap.unnormalizedMaximallyEntangledProjector a1)
        ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) :=
    hW.mul continuousOn_const
  have hall :
      ContinuousOn
        (fun M : CMatrix a1 =>
          (W M * MatrixMap.unnormalizedMaximallyEntangledProjector a1) * W M)
        ({M : CMatrix a1 | M.PosSemidef} : Set (CMatrix a1)) :=
    hleft.mul hW
  simpa [MatrixMap.cbOneToAlphaOriginalInput, W, Matrix.mul_assoc] using hall

private theorem matrixMap_continuous (Phi : MatrixMap a1 b1) :
    Continuous fun X : CMatrix a1 => Phi X := by
  simpa [LinearMap.coe_toContinuousLinearMap] using
    (LinearMap.toContinuousLinearMap Phi).continuous

private theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_log_continuousOn_density
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    (hsigma : sigma.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    ContinuousOn
      (sandwichedChannelOriginalValueLogDensity N sigma
        (SchattenOrder.ofOneLt halpha))
      (MState.densityMatrixSet a1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let S := {M : CMatrix a1 // M ∈ MState.densityMatrixSet a1}
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let X : S → CMatrix (a1 × a1) := fun M =>
    MatrixMap.cbOneToAlphaOriginalInput M.1 alpha
  have hXcont : Continuous X := by
    have hcontOn :
        ContinuousOn
          (fun M : CMatrix a1 => MatrixMap.cbOneToAlphaOriginalInput M alpha)
          (MState.densityMatrixSet a1) :=
      (cbOneToAlphaOriginalInput_continuousOn_posSemidef (a1 := a1)
        (lt_trans zero_lt_one halpha)).mono
          (fun M hM => (MState.mem_densityMatrixSet_iff.mp hM).1)
    simpa [S, X, Set.domRestrict_eq, Function.comp_def] using continuousOn_iff_continuous_domRestrict.mp hcontOn
  let Y : S → CMatrix (a1 × b1) := fun M => Phi.referenceLift (X M)
  have hYcont : Continuous Y := by
    exact (matrixMap_continuous (a1 := a1 × a1) (b1 := a1 × b1)
      Phi.referenceLift).comp hXcont
  have hYpsd : ∀ M : S, (Y M).PosSemidef := by
    intro M
    exact Phi.referenceLift_mapsPositive hPhi
      (MatrixMap.cbOneToAlphaOriginalInput_posSemidef
        ((MState.mem_densityMatrixSet_iff.mp M.2).1) alpha)
  let normValue : S → ℝ := fun M =>
    psdSchattenPNorm (Y M) (hYpsd M) (SchattenOrder.ofOneLt halpha)
  have hnorm_cont : Continuous normValue := by
    rw [continuous_iff_continuousAt]
    intro M
    exact psdSchattenPNorm_tendsto_of_tendsto_posSemidef
      (a := a1 × b1) (SchattenOrder.ofOneLt halpha) hYcont.continuousAt hYpsd
      (hYpsd M)
  have hnorm_pos : ∀ M : S, 0 < normValue M := by
    intro M
    have hpos :=
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
        N sigma hsigma (MState.densityMatrixSetState M.1 M.2)
        (lt_trans zero_lt_one halpha)
    simpa [Phi, hPhi, X, Y, normValue, MatrixMap.cbOneToAlphaOriginalValue,
      MatrixMap.CBOneToAlphaOriginalDomain.ofState,
      MState.densityMatrixSetState_matrix] using hpos
  have hlog_cont : Continuous fun M : S => log2 (normValue M) := by
    rw [continuous_iff_continuousAt]
    intro M
    unfold log2
    exact ((Real.continuousAt_log (ne_of_gt (hnorm_pos M))).div_const _).comp
      hnorm_cont.continuousAt
  have hscaled :
      Continuous fun M : S =>
        alpha / (alpha - 1) * log2 (normValue M) :=
    continuous_const.mul hlog_cont
  have hfun :
      (fun M : S => sandwichedChannelOriginalValueLogDensity N sigma
          (SchattenOrder.ofOneLt halpha) M.1) =
        fun M : S => alpha / (alpha - 1) * log2 (normValue M) := by
    funext M
    rw [sandwichedChannelOriginalValueLogDensity_of_mem N sigma
      halpha M.2]
    unfold normValue Y X Phi MatrixMap.cbOneToAlphaOriginalValue
      MatrixMap.CBOneToAlphaOriginalDomain.ofState
    simp [MState.densityMatrixSetState_matrix]
  change Continuous fun M : S => sandwichedChannelOriginalValueLogDensity N sigma
    (SchattenOrder.ofOneLt halpha) M.1
  rw [hfun]
  exact hscaled

/-- Matrix-domain quasiconcavity of the KW source-side channel objective.

This discharges the source-variable quasiconcavity part of Sion's hypotheses
for KW `EA_capacity.tex:2080-2084`, after translating the normalized-state
objective to the matrix density domain. -/
theorem sandwichedChannelOriginalValueLogDensity_quasiconcaveOn
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    (hsigma : sigma.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    QuasiconcaveOn ℝ (MState.densityMatrixSet a1)
      (sandwichedChannelOriginalValueLogDensity N sigma
        (SchattenOrder.ofOneLt halpha)) := by
  rw [quasiconcaveOn_iff_min_le]
  refine ⟨MState.densityMatrixSet_convex, ?_⟩
  intro X hX Y hY s t hs ht hst
  have ht_eq : t = 1 - s := by linarith
  subst t
  have hmix :
      s • X + (1 - s) • Y ∈ MState.densityMatrixSet a1 :=
    MState.densityMatrixSet_convex hX hY hs ht hst
  let tauX : MState a1 := MState.densityMatrixSetState X hX
  let tauY : MState a1 := MState.densityMatrixSetState Y hY
  have hmain :=
    cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_log_mix_min_le
      N sigma hsigma halpha hs (by linarith) tauX tauY
  simpa [sandwichedChannelOriginalValueLogDensity, hX, hY, hmix, tauX, tauY,
    MState.densityMatrixSetState] using hmain

/-- Matrix-domain wrapper for the reference-side logarithmic objective in the
KW channel Sion step.

The source proof optimizes over full-rank side states `sigma_B`.  This wrapper
keeps that variable as a matrix so Sion can be applied on the matrix domain;
outside the full-rank density domain its value is irrelevant. -/
def sandwichedChannelOriginalValueLogReferenceDensity
    (N : CPTPMap a1 b1) (tau : MState a1) (alpha : SchattenOrder)
    (M : CMatrix b1) : ℝ := by
  classical
  exact
    if hM : M ∈ MState.fullRankDensityMatrixSet b1 then
      let sigma : MState b1 :=
        MState.densityMatrixSetState M (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            alpha)
    else
      0

@[simp]
theorem sandwichedChannelOriginalValueLogReferenceDensity_of_mem
    (N : CPTPMap a1 b1) (tau : MState a1) {alpha : ℝ} (halpha : 1 < alpha)
    {M : CMatrix b1} (hM : M ∈ MState.fullRankDensityMatrixSet b1) :
    sandwichedChannelOriginalValueLogReferenceDensity N tau
        (SchattenOrder.ofOneLt halpha) M =
      let sigma : MState b1 :=
        MState.densityMatrixSetState M (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofOneLt halpha)) := by
  classical
  simp [sandwichedChannelOriginalValueLogReferenceDensity, hM]

/-- Raw reference-side objective underlying
`sandwichedChannelOriginalValueLogReferenceDensity`.

Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`, proves convexity on the
unlogged CB-norm expression before applying the positive logarithmic Renyi
prefactor.  This wrapper isolates that raw value on the same full-rank matrix
domain used in the Sion step. -/
def sandwichedChannelOriginalValueReferenceDensity
    (N : CPTPMap a1 b1) (tau : MState a1) (alpha : SchattenOrder)
    (M : CMatrix b1) : ℝ := by
  classical
  exact
    if hM : M ∈ MState.fullRankDensityMatrixSet b1 then
      let sigma : MState b1 :=
        MState.densityMatrixSetState M (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
        alpha
    else
      0

/-- Fixed source-side Choi input appearing in the KW channel alternate
expression proof. -/
private def sandwichedChannelReferenceBase
    (N : CPTPMap a1 b1) (tau : MState a1) (alpha : ℝ) : CMatrix (a1 × b1) :=
  MatrixMap.referenceLift N.map
    (MatrixMap.cbOneToAlphaOriginalInput tau.m alpha)

private theorem sandwichedChannelReferenceBase_posSemidef
    (N : CPTPMap a1 b1) (tau : MState a1) (alpha : ℝ) :
    (sandwichedChannelReferenceBase N tau alpha).PosSemidef :=
  MatrixMap.referenceLift_mapsPositive N.map N.map_cp
    (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.psd alpha)

/-- KW source-shaped matrix after the polar-decomposition/unitary-invariance
rewrite in `EA_capacity.tex:2071-2079`. -/
private def sandwichedChannelReferenceKWMatrix
    (N : CPTPMap a1 b1) (tau : MState a1) (alpha : ℝ) (M : CMatrix b1) :
    CMatrix (a1 × b1) :=
  let base : CMatrix (a1 × b1) := sandwichedChannelReferenceBase N tau alpha
  CFC.sqrt base *
    Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha)) *
      CFC.sqrt base

private theorem sandwichedChannelReferenceKWMatrix_posSemidef
    (N : CPTPMap a1 b1) (tau : MState a1) (alpha : ℝ)
    {M : CMatrix b1} (hM : M.PosSemidef) :
    (sandwichedChannelReferenceKWMatrix N tau alpha M).PosSemidef := by
  let base : CMatrix (a1 × b1) := sandwichedChannelReferenceBase N tau alpha
  let W : CMatrix (a1 × b1) :=
    Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha))
  have hbase : base.PosSemidef := sandwichedChannelReferenceBase_posSemidef N tau alpha
  have hW : W.PosSemidef :=
    Matrix.PosSemidef.one.kronecker
      (cMatrix_rpow_posSemidef (A := M) (s := (1 - alpha) / alpha) hM)
  have hsqrtHerm : (CFC.sqrt base).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg base)).isHermitian
  have h := hW.mul_mul_conjTranspose_same (CFC.sqrt base)
  simpa [sandwichedChannelReferenceKWMatrix, base, W, hsqrtHerm.eq] using h

private theorem real_reference_half_rpow_mul_self
    {x alpha : ℝ} (hx : 0 ≤ x) (halpha : 1 < alpha) :
    x ^ ((1 - alpha) / (2 * alpha)) * x ^ ((1 - alpha) / (2 * alpha)) =
      x ^ ((1 - alpha) / alpha) := by
  by_cases hx0 : x = 0
  · subst x
    have hhalf_ne : (1 - alpha) / (2 * alpha) ≠ 0 := by
      have hnum : 1 - alpha ≠ 0 := by linarith
      have hden : 2 * alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
      exact div_ne_zero hnum hden
    have hfull_ne : (1 - alpha) / alpha ≠ 0 := by
      have hnum : 1 - alpha ≠ 0 := by linarith
      have hden : alpha ≠ 0 := by linarith [lt_trans zero_lt_one halpha]
      exact div_ne_zero hnum hden
    simp [Real.zero_rpow hhalf_ne, Real.zero_rpow hfull_ne]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [← Real.rpow_add hxpos]
    congr 1
    field_simp [ne_of_gt (lt_trans zero_lt_one halpha)]
    ring

private theorem cMatrix_reference_half_rpow_mul_self
    {M : CMatrix b1} (hM : M.PosSemidef) {alpha : ℝ} (halpha : 1 < alpha) :
    CFC.rpow M ((1 - alpha) / (2 * alpha)) *
        CFC.rpow M ((1 - alpha) / (2 * alpha)) =
      CFC.rpow M ((1 - alpha) / alpha) :=
  cMatrix_rpow_mul_rpow_of_posSemidef_scalar hM
    (fun _ hx => real_reference_half_rpow_mul_self hx halpha)

private theorem referenceWeight_mul_self_eq_referencePower
    {M : CMatrix b1} (hM : M.PosSemidef) {alpha : ℝ} (halpha : 1 < alpha) :
    let D : CMatrix (a1 × b1) :=
      Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / (2 * alpha)))
    D * D =
      Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha)) := by
  intro D
  calc
    D * D =
        Matrix.kronecker ((1 : CMatrix a1) * (1 : CMatrix a1))
          (CFC.rpow M ((1 - alpha) / (2 * alpha)) *
            CFC.rpow M ((1 - alpha) / (2 * alpha))) := by
          simpa [D] using
            (Matrix.mul_kronecker_mul (1 : CMatrix a1) (1 : CMatrix a1)
              (CFC.rpow M ((1 - alpha) / (2 * alpha)))
              (CFC.rpow M ((1 - alpha) / (2 * alpha)))).symm
    _ = Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha)) := by
          rw [cMatrix_reference_half_rpow_mul_self hM halpha]
          simp

@[simp]
theorem sandwichedChannelOriginalValueReferenceDensity_of_mem
    (N : CPTPMap a1 b1) (tau : MState a1) {alpha : ℝ} (halpha : 1 < alpha)
    {M : CMatrix b1} (hM : M ∈ MState.fullRankDensityMatrixSet b1) :
    sandwichedChannelOriginalValueReferenceDensity N tau
        (SchattenOrder.ofOneLt halpha) M =
      let sigma : MState b1 :=
        MState.densityMatrixSetState M (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
        (SchattenOrder.ofOneLt halpha) := by
  classical
  simp [sandwichedChannelOriginalValueReferenceDensity, hM]

private theorem sandwichedChannelOriginalValueReferenceDensity_eq_kwMatrix_norm
    [Nonempty a1] (N : CPTPMap a1 b1) (tau : MState a1)
    {alpha : ℝ} (halpha : 1 < alpha)
    {M : CMatrix b1} (hM : M ∈ MState.fullRankDensityMatrixSet b1) :
    sandwichedChannelOriginalValueReferenceDensity N tau
        (SchattenOrder.ofOneLt halpha) M =
      psdSchattenPNorm (sandwichedChannelReferenceKWMatrix N tau alpha M)
        (sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hM.1.posSemidef)
        (SchattenOrder.ofOneLt halpha) := by
  let sigma : MState b1 :=
    MState.densityMatrixSetState M (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
  let X : CMatrix (a1 × a1) := MatrixMap.cbOneToAlphaOriginalInput tau.m alpha
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let base : CMatrix (a1 × b1) := sandwichedChannelReferenceBase N tau alpha
  let D : CMatrix (a1 × b1) :=
    Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / (2 * alpha)))
  let S : CMatrix (a1 × b1) := CFC.sqrt base
  let A : CMatrix (a1 × b1) := D * S
  let B : CMatrix (a1 × b1) := S * D
  have hbase : base.PosSemidef := sandwichedChannelReferenceBase_posSemidef N tau alpha
  have hDherm : D.conjTranspose = D := by
    have hpow :
        (CFC.rpow M ((1 - alpha) / (2 * alpha))).PosSemidef :=
      cMatrix_rpow_posSemidef (A := M) (s := (1 - alpha) / (2 * alpha))
        hM.1.posSemidef
    have hD : D.PosSemidef := Matrix.PosSemidef.one.kronecker hpow
    exact hD.isHermitian.eq
  have hsqrt : S * S = base := by
    simpa [S] using CFC.sqrt_mul_sqrt_self base hbase.nonneg
  have hDsq :
      D * D =
        Matrix.kronecker (1 : CMatrix a1) (CFC.rpow M ((1 - alpha) / alpha)) := by
    simpa [D] using referenceWeight_mul_self_eq_referencePower (a1 := a1)
      hM.1.posSemidef halpha
  have hYeq :
      Phi.referenceLift X = D * base * D := by
    dsimp [Phi, X, sigma]
    rw [sandwichedSideWeightedMap]
    rw [MatrixMap.referenceLift_comp_apply]
    rw [MatrixMap.referenceKron_sandwichedSideWeightMap_apply]
    simp only [MState.densityMatrixSetState_matrix]
    change D * base * D.conjTranspose = D * base * D
    rw [hDherm]
  have hAB :
      A * B = Phi.referenceLift X := by
    calc
      A * B = D * S * (S * D) := by simp [A, B, Matrix.mul_assoc]
      _ = D * (S * S) * D := by noncomm_ring
      _ = D * base * D := by rw [hsqrt]
      _ = Phi.referenceLift X := hYeq.symm
  have hBA :
      B * A = sandwichedChannelReferenceKWMatrix N tau alpha M := by
    calc
      B * A = S * D * (D * S) := by simp [A, B, Matrix.mul_assoc]
      _ = S * (D * D) * S := by noncomm_ring
      _ = S * Matrix.kronecker (1 : CMatrix a1)
            (CFC.rpow M ((1 - alpha) / alpha)) * S := by rw [hDsq]
      _ = sandwichedChannelReferenceKWMatrix N tau alpha M := by
            simp [S, base, sandwichedChannelReferenceKWMatrix, Matrix.mul_assoc]
  have hABpsd :
      (A * B).PosSemidef := by
    rw [hAB]
    exact Phi.referenceLift_mapsPositive hPhi
      (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.psd alpha)
  have hBApsd :
      (B * A).PosSemidef := by
    rw [hBA]
    exact sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hM.1.posSemidef
  have hPhiXpos :
      (Phi.referenceLift X).PosSemidef :=
    Phi.referenceLift_mapsPositive hPhi
      (MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.psd alpha)
  rw [sandwichedChannelOriginalValueReferenceDensity_of_mem N tau
    halpha hM]
  unfold MatrixMap.cbOneToAlphaOriginalValue MatrixMap.CBOneToAlphaOriginalDomain.ofState
  calc
    psdSchattenPNorm (Phi.referenceLift X) hPhiXpos
        (SchattenOrder.ofOneLt halpha) =
      psdSchattenPNorm (A * B) hABpsd (SchattenOrder.ofOneLt halpha) := by
          exact psdSchattenPNorm_congr hAB.symm hPhiXpos hABpsd
            (SchattenOrder.ofOneLt halpha)
    _ = psdSchattenPNorm (B * A) hBApsd (SchattenOrder.ofOneLt halpha) :=
          psdSchattenPNorm_mul_comm hABpsd hBApsd (lt_trans zero_lt_one halpha)
    _ =
        psdSchattenPNorm (sandwichedChannelReferenceKWMatrix N tau alpha M)
          (sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hM.1.posSemidef)
          (SchattenOrder.ofOneLt halpha) := by
          exact psdSchattenPNorm_congr hBA hBApsd
            (sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hM.1.posSemidef)
            (SchattenOrder.ofOneLt halpha)

private theorem cMatrix_conj_le_conj
    {A B S : CMatrix (a1 × b1)} (hAB : A ≤ B) :
    S * A * S.conjTranspose ≤ S * B * S.conjTranspose := by
  rw [Matrix.le_iff]
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hconj : (S * (B - A) * S.conjTranspose).PosSemidef :=
    hdiff.mul_mul_conjTranspose_same S
  have heq :
      S * B * S.conjTranspose - S * A * S.conjTranspose =
        S * (B - A) * S.conjTranspose := by
    noncomm_ring
  simpa [heq]

omit [DecidableEq b1] in
private theorem kronecker_one_left_le_of_le
    {A B : CMatrix b1} (hAB : A ≤ B) :
    Matrix.kronecker (1 : CMatrix a1) A ≤ Matrix.kronecker (1 : CMatrix a1) B := by
  rw [Matrix.le_iff]
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hdiffK :
      (Matrix.kronecker (1 : CMatrix a1) (B - A)).PosSemidef :=
    Matrix.PosSemidef.one.kronecker hdiff
  have heq :
      Matrix.kronecker (1 : CMatrix a1) B -
          Matrix.kronecker (1 : CMatrix a1) A =
        Matrix.kronecker (1 : CMatrix a1) (B - A) := by
    ext i j
    by_cases hij : i.1 = j.1
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply,
        sub_eq_add_neg, mul_add]
    · simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hij,
        sub_eq_add_neg]
  rw [heq]
  exact hdiffK

private theorem sandwichedChannelReferenceKWMatrix_le_convex_combo
    (N : CPTPMap a1 b1) (tau : MState a1)
    {alpha : ℝ} (halpha : 1 < alpha)
    {X Y : CMatrix b1} (hX : X ∈ MState.fullRankDensityMatrixSet b1)
    (hY : Y ∈ MState.fullRankDensityMatrixSet b1)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    sandwichedChannelReferenceKWMatrix N tau alpha (s • X + t • Y) ≤
      s • sandwichedChannelReferenceKWMatrix N tau alpha X +
        t • sandwichedChannelReferenceKWMatrix N tau alpha Y := by
  let p : ℝ := (1 - alpha) / alpha
  let base : CMatrix (a1 × b1) := sandwichedChannelReferenceBase N tau alpha
  let S : CMatrix (a1 × b1) := CFC.sqrt base
  let PX : CMatrix b1 := CFC.rpow X p
  let PY : CMatrix b1 := CFC.rpow Y p
  let Pmix : CMatrix b1 := CFC.rpow (s • X + t • Y) p
  let WX : CMatrix (a1 × b1) := Matrix.kronecker (1 : CMatrix a1) PX
  let WY : CMatrix (a1 × b1) := Matrix.kronecker (1 : CMatrix a1) PY
  let Wmix : CMatrix (a1 × b1) := Matrix.kronecker (1 : CMatrix a1) Pmix
  have hp : p ∈ Set.Icc (-1 : ℝ) 0 := by
    constructor
    · dsimp [p]
      have hapos : 0 < alpha := lt_trans zero_lt_one halpha
      rw [le_div_iff₀ hapos]
      linarith
    · dsimp [p]
      have hapos : 0 < alpha := lt_trans zero_lt_one halpha
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hapos)
  have hpow :
      Pmix ≤ s • PX + t • PY := by
    simpa [Pmix, PX, PY, p] using
      (MState.cMatrix_rpow_convexOn_posDef_of_mem_Icc_neg_one_zero (a := b1) hp).2
        hX.1 hY.1 hs ht hst
  have hW :
      Wmix ≤ s • WX + t • WY := by
    have hK := kronecker_one_left_le_of_le (a1 := a1) hpow
    have hlin :
        Matrix.kronecker (1 : CMatrix a1) (s • PX + t • PY) =
      s • WX + t • WY := by
      dsimp [WX, WY]
      rw [Matrix.kroneckerMap_add_right (fun x y : ℂ => x * y)
        (by intro x y z; exact mul_add x y z)
        (1 : CMatrix a1) (s • PX) (t • PY)]
      rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) s
        (by intro x y; exact mul_smul_comm s x y) (1 : CMatrix a1) PX]
      rw [Matrix.kroneckerMap_smul_right (fun x y : ℂ => x * y) t
        (by intro x y; exact mul_smul_comm t x y) (1 : CMatrix a1) PY]
    rw [hlin] at hK
    simpa [Wmix] using hK
  have hS : S.conjTranspose = S := by
    have hbase : base.PosSemidef := sandwichedChannelReferenceBase_posSemidef N tau alpha
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg base)).isHermitian.eq
  have hconj := cMatrix_conj_le_conj (a1 := a1) (b1 := b1) (S := S) hW
  have hleft :
      S * Wmix * S =
        sandwichedChannelReferenceKWMatrix N tau alpha (s • X + t • Y) := by
    simp [S, Wmix, Pmix, base, p, sandwichedChannelReferenceKWMatrix, Matrix.mul_assoc]
  have hright :
      S * (s • WX + t • WY) * S =
        s • sandwichedChannelReferenceKWMatrix N tau alpha X +
          t • sandwichedChannelReferenceKWMatrix N tau alpha Y := by
    simp [S, WX, WY, PX, PY, base, p, sandwichedChannelReferenceKWMatrix,
      Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc]
  simpa [hS, hleft, hright] using hconj

private theorem real_convex_combo_le_max
    {x y s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    s * x + t * y ≤ max x y := by
  by_cases hxy : x ≤ y
  · have hsx : s * x ≤ s * y := mul_le_mul_of_nonneg_left hxy hs
    calc
      s * x + t * y ≤ s * y + t * y := add_le_add hsx le_rfl
      _ = (s + t) * y := by ring
      _ = y := by rw [hst, one_mul]
      _ ≤ max x y := le_max_right _ _
  · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
    have hty : t * y ≤ t * x := mul_le_mul_of_nonneg_left hyx ht
    calc
      s * x + t * y ≤ s * x + t * x := add_le_add le_rfl hty
      _ = (s + t) * x := by ring
      _ = x := by rw [hst, one_mul]
      _ ≤ max x y := le_max_left _ _

private theorem sandwichedChannelOriginalValueReferenceDensity_quasiconvexOn
    [Nonempty a1] (N : CPTPMap a1 b1) (tau : MState a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    QuasiconvexOn ℝ (MState.fullRankDensityMatrixSet b1)
      (sandwichedChannelOriginalValueReferenceDensity N tau
        (SchattenOrder.ofOneLt halpha)) := by
  rw [quasiconvexOn_iff_le_max]
  refine ⟨MState.fullRankDensityMatrixSet_convex, ?_⟩
  intro X hX Y hY s t hs ht hst
  have hmix : s • X + t • Y ∈ MState.fullRankDensityMatrixSet b1 :=
    MState.fullRankDensityMatrixSet_convex hX hY hs ht hst
  let MX : CMatrix (a1 × b1) := sandwichedChannelReferenceKWMatrix N tau alpha X
  let MY : CMatrix (a1 × b1) := sandwichedChannelReferenceKWMatrix N tau alpha Y
  let MM : CMatrix (a1 × b1) :=
    sandwichedChannelReferenceKWMatrix N tau alpha (s • X + t • Y)
  have hMX : MX.PosSemidef :=
    sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hX.1.posSemidef
  have hMY : MY.PosSemidef :=
    sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hY.1.posSemidef
  have hMM : MM.PosSemidef :=
    sandwichedChannelReferenceKWMatrix_posSemidef N tau alpha hmix.1.posSemidef
  have hcombo : (s • MX + t • MY).PosSemidef :=
    Matrix.PosSemidef.add (Matrix.PosSemidef.smul hMX hs)
      (Matrix.PosSemidef.smul hMY ht)
  have hle :
      MM ≤ s • MX + t • MY := by
    simpa [MM, MX, MY] using
      sandwichedChannelReferenceKWMatrix_le_convex_combo
        N tau halpha hX hY hs ht hst
  have hnorm :
      psdSchattenPNorm MM hMM (SchattenOrder.ofOneLt halpha) ≤
        s * psdSchattenPNorm MX hMX (SchattenOrder.ofOneLt halpha) +
          t * psdSchattenPNorm MY hMY (SchattenOrder.ofOneLt halpha) := by
    exact (psdSchattenPNorm_mono_of_le hMM hcombo halpha hle).trans
      (psdSchattenPNorm_convex_combo_le hMX hMY halpha hs ht hst)
  have hmax :
      s * psdSchattenPNorm MX hMX (SchattenOrder.ofOneLt halpha) +
          t * psdSchattenPNorm MY hMY (SchattenOrder.ofOneLt halpha) ≤
        max (psdSchattenPNorm MX hMX (SchattenOrder.ofOneLt halpha))
          (psdSchattenPNorm MY hMY (SchattenOrder.ofOneLt halpha)) :=
    real_convex_combo_le_max hs ht hst
  rw [sandwichedChannelOriginalValueReferenceDensity_eq_kwMatrix_norm N tau halpha hmix,
    sandwichedChannelOriginalValueReferenceDensity_eq_kwMatrix_norm N tau halpha hX,
    sandwichedChannelOriginalValueReferenceDensity_eq_kwMatrix_norm N tau halpha hY]
  exact hnorm.trans hmax

private theorem sandwichedChannelOriginalValueReferenceDensity_pos_of_mem
    [Nonempty a1] (N : CPTPMap a1 b1) (tau : MState a1)
    {alpha : ℝ} (halpha : 1 < alpha)
    {M : CMatrix b1} (hM : M ∈ MState.fullRankDensityMatrixSet b1) :
    0 < sandwichedChannelOriginalValueReferenceDensity N tau
      (SchattenOrder.ofOneLt halpha) M := by
  let sigma : MState b1 :=
    MState.densityMatrixSetState M (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hM)
  have hsigma : sigma.m.PosDef := by
    simpa [sigma, MState.densityMatrixSetState_matrix] using hM.1
  rw [sandwichedChannelOriginalValueReferenceDensity_of_mem N tau
    halpha hM]
  exact cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
    N sigma hsigma tau (lt_trans zero_lt_one halpha)

private theorem sandwichedChannelOriginalValueLogReferenceDensity_eq_coeff_log_raw_of_mem
    (N : CPTPMap a1 b1) (tau : MState a1) {alpha : ℝ} (halpha : 1 < alpha)
    {M : CMatrix b1} (hM : M ∈ MState.fullRankDensityMatrixSet b1) :
    sandwichedChannelOriginalValueLogReferenceDensity N tau (SchattenOrder.ofOneLt halpha) M =
      alpha / (alpha - 1) *
        log2 (sandwichedChannelOriginalValueReferenceDensity N tau (SchattenOrder.ofOneLt halpha) M) := by
  rw [sandwichedChannelOriginalValueLogReferenceDensity_of_mem N tau halpha hM,
    sandwichedChannelOriginalValueReferenceDensity_of_mem N tau halpha hM]

private theorem sandwichedChannelOriginalValueLogReferenceDensity_quasiconvexOn_of_raw
    [Nonempty a1] (N : CPTPMap a1 b1) (tau : MState a1)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hRawQ :
      QuasiconvexOn ℝ (MState.fullRankDensityMatrixSet b1)
        (sandwichedChannelOriginalValueReferenceDensity N tau
          (SchattenOrder.ofOneLt halpha))) :
    QuasiconvexOn ℝ (MState.fullRankDensityMatrixSet b1)
      (sandwichedChannelOriginalValueLogReferenceDensity N tau
        (SchattenOrder.ofOneLt halpha)) := by
  rw [quasiconvexOn_iff_le_max] at hRawQ ⊢
  refine ⟨hRawQ.1, ?_⟩
  intro X hX Y hY s t hs ht hst
  have hmix : s • X + t • Y ∈ MState.fullRankDensityMatrixSet b1 :=
    hRawQ.1 hX hY hs ht hst
  let raw : CMatrix b1 → ℝ := sandwichedChannelOriginalValueReferenceDensity N tau
    (SchattenOrder.ofOneLt halpha)
  let logged : CMatrix b1 → ℝ :=
    sandwichedChannelOriginalValueLogReferenceDensity N tau
      (SchattenOrder.ofOneLt halpha)
  have hraw :
      raw (s • X + t • Y) ≤ max (raw X) (raw Y) := by
    simpa [raw] using hRawQ.2 hX hY hs ht hst
  have hxpos : 0 < raw X := by
    simpa [raw] using
      sandwichedChannelOriginalValueReferenceDensity_pos_of_mem N tau halpha hX
  have hypos : 0 < raw Y := by
    simpa [raw] using
      sandwichedChannelOriginalValueReferenceDensity_pos_of_mem N tau halpha hY
  have hmixpos : 0 < raw (s • X + t • Y) := by
    simpa [raw] using
      sandwichedChannelOriginalValueReferenceDensity_pos_of_mem N tau halpha hmix
  have hlog :
      log2 (raw (s • X + t • Y)) ≤ log2 (max (raw X) (raw Y)) :=
    log2_mono_of_pos hmixpos hraw
  have hlog_max :
      log2 (max (raw X) (raw Y)) =
        max (log2 (raw X)) (log2 (raw Y)) := by
    by_cases hxy : raw X ≤ raw Y
    · have hlogxy : log2 (raw X) ≤ log2 (raw Y) :=
        log2_mono_of_pos hxpos hxy
      rw [max_eq_right hxy, max_eq_right hlogxy]
    · have hyx : raw Y ≤ raw X := le_of_lt (lt_of_not_ge hxy)
      have hlogyx : log2 (raw Y) ≤ log2 (raw X) :=
        log2_mono_of_pos hypos hyx
      rw [max_eq_left hyx, max_eq_left hlogyx]
  have hlog' :
      log2 (raw (s • X + t • Y)) ≤ max (log2 (raw X)) (log2 (raw Y)) := by
    simpa [hlog_max] using hlog
  let coeff : ℝ := alpha / (alpha - 1)
  have hcoeff : 0 ≤ coeff := le_of_lt (by simpa [coeff] using highAlpha_conjExponent_pos halpha)
  have hscaled :
      coeff * log2 (raw (s • X + t • Y)) ≤
        max (coeff * log2 (raw X)) (coeff * log2 (raw Y)) := by
    by_cases hxy : log2 (raw X) ≤ log2 (raw Y)
    · have hlog_le_y : log2 (raw (s • X + t • Y)) ≤ log2 (raw Y) := by
        simpa [max_eq_right hxy] using hlog'
      have hscaled_xy : coeff * log2 (raw X) ≤ coeff * log2 (raw Y) :=
        mul_le_mul_of_nonneg_left hxy hcoeff
      rw [max_eq_right hscaled_xy]
      exact mul_le_mul_of_nonneg_left hlog_le_y hcoeff
    · have hyx : log2 (raw Y) ≤ log2 (raw X) := le_of_lt (lt_of_not_ge hxy)
      have hlog_le_x : log2 (raw (s • X + t • Y)) ≤ log2 (raw X) := by
        simpa [max_eq_left hyx] using hlog'
      have hscaled_yx : coeff * log2 (raw Y) ≤ coeff * log2 (raw X) :=
        mul_le_mul_of_nonneg_left hyx hcoeff
      rw [max_eq_left hscaled_yx]
      exact mul_le_mul_of_nonneg_left hlog_le_x hcoeff
  have hmix_log :
      logged (s • X + t • Y) = coeff * log2 (raw (s • X + t • Y)) := by
    simpa [logged, raw, coeff] using
      sandwichedChannelOriginalValueLogReferenceDensity_eq_coeff_log_raw_of_mem
        N tau halpha hmix
  have hx_log : logged X = coeff * log2 (raw X) := by
    simpa [logged, raw, coeff] using
      sandwichedChannelOriginalValueLogReferenceDensity_eq_coeff_log_raw_of_mem
        N tau halpha hX
  have hy_log : logged Y = coeff * log2 (raw Y) := by
    simpa [logged, raw, coeff] using
      sandwichedChannelOriginalValueLogReferenceDensity_eq_coeff_log_raw_of_mem
        N tau halpha hY
  simpa [logged, hmix_log, hx_log, hy_log] using hscaled

/-- Continuity of the KW channel Sion objective in the full-rank reference
density variable.

This is the topological half of the `sigma_B` side of
Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`: the map
`sigma_B ↦ ||(S_sigma^(alpha) ∘ N)(Y_tau)||_alpha` is continuous on the
full-rank density domain, hence its positive logarithmic rescaling is
continuous there. -/
private theorem sandwichedChannelOriginalValueLogReferenceDensity_continuousOn_fullRank
    [Nonempty a1] (N : CPTPMap a1 b1) (tau : MState a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ContinuousOn
      (sandwichedChannelOriginalValueLogReferenceDensity N tau
        (SchattenOrder.ofOneLt halpha))
      (MState.fullRankDensityMatrixSet b1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let S := {M : CMatrix b1 // M ∈ MState.fullRankDensityMatrixSet b1}
  let X : CMatrix (a1 × a1) := MatrixMap.cbOneToAlphaOriginalInput tau.m alpha
  let hX : X.PosSemidef := MatrixMap.cbOneToAlphaOriginalInput_posSemidef tau.psd alpha
  let W : S → CMatrix b1 := fun M =>
    CFC.rpow M.1 ((1 - alpha) / (2 * alpha))
  have hWcont : Continuous W := by
    have hcontOn :
        ContinuousOn
          (fun M : CMatrix b1 => CFC.rpow M ((1 - alpha) / (2 * alpha)))
          (MState.fullRankDensityMatrixSet b1) :=
      (MState.cMatrix_rpow_continuousOn_posDef
        (a := b1) ((1 - alpha) / (2 * alpha))).mono (fun M hM => hM.1)
    simpa [S, W, Set.domRestrict_eq, Function.comp_def] using continuousOn_iff_continuous_domRestrict.mp hcontOn
  let base : CMatrix (a1 × b1) := MatrixMap.referenceLift N.map X
  let Y : S → CMatrix (a1 × b1) := fun M =>
    MatrixMap.referenceLift
      (sandwichedSideWeightedMap N
        (MState.densityMatrixSetState M.1
          (MState.fullRankDensityMatrixSet_subset_densityMatrixSet M.2))
        alpha) X
  let Yexplicit : S → CMatrix (a1 × b1) := fun M =>
    Matrix.kronecker (1 : CMatrix a1) (W M) * base *
      Matrix.kronecker (1 : CMatrix a1) (W M)
  have hY_eq : Y = Yexplicit := by
    funext M
    dsimp [Y, Yexplicit, base, W]
    rw [sandwichedSideWeightedMap]
    rw [MatrixMap.referenceLift_comp_apply]
    rw [MatrixMap.referenceKron_sandwichedSideWeightMap_apply]
    have hDherm :
        (Matrix.kronecker (1 : CMatrix a1)
            (CFC.rpow
              (MState.densityMatrixSetState M.1
                (MState.fullRankDensityMatrixSet_subset_densityMatrixSet M.2)).m
              ((1 - alpha) / (2 * alpha)))).conjTranspose =
          Matrix.kronecker (1 : CMatrix a1)
            (CFC.rpow
              (MState.densityMatrixSetState M.1
                (MState.fullRankDensityMatrixSet_subset_densityMatrixSet M.2)).m
              ((1 - alpha) / (2 * alpha))) :=
      (Matrix.PosSemidef.one.kronecker
        (cMatrix_rpow_posSemidef
          (A := (MState.densityMatrixSetState M.1
            (MState.fullRankDensityMatrixSet_subset_densityMatrixSet M.2)).m)
          (s := (1 - alpha) / (2 * alpha))
          (MState.densityMatrixSetState M.1
            (MState.fullRankDensityMatrixSet_subset_densityMatrixSet M.2)).psd)).isHermitian.eq
    rw [hDherm]
    simp [MState.densityMatrixSetState_matrix]
  have hYexplicit_cont : Continuous Yexplicit := by
    have hkr :
        Continuous fun M : S => Matrix.kronecker (1 : CMatrix a1) (W M) := by
      unfold Matrix.kronecker
      exact _root_.continuous_matrix fun x y => by
        simpa [Matrix.kroneckerMap_apply, Pi.mul_def] using
          continuous_const.mul ((hWcont.matrix_elem x.2 y.2))
    exact (hkr.matrix_mul continuous_const).matrix_mul hkr
  have hYcont : Continuous Y := by
    rw [hY_eq]
    exact hYexplicit_cont
  have hYpsd : ∀ M : S, (Y M).PosSemidef := by
    intro M
    exact MatrixMap.referenceLift_mapsPositive
      (sandwichedSideWeightedMap N
        (MState.densityMatrixSetState M.1
          (MState.fullRankDensityMatrixSet_subset_densityMatrixSet M.2))
        alpha)
      (sandwichedSideWeightedMap_completelyPositive N
        (MState.densityMatrixSetState M.1
          (MState.fullRankDensityMatrixSet_subset_densityMatrixSet M.2))
        alpha)
      hX
  let normValue : S → ℝ := fun M =>
    psdSchattenPNorm (Y M) (hYpsd M) (SchattenOrder.ofOneLt halpha)
  have hnorm_cont : Continuous normValue := by
    rw [continuous_iff_continuousAt]
    intro M
    exact psdSchattenPNorm_tendsto_of_tendsto_posSemidef
      (a := a1 × b1) (SchattenOrder.ofOneLt halpha) hYcont.continuousAt hYpsd
      (hYpsd M)
  have hnorm_pos : ∀ M : S, 0 < normValue M := by
    intro M
    have hMpos : (MState.densityMatrixSetState M.1
        (MState.fullRankDensityMatrixSet_subset_densityMatrixSet M.2)).m.PosDef := by
      rw [MState.densityMatrixSetState_matrix]
      exact M.2.1
    have hpos :=
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
        N
        (MState.densityMatrixSetState M.1
          (MState.fullRankDensityMatrixSet_subset_densityMatrixSet M.2))
        hMpos tau (lt_trans zero_lt_one halpha)
    simpa [Y, normValue, MatrixMap.cbOneToAlphaOriginalValue,
      MatrixMap.CBOneToAlphaOriginalDomain.ofState] using hpos
  have hlog_cont : Continuous fun M : S => log2 (normValue M) := by
    rw [continuous_iff_continuousAt]
    intro M
    unfold log2
    exact ((Real.continuousAt_log (ne_of_gt (hnorm_pos M))).div_const _).comp
      hnorm_cont.continuousAt
  have hscaled :
      Continuous fun M : S =>
        alpha / (alpha - 1) * log2 (normValue M) :=
    continuous_const.mul hlog_cont
  have hfun :
      (fun M : S =>
        sandwichedChannelOriginalValueLogReferenceDensity N tau
          (SchattenOrder.ofOneLt halpha) M.1) =
        fun M : S => alpha / (alpha - 1) * log2 (normValue M) := by
    funext M
    rw [sandwichedChannelOriginalValueLogReferenceDensity_of_mem N tau
      halpha M.2]
    unfold normValue Y X
    simp [MatrixMap.cbOneToAlphaOriginalValue,
      MatrixMap.CBOneToAlphaOriginalDomain.ofState]
  change Continuous fun M : S =>
    sandwichedChannelOriginalValueLogReferenceDensity N tau
      (SchattenOrder.ofOneLt halpha) M.1
  rw [hfun]
  exact hscaled

/-- Two-matrix wrapper for the KW channel Sion objective.

The source proof in Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`, applies
Sion to the full-rank reference density `sigma_B` and the input density
`tau_A`.  This wrapper makes both variables matrix-valued so the local Sion API
can be applied directly.  Outside the Sion domains its value is irrelevant. -/
def sandwichedChannelOriginalValueLogMatrix
    (N : CPTPMap a1 b1) (alpha : SchattenOrder)
    (sigmaM : CMatrix b1) (tauM : CMatrix a1) :
    ℝ := by
  classical
  exact
    if hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1 then
      if hTau : tauM ∈ MState.densityMatrixSet a1 then
        let sigma : MState b1 :=
          MState.densityMatrixSetState sigmaM
            (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
        let tau : MState a1 := MState.densityMatrixSetState tauM hTau
        alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              alpha)
      else
        0
    else
      0

@[simp]
theorem sandwichedChannelOriginalValueLogMatrix_of_mem
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    {sigmaM : CMatrix b1} (hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1)
    {tauM : CMatrix a1} (hTau : tauM ∈ MState.densityMatrixSet a1) :
    sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha)
        sigmaM tauM =
      let sigma : MState b1 :=
        MState.densityMatrixSetState sigmaM
          (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
      let tau : MState a1 := MState.densityMatrixSetState tauM hTau
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofOneLt halpha)) := by
  classical
  simp [sandwichedChannelOriginalValueLogMatrix, hSigma, hTau]

private theorem quasiconvexOn_congr_on
    {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [SMul 𝕜 E] [LE β] {s : Set E} {f g : E → β}
    (hfg : ∀ x ∈ s, f x = g x) (hf : QuasiconvexOn 𝕜 s f) :
    QuasiconvexOn 𝕜 s g := by
  intro r
  have hset : {x | x ∈ s ∧ g x ≤ r} = {x | x ∈ s ∧ f x ≤ r} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, by simpa [hfg x hx.1] using hx.2⟩
    · intro hx
      exact ⟨hx.1, by simpa [hfg x hx.1] using hx.2⟩
  simpa [hset] using hf r

private theorem quasiconcaveOn_congr_on
    {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [SMul 𝕜 E] [LE β] {s : Set E} {f g : E → β}
    (hfg : ∀ x ∈ s, f x = g x) (hf : QuasiconcaveOn 𝕜 s f) :
    QuasiconcaveOn 𝕜 s g := by
  intro r
  have hset : {x | x ∈ s ∧ r ≤ g x} = {x | x ∈ s ∧ r ≤ f x} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, by simpa [hfg x hx.1] using hx.2⟩
    · intro hx
      exact ⟨hx.1, by simpa [hfg x hx.1] using hx.2⟩
  simpa [hset] using hf r

/-- Matrix-domain form of the KW channel Sion exchange, isolated to the
reference-density quasiconvexity input on the full-rank side.

The hypothesis records the convexity consequence of the Khatri--Wilde
polar-decomposition/CB-norm argument in `EA_capacity.tex:2080-2084`, separating
that analytic input from the finite-dimensional Sion bookkeeping. -/
private theorem sandwichedChannelOriginalValueLogMatrix_sion_of_reference_quasiconvexOn
    [Nonempty a1] [Nonempty b1] (N : CPTPMap a1 b1)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hRefQ :
      ∀ tau : MState a1,
        QuasiconvexOn ℝ (MState.fullRankDensityMatrixSet b1)
          (sandwichedChannelOriginalValueLogReferenceDensity N tau (SchattenOrder.ofOneLt halpha))) :
    (⨅ sigmaM : CMatrix b1,
      ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
        ⨆ tauM : CMatrix a1,
          ⨆ _hTau : tauM ∈ MState.densityMatrixSet a1,
            ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
              EReal)) =
      ⨆ tauM : CMatrix a1,
        ⨆ _hTau : tauM ∈ MState.densityMatrixSet a1,
          ⨅ sigmaM : CMatrix b1,
            ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
                EReal) := by
  let F : {sigmaM : CMatrix b1 // sigmaM ∈ MState.fullRankDensityMatrixSet b1} →
      {tauM : CMatrix a1 // tauM ∈ MState.densityMatrixSet a1} → EReal :=
    fun sigma tau =>
      ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigma.1 tau.1 : ℝ) : EReal)
  have hnegMem :
      (⨅ tauM : CMatrix a1,
        ⨅ _hTau : tauM ∈ MState.densityMatrixSet a1,
          ⨆ sigmaM : CMatrix b1,
            ⨆ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
              -((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
                EReal)) =
        ⨆ sigmaM : CMatrix b1,
          ⨆ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
            ⨅ tauM : CMatrix a1,
              ⨅ _hTau : tauM ∈ MState.densityMatrixSet a1,
                -((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
                  EReal) := by
    exact MState.sion_iInf_iSup_eq_iSup_iInf
      (MState.densityMatrixSet_nonempty (a := a1))
      (MState.densityMatrixSet_convex (a := a1))
      (MState.densityMatrixSet_isCompact (a := a1))
      (fun sigmaM hSigma => by
        let sigma : MState b1 :=
          MState.densityMatrixSetState sigmaM
            (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
        have hsigmaPos : sigma.m.PosDef := by
          simp only [sigma, MState.densityMatrixSetState_matrix]
          exact hSigma.1
        have hcontE : ContinuousOn
            (fun tauM : CMatrix a1 =>
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
                EReal))
            (MState.densityMatrixSet a1) := by
          have hcontReal :
              ContinuousOn
                (sandwichedChannelOriginalValueLogDensity N sigma (SchattenOrder.ofOneLt halpha))
                (MState.densityMatrixSet a1) :=
            cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_log_continuousOn_density
              N sigma hsigmaPos halpha
          refine continuous_coe_real_ereal.comp_continuousOn ?_
          refine hcontReal.congr ?_
          intro tauM hTau
          simp [sandwichedChannelOriginalValueLogDensity,
            sandwichedChannelOriginalValueLogMatrix, hSigma, hTau, sigma]
        exact ContinuousOn.lowerSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun sigmaM hSigma => by
        let sigma : MState b1 :=
          MState.densityMatrixSetState sigmaM
            (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
        have hsigmaPos : sigma.m.PosDef := by
          simp only [sigma, MState.densityMatrixSetState_matrix]
          exact hSigma.1
        have hq :
            QuasiconcaveOn ℝ (MState.densityMatrixSet a1)
              (sandwichedChannelOriginalValueLogDensity N sigma (SchattenOrder.ofOneLt halpha)) :=
          sandwichedChannelOriginalValueLogDensity_quasiconcaveOn N sigma hsigmaPos halpha
        have hqReal :
            QuasiconcaveOn ℝ (MState.densityMatrixSet a1)
              (fun tauM : CMatrix a1 =>
                sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM) := by
          refine quasiconcaveOn_congr_on ?_ hq
          intro tauM hTau
          simp [sandwichedChannelOriginalValueLogDensity,
            sandwichedChannelOriginalValueLogMatrix, hSigma, hTau, sigma]
        have hfinal := hqReal.antitone_comp antitone_ereal_neg_coe
        simpa [Function.comp_def] using hfinal)
      (MState.fullRankDensityMatrixSet_convex (a := b1))
      (fun tauM hTau => by
        let tau : MState a1 := MState.densityMatrixSetState tauM hTau
        have hcontE : ContinuousOn
            (fun sigmaM : CMatrix b1 =>
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
                EReal))
            (MState.fullRankDensityMatrixSet b1) := by
          have hcontReal :
              ContinuousOn
                (sandwichedChannelOriginalValueLogReferenceDensity N tau (SchattenOrder.ofOneLt halpha))
                (MState.fullRankDensityMatrixSet b1) :=
            sandwichedChannelOriginalValueLogReferenceDensity_continuousOn_fullRank
              N tau halpha
          refine continuous_coe_real_ereal.comp_continuousOn ?_
          refine hcontReal.congr ?_
          intro sigmaM hSigma
          simp [sandwichedChannelOriginalValueLogReferenceDensity,
            sandwichedChannelOriginalValueLogMatrix, hSigma, hTau, tau]
        exact ContinuousOn.upperSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun tauM hTau => by
        let tau : MState a1 := MState.densityMatrixSetState tauM hTau
        have hq :
            QuasiconvexOn ℝ (MState.fullRankDensityMatrixSet b1)
              (sandwichedChannelOriginalValueLogReferenceDensity N tau (SchattenOrder.ofOneLt halpha)) :=
          hRefQ tau
        have hqReal :
            QuasiconvexOn ℝ (MState.fullRankDensityMatrixSet b1)
              (fun sigmaM : CMatrix b1 =>
                sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM) := by
          refine quasiconvexOn_congr_on ?_ hq
          intro sigmaM hSigma
          simp [sandwichedChannelOriginalValueLogReferenceDensity,
            sandwichedChannelOriginalValueLogMatrix, hSigma, hTau, tau]
        have hfinal := hqReal.antitone_comp antitone_ereal_neg_coe
        simpa [Function.comp_def] using hfinal)
  have hnegSub :
      (⨅ tau : {tauM : CMatrix a1 // tauM ∈ MState.densityMatrixSet a1},
        ⨆ sigma : {sigmaM : CMatrix b1 // sigmaM ∈ MState.fullRankDensityMatrixSet b1},
          -F sigma tau) =
        ⨆ sigma : {sigmaM : CMatrix b1 // sigmaM ∈ MState.fullRankDensityMatrixSet b1},
          ⨅ tau : {tauM : CMatrix a1 // tauM ∈ MState.densityMatrixSet a1},
            -F sigma tau := by
    simpa [F, iInf_subtype', iSup_subtype'] using hnegMem
  have hsub := ereal_sion_from_neg F hnegSub
  simpa [F, iInf_subtype', iSup_subtype'] using hsub

/-- Logarithmic CB upper bound for the original weighted-`Γ` candidate
associated with a state reference.

This combines the pure rank-one quotient bound with the state denominator
normalization above.  It is the `U = 1` normalized branch of the polar
decomposition route in KW `EA_capacity.tex:2054-2093`. -/
theorem cbOneToAlphaOriginalValue_state_log_le_CBNormExpression
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1) (tau : MState a1)
    (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            { matrix := tau.m,
              pos := tau.psd,
              trace_le_one := by
                rw [tau.tr']
                norm_num }
            (SchattenOrder.ofOneLt halpha)) ≤
      sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha) := by
  let Y : MatrixMap.CBOneToAlphaOriginalDomain a1 :=
    { matrix := tau.m,
      pos := tau.psd,
      trace_le_one := by
        rw [tau.tr']
        norm_num }
  let psi : a1 × a1 → ℂ :=
    fun ra => CFC.rpow tau.m (1 / (2 * alpha)) ra.1 ra.2
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hinput :
      MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha = rankOneMatrix psi := by
    simpa [Y, psi] using
      MatrixMap.cbOneToAlphaOriginalInput_eq_rankOne_rpow tau.psd alpha
  have hden_matrix :
      Matrix.traceRight (rankOneMatrix psi) =
        Matrix.traceRight
          (MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha) := by
    rw [← hinput]
  have hden_one :
      psdSchattenPNorm
          (Matrix.traceRight (rankOneMatrix psi))
          (traceRight_posSemidef (rankOneMatrix_pos psi))
          (SchattenOrder.ofOneLt halpha) =
        1 := by
    calc
      psdSchattenPNorm
          (Matrix.traceRight (rankOneMatrix psi))
          (traceRight_posSemidef (rankOneMatrix_pos psi))
          (SchattenOrder.ofOneLt halpha) =
        psdSchattenPNorm
          (Matrix.traceRight
            (MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha))
          (traceRight_posSemidef
            (MatrixMap.cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
          (SchattenOrder.ofOneLt halpha) := by
            exact psdSchattenPNorm_congr hden_matrix _ _
              (SchattenOrder.ofOneLt halpha)
      _ = 1 := by
            simpa [Y] using
              cbOneToAlphaOriginalInput_state_denominator_eq_one tau halpha_pos
  have hden_pos :
      0 <
        psdSchattenPNorm
          (Matrix.traceRight (rankOneMatrix psi))
          (traceRight_posSemidef (rankOneMatrix_pos psi))
          (SchattenOrder.ofOneLt halpha) := by
    rw [hden_one]
    norm_num
  have hnum_eq :
      psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix psi))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos psi))
          (SchattenOrder.ofOneLt halpha) =
        MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y
          (SchattenOrder.ofOneLt halpha) := by
    unfold MatrixMap.cbOneToAlphaOriginalValue
    have hnum_matrix :
        MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix psi) =
          MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (MatrixMap.cbOneToAlphaOriginalInput Y.matrix alpha) := by
      rw [← hinput]
    exact psdSchattenPNorm_congr hnum_matrix _ _ (SchattenOrder.ofOneLt halpha)
  have hnum_pos :
      0 <
        psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix psi))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos psi))
          (SchattenOrder.ofOneLt halpha) := by
    rw [hnum_eq]
    exact cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
      N sigma hsigma tau halpha_pos
  have hmain :=
    sandwichedPureRankOneLogQuotient_le_CBNormExpression
      N sigma halpha psi hden_pos hnum_pos
  rw [hden_one, div_one] at hmain
  rw [hnum_eq] at hmain
  simpa [Y] using hmain

/-- Fixed-side-reference form of KW `EA_capacity.tex:2090-2093`.

After the CB original-domain supremum is restricted to `Tr[Y_R] = 1`, the
weighted-channel CB expression is the supremum over normalized input states
`tau_R`.  This is the logarithmic scalar shell needed before the channel-level
Sion exchange. -/
theorem sandwichedRenyiCBNormExpression_eq_sSup_stateOriginalValue_log
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    (hsigma : sigma.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha) =
      sSup (Set.range fun tau : MState a1 =>
        alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              (SchattenOrder.ofOneLt halpha))) := by
  let Phi : MatrixMap a1 b1 := sandwichedSideWeightedMap N sigma alpha
  let hPhi : MatrixMap.IsCompletelyPositive Phi :=
    sandwichedSideWeightedMap_completelyPositive N sigma alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let v : MState a1 → ℝ := fun tau =>
    MatrixMap.cbOneToAlphaOriginalValue Phi hPhi
      (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
      (SchattenOrder.ofOneLt halpha)
  have : Nonempty (MState a1) := ⟨(MState.uniform : MState a1)⟩
  have hnorm :
      MatrixMap.cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) =
        sSup (Set.range v) := by
    simpa [v, MatrixMap.cbOneToAlphaStateOriginalValueSet] using
      MatrixMap.cbOneToAlphaNorm_eq_sSup_stateOriginalValueSet_of_one_lt
        (a1 := a1) Phi hPhi halpha
  have hbdd : BddAbove (Set.range v) := by
    refine ⟨MatrixMap.cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha), ?_⟩
    rintro y ⟨tau, rfl⟩
    exact MatrixMap.cbOneToAlphaOriginalValue_le_cbOneToAlphaNorm_of_one_lt
      Phi hPhi halpha (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
  have hpos : ∀ x ∈ Set.range v, 0 < x := by
    rintro x ⟨tau, rfl⟩
    exact cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_pos_of_state
      N sigma hsigma tau (lt_trans zero_lt_one halpha)
  have hlogSup :
      sSup (log2 '' Set.range v) = log2 (sSup (Set.range v)) :=
    log2_sSup_image_eq (Set.range_nonempty v) hbdd hpos
  have hlogImage :
      log2 '' Set.range v = Set.range fun tau : MState a1 => log2 (v tau) := by
    ext x
    constructor
    · rintro ⟨y, ⟨tau, rfl⟩, rfl⟩
      exact ⟨tau, rfl⟩
    · rintro ⟨tau, rfl⟩
      exact ⟨v tau, ⟨tau, rfl⟩, rfl⟩
  have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
    simpa [coeff] using highAlpha_conjExponent_pos halpha)
  have hmulSup :
      coeff * sSup (Set.range fun tau : MState a1 => log2 (v tau)) =
        sSup (Set.range fun tau : MState a1 => coeff * log2 (v tau)) := by
    rw [sSup_range, sSup_range]
    exact Real.mul_iSup_of_nonneg hcoeff_nonneg
      (fun tau : MState a1 => log2 (v tau))
  unfold sandwichedRenyiCBNormExpression
  change coeff * log2
      (MatrixMap.cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha)) =
    sSup (Set.range fun tau : MState a1 => coeff * log2 (v tau))
  rw [hnorm]
  calc
    coeff * log2 (sSup (Set.range v)) =
        coeff * sSup (Set.range fun tau : MState a1 => log2 (v tau)) := by
          rw [← hlogSup, hlogImage]
    _ = sSup (Set.range fun tau : MState a1 => coeff * log2 (v tau)) := hmulSup

/-- Full-rank side-reference form of the last KW channel rewrite before Sion.

This is the `inf_{sigma_B} log sup_{rho_R}` surface in
`EA_capacity.tex:2087-2092`, with the fixed-`sigma_B` endpoint supplied by
`sandwichedRenyiCBNormExpression_eq_sSup_stateOriginalValue_log`.  The KW Sion
exchange that upgrades this to equality with the optimized channel mutual
information is `sandwichedChannelAlternateSionExchange_proved`. -/
theorem fullRankCB_sInf_EReal_eq_iInf_stateOriginalValue_log_iSup
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
      ((sandwichedRenyiCBNormExpression N sigma.1
        (SchattenOrder.ofOneLt halpha) : ℝ) : EReal)) =
      ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
        ((sSup (Set.range fun tau : MState a1 =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                (SchattenOrder.ofOneLt halpha))) : ℝ) : EReal) := by
  rw [sInf_range]
  apply iInf_congr
  intro sigma
  rw [sandwichedRenyiCBNormExpression_eq_sSup_stateOriginalValue_log
    N sigma.1 sigma.2 halpha]

/-- Fixed pure-input KW CB upper bound.

This is the arbitrary-input version of the channel alternate-expression
direction in `EA_capacity.tex:2054-2093`: once a full-rank side reference
`sigma_B` is fixed, the sandwiched mutual information of any full-support
channel output is bounded by the logarithmic CB norm of the weighted channel
map. -/
theorem inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    (psi : Ket (a1 × a1))
    (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE psi alpha ≤
      ((sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha) : ℝ) : EReal) := by
  let rho : MState (a1 × b1) := N.hypothesisTestingOutputState psi
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let weighted : a1 × a1 → ℂ :=
    Matrix.mulVec
      (Matrix.kronecker (CFC.rpow psi.state.traceRight.m s) (1 : CMatrix a1))
      psi.vec
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hmarg : rho.traceRight = psi.state.traceRight := by
    simpa [rho] using CPTPOp.hypothesisTestingOutputState_traceRight N psi
  have hProdSupport :
      Matrix.Supports (rho.traceRight.prod rho.traceLeft).m
        (rho.traceRight.prod sigma).m := by
    simpa [MState.prod_m] using
      Matrix.Supports.kronecker_right_of_posDef
        rho.traceRight.m rho.traceLeft.m sigma.m hsigma
  have hSupport :
      Matrix.Supports rho.m (rho.traceRight.prod sigma).m :=
    rho.matrix_supports_prod_marginals.trans hProdSupport
  let inner : CMatrix (a1 × b1) :=
    MState.sandwichedRenyiReferenceInner rho (rho.traceRight.prod sigma).m alpha
  let hinner : inner.PosSemidef :=
    MState.sandwichedRenyiReferenceInner_posSemidef rho
      (rho.traceRight.prod sigma).psd alpha
  have hinner_eq :
      inner =
        MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
          (rankOneMatrix weighted) := by
    simpa [inner, rho, s, weighted] using
      referenceInner_eq_referenceLift_weightedRankOne
        N sigma psi hsigma halpha
  have hnorm_eq :
      psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha) =
        psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix weighted))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos weighted))
          (SchattenOrder.ofOneLt halpha) := by
    exact psdSchattenPNorm_congr hinner_eq hinner _ (SchattenOrder.ofOneLt halpha)
  have hcandidate_eq :
      rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
        ((alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                (rankOneMatrix weighted))
              (MatrixMap.referenceLift_mapsPositive
                (sandwichedSideWeightedMap N sigma alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                (rankOneMatrix_pos weighted))
              (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
    calc
      rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
          ((alpha / (alpha - 1) *
            log2 (psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha)) : ℝ) :
            EReal) := by
            simpa [inner, hinner, EReal.coe_div] using
              MState.sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_supports
                rho sigma hSupport halpha
      _ =
          ((alpha / (alpha - 1) *
            log2
              (psdSchattenPNorm
                (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                  (rankOneMatrix weighted))
                (MatrixMap.referenceLift_mapsPositive
                  (sandwichedSideWeightedMap N sigma alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                  (rankOneMatrix_pos weighted))
                (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
            rw [hnorm_eq]
  have hden_one :
      psdSchattenPNorm
          (Matrix.traceRight (rankOneMatrix weighted))
          (traceRight_posSemidef (rankOneMatrix_pos weighted))
          (SchattenOrder.ofOneLt halpha) =
        1 := by
    simpa [s, weighted] using
      weightedRankOne_denominator_eq_one_psd psi halpha
  have hden_pos :
      0 <
        psdSchattenPNorm
          (Matrix.traceRight (rankOneMatrix weighted))
          (traceRight_posSemidef (rankOneMatrix_pos weighted))
          (SchattenOrder.ofOneLt halpha) := by
    rw [hden_one]
    norm_num
  have hweighted_ne : rankOneMatrix weighted ≠ 0 := by
    intro hzero
    have hpartial_zero :
        Matrix.traceRight (rankOneMatrix weighted) = 0 := by
      rw [hzero]
      ext i j
      simp [Matrix.traceRight]
    have hden_zero :
        psdSchattenPNorm
            (Matrix.traceRight (rankOneMatrix weighted))
            (traceRight_posSemidef (rankOneMatrix_pos weighted))
            (SchattenOrder.ofOneLt halpha) =
          0 := by
      calc
        psdSchattenPNorm
            (Matrix.traceRight (rankOneMatrix weighted))
            (traceRight_posSemidef (rankOneMatrix_pos weighted))
            (SchattenOrder.ofOneLt halpha) =
          psdSchattenPNorm (0 : CMatrix a1) Matrix.PosSemidef.zero
            (SchattenOrder.ofOneLt halpha) := by
            exact psdSchattenPNorm_congr hpartial_zero _ _
              (SchattenOrder.ofOneLt halpha)
        _ = 0 := psdSchattenPNorm_zero (SchattenOrder.ofOneLt halpha)
    have hcontr : (0 : ℝ) = 1 := by
      rw [← hden_one, hden_zero]
    norm_num at hcontr
  have hnum_pos :
      0 <
        psdSchattenPNorm
          (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
            (rankOneMatrix weighted))
          (MatrixMap.referenceLift_mapsPositive
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (rankOneMatrix_pos weighted))
          (SchattenOrder.ofOneLt halpha) := by
    have hPhi_ne :
        MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
          (rankOneMatrix weighted) ≠ 0 :=
      sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
        N sigma hsigma alpha (rankOneMatrix_pos weighted) hweighted_ne
    exact psdSchattenPNorm_pos_of_ne_zero
      (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
        (rankOneMatrix weighted))
      _ hPhi_ne
  have hmain :
      alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
                (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                  (rankOneMatrix weighted))
                (MatrixMap.referenceLift_mapsPositive
                  (sandwichedSideWeightedMap N sigma alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                  (rankOneMatrix_pos weighted))
                (SchattenOrder.ofOneLt halpha) /
              psdSchattenPNorm
                (Matrix.traceRight (rankOneMatrix weighted))
                (traceRight_posSemidef (rankOneMatrix_pos weighted))
                (SchattenOrder.ofOneLt halpha)) ≤
        sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha) :=
    sandwichedPureRankOneLogQuotient_le_CBNormExpression
      N sigma halpha weighted hden_pos hnum_pos
  rw [hden_one, div_one] at hmain
  calc
    N.inputSandwichedRenyiMutualInformationE psi alpha =
        rho.sandwichedRenyiMutualInformationE alpha := by
          rfl
    _ ≤ rho.sandwichedRenyiMutualInformationCandidateE sigma alpha :=
        MState.sandwichedRenyiMutualInformationE_le_candidate rho sigma alpha
    _ =
        ((alpha / (alpha - 1) *
          log2
            (psdSchattenPNorm
              (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
                (rankOneMatrix weighted))
              (MatrixMap.referenceLift_mapsPositive
                (sandwichedSideWeightedMap N sigma alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
                (rankOneMatrix_pos weighted))
              (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := hcandidate_eq
    _ ≤ ((sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr hmain

/-- Full-rank input-marginal canonical branch of the KW CB upper bound.

This is the same weighted-channel estimate as
`inputSandwichedRenyiMutualInformationE_le_CBNormExpression`, specialized to
the canonical purification of a full-rank input state.  The reference marginal
of this purification is the transpose of the input state, hence full rank. -/
theorem inputSandwichedRenyiMutualInformationE_canonical_traceLeft_le_CBNormExpression
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1) (tau : MState a1)
    (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE tau.canonicalPurification alpha ≤
      ((sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha) : ℝ) : EReal) := by
  exact inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    N sigma tau.canonicalPurification hsigma halpha

/-- KW canonical-input equality before taking the CB supremum.

This isolates the exact bridge in `EA_capacity.tex:2054-2079`: after replacing
the pure channel input by the swapped canonical purification of a full-rank
input state, the sandwiched candidate against a full-rank side reference is
the logarithm of the corresponding CB `1 → alpha` original-domain value. -/
theorem swappedCanonical_sandwichedRenyiMutualInformationCandidateE_eq_cbOriginalValue
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1) (tau : MState a1)
    (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    let psi : Ket (a1 × a1) :=
      tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
    let rho : MState (a1 × b1) := N.hypothesisTestingOutputState psi
    rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
      ((alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            { matrix := tau.m,
              pos := tau.psd,
              trace_le_one := by
                rw [tau.tr']
                norm_num }
            (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
  let psi : Ket (a1 × a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  let rho : MState (a1 × b1) := N.hypothesisTestingOutputState psi
  let Y : MatrixMap.CBOneToAlphaOriginalDomain a1 :=
    { matrix := tau.m,
      pos := tau.psd,
      trace_le_one := by
        rw [tau.tr']
        norm_num }
  change rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
    ((alpha / (alpha - 1) *
      log2
        (MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y
          (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal)
  have hmarg : rho.traceRight = tau := by
    calc
      rho.traceRight = psi.state.traceRight := by
        simpa [rho] using CPTPOp.hypothesisTestingOutputState_traceRight N psi
      _ = tau := by
        simpa [psi] using MState.canonicalPurification_reindex_prodComm_traceRight tau
  have hSupport :
      Matrix.Supports rho.m (rho.traceRight.prod sigma).m :=
    MState.supports_traceRight_prod_of_side_posDef rho sigma hsigma
  let inner : CMatrix (a1 × b1) :=
    MState.sandwichedRenyiReferenceInner rho (rho.traceRight.prod sigma).m alpha
  let hinner : inner.PosSemidef :=
    MState.sandwichedRenyiReferenceInner_posSemidef rho
      (rho.traceRight.prod sigma).psd alpha
  have hinner_eq :
      inner =
        MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha)
          (MatrixMap.cbOneToAlphaOriginalInput tau.m alpha) := by
    simpa [inner, rho, psi] using
      swappedCanonical_referenceInner_eq_referenceLift_cbOneToAlphaOriginalInput
        N sigma tau halpha
  have hnorm_eq :
      psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha) =
        MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y
          (SchattenOrder.ofOneLt halpha) := by
    unfold MatrixMap.cbOneToAlphaOriginalValue
    exact psdSchattenPNorm_congr hinner_eq hinner _ (SchattenOrder.ofOneLt halpha)
  calc
    rho.sandwichedRenyiMutualInformationCandidateE sigma alpha =
        ((alpha / (alpha - 1) *
          log2 (psdSchattenPNorm inner hinner (SchattenOrder.ofOneLt halpha)) : ℝ) :
          EReal) := by
          simpa [inner, hinner, EReal.coe_div] using
            MState.sandwichedRenyiMutualInformationCandidateE_eq_coe_schattenNorm_of_supports
              rho sigma hSupport halpha
    _ =
        ((alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
              Y
              (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
          rw [hnorm_eq]

theorem inputSandwichedRenyiMutualInformationE_swappedCanonical_le_CBNormExpression
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1) (tau : MState a1)
    (hsigma : sigma.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha ≤
      ((sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha) : ℝ) : EReal) := by
  exact inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    N sigma (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) hsigma halpha

/-- Full-rank channel outputs make a fixed-input sandwiched objective a real
full-rank side-reference infimum.

This is the bookkeeping needed to turn the KW pointwise estimate
`input ≤ CB(sigma)` into a real lower bound for the whole full-rank
CB-expression family. -/
theorem inputSandwichedRenyiMutualInformationE_eq_coe_fullRankCandidateReal_sInf
    [Nonempty b1] (N : CPTPMap a1 b1) (psi : Ket (a1 × a1))
    (hOut : (N.hypothesisTestingOutputState psi).m.PosDef)
    (hOutA : (N.hypothesisTestingOutputState psi).traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE psi alpha =
      ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        MState.sandwichedRenyiMutualInformationCandidateRealPosDef
          (N.hypothesisTestingOutputState psi) sigma.1 hOut hOutA sigma.2
          alpha halpha) : ℝ) : EReal) := by
  have : Nonempty {sigma : MState b1 // sigma.m.PosDef} :=
    ⟨⟨(MState.uniform : MState b1), MState.uniform_posDef⟩⟩
  let rho : MState (a1 × b1) := N.hypothesisTestingOutputState psi
  have hraw :
      rho.sandwichedRenyiMutualInformationE alpha =
        sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
          (MState.sandwichedRenyiMutualInformationCandidateRealPosDef
            rho sigma.1 hOut hOutA sigma.2 alpha halpha : EReal)) := by
    simpa [rho] using
      MState.sandwichedRenyiMutualInformationE_eq_sInf_fullRankCandidateReal
        rho hOut hOutA halpha
  have hbdd :
      BddBelow (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        MState.sandwichedRenyiMutualInformationCandidateRealPosDef
          rho sigma.1 hOut hOutA sigma.2 alpha halpha) := by
    exact MState.sandwichedRenyiMutualInformationCandidateRealPosDef_bddBelow
      rho hOut hOutA halpha
  calc
    N.inputSandwichedRenyiMutualInformationE psi alpha =
        rho.sandwichedRenyiMutualInformationE alpha := by
          rfl
    _ =
        sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
          (MState.sandwichedRenyiMutualInformationCandidateRealPosDef
            rho sigma.1 hOut hOutA sigma.2 alpha halpha : EReal)) := hraw
    _ =
        ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
          MState.sandwichedRenyiMutualInformationCandidateRealPosDef
            rho sigma.1 hOut hOutA sigma.2 alpha halpha) : ℝ) : EReal) := by
          exact ereal_sInf_range_coe_eq_coe_real_sInf
            (fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
              MState.sandwichedRenyiMutualInformationCandidateRealPosDef
                rho sigma.1 hOut hOutA sigma.2 alpha halpha)
            hbdd
    _ =
        ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
          MState.sandwichedRenyiMutualInformationCandidateRealPosDef
            (N.hypothesisTestingOutputState psi) sigma.1 hOut hOutA sigma.2
            alpha halpha) : ℝ) : EReal) := by
          rfl

/-- Fixed full-rank input form of the KW channel alternate expression.

This is the `inf_sigma` identification used after the source Sion step in
`EA_capacity.tex:2054-2093`: for the swapped canonical purification of a
full-rank input state, the full-rank side-reference optimization is exactly the
corresponding CB original-domain value optimization. -/
theorem inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_coe_fullRankCBOriginalValue_sInf
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) (tau : MState a1) (htau : tau.m.PosDef)
    (hOut : (N.hypothesisTestingOutputState
      (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1))).m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha =
      ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma.1 alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              (SchattenOrder.ofOneLt halpha))) : ℝ) : EReal) := by
  let psi : Ket (a1 × a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  let rho : MState (a1 × b1) := N.hypothesisTestingOutputState psi
  have hOutRho : rho.m.PosDef := by
    simpa [rho, psi] using hOut
  have hmarg : rho.traceRight = tau := by
    calc
      rho.traceRight = psi.state.traceRight := by
        simpa [rho] using CPTPOp.hypothesisTestingOutputState_traceRight N psi
      _ = tau := by
        simpa [psi] using MState.canonicalPurification_reindex_prodComm_traceRight tau
  have hOutARho : rho.traceRight.m.PosDef := by
    rw [hmarg]
    exact htau
  have hinput :
      N.inputSandwichedRenyiMutualInformationE psi alpha =
        ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
          MState.sandwichedRenyiMutualInformationCandidateRealPosDef
            (N.hypothesisTestingOutputState psi) sigma.1
            (by simpa [psi] using hOut) (by simpa [rho] using hOutARho)
            sigma.2 alpha halpha) : ℝ) : EReal) := by
    exact inputSandwichedRenyiMutualInformationE_eq_coe_fullRankCandidateReal_sInf
      N psi (by simpa [psi] using hOut) (by simpa [rho] using hOutARho) halpha
  let f : {sigma : MState b1 // sigma.m.PosDef} → ℝ := fun sigma =>
    MState.sandwichedRenyiMutualInformationCandidateRealPosDef
      (N.hypothesisTestingOutputState psi) sigma.1
      (by simpa [psi] using hOut) (by simpa [rho] using hOutARho)
      sigma.2 alpha halpha
  let g : {sigma : MState b1 // sigma.m.PosDef} → ℝ := fun sigma =>
    alpha / (alpha - 1) *
      log2
        (MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma.1 alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
          (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
          (SchattenOrder.ofOneLt halpha))
  have hfg : f = g := by
    funext sigma
    have hcandidate :
        rho.sandwichedRenyiMutualInformationCandidateE sigma.1 alpha =
          (MState.sandwichedRenyiMutualInformationCandidateRealPosDef
            rho sigma.1 hOutRho hOutARho sigma.2 alpha halpha : EReal) :=
      MState.sandwichedRenyiMutualInformationCandidateE_eq_coe_candidateRealPosDef
        rho sigma.1 hOutRho hOutARho sigma.2 halpha
    have hcb :
        rho.sandwichedRenyiMutualInformationCandidateE sigma.1 alpha =
          ((g sigma : ℝ) : EReal) := by
      simpa [rho, psi, g, MatrixMap.CBOneToAlphaOriginalDomain.ofState] using
        swappedCanonical_sandwichedRenyiMutualInformationCandidateE_eq_cbOriginalValue
          N sigma.1 tau sigma.2 halpha
    have hE :
        ((MState.sandwichedRenyiMutualInformationCandidateRealPosDef
          rho sigma.1 hOutRho hOutARho sigma.2 alpha halpha : ℝ) : EReal) =
          ((g sigma : ℝ) : EReal) :=
      hcandidate.symm.trans hcb
    have hreal : MState.sandwichedRenyiMutualInformationCandidateRealPosDef
        rho sigma.1 hOutRho hOutARho sigma.2 alpha halpha = g sigma :=
      EReal.coe_eq_coe_iff.mp hE
    simpa [f, rho] using hreal
  calc
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha =
        N.inputSandwichedRenyiMutualInformationE psi alpha := by
          rfl
    _ = ((sInf (Set.range f) : ℝ) : EReal) := by
          simpa [f] using hinput
    _ = ((sInf (Set.range g) : ℝ) : EReal) := by
          rw [hfg]
    _ =
        ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                (SchattenOrder.ofOneLt halpha))) : ℝ) : EReal) := by
          rfl

/-- Fixed full-rank input form of the KW channel alternate expression using the
high-`alpha` full-rank side-reference reduction.

Unlike
`inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_coe_fullRankCBOriginalValue_sInf`,
this form does not assume the channel output on the canonical input is
positive definite.  It is the support-closure version of the fixed-input
`inf_sigma` identity needed before the KW Sion exchange in
`EA_capacity.tex:2039-2093`. -/
theorem inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_iInf_fullRankCBOriginalValue
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) (tau : MState a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha =
      ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
        ((alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma.1 alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
  let psi : Ket (a1 × a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  let rho : MState (a1 × b1) := N.hypothesisTestingOutputState psi
  have hraw :
      rho.sandwichedRenyiMutualInformationE alpha =
        ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          rho.sandwichedRenyiMutualInformationCandidateE sigma.1 alpha := by
    exact MState.sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_highAlpha
      rho halpha
  calc
    N.inputSandwichedRenyiMutualInformationE
        (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)) alpha =
        rho.sandwichedRenyiMutualInformationE alpha := by
          rfl
    _ =
        ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          rho.sandwichedRenyiMutualInformationCandidateE sigma.1 alpha := hraw
    _ =
        ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ((alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
          apply iInf_congr
          intro sigma
          simpa [rho, psi, MatrixMap.CBOneToAlphaOriginalDomain.ofState] using
            swappedCanonical_sandwichedRenyiMutualInformationCandidateE_eq_cbOriginalValue
              N sigma.1 tau sigma.2 halpha

/-- Fixed full-rank input branch after the KW Sion exchange, without assuming
the corresponding channel output is full rank. -/
theorem fullRankCBOriginalValue_iInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) (tau : MState a1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
      ((alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  let psi : Ket (a1 × a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  have heq :
      N.inputSandwichedRenyiMutualInformationE psi alpha =
        ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ((alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
    simpa [psi] using
      inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_iInf_fullRankCBOriginalValue
        N tau halpha
  rw [← heq]
  exact N.inputSandwichedRenyiMutualInformationE_le_channel psi alpha

/-- Post-Sion channel branch for KW `EA_capacity.tex:2084-2093`.

Once the source minimax step has exchanged
`inf_sigma sup_tau` with `sup_tau inf_sigma`, each fixed `tau_R` branch is the
swapped-canonical channel input already identified above, hence is bounded by
the optimized channel sandwiched-Renyi mutual information.  This theorem does
not perform the Sion exchange; it is the exact no-extra-hypothesis endpoint
needed immediately after that exchange. -/
theorem fullRankCBOriginalValue_iSup_iInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    (⨆ tau : MState a1, ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
      ((alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  refine iSup_le ?_
  intro tau
  exact fullRankCBOriginalValue_iInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    N tau halpha

/-- The exact KW channel alternate-expression Sion exchange.

This is the minimax step in Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`.
It is a transparent predicate that only keeps the staging lemmas below readable;
`sandwichedChannelAlternateSionExchange_proved` discharges it. -/
def sandwichedChannelAlternateSionExchange
    (N : CPTPMap a1 b1) (alpha : ℝ) (halpha : 1 < alpha) : Prop :=
  (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
    ((sSup (Set.range fun tau : MState a1 =>
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofOneLt halpha))) : ℝ) : EReal)) =
    (⨆ tau : MState a1,
      ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
        ((alpha / (alpha - 1) *
          log2
            (MatrixMap.cbOneToAlphaOriginalValue
              (sandwichedSideWeightedMap N sigma.1 alpha)
              (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
              (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
              (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))

/-- The fixed full-rank `sigma_B` source-side logarithmic channel objective is
bounded above by the corresponding CB-norm expression.

This is the scalar boundedness bridge needed to identify the real `sSup`
surface in `sandwichedChannelAlternateSionExchange` with the `EReal` supremum
surface used by the matrix-domain Sion theorem. -/
private theorem sandwichedChannelOriginalValueLogDensity_bddAbove
    [Nonempty a1] (N : CPTPMap a1 b1) (sigma : MState b1)
    (hsigma : sigma.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    BddAbove (Set.range fun tau : MState a1 =>
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofOneLt halpha))) := by
  refine ⟨sandwichedRenyiCBNormExpression N sigma (SchattenOrder.ofOneLt halpha), ?_⟩
  rintro y ⟨tau, rfl⟩
  exact cbOneToAlphaOriginalValue_state_log_le_CBNormExpression
    N sigma tau hsigma halpha

/-- Predicate-form KW channel Sion exchange from the remaining reference-side
quasiconvexity input.

This theorem removes the bookkeeping gap between the matrix-domain Sion
surface and the channel alternate-expression predicate.  The only remaining
mathematical hypothesis is exactly the reference-density quasiconvexity in
Khatri--Wilde 2024, `EA_capacity.tex:2080-2084`, before the
polar-decomposition/CB-norm argument is applied. -/
theorem sandwichedChannelAlternateSionExchange_of_reference_quasiconvexOn
    [Nonempty a1] [Nonempty b1] (N : CPTPMap a1 b1)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hRefQ :
      ∀ tau : MState a1,
        QuasiconvexOn ℝ (MState.fullRankDensityMatrixSet b1)
          (sandwichedChannelOriginalValueLogReferenceDensity N tau (SchattenOrder.ofOneLt halpha))) :
    N.sandwichedChannelAlternateSionExchange alpha halpha := by
  have : Nonempty (MState a1) := ⟨(MState.uniform : MState a1)⟩
  let stateLog : {sigma : MState b1 // sigma.m.PosDef} → MState a1 → ℝ :=
    fun sigma tau =>
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofOneLt halpha))
  have hleftSup :
      (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
        ((sSup (Set.range fun tau : MState a1 => stateLog sigma tau) : ℝ) :
          EReal)) =
        (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ⨆ tau : MState a1, ((stateLog sigma tau : ℝ) : EReal)) := by
    apply iInf_congr
    intro sigma
    have hbdd :
        BddAbove (Set.range fun tau : MState a1 => stateLog sigma tau) := by
      simpa [stateLog] using
        sandwichedChannelOriginalValueLogDensity_bddAbove
          N sigma.1 sigma.2 halpha
    exact (ereal_sSup_range_coe_eq_coe_real_sSup
      (fun tau : MState a1 => stateLog sigma tau) hbdd).symm
  have hmatrix :=
    sandwichedChannelOriginalValueLogMatrix_sion_of_reference_quasiconvexOn
      N halpha hRefQ
  have hleftToMatrix :
      (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ⨆ tau : MState a1, ((stateLog sigma tau : ℝ) : EReal)) =
        (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
            ⨆ tau : MState a1,
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tau.m :
                ℝ) : EReal)) := by
    calc
      (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ⨆ tau : MState a1, ((stateLog sigma tau : ℝ) : EReal))
          =
        (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ⨆ tau : MState a1,
            ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigma.1.m tau.m :
              ℝ) : EReal)) := by
          apply iInf_congr
          intro sigma
          apply iSup_congr
          intro tau
          have hSigma : sigma.1.m ∈ MState.fullRankDensityMatrixSet b1 :=
            ⟨sigma.2, sigma.1.tr'⟩
          have hTau : tau.m ∈ MState.densityMatrixSet a1 :=
            MState.state_matrix_mem_densityMatrixSet tau
          have hSigmaState :
              MState.densityMatrixSetState sigma.1.m
                  (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma) =
                sigma.1 := by
            apply MState.ext
            exact MState.densityMatrixSetState_matrix sigma.1.m
              (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
          have hTauState :
              MState.densityMatrixSetState tau.m hTau = tau := by
            apply MState.ext
            exact MState.densityMatrixSetState_matrix tau.m hTau
          simp [stateLog, sandwichedChannelOriginalValueLogMatrix, hSigma, hTau,
            hSigmaState, hTauState]
      _ =
        (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
            ⨆ tau : MState a1,
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tau.m :
                ℝ) : EReal)) := by
          exact fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
            (fun sigmaM : CMatrix b1 =>
              ⨆ tau : MState a1,
                ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tau.m :
                  ℝ) : EReal))
  have hrightFromMatrix :
      (⨆ tau : MState a1,
          ⨅ sigmaM : CMatrix b1,
            ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tau.m : ℝ) :
                EReal)) =
        (⨆ tau : MState a1,
          ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
            ((stateLog sigma tau : ℝ) : EReal)) := by
    apply iSup_congr
    intro tau
    calc
      (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
            ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tau.m : ℝ) :
              EReal))
          =
        (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigma.1.m tau.m :
            ℝ) : EReal)) := by
          exact (fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
            (fun sigmaM : CMatrix b1 =>
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tau.m :
                ℝ) : EReal))).symm
      _ =
        (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ((stateLog sigma tau : ℝ) : EReal)) := by
          apply iInf_congr
          intro sigma
          have hSigma : sigma.1.m ∈ MState.fullRankDensityMatrixSet b1 :=
            ⟨sigma.2, sigma.1.tr'⟩
          have hTau : tau.m ∈ MState.densityMatrixSet a1 :=
            MState.state_matrix_mem_densityMatrixSet tau
          have hSigmaState :
              MState.densityMatrixSetState sigma.1.m
                  (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma) =
                sigma.1 := by
            apply MState.ext
            exact MState.densityMatrixSetState_matrix sigma.1.m
              (MState.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma)
          have hTauState :
              MState.densityMatrixSetState tau.m hTau = tau := by
            apply MState.ext
            exact MState.densityMatrixSetState_matrix tau.m hTau
          simp [stateLog, sandwichedChannelOriginalValueLogMatrix, hSigma, hTau,
            hSigmaState, hTauState]
  have hmatrixState :
      (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ⨆ tau : MState a1, ((stateLog sigma tau : ℝ) : EReal)) =
        (⨆ tau : MState a1,
          ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
            ((stateLog sigma tau : ℝ) : EReal)) := by
    calc
      (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
          ⨆ tau : MState a1, ((stateLog sigma tau : ℝ) : EReal))
          =
        (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
            ⨆ tau : MState a1,
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tau.m :
                ℝ) : EReal)) := hleftToMatrix
      _ =
        (⨅ sigmaM : CMatrix b1,
          ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
            ⨆ tauM : CMatrix a1,
              ⨆ _hTau : tauM ∈ MState.densityMatrixSet a1,
                ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
                  EReal)) := by
          apply iInf_congr
          intro sigmaM
          apply iInf_congr
          intro hSigma
          exact state_iSup_matrix_eq_densityMatrixSet_iSup
            (fun tauM : CMatrix a1 =>
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
                EReal))
      _ =
        (⨆ tauM : CMatrix a1,
          ⨆ _hTau : tauM ∈ MState.densityMatrixSet a1,
            ⨅ sigmaM : CMatrix b1,
              ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
                ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
                  EReal)) := hmatrix
      _ =
        (⨆ tau : MState a1,
          ⨅ sigmaM : CMatrix b1,
            ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
              ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tau.m : ℝ) :
                EReal)) := by
          exact (state_iSup_matrix_eq_densityMatrixSet_iSup
            (fun tauM : CMatrix a1 =>
              ⨅ sigmaM : CMatrix b1,
                ⨅ _hSigma : sigmaM ∈ MState.fullRankDensityMatrixSet b1,
                  ((sandwichedChannelOriginalValueLogMatrix N (SchattenOrder.ofOneLt halpha) sigmaM tauM : ℝ) :
                    EReal))).symm
      _ =
        (⨆ tau : MState a1,
          ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
            ((stateLog sigma tau : ℝ) : EReal)) := hrightFromMatrix
  unfold sandwichedChannelAlternateSionExchange
  simpa [stateLog] using hleftSup.trans hmatrixState

/-- The KW channel alternate-expression Sion exchange with no remaining
reference-side quasiconvexity hypothesis.

This closes the local minimax gap from Khatri--Wilde 2024,
`EA_capacity.tex:2080-2084`: the full-rank reference density objective is
quasiconvex by the polar-decomposition/CB-norm rewrite above, and the existing
matrix-domain Sion wrapper then gives the channel predicate used by the
alternate expression. -/
theorem sandwichedChannelAlternateSionExchange_proved
    [Nonempty a1] [Nonempty b1] (N : CPTPMap a1 b1)
    {alpha : ℝ} (halpha : 1 < alpha) :
    N.sandwichedChannelAlternateSionExchange alpha halpha := by
  refine sandwichedChannelAlternateSionExchange_of_reference_quasiconvexOn
    N halpha ?_
  intro tau
  exact sandwichedChannelOriginalValueLogReferenceDensity_quasiconvexOn_of_raw
    N tau halpha
    (sandwichedChannelOriginalValueReferenceDensity_quasiconvexOn N tau halpha)

/-- Channel alternate-expression lower branch after the KW Sion exchange.

This theorem does not prove Sion's minimax hypothesis.  It records the exact
handoff after the source exchange in
KhatriWilde2024Principles, `EA_capacity.tex:2080-2093`: the already-proved
`inf_sigma sup_tau` CB surface is rewritten to the post-Sion
`sup_tau inf_sigma` surface, and every fixed `tau` branch is the swapped
canonical input branch bounded by the channel mutual information. -/
theorem fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hSion :
      (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
        ((sSup (Set.range fun tau : MState a1 =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                (SchattenOrder.ofOneLt halpha))) : ℝ) : EReal)) =
        (⨆ tau : MState a1,
          ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
            ((alpha / (alpha - 1) *
              log2
                (MatrixMap.cbOneToAlphaOriginalValue
                  (sandwichedSideWeightedMap N sigma.1 alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                  (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                  (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))) :
    sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
      ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  rw [fullRankCB_sInf_EReal_eq_iInf_stateOriginalValue_log_iSup N halpha]
  rw [hSion]
  exact fullRankCBOriginalValue_iSup_iInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    N halpha

/-- Predicate-form version of
`fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion`. -/
theorem fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sionExchange
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hSion : N.sandwichedChannelAlternateSionExchange alpha halpha) :
    sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
      ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  exact fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion
    N halpha (by simpa [sandwichedChannelAlternateSionExchange] using hSion)

/-- KW channel alternate-expression lower branch with the Sion exchange proved.

This is the `≥` half of `EA_capacity.tex:2039-2093`, after discharging the
minimax step in `sandwichedChannelAlternateSionExchange_proved`. -/
theorem fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
      ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal)) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  exact fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sionExchange
    N halpha (sandwichedChannelAlternateSionExchange_proved N halpha)

/-- Fixed full-rank input branch after the KW Sion exchange.

Once the inner `inf_sigma` has been identified with the swapped canonical
input sandwiched mutual information, optimizing over channel inputs bounds it
by the channel sandwiched-Renyi mutual information. -/
theorem fullRankCBOriginalValue_sInf_swappedCanonical_le_sandwichedRenyiMutualInformationE
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) (tau : MState a1) (htau : tau.m.PosDef)
    (hOut : (N.hypothesisTestingOutputState
      (tau.canonicalPurification.reindex (Equiv.prodComm a1 a1))).m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
      alpha / (alpha - 1) *
        log2
          (MatrixMap.cbOneToAlphaOriginalValue
            (sandwichedSideWeightedMap N sigma.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
            (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
            (SchattenOrder.ofOneLt halpha))) : ℝ) : EReal) ≤
      N.sandwichedRenyiMutualInformationE alpha := by
  let psi : Ket (a1 × a1) :=
    tau.canonicalPurification.reindex (Equiv.prodComm a1 a1)
  have heq :
      N.inputSandwichedRenyiMutualInformationE psi alpha =
        ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                (SchattenOrder.ofOneLt halpha))) : ℝ) : EReal) := by
    simpa [psi] using
      inputSandwichedRenyiMutualInformationE_swappedCanonical_eq_coe_fullRankCBOriginalValue_sInf
        N tau htau hOut halpha
  rw [← heq]
  exact N.inputSandwichedRenyiMutualInformationE_le_channel psi alpha

/-- A single full-rank channel output gives a real lower bound for the KW
full-rank weighted-channel CB-expression family.

The proof follows KW's channel alternate-expression route in the already
formalized direction: the fixed input objective is a finite real quantity, and
the pointwise weighted-rank-one estimate bounds it by every full-rank
`sigma_B` CB expression. -/
theorem sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_input_output_posDef
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) (psi : Ket (a1 × a1))
    (hOut : (N.hypothesisTestingOutputState psi).m.PosDef)
    (hOutA : (N.hypothesisTestingOutputState psi).traceRight.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    BddBelow (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
      sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)) := by
  have : Nonempty {sigma : MState b1 // sigma.m.PosDef} :=
    ⟨⟨(MState.uniform : MState b1), MState.uniform_posDef⟩⟩
  let lower : ℝ :=
    sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
      MState.sandwichedRenyiMutualInformationCandidateRealPosDef
        (N.hypothesisTestingOutputState psi) sigma.1 hOut hOutA sigma.2 alpha
        halpha)
  refine ⟨lower, ?_⟩
  rintro y ⟨sigma, rfl⟩
  have hinput_eq :
      N.inputSandwichedRenyiMutualInformationE psi alpha =
        ((lower : ℝ) : EReal) := by
    simpa [lower] using
      inputSandwichedRenyiMutualInformationE_eq_coe_fullRankCandidateReal_sInf
        N psi hOut hOutA halpha
  have hpoint :
      N.inputSandwichedRenyiMutualInformationE psi alpha ≤
        ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal) :=
    inputSandwichedRenyiMutualInformationE_le_CBNormExpression
      N sigma.1 psi sigma.2 halpha
  have hreal :
      ((lower : ℝ) : EReal) ≤
        ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal) := by
    simpa [hinput_eq] using hpoint
  exact EReal.coe_le_coe_iff.mp hreal

/-- Full-support output hypotheses supply the `BddBelow` side condition needed
by the KW full-rank CB `sInf` bookkeeping. -/
theorem sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : Ket (a1 × a1),
      (N.hypothesisTestingOutputState psi).m.PosDef) :
    BddBelow (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
      sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)) := by
  let psi0 : Ket (a1 × a1) := default
  have hpsi0 : (N.hypothesisTestingOutputState psi0).m.PosDef := hOut psi0
  have hpsi0A : (N.hypothesisTestingOutputState psi0).traceRight.m.PosDef :=
    MState.traceRight_posDef_of_posDef (N.hypothesisTestingOutputState psi0) hpsi0
  exact sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_input_output_posDef
    N psi0 hpsi0 hpsi0A halpha

/-- Boundedness below of the full-rank weighted-channel CB-expression family.

This removes the full-support output hypothesis from
`sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef`.  The
fixed-input lower bound is a real number because the support-convention state
alternate expression realizes the corresponding input mutual information as a
coerced real value. -/
theorem sandwichedRenyiCBNormExpression_fullRank_bddBelow
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    BddBelow (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
      sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)) := by
  let psi0 : Ket (a1 × a1) := default
  let rho : MState (a1 × b1) := N.hypothesisTestingOutputState psi0
  let chi : Ket ((a1 × b1) × (a1 × b1)) :=
    rho.canonicalPurification.reindex (Equiv.prodComm (a1 × b1) (a1 × b1))
  let lower : ℝ :=
    alpha / (alpha - 1) *
      log2
        (sSup (Set.range fun τC : MState (a1 × b1) =>
          psdSchattenPNorm
            (Ket.sandwichedMutualInformationACTraceMatrix
              chi.state.marginalAB.traceRight chi τC alpha)
            (Ket.sandwichedMutualInformationACTraceMatrix_posSemidef
              chi.state.marginalAB.traceRight chi τC alpha)
            (Ket.sandwichedAlternateSchattenOrder halpha)))
  refine ⟨lower, ?_⟩
  rintro y ⟨sigma, rfl⟩
  have hchiAB : chi.state.marginalAB = rho := by
    simpa [chi] using MState.canonicalPurification_swap_marginalAB rho
  have hinput_eq :
      N.inputSandwichedRenyiMutualInformationE psi0 alpha = (lower : EReal) := by
    change rho.sandwichedRenyiMutualInformationE alpha = (lower : EReal)
    rw [← hchiAB]
    simpa [lower] using
      Ket.sandwichedRenyiMutualInformationE_eq_coeff_log2_sSup_ACTraceMatrixNorm_support
        chi halpha
  have hpoint :
      N.inputSandwichedRenyiMutualInformationE psi0 alpha ≤
        ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal) :=
    inputSandwichedRenyiMutualInformationE_le_CBNormExpression
      N sigma.1 psi0 sigma.2 halpha
  have hreal :
      (lower : EReal) ≤
        ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal) := by
    simpa [hinput_eq] using hpoint
  exact EReal.coe_le_coe_iff.mp hreal

/-- KW channel alternate-expression upper bound.

This combines the source-shaped weighted-rank-one step with the
`sup_psi`/`inf_sigma` order bridge.  The proof follows
`EA_capacity.tex:2039-2093`, using the supported PSD-reference branch for
possibly singular input marginals. -/
theorem sandwichedRenyiMutualInformationE_le_fullRankCB_sInf
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hBelow :
      BddBelow (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha))) :
    N.sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
  refine sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_of_input_le
    N (SchattenOrder.ofOneLt halpha) hBelow ?_
  intro psi sigma
  exact inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    N sigma.1 psi sigma.2 halpha

/-- KW channel alternate-expression upper bound in extended-real `inf` form.

This is the same `sup_psi`/`inf_sigma` order step as
`sandwichedRenyiMutualInformationE_le_fullRankCB_sInf`, but it keeps the
infimum in `EReal`.  Consequently it does not need a separate bounded-below or
full-support hypothesis; those scalar side conditions only enter when one
identifies this `EReal` infimum with a coerced real infimum. -/
theorem sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_EReal
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    N.sandwichedRenyiMutualInformationE alpha ≤
      sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal)) := by
  rw [N.sandwichedRenyiMutualInformationE_eq_sSup]
  refine csSup_le (N.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  rintro y ⟨psi, rfl⟩
  refine le_csInf (Set.range_nonempty _) ?_
  rintro z ⟨sigma, rfl⟩
  exact inputSandwichedRenyiMutualInformationE_le_CBNormExpression
    N sigma.1 psi sigma.2 halpha

/-- Channel alternate-expression equality assuming exactly the source Sion
exchange from KW `EA_capacity.tex:2080-2084`.

The forward inequality is the weighted-rank-one/CB upper bound; the reverse
inequality is
`fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion`.  The
displayed Sion exchange is itself proved in
`sandwichedChannelAlternateSionExchange_proved`, which is what the
unconditional version below feeds in. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sion
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hSion :
      (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
        ((sSup (Set.range fun tau : MState a1 =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                (SchattenOrder.ofOneLt halpha))) : ℝ) : EReal)) =
        (⨆ tau : MState a1,
          ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
            ((alpha / (alpha - 1) *
              log2
                (MatrixMap.cbOneToAlphaOriginalValue
                  (sandwichedSideWeightedMap N sigma.1 alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                  (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                  (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))) :
    N.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal)) := by
  exact le_antisymm
    (sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_EReal N halpha)
    (fullRankCB_sInf_EReal_le_sandwichedRenyiMutualInformationE_of_sion
      N halpha hSion)

/-- Predicate-form version of
`sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sion`. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sionExchange
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hSion : N.sandwichedChannelAlternateSionExchange alpha halpha) :
    N.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal)) := by
  exact sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sion
    N halpha (by simpa [sandwichedChannelAlternateSionExchange] using hSion)

/-- KW channel alternate expression in `EReal` form, with the Sion step proved.

This is the source statement `EA_capacity.tex:2090-2093` at the full-rank
side-reference surface.  The real-valued `sInf` version below goes through the
separate scalar boundedness/full-support bridge. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    N.sandwichedRenyiMutualInformationE alpha =
      sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        ((sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha) : ℝ) : EReal)) := by
  exact sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sionExchange
    N halpha (sandwichedChannelAlternateSionExchange_proved N halpha)

/-- KW channel alternate expression in real `sInf` form, without full-support
output hypotheses.

The boundedness side condition is supplied by
`sandwichedRenyiCBNormExpression_fullRank_bddBelow`, whose lower bound uses the
support-convention state alternate expression. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha) :
    N.sandwichedRenyiMutualInformationE alpha =
      ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
  let S := {sigma : MState b1 // sigma.m.PosDef}
  let f : S → ℝ := fun sigma =>
    sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)
  have hBelow : BddBelow (Set.range f) := by
    simpa [S, f] using sandwichedRenyiCBNormExpression_fullRank_bddBelow N halpha
  rw [sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal N halpha]
  simpa [S, f] using ereal_sInf_range_coe_eq_coe_real_sInf f hBelow

/-- Real-valued full-rank CB alternate expression after the KW Sion exchange,
under the full-support output condition that supplies the real `sInf`
boundedness side condition.

This packages two already separated source obligations:
* KW `EA_capacity.tex:2080-2084`, the Sion exchange, supplied as `hSion`;
* the scalar full-rank closure from `EReal` to real `sInf`, supplied here by
  full-support channel outputs.

It is intentionally not the unconditional channel alternate-expression theorem:
the Sion exchange is still an explicit hypothesis. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sion
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : Ket (a1 × a1),
      (N.hypothesisTestingOutputState psi).m.PosDef)
    (hSion :
      (⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
        ((sSup (Set.range fun tau : MState a1 =>
          alpha / (alpha - 1) *
            log2
              (MatrixMap.cbOneToAlphaOriginalValue
                (sandwichedSideWeightedMap N sigma.1 alpha)
                (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                (SchattenOrder.ofOneLt halpha))) : ℝ) : EReal)) =
        (⨆ tau : MState a1,
          ⨅ sigma : {sigma : MState b1 // sigma.m.PosDef},
            ((alpha / (alpha - 1) *
              log2
                (MatrixMap.cbOneToAlphaOriginalValue
                  (sandwichedSideWeightedMap N sigma.1 alpha)
                  (sandwichedSideWeightedMap_completelyPositive N sigma.1 alpha)
                  (MatrixMap.CBOneToAlphaOriginalDomain.ofState tau)
                  (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))) :
    N.sandwichedRenyiMutualInformationE alpha =
      ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
  let S := {sigma : MState b1 // sigma.m.PosDef}
  let f : S → ℝ := fun sigma => sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)
  have hBelow : BddBelow (Set.range f) := by
    simpa [S, f] using
      sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef N halpha hOut
  have hE :
      N.sandwichedRenyiMutualInformationE alpha =
        sInf (Set.range fun sigma : S => ((f sigma : ℝ) : EReal)) := by
    simpa [S, f] using
      sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_EReal_of_sion
        N halpha hSion
  have hInf :
      sInf (Set.range fun sigma : S => ((f sigma : ℝ) : EReal)) =
        ((sInf (Set.range f) : ℝ) : EReal) :=
    ereal_sInf_range_coe_eq_coe_real_sInf f hBelow
  simpa [S, f] using hE.trans hInf

/-- Predicate-form version of
`sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sion`. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sionExchange
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : Ket (a1 × a1),
      (N.hypothesisTestingOutputState psi).m.PosDef)
    (hSion : N.sandwichedChannelAlternateSionExchange alpha halpha) :
    N.sandwichedRenyiMutualInformationE alpha =
      ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
  exact sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sion
    N halpha hOut (by simpa [sandwichedChannelAlternateSionExchange] using hSion)

/-- Real-valued full-rank CB alternate expression with Sion proved, under the
existing full-support output condition that supplies scalar boundedness. -/
theorem sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : Ket (a1 × a1),
      (N.hypothesisTestingOutputState psi).m.PosDef) :
    N.sandwichedRenyiMutualInformationE alpha =
      ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
  exact sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sionExchange
    N halpha hOut (sandwichedChannelAlternateSionExchange_proved N halpha)

/-- Full-support channel outputs supply the boundedness side condition in the
KW channel alternate-expression upper bound. -/
theorem sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_of_outputs_posDef
    [Nonempty a1] [Nonempty b1]
    (N : CPTPMap a1 b1) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut : ∀ psi : Ket (a1 × a1),
      (N.hypothesisTestingOutputState psi).m.PosDef) :
    N.sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun sigma : {sigma : MState b1 // sigma.m.PosDef} =>
        sandwichedRenyiCBNormExpression N sigma.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) := by
  exact sandwichedRenyiMutualInformationE_le_fullRankCB_sInf N halpha
    (sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N halpha hOut)

end CPTPOp

end
