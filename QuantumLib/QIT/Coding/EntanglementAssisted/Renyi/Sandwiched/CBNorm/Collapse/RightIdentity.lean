/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Collapse.LeftIdentity

/-!
# Right identity-reference collapse for the positive `alpha → alpha` norm

This module proves the right-reference version of the Khatri--Wilde source
collapse step for completely positive maps.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u v w

noncomputable section

open MState

variable {r : Type w} {a : Type u} {b : Type v}
variable [Fintype r] [DecidableEq r]
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace MatrixMap

private def AlphaToAlphaTraceDomain.partialTraceRightIdentity
    {alpha : SchattenOrder}
    (Y : AlphaToAlphaTraceDomain (a × r) alpha) :
    AlphaToAlphaTraceDomain a alpha where
  matrix := Matrix.traceRight Y.matrix
  pos := traceRight_posSemidef (a := a) (b := r) Y.pos
  trace_le_one := by
    have htrace := congrArg Complex.re
      (Matrix.traceRight_trace Y.matrix)
    simpa [htrace] using Y.trace_le_one

private theorem kron_id_signPermutation_conj
    (Phi : MatrixMap a b)
    (ε : r → Bool) (π : Equiv.Perm r) (X : CMatrix (a × r)) :
    MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map
        ((localRightUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (a × r)) *
          X *
          star (localRightUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (a × r))) =
      (localRightUnitary (a := b)
          (permutationUnitary π * diagonalSignUnitary ε) :
            CMatrix (b × r)) *
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map X) *
          star (localRightUnitary (a := b)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (b × r)) := by
  ext br br'
  rw [MatrixMap.kron_idChannel_apply_slice]
  have hslice :
      (fun i i' =>
        (((localRightUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (a × r)) *
          X *
          star (localRightUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (a × r))) (i, br.2) (i', br'.2))) =
        (boolSignComplex (ε (π br.2)) * boolSignComplex (ε (π br'.2))) •
          (fun i i' => X (i, π br.2) (i', π br'.2)) := by
    ext i i'
    rw [localRightSignPermutationUnitary_conj_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hslice]
  let c : ℂ := boolSignComplex (ε (π br.2)) * boolSignComplex (ε (π br'.2))
  let S : CMatrix a := Matrix.of fun i i' => X (i, π br.2) (i', π br'.2)
  have hmap := congrFun (congrFun
    (LinearMap.map_smul Phi
      c S) br.1) br'.1
  change Phi (c • S) br.1 br'.1 =
    ((localRightUnitary (a := b)
        (permutationUnitary π * diagonalSignUnitary ε) : CMatrix (b × r)) *
      MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map X *
      star (localRightUnitary (a := b)
        (permutationUnitary π * diagonalSignUnitary ε) : CMatrix (b × r))) br br'
  calc
    Phi (c • S) br.1 br'.1 = (c • Phi S) br.1 br'.1 := hmap
    _ =
        ((localRightUnitary (a := b)
            (permutationUnitary π * diagonalSignUnitary ε) : CMatrix (b × r)) *
          MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map X *
          star (localRightUnitary (a := b)
            (permutationUnitary π * diagonalSignUnitary ε) : CMatrix (b × r))) br br' := by
          rw [localRightSignPermutationUnitary_conj_apply]
          rw [MatrixMap.kron_idChannel_apply_slice]
          simp [c, S, Matrix.smul_apply, mul_assoc, mul_left_comm, mul_comm]

private theorem kron_id_signPermutation_cpValue_eq
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : ℝ))
    (ε : r → Bool) (π : Equiv.Perm r)
    (Y : CMatrix (a × r)) (hY : Y.PosSemidef) :
    cpValueOnPSD
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
        (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
        alpha
        ((localRightUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (a × r)) *
          Y *
          star (localRightUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (a × r))) =
      cpValueOnPSD
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
        (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
        alpha Y := by
  let K : MatrixMap (a × r) (b × r) :=
    MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp
  let Uin : Matrix.unitaryGroup (a × r) ℂ :=
    localRightUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε)
  let Uout : Matrix.unitaryGroup (b × r) ℂ :=
    localRightUnitary (a := b) (permutationUnitary π * diagonalSignUnitary ε)
  have halpha_pos : 0 < (alpha : ℝ) := lt_trans zero_lt_one halpha
  have hinv_nonneg : 0 ≤ 1 / (alpha : ℝ) :=
    one_div_nonneg.mpr (le_of_lt halpha_pos)
  have hconj_pos : ((Uin : CMatrix (a × r)) * Y * star (Uin : CMatrix (a × r))).PosSemidef :=
    posSemidef_unitary_conj_forward hY Uin
  rw [cpValueOnPSD_of_pos K hK alpha hconj_pos,
    cpValueOnPSD_of_pos K hK alpha hY]
  unfold cpPsdSchattenRpowValue
  have hrpow :
      CFC.rpow ((Uin : CMatrix (a × r)) * Y * star (Uin : CMatrix (a × r)))
          (1 / (alpha : ℝ)) =
        (Uin : CMatrix (a × r)) * CFC.rpow Y (1 / (alpha : ℝ)) *
          star (Uin : CMatrix (a × r)) :=
    cMatrix_rpow_unitary_conj_forward hY Uin hinv_nonneg
  have hmap :
      K (CFC.rpow ((Uin : CMatrix (a × r)) * Y * star (Uin : CMatrix (a × r)))
          (1 / (alpha : ℝ))) =
        (Uout : CMatrix (b × r)) * K (CFC.rpow Y (1 / (alpha : ℝ))) *
          star (Uout : CMatrix (b × r)) := by
    rw [hrpow]
    simpa [K, Uin, Uout] using
      kron_id_signPermutation_conj (r := r) (a := a) (b := b)
        Phi ε π (CFC.rpow Y (1 / (alpha : ℝ)))
  have hKY : (K (CFC.rpow Y (1 / (alpha : ℝ)))).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive K hK
      (CFC.rpow Y (1 / (alpha : ℝ)))
      (cMatrix_rpow_posSemidef (A := Y) (s := 1 / (alpha : ℝ)) hY)
  have hKYconj :
      ((Uout : CMatrix (b × r)) * K (CFC.rpow Y (1 / (alpha : ℝ))) *
        star (Uout : CMatrix (b × r))).PosSemidef :=
    posSemidef_unitary_conj_forward hKY Uout
  calc
    psdSchattenPNorm
        (K (CFC.rpow ((Uin : CMatrix (a × r)) * Y * star (Uin : CMatrix (a × r)))
          (1 / (alpha : ℝ)))) _ alpha =
      psdSchattenPNorm
        ((Uout : CMatrix (b × r)) * K (CFC.rpow Y (1 / (alpha : ℝ))) *
          star (Uout : CMatrix (b × r)))
        hKYconj alpha := by
          exact psdSchattenPNorm_congr hmap _ hKYconj alpha
    _ = psdSchattenPNorm (K (CFC.rpow Y (1 / (alpha : ℝ)))) hKY alpha :=
          psdSchattenPNorm_unitary_conj_forward hKY Uout alpha

private theorem kron_id_traceValue_tensor_uniform
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : ℝ))
    (Y : AlphaToAlphaTraceDomain a alpha) :
    cpValueOnPSD
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
        (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
        alpha
        (Y.matrix ⊗ₖ (MState.uniform : MState r).m) =
      alphaToAlphaTraceValue Phi hPhi Y := by
  let K : MatrixMap (a × r) (b × r) :=
    MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp
  have hprod : (Y.matrix ⊗ₖ (MState.uniform : MState r).m).PosSemidef :=
    Y.pos.kronecker (MState.uniform : MState r).psd
  rw [cpValueOnPSD_of_pos K hK alpha hprod]
  unfold cpPsdSchattenRpowValue alphaToAlphaTraceValue
  have hpow :
      CFC.rpow (Y.matrix ⊗ₖ (MState.uniform : MState r).m)
          (1 / (alpha : ℝ)) =
        (CFC.rpow Y.matrix (1 / (alpha : ℝ))) ⊗ₖ
          (CFC.rpow (MState.uniform : MState r).m (1 / (alpha : ℝ))) :=
    cMatrix_rpow_kronecker Y.pos (MState.uniform : MState r).psd (1 / (alpha : ℝ))
  let Ypow : CMatrix a := CFC.rpow Y.matrix (1 / (alpha : ℝ))
  let Rpow : CMatrix r :=
    CFC.rpow (MState.uniform : MState r).m (1 / (alpha : ℝ))
  have hYpow : Ypow.PosSemidef :=
    cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : ℝ)) Y.pos
  have hRpow : Rpow.PosSemidef :=
    cMatrix_rpow_posSemidef
      (A := (MState.uniform : MState r).m) (s := 1 / (alpha : ℝ))
      (MState.uniform : MState r).psd
  have hPhiYpow : (Phi Ypow).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Ypow hYpow
  have hmap :
      K (CFC.rpow (Y.matrix ⊗ₖ (MState.uniform : MState r).m)
          (1 / (alpha : ℝ))) =
        (Phi Ypow) ⊗ₖ Rpow := by
    rw [hpow]
    change MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map
        (Ypow ⊗ₖ Rpow) =
      (Phi Ypow) ⊗ₖ Rpow
    rw [MatrixMap.kron_map_of_kron_state, CPTPOp.idChannel_map]
  have hKpow : (K (CFC.rpow (Y.matrix ⊗ₖ (MState.uniform : MState r).m)
          (1 / (alpha : ℝ)))).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive K hK
      (CFC.rpow (Y.matrix ⊗ₖ (MState.uniform : MState r).m)
          (1 / (alpha : ℝ)))
      (cMatrix_rpow_posSemidef
        (A := Y.matrix ⊗ₖ (MState.uniform : MState r).m)
        (s := 1 / (alpha : ℝ)) hprod)
  calc
    psdSchattenPNorm
        (K (CFC.rpow (Y.matrix ⊗ₖ (MState.uniform : MState r).m)
          (1 / (alpha : ℝ)))) _ alpha =
      psdSchattenPNorm ((Phi Ypow) ⊗ₖ Rpow)
        (hPhiYpow.kronecker hRpow) alpha := by
          exact psdSchattenPNorm_congr hmap hKpow
            (hPhiYpow.kronecker hRpow) alpha
    _ =
      psdSchattenPNorm (Phi Ypow) hPhiYpow alpha *
        psdSchattenPNorm Rpow hRpow alpha := by
          rw [psdSchattenPNorm_kronecker hPhiYpow hRpow alpha]
    _ = psdSchattenPNorm (Phi Ypow) hPhiYpow alpha := by
          rw [uniform_rpow_schatten_norm_eq_one (r := r) halpha]
          simp

private theorem kron_id_traceValue_le_partialTrace_traceValue
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : ℝ))
    (Y : AlphaToAlphaTraceDomain (a × r) alpha) :
    alphaToAlphaTraceValue
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
        (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
        Y ≤
      alphaToAlphaTraceValue Phi hPhi (Y.partialTraceRightIdentity (r := r)) := by
  classical
  let K : MatrixMap (a × r) (b × r) :=
    MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp
  let ι := (r → Bool) × Equiv.Perm r
  let U : ι → Matrix.unitaryGroup r ℂ :=
    fun idx => permutationUnitary idx.2 * diagonalSignUnitary idx.1
  let X : ι → CMatrix (a × r) := fun idx =>
    (localRightUnitary (a := a) (U idx) : CMatrix (a × r)) *
      Y.matrix *
      star (localRightUnitary (a := a) (U idx) : CMatrix (a × r))
  have hX : ∀ idx : ι, (X idx).PosSemidef := by
    intro idx
    simpa [X, U] using
      posSemidef_unitary_conj_forward Y.pos
        (localRightUnitary (a := a) (U idx))
  have hvalue_eq : ∀ idx : ι,
      cpValueOnPSD K hK alpha (X idx) =
        alphaToAlphaTraceValue K hK Y := by
    intro idx
    rcases idx with ⟨ε, π⟩
    rw [show X (ε, π) =
        (localRightUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (a × r)) *
          Y.matrix *
          star (localRightUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (a × r)) by
        simp [X, U]]
    rw [kron_id_signPermutation_cpValue_eq
      (r := r) (a := a) (b := b) Phi hPhi halpha ε π Y.matrix Y.pos]
    rw [cpValueOnPSD_of_pos K hK alpha Y.pos]
    rfl
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hsum_weights : ∑ _idx : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    simp
  have hstart :
      alphaToAlphaTraceValue K hK Y =
        ∑ idx : ι, (Fintype.card ι : ℝ)⁻¹ *
          cpValueOnPSD K hK alpha (X idx) := by
    calc
      alphaToAlphaTraceValue K hK Y =
          (∑ _idx : ι, (Fintype.card ι : ℝ)⁻¹) *
            alphaToAlphaTraceValue K hK Y := by rw [hsum_weights, one_mul]
      _ = ∑ idx : ι, (Fintype.card ι : ℝ)⁻¹ *
            alphaToAlphaTraceValue K hK Y := by
            rw [Finset.sum_mul]
      _ = ∑ idx : ι, (Fintype.card ι : ℝ)⁻¹ *
            cpValueOnPSD K hK alpha (X idx) := by
            refine Finset.sum_congr rfl fun idx _ => ?_
            rw [hvalue_eq idx]
  have hjensen :
      (∑ idx : ι, (Fintype.card ι : ℝ)⁻¹ *
          cpValueOnPSD K hK alpha (X idx)) ≤
        cpValueOnPSD K hK alpha
          (∑ idx : ι, (Fintype.card ι : ℝ)⁻¹ • X idx) :=
    cpValueOnPSD_uniform_average_le K hK halpha X hX
  have hcoef :
      ((((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ)) =
        (Fintype.card ι : ℂ)⁻¹ := by
    norm_num [show (Fintype.card ι : ℝ) ≠ 0 from ne_of_gt hcard_pos]
  have htwirl :
      (∑ idx : ι, (Fintype.card ι : ℝ)⁻¹ • X idx) =
        (Matrix.traceRight Y.matrix) ⊗ₖ
          (MState.uniform : MState r).m := by
    change (∑ idx : ι,
        ((((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) • X idx)) =
      (Matrix.traceRight Y.matrix) ⊗ₖ
        (MState.uniform : MState r).m
    rw [hcoef]
    dsimp [X, U, ι]
    exact localRightSignPermutationTwirl_eq_traceRight_kronecker_uniform
      (a := a) (b := r) Y.matrix
  have hproduct :
      cpValueOnPSD K hK alpha
        ((Matrix.traceRight Y.matrix) ⊗ₖ
          (MState.uniform : MState r).m) =
      alphaToAlphaTraceValue Phi hPhi (Y.partialTraceRightIdentity (r := r)) :=
    kron_id_traceValue_tensor_uniform
      (r := r) (a := a) (b := b) Phi hPhi halpha
      (Y.partialTraceRightIdentity (r := r))
  calc
    alphaToAlphaTraceValue K hK Y =
        ∑ idx : ι, (Fintype.card ι : ℝ)⁻¹ *
          cpValueOnPSD K hK alpha (X idx) := hstart
    _ ≤ cpValueOnPSD K hK alpha
          (∑ idx : ι, (Fintype.card ι : ℝ)⁻¹ • X idx) := hjensen
    _ = cpValueOnPSD K hK alpha
          ((Matrix.traceRight Y.matrix) ⊗ₖ
            (MState.uniform : MState r).m) := by
          rw [htwirl]
    _ = alphaToAlphaTraceValue Phi hPhi (Y.partialTraceRightIdentity (r := r)) := hproduct

private theorem alphaToAlphaPositiveValueSet_subset_kron_id
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : ℝ)) :
    alphaToAlphaPositiveValueSet Phi hPhi alpha ⊆
      alphaToAlphaPositiveValueSet
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
        (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
        alpha := by
  rintro x ⟨Z, rfl⟩
  let K : MatrixMap (a × r) (b × r) :=
    MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp
  let R : CMatrix r := (MState.uniform : MState r).m
  let hR : R.PosSemidef := (MState.uniform : MState r).psd
  have halpha_pos : 0 < (alpha : ℝ) := lt_trans zero_lt_one halpha
  have hRnorm_pos : 0 < psdSchattenPNorm R hR alpha := by
    simpa [R, hR] using uniform_schatten_norm_pos (r := r) alpha
  let X : AlphaToAlphaPositiveDomain (a × r) alpha :=
    { matrix := Z.matrix ⊗ₖ R,
      pos := Z.pos.kronecker hR,
      norm_pos := by
        rw [psdSchattenPNorm_kronecker Z.pos hR alpha]
        exact mul_pos Z.norm_pos hRnorm_pos }
  refine ⟨X, ?_⟩
  have hPhiZ : (Phi Z.matrix).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Z.matrix Z.pos
  have hKprod :
      K (Z.matrix ⊗ₖ R) = (Phi Z.matrix) ⊗ₖ R := by
    dsimp [K]
    change MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map
        (Z.matrix ⊗ₖ R) =
      (Phi Z.matrix) ⊗ₖ R
    rw [MatrixMap.kron_map_of_kron_state, CPTPOp.idChannel_map]
  have hKpos : (K (Z.matrix ⊗ₖ R)).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive K hK
      (Z.matrix ⊗ₖ R) (Z.pos.kronecker hR)
  have hnum :
      psdSchattenPNorm (K (Z.matrix ⊗ₖ R)) hKpos alpha =
        psdSchattenPNorm ((Phi Z.matrix) ⊗ₖ R)
          (hPhiZ.kronecker hR) alpha :=
    psdSchattenPNorm_congr hKprod hKpos (hPhiZ.kronecker hR) alpha
  unfold alphaToAlphaPositiveValue
  change
    psdSchattenPNorm (K (Z.matrix ⊗ₖ R)) _ alpha /
      psdSchattenPNorm (Z.matrix ⊗ₖ R) _ alpha =
    psdSchattenPNorm (Phi Z.matrix)
        (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Z.matrix Z.pos)
        alpha /
      psdSchattenPNorm Z.matrix Z.pos alpha
  rw [hnum]
  rw [psdSchattenPNorm_kronecker hPhiZ hR alpha,
    psdSchattenPNorm_kronecker Z.pos hR alpha]
  field_simp [ne_of_gt hRnorm_pos]

private theorem kron_id_positiveValue_eq_zero_or_le_positiveValue
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : ℝ)) :
    ∀ x ∈
      alphaToAlphaPositiveValueSet
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
        (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
        alpha,
      x = 0 ∨ ∃ p ∈ alphaToAlphaPositiveValueSet Phi hPhi alpha, x ≤ p := by
  intro x hx
  rcases hx with ⟨Z, rfl⟩
  let K : MatrixMap (a × r) (b × r) :=
    MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp
  let Y : AlphaToAlphaTraceDomain (a × r) alpha := Z.toTraceDomain halpha
  have htrace_eq :
      alphaToAlphaTraceValue K hK Y = alphaToAlphaPositiveValue K hK Z :=
    alphaToAlphaTraceValue_toTraceDomain_eq_positiveValue K hK halpha Z
  have hle :
      alphaToAlphaPositiveValue K hK Z ≤
        alphaToAlphaTraceValue Phi hPhi (Y.partialTraceRightIdentity (r := r)) := by
    rw [← htrace_eq]
    exact kron_id_traceValue_le_partialTrace_traceValue
      (r := r) (a := a) (b := b) Phi hPhi halpha Y
  rcases alphaToAlphaTraceValue_eq_zero_or_le_positiveValue Phi hPhi halpha
      (Y.partialTraceRightIdentity (r := r)) with hzero | ⟨p, hp, hyp⟩
  · left
    have hx_nonneg : 0 ≤ alphaToAlphaPositiveValue K hK Z :=
      alphaToAlphaPositiveValue_nonneg K hK Z
    exact le_antisymm (by simpa [-CPTPOp.id_map, hzero] using hle) hx_nonneg
  · right
    exact ⟨p, hp, hle.trans hyp⟩

private theorem alphaToAlphaNorm_kron_id_compare
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : ℝ)) :
    alphaToAlphaNorm Phi hPhi alpha ≤
        alphaToAlphaNorm
          (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
          (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
          alpha ∧
      alphaToAlphaNorm
          (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
          (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
          alpha ≤
        alphaToAlphaNorm Phi hPhi alpha := by
  let K : MatrixMap (a × r) (b × r) :=
    MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp
  let P : Set ℝ := alphaToAlphaPositiveValueSet Phi hPhi alpha
  let T : Set ℝ := alphaToAlphaPositiveValueSet K hK alpha
  have hP_nonneg : ∀ x ∈ P, 0 ≤ x := by
    rintro x ⟨Y, rfl⟩
    exact alphaToAlphaPositiveValue_nonneg Phi hPhi Y
  have hT_nonneg : ∀ x ∈ T, 0 ≤ x := by
    rintro x ⟨Y, rfl⟩
    exact alphaToAlphaPositiveValue_nonneg K hK Y
  have hP_subset_T : P ⊆ T := by
    simpa [P, T, K, hK] using
      alphaToAlphaPositiveValueSet_subset_kron_id
        (r := r) (a := a) (b := b) Phi hPhi halpha
  have hT_le_zero_or_P : ∀ x ∈ T, x = 0 ∨ ∃ p ∈ P, x ≤ p := by
    simpa [P, T, K, hK] using
      kron_id_positiveValue_eq_zero_or_le_positiveValue
        (r := r) (a := a) (b := b) Phi hPhi halpha
  have hTbdd_of_hPbdd : BddAbove P → BddAbove T := by
    rintro ⟨M, hM⟩
    refine ⟨max M 0, ?_⟩
    intro x hx
    rcases hT_le_zero_or_P x hx with hzero | ⟨p, hp, hxp⟩
    · rw [hzero]
      exact le_max_right M 0
    · exact hxp.trans ((hM hp).trans (le_max_left M 0))
  have hPbdd_of_hTbdd : BddAbove T → BddAbove P := by
    rintro ⟨M, hM⟩
    exact ⟨M, fun x hx => hM (hP_subset_T hx)⟩
  unfold alphaToAlphaNorm
  change sSup P ≤ sSup T ∧ sSup T ≤ sSup P
  by_cases hPbdd : BddAbove P
  · have hTbdd : BddAbove T := hTbdd_of_hPbdd hPbdd
    constructor
    · refine Real.sSup_le ?_ (Real.sSup_nonneg hT_nonneg)
      intro x hx
      exact le_csSup hTbdd (hP_subset_T hx)
    · refine Real.sSup_le ?_ (Real.sSup_nonneg hP_nonneg)
      intro x hx
      rcases hT_le_zero_or_P x hx with hzero | ⟨p, hp, hxp⟩
      · rw [hzero]
        exact Real.sSup_nonneg hP_nonneg
      · exact hxp.trans (le_csSup hPbdd hp)
  · have hTnotbdd : ¬ BddAbove T := by
      intro hTbdd
      exact hPbdd (hPbdd_of_hTbdd hTbdd)
    rw [Real.sSup_of_not_bddAbove hPbdd, Real.sSup_of_not_bddAbove hTnotbdd]
    exact ⟨le_rfl, le_rfl⟩

/-- Product-input restriction gives the easy direction of the right-identity
source collapse lemma. -/
theorem alphaToAlphaNorm_le_kron_id
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) ≤
      alphaToAlphaNorm
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
        (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
        (SchattenOrder.ofOneLt halpha) :=
  (alphaToAlphaNorm_kron_id_compare (r := r) Phi hPhi halpha).1

/-- Right-reference twirling gives the nontrivial direction of the
right-identity source collapse lemma. -/
theorem kron_id_alphaToAlphaNorm_le
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alphaToAlphaNorm
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
        (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
        (SchattenOrder.ofOneLt halpha) ≤
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
  exact (alphaToAlphaNorm_kron_id_compare (r := r) Phi hPhi halpha).2

/-- Tensoring a completely positive map with an identity right factor does not
change the positive `alpha → alpha` norm. -/
theorem alphaToAlphaNorm_kron_id_eq
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alphaToAlphaNorm
        (MatrixMap.kron Phi (CPTPOp.id (dIn := r)).map)
        (MatrixMap.IsCompletelyPositive.kron hPhi (CPTPOp.id (dIn := r)).map_cp)
        (SchattenOrder.ofOneLt halpha) =
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
  exact le_antisymm
    (kron_id_alphaToAlphaNorm_le (r := r) Phi hPhi halpha)
    (alphaToAlphaNorm_le_kron_id (r := r) Phi hPhi halpha)

end MatrixMap

end

end QIT
