/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Induced
public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Complement
public import QuantumLib.QIT.States.Purification.Schatten
public import QuantumLib.QIT.Information.Renyi.FrankLieb.Variational

/-!
# Complement bridge for the EA CB `1 → alpha` norm

This module formalizes the pointwise Stinespring/complement bridge in the
Khatri--Wilde completely bounded norm multiplicativity proof.

Source alignment:
* KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2197-2204 use that
  the weighted Stinespring output is rank one, so tracing either side has the
  same nonzero spectrum.
* KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2205-2212 identify
  the complementary marginal with `M^c((Y^t)^(1/alpha))` by the transpose
  trick.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {κ : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype κ] [DecidableEq κ]

namespace MatrixMap

/-- Reference/Stinespring vector whose rank-one matrix has the two marginals
used in the source's Schmidt-spectrum step. -/
def krausStinespringReferenceVector
    (K : κ → Matrix b a ℂ) (psi : a × a → ℂ) :
    (a × b) × κ → ℂ :=
  fun rbk => ∑ x : a, K rbk.2 rbk.1.2 x * psi (rbk.1.1, x)

omit [DecidableEq κ] in
/-- Applying `id_R ⊗ ofKraus K` to a rank-one reference/input vector is the
environment marginal of the associated rank-one Stinespring/reference vector.
-/
theorem referenceLift_ofKraus_rankOne_eq_traceRight
    (K : κ → Matrix b a ℂ) (psi : a × a → ℂ) :
    (MatrixMap.ofKraus K).referenceLift (rankOneMatrix psi) =
      Matrix.traceRight
        (rankOneMatrix (krausStinespringReferenceVector K psi)) := by
  ext rb rb'
  rcases rb with ⟨r, bout⟩
  rcases rb' with ⟨r', bout'⟩
  change
    (MatrixMap.ofKraus K).referenceLift (rankOneMatrix psi) (r, bout) (r', bout') =
      ∑ k : κ,
        rankOneMatrix (krausStinespringReferenceVector K psi) ((r, bout), k) ((r', bout'), k)
  calc
    (MatrixMap.ofKraus K).referenceLift (rankOneMatrix psi) (r, bout) (r', bout')
        =
      ∑ k : κ, ∑ x' : a, ∑ x : a,
        K k bout x * (psi (r, x) * (star (K k bout' x') * star (psi (r', x')))) := by
          simp only [referenceLift]
          rw [MatrixMap.kron_idChannel_left_apply_slice]
          simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.of_apply, rankOneMatrix_apply, Finset.sum_mul]
          simp [mul_left_comm, mul_comm]
    _ =
      ∑ k : κ,
        rankOneMatrix (krausStinespringReferenceVector K psi) ((r, bout), k) ((r', bout'), k) := by
          simp [rankOneMatrix_apply, krausStinespringReferenceVector,
            Finset.sum_mul, Finset.mul_sum, mul_assoc]

omit [DecidableEq b] in
/-- Tracing the output side of the rank-one Stinespring/reference vector gives
the Kraus complement applied to the input-side rank-one marginal. -/
theorem traceLeft_rankOne_stinespringReference_eq_krausComplement_traceLeft_rankOne
    (K : κ → Matrix b a ℂ) (psi : a × a → ℂ) :
    Matrix.traceLeft
        (rankOneMatrix (krausStinespringReferenceVector K psi)) =
      MatrixMap.krausComplement K
        (Matrix.traceLeft (rankOneMatrix psi)) := by
  ext k k'
  change
    (∑ rb : a × b,
      rankOneMatrix (krausStinespringReferenceVector K psi) (rb, k) (rb, k')) =
      MatrixMap.krausComplement K
        (Matrix.traceLeft (rankOneMatrix psi)) k k'
  calc
    (∑ rb : a × b,
      rankOneMatrix (krausStinespringReferenceVector K psi) (rb, k) (rb, k'))
        =
      ∑ r : a, ∑ bout : b, ∑ y : a, ∑ x : a,
        K k bout x *
          (psi (r, x) * (star (K k' bout y) * star (psi (r, y)))) := by
          simp [rankOneMatrix_apply, krausStinespringReferenceVector,
            Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ =
      ∑ bout : b, ∑ x : a, ∑ y : a, ∑ r : a,
        K k bout x *
          (psi (r, x) * (star (K k' bout y) * star (psi (r, y)))) := by
          calc
            (∑ r : a, ∑ bout : b, ∑ y : a, ∑ x : a,
              K k bout x *
                (psi (r, x) * (star (K k' bout y) * star (psi (r, y)))))
                =
              ∑ bout : b, ∑ r : a, ∑ y : a, ∑ x : a,
                K k bout x *
                  (psi (r, x) * (star (K k' bout y) * star (psi (r, y)))) := by
                  rw [Finset.sum_comm]
            _ =
              ∑ bout : b, ∑ y : a, ∑ r : a, ∑ x : a,
                K k bout x *
                  (psi (r, x) * (star (K k' bout y) * star (psi (r, y)))) := by
                  apply Finset.sum_congr rfl
                  intro bout _
                  rw [Finset.sum_comm]
            _ =
              ∑ bout : b, ∑ y : a, ∑ x : a, ∑ r : a,
                K k bout x *
                  (psi (r, x) * (star (K k' bout y) * star (psi (r, y)))) := by
                  apply Finset.sum_congr rfl
                  intro bout _
                  apply Finset.sum_congr rfl
                  intro y _
                  rw [Finset.sum_comm]
            _ =
              ∑ bout : b, ∑ x : a, ∑ y : a, ∑ r : a,
                K k bout x *
                  (psi (r, x) * (star (K k' bout y) * star (psi (r, y)))) := by
                  apply Finset.sum_congr rfl
                  intro bout _
                  rw [Finset.sum_comm]
    _ =
      ∑ bout : b, ∑ x : a, ∑ y : a,
        K k bout x *
          ((∑ r : a, psi (r, x) * star (psi (r, y))) * star (K k' bout y)) := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ =
      ∑ bout : b, ∑ x : a, ∑ y : a,
        K k bout x *
          (Matrix.traceLeft (rankOneMatrix psi) x y *
            star (K k' bout y)) := by
          have hpt : ∀ x y : a,
              Matrix.traceLeft (rankOneMatrix psi) x y =
                ∑ r : a, psi (r, x) * star (psi (r, y)) := by
            intro x y
            change (∑ r : a, rankOneMatrix psi (r, x) (r, y)) =
              ∑ r : a, psi (r, x) * star (psi (r, y))
            simp [rankOneMatrix_apply]
          apply Finset.sum_congr rfl
          intro bout _
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          rw [hpt x y]
    _ =
      ∑ bout : b, ∑ y : a, ∑ x : a,
        K k bout x *
          (Matrix.traceLeft (rankOneMatrix psi) x y *
            star (K k' bout y)) := by
          apply Finset.sum_congr rfl
          intro bout _
          rw [Finset.sum_comm]
    _ =
      MatrixMap.krausComplement K
        (Matrix.traceLeft (rankOneMatrix psi)) k k' := by
          simp [MatrixMap.krausComplement, MatrixMap.ofKraus,
            Matrix.sum_apply, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Finset.sum_mul, mul_assoc]

/-- The source weighted Choi input is rank one. -/
theorem cbOneToAlphaOriginalInput_eq_rankOne_rpow
    {Y : CMatrix a} (hY : Y.PosSemidef) (alpha : ℝ) :
    cbOneToAlphaOriginalInput Y alpha =
      rankOneMatrix
        (fun ra : a × a => CFC.rpow Y (1 / (2 * alpha)) ra.1 ra.2) := by
  let R : CMatrix a := CFC.rpow Y (1 / (2 * alpha))
  have hR : R.IsHermitian :=
    (cMatrix_rpow_posSemidef (A := Y) (s := 1 / (2 * alpha)) hY).isHermitian
  ext ra ra'
  rcases ra with ⟨r, x⟩
  rcases ra' with ⟨r', x'⟩
  calc
    cbOneToAlphaOriginalInput Y alpha (r, x) (r', x')
        =
      ∑ x1 : a, R x1 r' * ∑ x2 : a,
        if x2 = x ∧ x1 = x' then R r x2 else 0 := by
          simp [cbOneToAlphaOriginalInput, cbOneToAlphaReferenceWeight,
            unnormalizedMaximallyEntangledProjector, MatrixMap.choi,
            Matrix.kroneckerMap_apply, Matrix.mul_apply,
            Matrix.one_apply, Matrix.single, Fintype.sum_prod_type, R,
            mul_comm]
    _ = ∑ x1 : a, if x1 = x' then R x1 r' * R r x else 0 := by
          apply Finset.sum_congr rfl
          intro x1 _
          by_cases hx1 : x1 = x'
          · subst x1
            simp
          · simp [hx1]
    _ = R x' r' * R r x := by
          simp
    _ = rankOneMatrix
          (fun ra : a × a => CFC.rpow Y (1 / (2 * alpha)) ra.1 ra.2)
          (r, x) (r', x') := by
          have hstar : R x' r' = star (R r' x') := by
            have h := congrArg star (hR.apply r' x')
            simpa using h
          rw [rankOneMatrix_apply]
          change R x' r' * R r x = R r x * star (R r' x')
          rw [hstar]
          rw [mul_comm]

/-- The rank-one reference marginal of the source weight is
`(Y^t)^(1/alpha)`. -/
theorem traceLeft_rankOne_rpow_weight_eq_rpow_transpose
    {Y : CMatrix a} (hY : Y.PosSemidef) {alpha : ℝ} (halpha : 0 < alpha) :
    Matrix.traceLeft
        (rankOneMatrix
          (fun ra : a × a => CFC.rpow Y (1 / (2 * alpha)) ra.1 ra.2)) =
      CFC.rpow Y.transpose (1 / alpha) := by
  let t : ℝ := 1 / (2 * alpha)
  let R : CMatrix a := CFC.rpow Y t
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have h1 : 0 ≤ (1 / alpha : ℝ) := by
    positivity
  have hRherm : R.IsHermitian :=
    (cMatrix_rpow_posSemidef (A := Y) (s := t) hY).isHermitian
  have htadd : t + t = 1 / alpha := by
    dsimp [t]
    field_simp [halpha.ne']
    ring
  have hRmul : R * R = CFC.rpow Y (1 / alpha) := by
    have h := cMatrix_rpow_mul_rpow_of_nonneg (A := Y) hY ht ht
    calc
      R * R = CFC.rpow Y (t + t) := by
        simpa [R] using h
      _ = CFC.rpow Y (1 / alpha) := by
        rw [htadd]
  ext x y
  calc
    Matrix.traceLeft
        (rankOneMatrix
          (fun ra : a × a => CFC.rpow Y (1 / (2 * alpha)) ra.1 ra.2)) x y
        = ∑ r : a, R r x * star (R r y) := by
          change (∑ r : a,
            rankOneMatrix
              (fun ra : a × a => CFC.rpow Y (1 / (2 * alpha)) ra.1 ra.2)
              (r, x) (r, y)) =
              ∑ r : a, R r x * star (R r y)
          simp [rankOneMatrix_apply, R, t]
    _ = ∑ r : a, R y r * R r x := by
          apply Finset.sum_congr rfl
          intro r _
          have hstar : star (R r y) = R y r := by
            simpa using hRherm.apply y r
          rw [hstar]
          ring
    _ = (R * R) y x := by
          simp [Matrix.mul_apply]
    _ = CFC.rpow Y.transpose (1 / alpha) x y := by
          rw [hRmul]
          rw [cMatrix_rpow_transpose_nonneg (A := Y) hY h1]
          rfl

/-- The source original-domain input, transposed as in the complement-side
power substitution. -/
def CBOneToAlphaOriginalDomain.toTransposeTraceDomain
    (Y : CBOneToAlphaOriginalDomain a) {alpha : ℝ} (_halpha : 0 < alpha) :
    AlphaToAlphaTraceDomain a (SchattenOrder.ofPositive _halpha) where
  matrix := Y.matrix.transpose
  pos := Y.pos.transpose
  trace_le_one := by
    simpa [Matrix.trace_transpose] using Y.trace_le_one

/-- Pointwise equality between the original CB `1 → alpha` value for an
explicit Kraus-form map and the trace-normalized `alpha → alpha` value of
that Kraus complement. -/
theorem cbOneToAlphaOriginalValue_eq_krausComplement_alphaToAlphaTraceValue_transpose
    (K : κ → Matrix b a ℂ)
    {alpha : ℝ} (halpha : 0 < alpha)
    (Y : CBOneToAlphaOriginalDomain a) :
    cbOneToAlphaOriginalValue
        (MatrixMap.ofKraus K)
        (MatrixMap.ofKraus_completelyPositive K)
        Y
        (SchattenOrder.ofPositive halpha) =
      alphaToAlphaTraceValue
        (MatrixMap.krausComplement K)
        (MatrixMap.krausComplement_isCompletelyPositive K)
        (Y.toTransposeTraceDomain (alpha := alpha) halpha) := by
  let psi : a × a → ℂ :=
    fun ra => CFC.rpow Y.matrix (1 / (2 * alpha)) ra.1 ra.2
  have hleft :
      (MatrixMap.ofKraus K).referenceLift (cbOneToAlphaOriginalInput Y.matrix alpha) =
        Matrix.traceRight
          (rankOneMatrix (krausStinespringReferenceVector K psi)) := by
    calc
      (MatrixMap.ofKraus K).referenceLift (cbOneToAlphaOriginalInput Y.matrix alpha) =
          (MatrixMap.ofKraus K).referenceLift (rankOneMatrix psi) := by
            rw [cbOneToAlphaOriginalInput_eq_rankOne_rpow Y.pos alpha]
      _ = Matrix.traceRight
          (rankOneMatrix (krausStinespringReferenceVector K psi)) := by
            rw [referenceLift_ofKraus_rankOne_eq_traceRight]
  have hright :
      Matrix.traceLeft
          (rankOneMatrix (krausStinespringReferenceVector K psi)) =
        MatrixMap.krausComplement K
          (CFC.rpow Y.matrix.transpose (1 / alpha)) := by
    calc
      Matrix.traceLeft
          (rankOneMatrix (krausStinespringReferenceVector K psi)) =
        MatrixMap.krausComplement K
          (Matrix.traceLeft (rankOneMatrix psi)) := by
          rw [traceLeft_rankOne_stinespringReference_eq_krausComplement_traceLeft_rankOne]
      _ = MatrixMap.krausComplement K
          (CFC.rpow Y.matrix.transpose (1 / alpha)) := by
          rw [traceLeft_rankOne_rpow_weight_eq_rpow_transpose Y.pos halpha]
  unfold cbOneToAlphaOriginalValue alphaToAlphaTraceValue
  calc
    psdSchattenPNorm
        ((MatrixMap.ofKraus K).referenceLift (cbOneToAlphaOriginalInput Y.matrix alpha))
        ((MatrixMap.ofKraus K).referenceLift_mapsPositive
          (MatrixMap.ofKraus_completelyPositive K)
          (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
        (SchattenOrder.ofPositive halpha) =
      psdSchattenPNorm
        (Matrix.traceRight
          (rankOneMatrix (krausStinespringReferenceVector K psi)))
        (traceRight_posSemidef (rankOneMatrix_pos (krausStinespringReferenceVector K psi)))
        (SchattenOrder.ofPositive halpha) := by
          exact psdSchattenPNorm_congr hleft
            ((MatrixMap.ofKraus K).referenceLift_mapsPositive
              (MatrixMap.ofKraus_completelyPositive K)
              (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
            (traceRight_posSemidef
              (rankOneMatrix_pos (krausStinespringReferenceVector K psi)))
            (SchattenOrder.ofPositive halpha)
    _ =
      psdSchattenPNorm
        (Matrix.traceLeft
          (rankOneMatrix (krausStinespringReferenceVector K psi)))
        (traceLeft_posSemidef (rankOneMatrix_pos (krausStinespringReferenceVector K psi)))
        (SchattenOrder.ofPositive halpha) := by
          exact psdSchattenPNorm_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix
            (krausStinespringReferenceVector K psi)
            (SchattenOrder.ofPositive halpha)
    _ =
      psdSchattenPNorm
        (MatrixMap.krausComplement K
          (CFC.rpow (CBOneToAlphaOriginalDomain.toTransposeTraceDomain Y halpha).matrix
            (1 / alpha)))
        (MatrixMap.isCompletelyPositive_mapsPositive (MatrixMap.krausComplement K)
          (MatrixMap.krausComplement_isCompletelyPositive K)
          (CFC.rpow (CBOneToAlphaOriginalDomain.toTransposeTraceDomain Y halpha).matrix
            (1 / alpha))
          (cMatrix_rpow_posSemidef
            (A := (CBOneToAlphaOriginalDomain.toTransposeTraceDomain Y halpha).matrix)
            (s := 1 / alpha)
            (CBOneToAlphaOriginalDomain.toTransposeTraceDomain Y halpha).pos))
        (SchattenOrder.ofPositive halpha) := by
          simp only [CBOneToAlphaOriginalDomain.toTransposeTraceDomain]
          exact psdSchattenPNorm_congr hright
            (traceLeft_posSemidef
              (rankOneMatrix_pos (krausStinespringReferenceVector K psi)))
            (MatrixMap.isCompletelyPositive_mapsPositive (MatrixMap.krausComplement K)
              (MatrixMap.krausComplement_isCompletelyPositive K)
              (CFC.rpow Y.matrix.transpose (1 / alpha))
              (cMatrix_rpow_posSemidef
                (A := Y.matrix.transpose) (s := 1 / alpha) Y.pos.transpose))
            (SchattenOrder.ofPositive halpha)

/-- Pointwise equality between the original CB `1 → alpha` value and the
trace-normalized `alpha → alpha` value of the chosen complementary map. -/
theorem cbOneToAlphaOriginalValue_eq_cpComplement_alphaToAlphaTraceValue_transpose
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 0 < alpha)
    (Y : CBOneToAlphaOriginalDomain a) :
    cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofPositive halpha) =
      alphaToAlphaTraceValue
        (MatrixMap.cpComplement Phi hPhi)
        (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
        (Y.toTransposeTraceDomain (alpha := alpha) halpha) := by
  let K : (a × b) → Matrix b a ℂ := MatrixMap.cpKraus Phi hPhi
  have hcb :
      cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofPositive halpha) =
        cbOneToAlphaOriginalValue
          (MatrixMap.ofKraus K)
          (MatrixMap.ofKraus_completelyPositive K)
          Y
          (SchattenOrder.ofPositive halpha) := by
    unfold cbOneToAlphaOriginalValue
    exact psdSchattenPNorm_congr
      (by rw [MatrixMap.cpKraus_spec Phi hPhi])
      (Phi.referenceLift_mapsPositive hPhi
        (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
      ((MatrixMap.ofKraus K).referenceLift_mapsPositive
        (MatrixMap.ofKraus_completelyPositive K)
        (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
      (SchattenOrder.ofPositive halpha)
  calc
    cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofPositive halpha) =
      cbOneToAlphaOriginalValue
        (MatrixMap.ofKraus K)
        (MatrixMap.ofKraus_completelyPositive K)
        Y
        (SchattenOrder.ofPositive halpha) := hcb
    _ =
      alphaToAlphaTraceValue
        (MatrixMap.krausComplement K)
        (MatrixMap.krausComplement_isCompletelyPositive K)
        (Y.toTransposeTraceDomain (alpha := alpha) halpha) :=
        cbOneToAlphaOriginalValue_eq_krausComplement_alphaToAlphaTraceValue_transpose
          K halpha Y
    _ =
      alphaToAlphaTraceValue
        (MatrixMap.cpComplement Phi hPhi)
        (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
        (Y.toTransposeTraceDomain (alpha := alpha) halpha) := by
        rfl

/-- The source CB `1 → alpha` value set for an explicit Kraus-form map is
exactly the trace-power value set of that Kraus complement. -/
private theorem cbOneToAlphaOriginalValueSet_eq_krausComplement_alphaToAlphaTraceValueSet
    (K : κ → Matrix b a ℂ)
    {alpha : ℝ} (halpha : 1 < alpha) :
    cbOneToAlphaOriginalValueSet
        (MatrixMap.ofKraus K)
        (MatrixMap.ofKraus_completelyPositive K)
        (SchattenOrder.ofOneLt halpha) =
      alphaToAlphaTraceValueSet
        (MatrixMap.krausComplement K)
        (MatrixMap.krausComplement_isCompletelyPositive K)
        (SchattenOrder.ofOneLt halpha) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  apply Set.ext
  intro x
  constructor
  · rintro ⟨Y, rfl⟩
    refine ⟨Y.toTransposeTraceDomain (alpha := alpha) halpha_pos, ?_⟩
    exact (cbOneToAlphaOriginalValue_eq_krausComplement_alphaToAlphaTraceValue_transpose
      K halpha_pos Y).symm
  · rintro ⟨Z, rfl⟩
    let Y : CBOneToAlphaOriginalDomain a := {
      matrix := Z.matrix.transpose
      pos := Z.pos.transpose
      trace_le_one := by
        simpa [Matrix.trace_transpose] using Z.trace_le_one }
    refine ⟨Y, ?_⟩
    have hdomain :
        Y.toTransposeTraceDomain (alpha := alpha) halpha_pos = Z := by
      cases Z with
      | mk matrix pos trace_le_one =>
          simp [Y, CBOneToAlphaOriginalDomain.toTransposeTraceDomain]
          congr
    rw [← hdomain]
    exact cbOneToAlphaOriginalValue_eq_krausComplement_alphaToAlphaTraceValue_transpose
      K halpha_pos Y

/-- Supremum-level bridge from the source CB `1 → alpha` norm of an explicit
Kraus-form map to the positive `alpha → alpha` norm of that Kraus complement. -/
theorem cbOneToAlphaNorm_eq_krausComplement_alphaToAlphaNorm
    (K : κ → Matrix b a ℂ)
    {alpha : ℝ} (halpha : 1 < alpha) :
    cbOneToAlphaNorm
        (MatrixMap.ofKraus K)
        (MatrixMap.ofKraus_completelyPositive K)
        (SchattenOrder.ofOneLt halpha) =
      alphaToAlphaNorm
        (MatrixMap.krausComplement K)
        (MatrixMap.krausComplement_isCompletelyPositive K)
        (SchattenOrder.ofOneLt halpha) := by
  rw [cbOneToAlphaNorm_eq_sSup]
  rw [cbOneToAlphaOriginalValueSet_eq_krausComplement_alphaToAlphaTraceValueSet K halpha]
  exact (alphaToAlphaNorm_eq_tracePower_sSup_of_one_lt
    (MatrixMap.krausComplement K)
    (MatrixMap.krausComplement_isCompletelyPositive K)
    halpha).symm

/-- Supremum-level bridge from the source CB `1 → alpha` norm to the positive
`alpha → alpha` norm of the chosen complementary map. -/
theorem cbOneToAlphaNorm_eq_cpComplement_alphaToAlphaNorm
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : ℝ} (halpha : 1 < alpha) :
    cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) =
      alphaToAlphaNorm
        (MatrixMap.cpComplement Phi hPhi)
        (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
        (SchattenOrder.ofOneLt halpha) := by
  let K : (a × b) → Matrix b a ℂ := MatrixMap.cpKraus Phi hPhi
  have hvalue :
      ∀ Y : CBOneToAlphaOriginalDomain a,
        cbOneToAlphaOriginalValue Phi hPhi Y (SchattenOrder.ofOneLt halpha) =
          cbOneToAlphaOriginalValue
            (MatrixMap.ofKraus K)
            (MatrixMap.ofKraus_completelyPositive K)
            Y
            (SchattenOrder.ofOneLt halpha) := by
    intro Y
    unfold cbOneToAlphaOriginalValue
    exact psdSchattenPNorm_congr
      (by rw [MatrixMap.cpKraus_spec Phi hPhi])
      (Phi.referenceLift_mapsPositive hPhi
        (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
      ((MatrixMap.ofKraus K).referenceLift_mapsPositive
        (MatrixMap.ofKraus_completelyPositive K)
        (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
      (SchattenOrder.ofOneLt halpha)
  have hnorm :
      cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) =
        cbOneToAlphaNorm
          (MatrixMap.ofKraus K)
          (MatrixMap.ofKraus_completelyPositive K)
          (SchattenOrder.ofOneLt halpha) := by
    unfold cbOneToAlphaNorm cbOneToAlphaOriginalValueSet
    exact congrArg sSup (congrArg Set.range (funext hvalue))
  calc
    cbOneToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) =
      cbOneToAlphaNorm
        (MatrixMap.ofKraus K)
        (MatrixMap.ofKraus_completelyPositive K)
        (SchattenOrder.ofOneLt halpha) := hnorm
    _ =
      alphaToAlphaNorm
        (MatrixMap.krausComplement K)
        (MatrixMap.krausComplement_isCompletelyPositive K)
        (SchattenOrder.ofOneLt halpha) :=
        cbOneToAlphaNorm_eq_krausComplement_alphaToAlphaNorm K halpha
    _ =
      alphaToAlphaNorm
        (MatrixMap.cpComplement Phi hPhi)
        (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
        (SchattenOrder.ofOneLt halpha) := by
        rfl

end MatrixMap

end

end QIT
