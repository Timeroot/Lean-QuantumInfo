/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Product

/-!
# Alternate expression for the CB `1 -> alpha` norm

This file proves the source alternate expression from
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2102-2140].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z

noncomputable section

namespace MatrixMap

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- The reference marginal of the rank-one weighted Gamma input is
`Y^(1 / alpha)`.

This is the denominator rewrite in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2102-2140], specifically
source lines 2110-2118, for the reference-side orientation used by
`CBOneToAlphaAlternateDomain`. -/
theorem partialTraceB_rankOne_rpow_weight_eq_rpow
    {Y : CMatrix a} (hY : Y.PosSemidef) {alpha : ℝ} (halpha : 0 < alpha) :
    partialTraceB (a := a) (b := a)
        (rankOneMatrix
          (fun ra : Prod a a => CFC.rpow Y (1 / (2 * alpha)) ra.1 ra.2)) =
      CFC.rpow Y (1 / alpha) := by
  let t : ℝ := 1 / (2 * alpha)
  let R : CMatrix a := CFC.rpow Y t
  have ht : 0 ≤ t := by
    dsimp [t]
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
    partialTraceB (a := a) (b := a)
        (rankOneMatrix
          (fun ra : Prod a a => CFC.rpow Y (1 / (2 * alpha)) ra.1 ra.2)) x y
        = ∑ r : a, R x r * star (R y r) := by
          change (∑ r : a,
            rankOneMatrix
              (fun ra : Prod a a => CFC.rpow Y (1 / (2 * alpha)) ra.1 ra.2)
              (x, r) (y, r)) =
              ∑ r : a, R x r * star (R y r)
          simp [rankOneMatrix_apply, R, t]
    _ = ∑ r : a, R x r * R r y := by
          apply Finset.sum_congr rfl
          intro r _
          have hstar : star (R y r) = R r y := by
            simpa using hRherm.apply r y
          rw [hstar]
    _ = (R * R) x y := by
          simp [Matrix.mul_apply]
    _ = CFC.rpow Y (1 / alpha) x y := by
          rw [hRmul]

/-- The reference marginal of the original CB-norm input is `Y^(1 / alpha)`.

This packages `cbOneToAlphaOriginalInput_eq_rankOne_rpow` with
`partialTraceB_rankOne_rpow_weight_eq_rpow`. -/
theorem partialTraceB_cbOneToAlphaOriginalInput_eq_rpow
    {Y : CMatrix a} (hY : Y.PosSemidef) {alpha : ℝ} (halpha : 0 < alpha) :
    partialTraceB (a := a) (b := a) (cbOneToAlphaOriginalInput Y alpha) =
      CFC.rpow Y (1 / alpha) := by
  rw [cbOneToAlphaOriginalInput_eq_rankOne_rpow hY alpha]
  exact partialTraceB_rankOne_rpow_weight_eq_rpow hY halpha

/-- A pure-state reference/input quotient is bounded by the source
`CB, 1 -> alpha` norm.

This is the fixed-reference pure-vector bridge used in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2102-2140], specifically
source lines 2114-2121.  The proof routes the rank-one Stinespring output
through the complementary map and then uses the positive `alpha -> alpha`
supremum bridge. -/
theorem cbOneToAlphaPureRankOneValue_le_cbOneToAlphaNorm
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (psi : Prod a a → ℂ)
    (hden :
      0 < psdSchattenPNorm
        (partialTraceB (a := a) (b := a) (rankOneMatrix psi))
        (partialTraceB_posSemidef (rankOneMatrix_pos psi)) alpha) :
    psdSchattenPNorm
        (Phi.referenceLift (rankOneMatrix psi))
        (Phi.referenceLift_mapsPositive hPhi (rankOneMatrix_pos psi))
        alpha /
      psdSchattenPNorm
        (partialTraceB (a := a) (b := a) (rankOneMatrix psi))
        (partialTraceB_posSemidef (rankOneMatrix_pos psi))
        alpha ≤
      cbOneToAlphaNorm Phi hPhi alpha := by
  let K : (a × b) → Matrix b a ℂ := MatrixMap.cpKraus Phi hPhi
  let chi : Prod (Prod a b) (a × b) → ℂ :=
    MatrixMap.krausStinespringReferenceVector K psi
  let Z : AlphaToAlphaPositiveDomain a alpha :=
    { matrix := partialTraceA (a := a) (b := a) (rankOneMatrix psi),
      pos := partialTraceA_posSemidef (rankOneMatrix_pos psi),
      norm_pos := by
        have hEq :=
          psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
            (r := a) (a := a) psi alpha
        exact hEq ▸ hden }
  have hNum :
      psdSchattenPNorm
          (Phi.referenceLift (rankOneMatrix psi))
          (Phi.referenceLift_mapsPositive hPhi (rankOneMatrix_pos psi))
          alpha =
        psdSchattenPNorm
          (MatrixMap.cpComplement Phi hPhi
            (partialTraceA (a := a) (b := a) (rankOneMatrix psi)))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.cpComplement Phi hPhi)
            (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
            (partialTraceA (a := a) (b := a) (rankOneMatrix psi))
            (partialTraceA_posSemidef (rankOneMatrix_pos psi)))
          alpha := by
    have hLeft :
        Phi.referenceLift (rankOneMatrix psi) =
          partialTraceB (a := Prod a b) (b := a × b)
            (rankOneMatrix chi) := by
      calc
        Phi.referenceLift (rankOneMatrix psi) =
            (MatrixMap.ofKraus K).referenceLift (rankOneMatrix psi) := by
              rw [MatrixMap.cpKraus_spec Phi hPhi]
        _ = partialTraceB (a := Prod a b) (b := a × b)
            (rankOneMatrix chi) := by
              simpa [chi] using
                MatrixMap.referenceLift_ofKraus_rankOne_eq_partialTraceB K psi
    have hSchmidt :=
      psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
        (r := Prod a b) (a := a × b) chi alpha
    have hRight :
        partialTraceA (a := Prod a b) (b := a × b) (rankOneMatrix chi) =
          MatrixMap.cpComplement Phi hPhi
            (partialTraceA (a := a) (b := a) (rankOneMatrix psi)) := by
      simpa [chi, K] using
        MatrixMap.partialTraceA_rankOne_stinespringReference_eq_krausComplement_partialTraceA_rankOne
          K psi
    calc
      psdSchattenPNorm
          (Phi.referenceLift (rankOneMatrix psi))
          (Phi.referenceLift_mapsPositive hPhi (rankOneMatrix_pos psi))
          alpha =
        psdSchattenPNorm
          (partialTraceB (a := Prod a b) (b := a × b) (rankOneMatrix chi))
          (partialTraceB_posSemidef (rankOneMatrix_pos chi))
          alpha := by
            exact psdSchattenPNorm_congr hLeft _ _ alpha
      _ =
        psdSchattenPNorm
          (partialTraceA (a := Prod a b) (b := a × b) (rankOneMatrix chi))
          (partialTraceA_posSemidef (rankOneMatrix_pos chi))
          alpha := hSchmidt
      _ =
        psdSchattenPNorm
          (MatrixMap.cpComplement Phi hPhi
            (partialTraceA (a := a) (b := a) (rankOneMatrix psi)))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.cpComplement Phi hPhi)
            (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
            (partialTraceA (a := a) (b := a) (rankOneMatrix psi))
            (partialTraceA_posSemidef (rankOneMatrix_pos psi)))
          alpha := by
            exact psdSchattenPNorm_congr hRight _ _ alpha
  have hDen :
      psdSchattenPNorm
          (partialTraceB (a := a) (b := a) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi))
          alpha =
        psdSchattenPNorm
          (partialTraceA (a := a) (b := a) (rankOneMatrix psi))
          (partialTraceA_posSemidef (rankOneMatrix_pos psi))
          alpha := by
    exact
      psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
        (r := a) (a := a) psi alpha
  have hQuot :
      psdSchattenPNorm
          (Phi.referenceLift (rankOneMatrix psi))
          (Phi.referenceLift_mapsPositive hPhi (rankOneMatrix_pos psi))
          alpha /
        psdSchattenPNorm
          (partialTraceB (a := a) (b := a) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi))
          alpha =
        alphaToAlphaPositiveValue
          (MatrixMap.cpComplement Phi hPhi)
          (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
          Z := by
    unfold alphaToAlphaPositiveValue
    rw [hNum, hDen]
  rw [hQuot]
  have hbridge :
      cbOneToAlphaNorm Phi hPhi alpha =
        alphaToAlphaNorm (MatrixMap.cpComplement Phi hPhi)
          (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi) alpha := by
    simpa [SchattenOrder.ofOneLt] using
      (MatrixMap.cbOneToAlphaNorm_eq_cpComplement_alphaToAlphaNorm
        Phi hPhi halpha)
  rw [hbridge]
  exact MatrixMap.alphaToAlphaPositiveValue_le_alphaToAlphaNorm_of_one_lt
    (MatrixMap.cpComplement Phi hPhi)
    (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
    halpha Z

private def krausStinespringReferenceVectorWithRef
    {r : Type w} {κ : Type x} [Fintype a]
    (K : κ → Matrix b a ℂ) (psi : Prod r a → ℂ) :
    Prod (Prod r b) κ → ℂ :=
  fun rbk => ∑ x : a, K rbk.2 rbk.1.2 x * psi (rbk.1.1, x)

private theorem sum_matrixSingle_two_ref
    {r : Type w} [Fintype r] [DecidableEq r]
    (F : r → r → ℂ) (r₀ r₁ : r) :
    (∑ x : r, ∑ y : r, Matrix.single x y (1 : ℂ) r₀ r₁ * F x y) =
      F r₀ r₁ := by
  calc
    (∑ x : r, ∑ y : r, Matrix.single x y (1 : ℂ) r₀ r₁ * F x y)
        = ∑ x : r, ∑ y : r, if x = r₀ ∧ y = r₁ then F x y else 0 := by
          simp [Matrix.single]
    _ = ∑ x : r, if x = r₀ then F r₀ r₁ else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = r₀
          · subst x
            simp
          · simp [hx]
    _ = F r₀ r₁ := by
          simp

private theorem sum_matrixSingle_two_three_ref
    {r : Type w} {κ : Type x} [Fintype r] [DecidableEq r] [Fintype κ]
    (F : r → r → κ → ℂ) (r₀ r₁ : r) :
    (∑ x : r, ∑ y : r, ∑ k : κ,
        Matrix.single x y (1 : ℂ) r₀ r₁ * F x y k) =
      ∑ k : κ, F r₀ r₁ k := by
  calc
    (∑ x : r, ∑ y : r, ∑ k : κ,
        Matrix.single x y (1 : ℂ) r₀ r₁ * F x y k)
        = ∑ x : r, ∑ y : r,
            Matrix.single x y (1 : ℂ) r₀ r₁ * (∑ k : κ, F x y k) := by
          simp [Finset.mul_sum]
    _ = ∑ k : κ, F r₀ r₁ k := by
          exact sum_matrixSingle_two_ref (fun x y => ∑ k : κ, F x y k) r₀ r₁

private theorem ofKraus_single_apply_local
    {κ : Type x} [Fintype κ]
    (K : κ → Matrix b a ℂ) (x x' : a) (y y' : b) :
    MatrixMap.ofKraus K (Matrix.single x x' (1 : ℂ)) y y' =
      ∑ k : κ, K k y x * star (K k y' x') := by
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  change (K k * Matrix.single x x' (1 : ℂ) * Matrix.conjTranspose (K k)) y y' =
    K k y x * star (K k y' x')
  simp only [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply]
  have hinner : ∀ x1 : a,
      (∑ x2 : a, (if x = x2 ∧ x' = x1 then K k y x2 else 0)) =
        if x' = x1 then K k y x else 0 := by
    intro x1
    by_cases hx1 : x' = x1
    · subst x1
      simp
    · simp [hx1]
  simp [hinner]

private theorem referenceLift_ofKraus_rankOne_eq_partialTraceB_withRef
    {r : Type w} {κ : Type x}
    [Fintype r] [DecidableEq r] [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) (psi : Prod r a → ℂ) :
    MatrixMap.kron (Channel.idChannel r).map (MatrixMap.ofKraus K)
        (rankOneMatrix psi) =
      partialTraceB (a := Prod r b) (b := κ)
        (rankOneMatrix (krausStinespringReferenceVectorWithRef K psi)) := by
  ext rb rb'
  rcases rb with ⟨r₀, bout⟩
  rcases rb' with ⟨r₁, bout'⟩
  change
    MatrixMap.kron (Channel.idChannel r).map (MatrixMap.ofKraus K)
        (rankOneMatrix psi) (r₀, bout) (r₁, bout') =
      ∑ k : κ,
        rankOneMatrix (krausStinespringReferenceVectorWithRef K psi)
          ((r₀, bout), k) ((r₁, bout'), k)
  calc
    MatrixMap.kron (Channel.idChannel r).map (MatrixMap.ofKraus K)
        (rankOneMatrix psi) (r₀, bout) (r₁, bout')
        =
      ∑ x : a, ∑ x' : a, ∑ s : r, ∑ s' : r, ∑ k : κ,
        K k bout x *
          (Matrix.single s s' (1 : ℂ) r₀ r₁ *
            (psi (s, x) * (star (K k bout' x') * star (psi (s', x'))))) := by
          simp [MatrixMap.kron, rankOneMatrix_apply,
            ofKraus_single_apply_local, Channel.idChannel_map,
            Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ =
      ∑ x : a, ∑ x' : a, ∑ k : κ,
        K k bout x * (psi (r₀, x) * (star (K k bout' x') * star (psi (r₁, x')))) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro x' _
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            sum_matrixSingle_two_three_ref
              (F := fun s s' k =>
                K k bout x * (psi (s, x) * (star (K k bout' x') * star (psi (s', x')))))
              r₀ r₁
    _ =
      ∑ k : κ, ∑ x : a, ∑ x' : a,
        K k bout x * (psi (r₀, x) * (star (K k bout' x') * star (psi (r₁, x')))) := by
          calc
            (∑ x : a, ∑ x' : a, ∑ k : κ,
              K k bout x * (psi (r₀, x) *
                (star (K k bout' x') * star (psi (r₁, x')))))
                =
              ∑ x : a, ∑ k : κ, ∑ x' : a,
                K k bout x * (psi (r₀, x) *
                  (star (K k bout' x') * star (psi (r₁, x')))) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  rw [Finset.sum_comm]
            _ =
              ∑ k : κ, ∑ x : a, ∑ x' : a,
                K k bout x * (psi (r₀, x) *
                  (star (K k bout' x') * star (psi (r₁, x')))) := by
                  rw [Finset.sum_comm]
    _ =
      ∑ k : κ, ∑ x' : a, ∑ x : a,
        K k bout x * (psi (r₀, x) * (star (K k bout' x') * star (psi (r₁, x')))) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]
    _ =
      ∑ k : κ,
        rankOneMatrix (krausStinespringReferenceVectorWithRef K psi)
          ((r₀, bout), k) ((r₁, bout'), k) := by
          simp [rankOneMatrix_apply, krausStinespringReferenceVectorWithRef,
            Finset.sum_mul, Finset.mul_sum, mul_assoc]

private theorem partialTraceA_rankOne_stinespringReference_eq_krausComplement_partialTraceA_rankOne_withRef
    {r : Type w} {κ : Type x}
    [Fintype r] [DecidableEq r] [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) (psi : Prod r a → ℂ) :
    partialTraceA (a := Prod r b) (b := κ)
        (rankOneMatrix (krausStinespringReferenceVectorWithRef K psi)) =
      MatrixMap.krausComplement K
        (partialTraceA (a := r) (b := a) (rankOneMatrix psi)) := by
  ext k k'
  change
    (∑ rb : Prod r b,
      rankOneMatrix (krausStinespringReferenceVectorWithRef K psi) (rb, k) (rb, k')) =
      MatrixMap.krausComplement K
        (partialTraceA (a := r) (b := a) (rankOneMatrix psi)) k k'
  calc
    (∑ rb : Prod r b,
      rankOneMatrix (krausStinespringReferenceVectorWithRef K psi) (rb, k) (rb, k'))
        =
      ∑ r₀ : r, ∑ bout : b, ∑ y : a, ∑ x : a,
        K k bout x *
          (psi (r₀, x) * (star (K k' bout y) * star (psi (r₀, y)))) := by
          simp [rankOneMatrix_apply, krausStinespringReferenceVectorWithRef,
            Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ =
      ∑ bout : b, ∑ x : a, ∑ y : a, ∑ r₀ : r,
        K k bout x *
          (psi (r₀, x) * (star (K k' bout y) * star (psi (r₀, y)))) := by
          calc
            (∑ r₀ : r, ∑ bout : b, ∑ y : a, ∑ x : a,
              K k bout x *
                (psi (r₀, x) * (star (K k' bout y) * star (psi (r₀, y)))))
                =
              ∑ bout : b, ∑ r₀ : r, ∑ y : a, ∑ x : a,
                K k bout x *
                  (psi (r₀, x) * (star (K k' bout y) * star (psi (r₀, y)))) := by
                  rw [Finset.sum_comm]
            _ =
              ∑ bout : b, ∑ y : a, ∑ r₀ : r, ∑ x : a,
                K k bout x *
                  (psi (r₀, x) * (star (K k' bout y) * star (psi (r₀, y)))) := by
                  apply Finset.sum_congr rfl
                  intro bout _
                  rw [Finset.sum_comm]
            _ =
              ∑ bout : b, ∑ y : a, ∑ x : a, ∑ r₀ : r,
                K k bout x *
                  (psi (r₀, x) * (star (K k' bout y) * star (psi (r₀, y)))) := by
                  apply Finset.sum_congr rfl
                  intro bout _
                  apply Finset.sum_congr rfl
                  intro y _
                  rw [Finset.sum_comm]
            _ =
              ∑ bout : b, ∑ x : a, ∑ y : a, ∑ r₀ : r,
                K k bout x *
                  (psi (r₀, x) * (star (K k' bout y) * star (psi (r₀, y)))) := by
                  apply Finset.sum_congr rfl
                  intro bout _
                  rw [Finset.sum_comm]
    _ =
      ∑ bout : b, ∑ x : a, ∑ y : a,
        K k bout x *
          ((∑ r₀ : r, psi (r₀, x) * star (psi (r₀, y))) * star (K k' bout y)) := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ =
      ∑ bout : b, ∑ x : a, ∑ y : a,
        K k bout x *
          (partialTraceA (a := r) (b := a) (rankOneMatrix psi) x y *
            star (K k' bout y)) := by
          have hpt : ∀ x y : a,
              partialTraceA (a := r) (b := a) (rankOneMatrix psi) x y =
                ∑ r₀ : r, psi (r₀, x) * star (psi (r₀, y)) := by
            intro x y
            change (∑ r₀ : r, rankOneMatrix psi (r₀, x) (r₀, y)) =
              ∑ r₀ : r, psi (r₀, x) * star (psi (r₀, y))
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
          (partialTraceA (a := r) (b := a) (rankOneMatrix psi) x y *
            star (K k' bout y)) := by
          apply Finset.sum_congr rfl
          intro bout _
          rw [Finset.sum_comm]
    _ =
      MatrixMap.krausComplement K
        (partialTraceA (a := r) (b := a) (rankOneMatrix psi)) k k' := by
          simp [MatrixMap.krausComplement, MatrixMap.ofKraus,
            Matrix.sum_apply, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Finset.sum_mul, mul_assoc]

private theorem cbOneToAlphaPureRankOneValueWithRef_le_cbOneToAlphaNorm
    {r : Type w} [Fintype r] [DecidableEq r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (psi : Prod r a → ℂ)
    (hden :
      0 < psdSchattenPNorm
        (partialTraceB (a := r) (b := a) (rankOneMatrix psi))
        (partialTraceB_posSemidef (rankOneMatrix_pos psi)) alpha) :
    psdSchattenPNorm
        (MatrixMap.kron (Channel.idChannel r).map Phi (rankOneMatrix psi))
        (MatrixMap.isCompletelyPositive_mapsPositive
          (MatrixMap.kron (Channel.idChannel r).map Phi)
          (MatrixMap.isCompletelyPositive_kron
            (Channel.idChannel r).map Phi
            (Channel.idChannel r).completelyPositive hPhi)
          (rankOneMatrix psi) (rankOneMatrix_pos psi))
        alpha /
      psdSchattenPNorm
        (partialTraceB (a := r) (b := a) (rankOneMatrix psi))
        (partialTraceB_posSemidef (rankOneMatrix_pos psi))
        alpha ≤
      cbOneToAlphaNorm Phi hPhi alpha := by
  let K : (a × b) → Matrix b a ℂ := MatrixMap.cpKraus Phi hPhi
  let chi : Prod (Prod r b) (a × b) → ℂ :=
    krausStinespringReferenceVectorWithRef K psi
  let Z : AlphaToAlphaPositiveDomain a alpha :=
    { matrix := partialTraceA (a := r) (b := a) (rankOneMatrix psi),
      pos := partialTraceA_posSemidef (rankOneMatrix_pos psi),
      norm_pos := by
        have hEq :=
          psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
            (r := r) (a := a) psi alpha
        exact hEq ▸ hden }
  have hNum :
      psdSchattenPNorm
          (MatrixMap.kron (Channel.idChannel r).map Phi (rankOneMatrix psi))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.kron (Channel.idChannel r).map Phi)
            (MatrixMap.isCompletelyPositive_kron
              (Channel.idChannel r).map Phi
              (Channel.idChannel r).completelyPositive hPhi)
            (rankOneMatrix psi) (rankOneMatrix_pos psi))
          alpha =
        psdSchattenPNorm
          (MatrixMap.cpComplement Phi hPhi
            (partialTraceA (a := r) (b := a) (rankOneMatrix psi)))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.cpComplement Phi hPhi)
            (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
            (partialTraceA (a := r) (b := a) (rankOneMatrix psi))
            (partialTraceA_posSemidef (rankOneMatrix_pos psi)))
          alpha := by
    have hLeft :
        MatrixMap.kron (Channel.idChannel r).map Phi (rankOneMatrix psi) =
          partialTraceB (a := Prod r b) (b := a × b)
            (rankOneMatrix chi) := by
      calc
        MatrixMap.kron (Channel.idChannel r).map Phi (rankOneMatrix psi) =
            MatrixMap.kron (Channel.idChannel r).map
              (MatrixMap.ofKraus K) (rankOneMatrix psi) := by
              rw [MatrixMap.cpKraus_spec Phi hPhi]
        _ = partialTraceB (a := Prod r b) (b := a × b)
            (rankOneMatrix chi) := by
              simpa [chi] using
                referenceLift_ofKraus_rankOne_eq_partialTraceB_withRef K psi
    have hSchmidt :=
      psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
        (r := Prod r b) (a := a × b) chi alpha
    have hRight :
        partialTraceA (a := Prod r b) (b := a × b) (rankOneMatrix chi) =
          MatrixMap.cpComplement Phi hPhi
            (partialTraceA (a := r) (b := a) (rankOneMatrix psi)) := by
      simpa [chi, K] using
        partialTraceA_rankOne_stinespringReference_eq_krausComplement_partialTraceA_rankOne_withRef
          K psi
    calc
      psdSchattenPNorm
          (MatrixMap.kron (Channel.idChannel r).map Phi (rankOneMatrix psi))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.kron (Channel.idChannel r).map Phi)
            (MatrixMap.isCompletelyPositive_kron
              (Channel.idChannel r).map Phi
              (Channel.idChannel r).completelyPositive hPhi)
            (rankOneMatrix psi) (rankOneMatrix_pos psi))
          alpha =
        psdSchattenPNorm
          (partialTraceB (a := Prod r b) (b := a × b) (rankOneMatrix chi))
          (partialTraceB_posSemidef (rankOneMatrix_pos chi))
          alpha := by
            exact psdSchattenPNorm_congr hLeft _ _ alpha
      _ =
        psdSchattenPNorm
          (partialTraceA (a := Prod r b) (b := a × b) (rankOneMatrix chi))
          (partialTraceA_posSemidef (rankOneMatrix_pos chi))
          alpha := hSchmidt
      _ =
        psdSchattenPNorm
          (MatrixMap.cpComplement Phi hPhi
            (partialTraceA (a := r) (b := a) (rankOneMatrix psi)))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.cpComplement Phi hPhi)
            (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
            (partialTraceA (a := r) (b := a) (rankOneMatrix psi))
            (partialTraceA_posSemidef (rankOneMatrix_pos psi)))
          alpha := by
            exact psdSchattenPNorm_congr hRight _ _ alpha
  have hDen :
      psdSchattenPNorm
          (partialTraceB (a := r) (b := a) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi))
          alpha =
        psdSchattenPNorm
          (partialTraceA (a := r) (b := a) (rankOneMatrix psi))
          (partialTraceA_posSemidef (rankOneMatrix_pos psi))
          alpha := by
    exact
      psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
        (r := r) (a := a) psi alpha
  have hQuot :
      psdSchattenPNorm
          (MatrixMap.kron (Channel.idChannel r).map Phi (rankOneMatrix psi))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.kron (Channel.idChannel r).map Phi)
            (MatrixMap.isCompletelyPositive_kron
              (Channel.idChannel r).map Phi
              (Channel.idChannel r).completelyPositive hPhi)
            (rankOneMatrix psi) (rankOneMatrix_pos psi))
          alpha /
        psdSchattenPNorm
          (partialTraceB (a := r) (b := a) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi))
          alpha =
        alphaToAlphaPositiveValue
          (MatrixMap.cpComplement Phi hPhi)
          (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
          Z := by
    unfold alphaToAlphaPositiveValue
    rw [hNum, hDen]
  rw [hQuot]
  have hbridge :
      cbOneToAlphaNorm Phi hPhi alpha =
        alphaToAlphaNorm (MatrixMap.cpComplement Phi hPhi)
          (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi) alpha := by
    simpa [SchattenOrder.ofOneLt] using
      (MatrixMap.cbOneToAlphaNorm_eq_cpComplement_alphaToAlphaNorm
        Phi hPhi halpha)
  rw [hbridge]
  exact MatrixMap.alphaToAlphaPositiveValue_le_alphaToAlphaNorm_of_one_lt
    (MatrixMap.cpComplement Phi hPhi)
    (MatrixMap.cpComplement_isCompletelyPositive Phi hPhi)
    halpha Z

theorem cbOneToAlphaAlternateExpression_nonneg
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) :
    0 ≤ cbOneToAlphaAlternateExpression Phi hPhi alpha := by
  unfold cbOneToAlphaAlternateExpression
  exact Real.sSup_nonneg (by
    rintro x ⟨Y, rfl⟩
    exact cbOneToAlphaAlternateValue_nonneg Phi hPhi Y)

private theorem cbOneToAlphaOriginalValue_le_alternateValue_of_marginal_norm_pos
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (Y : CBOneToAlphaOriginalDomain a)
    (hnorm_pos :
      0 < psdSchattenPNorm
        (partialTraceB (a := a) (b := a) (cbOneToAlphaOriginalInput Y.matrix alpha))
        (partialTraceB_posSemidef
          (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
        alpha) :
    cbOneToAlphaOriginalValue Phi hPhi Y alpha ≤
      cbOneToAlphaAlternateValue Phi hPhi
        { matrix := cbOneToAlphaOriginalInput Y.matrix alpha,
          pos := cbOneToAlphaOriginalInput_posSemidef Y.pos alpha,
          marginal_norm_pos := hnorm_pos } := by
  let X : CMatrix (Prod a a) := cbOneToAlphaOriginalInput Y.matrix alpha
  let hX : X.PosSemidef := cbOneToAlphaOriginalInput_posSemidef Y.pos alpha
  let Z : CMatrix a := partialTraceB (a := a) (b := a) X
  let hZ : Z.PosSemidef := partialTraceB_posSemidef hX
  let normZ : ℝ := psdSchattenPNorm Z hZ alpha
  have hnormZ_pos : 0 < normZ := by
    simpa [X, hX, Z, hZ, normZ] using hnorm_pos
  let A : CBOneToAlphaAlternateDomain a alpha :=
    { matrix := X, pos := hX, marginal_norm_pos := hnormZ_pos }
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have hZ_eq :
      Z = CFC.rpow Y.matrix (1 / (alpha : Real)) := by
    simpa [X, Z] using
      partialTraceB_cbOneToAlphaOriginalInput_eq_rpow
        (a := a) Y.pos halpha_pos
  have hRpow : (CFC.rpow Y.matrix (1 / (alpha : Real))).PosSemidef :=
    cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos
  have hnorm_le_one : normZ ≤ 1 := by
    let T : AlphaToAlphaTraceDomain a alpha :=
      { matrix := Y.matrix, pos := Y.pos, trace_le_one := Y.trace_le_one }
    have hT := T.rpow_schatten_norm_le_one halpha
    have hnorm_eq :
        normZ =
          psdSchattenPNorm (CFC.rpow Y.matrix (1 / (alpha : Real))) hRpow alpha :=
      psdSchattenPNorm_congr hZ_eq hZ hRpow alpha
    exact hnorm_eq.trans_le hT
  have hratio_nonneg : 0 ≤ cbOneToAlphaAlternateValue Phi hPhi A :=
    cbOneToAlphaAlternateValue_nonneg Phi hPhi A
  have hvalue_eq_mul :
      cbOneToAlphaOriginalValue Phi hPhi Y alpha =
        normZ * cbOneToAlphaAlternateValue Phi hPhi A := by
    unfold cbOneToAlphaOriginalValue cbOneToAlphaAlternateValue
    change
      psdSchattenPNorm (Phi.referenceLift X) _ alpha =
        normZ *
          (psdSchattenPNorm (Phi.referenceLift X) _ alpha / normZ)
    rw [mul_div_cancel₀ _ (ne_of_gt hnormZ_pos)]
  calc
    cbOneToAlphaOriginalValue Phi hPhi Y alpha =
        normZ * cbOneToAlphaAlternateValue Phi hPhi A := hvalue_eq_mul
    _ ≤ cbOneToAlphaAlternateValue Phi hPhi A :=
        mul_le_of_le_one_left hratio_nonneg hnorm_le_one

private theorem cbOneToAlphaOriginalValue_eq_zero_of_marginal_norm_zero
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (Y : CBOneToAlphaOriginalDomain a)
    (hnorm_zero :
      psdSchattenPNorm
        (partialTraceB (a := a) (b := a) (cbOneToAlphaOriginalInput Y.matrix alpha))
        (partialTraceB_posSemidef
          (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
        alpha = 0) :
    cbOneToAlphaOriginalValue Phi hPhi Y alpha = 0 := by
  let X : CMatrix (Prod a a) := cbOneToAlphaOriginalInput Y.matrix alpha
  let hX : X.PosSemidef := cbOneToAlphaOriginalInput_posSemidef Y.pos alpha
  let Z : CMatrix a := partialTraceB (a := a) (b := a) X
  let hZ : Z.PosSemidef := partialTraceB_posSemidef hX
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have hnormZ_zero : psdSchattenPNorm Z hZ alpha = 0 := by
    simpa [X, hX, Z, hZ] using hnorm_zero
  have hZzero : Z = 0 := by
    by_contra hZne
    have hZnorm_pos : 0 < psdSchattenPNorm Z hZ alpha :=
      psdSchattenPNorm_pos_of_ne_zero Z hZ hZne
    exact (ne_of_gt hZnorm_pos) hnormZ_zero
  have hXtrace_zero : X.trace = 0 := by
    rw [← partialTraceB_trace (a := a) (b := a) X]
    simpa [Z] using congrArg Matrix.trace hZzero
  have hXzero : X = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff hX).mp hXtrace_zero
  have hPhiXpos :
      (Phi.referenceLift X).PosSemidef :=
    Phi.referenceLift_mapsPositive hPhi hX
  have hPhiXzero : Phi.referenceLift X = 0 := by
    rw [hXzero]
    exact map_zero Phi.referenceLift
  unfold cbOneToAlphaOriginalValue
  change psdSchattenPNorm (Phi.referenceLift X) _ alpha = 0
  calc
    psdSchattenPNorm (Phi.referenceLift X) _ alpha =
        psdSchattenPNorm (0 : CMatrix (Prod a b))
          Matrix.PosSemidef.zero alpha := by
          exact psdSchattenPNorm_congr hPhiXzero hPhiXpos
            Matrix.PosSemidef.zero alpha
    _ = 0 := psdSchattenPNorm_zero alpha

private theorem cbOneToAlphaOriginalValue_le_alternateExpression_of_bddAbove
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (hbdd : BddAbove (cbOneToAlphaAlternateValueSet Phi hPhi alpha))
    (Y : CBOneToAlphaOriginalDomain a) :
    cbOneToAlphaOriginalValue Phi hPhi Y alpha ≤
      cbOneToAlphaAlternateExpression Phi hPhi alpha := by
  let X : CMatrix (Prod a a) := cbOneToAlphaOriginalInput Y.matrix alpha
  let hX : X.PosSemidef := cbOneToAlphaOriginalInput_posSemidef Y.pos alpha
  let Z : CMatrix a := partialTraceB (a := a) (b := a) X
  let hZ : Z.PosSemidef := partialTraceB_posSemidef hX
  let normZ : ℝ := psdSchattenPNorm Z hZ alpha
  have hnormZ_nonneg : 0 ≤ normZ :=
    psdSchattenPNorm_nonneg Z hZ alpha
  by_cases hnormZ_zero : normZ = 0
  · rw [cbOneToAlphaOriginalValue_eq_zero_of_marginal_norm_zero
      Phi hPhi halpha Y (by simpa [X, hX, Z, hZ, normZ] using hnormZ_zero)]
    exact cbOneToAlphaAlternateExpression_nonneg Phi hPhi alpha
  · have hnormZ_pos : 0 < normZ :=
      lt_of_le_of_ne hnormZ_nonneg (Ne.symm hnormZ_zero)
    let A : CBOneToAlphaAlternateDomain a alpha :=
      { matrix := X, pos := hX, marginal_norm_pos := hnormZ_pos }
    have hle :
        cbOneToAlphaOriginalValue Phi hPhi Y alpha ≤
          cbOneToAlphaAlternateValue Phi hPhi A :=
      cbOneToAlphaOriginalValue_le_alternateValue_of_marginal_norm_pos
        Phi hPhi halpha Y (by simpa [X, hX, Z, hZ, normZ] using hnormZ_pos)
    exact hle.trans
      (le_csSup hbdd
        (cbOneToAlphaAlternateValue_mem_valueSet Phi hPhi A))

theorem cbOneToAlphaNorm_le_cbOneToAlphaAlternateExpression_of_bddAbove
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (hbdd : BddAbove (cbOneToAlphaAlternateValueSet Phi hPhi alpha)) :
    cbOneToAlphaNorm Phi hPhi alpha ≤
      cbOneToAlphaAlternateExpression Phi hPhi alpha := by
  unfold cbOneToAlphaNorm
  refine csSup_le ?_ ?_
  · exact ⟨cbOneToAlphaOriginalValue Phi hPhi
        (CBOneToAlphaOriginalDomain.zero a) alpha,
      ⟨CBOneToAlphaOriginalDomain.zero a, rfl⟩⟩
  rintro x ⟨Y, rfl⟩
  exact cbOneToAlphaOriginalValue_le_alternateExpression_of_bddAbove
    Phi hPhi halpha hbdd Y

omit [Fintype b] [DecidableEq b] in
private theorem alphaToAlphaPositiveValue_id_eq_one
    {alpha : SchattenOrder} (Z : AlphaToAlphaPositiveDomain a alpha) :
    alphaToAlphaPositiveValue (Channel.idChannel a).map
      (Channel.idChannel a).completelyPositive Z = 1 := by
  unfold alphaToAlphaPositiveValue
  calc
    psdSchattenPNorm ((Channel.idChannel a).map Z.matrix)
        (MatrixMap.isCompletelyPositive_mapsPositive (Channel.idChannel a).map
          (Channel.idChannel a).completelyPositive Z.matrix Z.pos) alpha /
      psdSchattenPNorm Z.matrix Z.pos alpha =
        psdSchattenPNorm Z.matrix Z.pos alpha /
          psdSchattenPNorm Z.matrix Z.pos alpha := by
          exact congrArg (fun x => x / psdSchattenPNorm Z.matrix Z.pos alpha)
            (psdSchattenPNorm_congr (Channel.idChannel_map Z.matrix)
              (MatrixMap.isCompletelyPositive_mapsPositive (Channel.idChannel a).map
                (Channel.idChannel a).completelyPositive Z.matrix Z.pos)
              Z.pos alpha)
    _ = 1 := div_self (ne_of_gt Z.norm_pos)

omit [Fintype b] [DecidableEq b] in
private theorem alphaToAlphaNorm_id_eq_one
    [Nonempty a] {alpha : SchattenOrder} :
    alphaToAlphaNorm (Channel.idChannel a).map
      (Channel.idChannel a).completelyPositive alpha = 1 := by
  let Z0 : AlphaToAlphaPositiveDomain a alpha :=
    { matrix := 1,
      pos := Matrix.PosSemidef.one,
      norm_pos := by
        exact psdSchattenPNorm_pos_of_posDef Matrix.PosDef.one }
  apply le_antisymm
  · unfold alphaToAlphaNorm alphaToAlphaPositiveValueSet
    refine csSup_le ?_ ?_
    · exact ⟨alphaToAlphaPositiveValue (Channel.idChannel a).map
          (Channel.idChannel a).completelyPositive Z0, ⟨Z0, rfl⟩⟩
    · rintro x ⟨Z, rfl⟩
      change alphaToAlphaPositiveValue (Channel.idChannel a).map
        (Channel.idChannel a).completelyPositive Z ≤ 1
      rw [alphaToAlphaPositiveValue_id_eq_one Z]
  · unfold alphaToAlphaNorm alphaToAlphaPositiveValueSet
    exact le_csSup
      (by
        exact ⟨1, by
          rintro x ⟨Z, rfl⟩
          change alphaToAlphaPositiveValue (Channel.idChannel a).map
            (Channel.idChannel a).completelyPositive Z ≤ 1
          rw [alphaToAlphaPositiveValue_id_eq_one Z]⟩)
      ⟨Z0, by
        change alphaToAlphaPositiveValue (Channel.idChannel a).map
          (Channel.idChannel a).completelyPositive Z0 = 1
        rw [alphaToAlphaPositiveValue_id_eq_one Z0]⟩

omit [Fintype b] [DecidableEq b] in
private theorem psdSqrt_one : psdSqrt (1 : CMatrix a) = 1 := by
  have hsquare : (1 : CMatrix a) * (1 : CMatrix a) = (1 : CMatrix a) := by simp
  have hpos : (1 : CMatrix a).PosSemidef := Matrix.PosSemidef.one
  have hnonneg : (0 : CMatrix a) ≤ (1 : CMatrix a) :=
    Matrix.nonneg_iff_posSemidef.mpr hpos
  change CFC.sqrt (1 : CMatrix a) = 1
  exact CFC.sqrt_unique (a := (1 : CMatrix a)) (b := (1 : CMatrix a))
    hsquare hnonneg

omit [Fintype b] [DecidableEq b] in
private theorem traceEffectToUnit_one_krausComplement_eq_id :
    MatrixMap.krausComplement
        (fun k : a => fun (_ : PUnit) (i : a) =>
          (psdSqrt (1 : CMatrix a)) k i) =
      (Channel.idChannel a).map := by
  ext X i j
  simp [MatrixMap.krausComplement, MatrixMap.ofKraus, Channel.idChannel_map,
    psdSqrt_one]

private theorem cbOneToAlphaNorm_congr_map_unit
    {Phi Psi : MatrixMap a PUnit}
    (hmap : Phi = Psi)
    (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (hPsi : MatrixMap.IsCompletelyPositive Psi)
    (alpha : SchattenOrder) :
    cbOneToAlphaNorm Phi hPhi alpha =
      cbOneToAlphaNorm Psi hPsi alpha := by
  subst hmap
  rfl

omit [Fintype b] [DecidableEq b] in
private theorem alphaToAlphaNorm_congr_map_self
    {Phi Psi : MatrixMap a a}
    (hmap : Phi = Psi)
    (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (hPsi : MatrixMap.IsCompletelyPositive Psi)
    (alpha : SchattenOrder) :
    alphaToAlphaNorm Phi hPhi alpha =
      alphaToAlphaNorm Psi hPsi alpha := by
  subst hmap
  rfl

omit [Fintype b] [DecidableEq b] in
/-- The discard/trace functional has CB `1 -> alpha` norm one.

This is the final trace-factor step in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2102-2140], specifically
source lines 2137-2140. -/
theorem cbOneToAlphaNorm_traceEffectToUnit_one
    [Nonempty a] {alpha : SchattenOrder} (halpha : 1 < (alpha : Real)) :
    MatrixMap.cbOneToAlphaNorm
      (MatrixMap.traceEffectToUnit (1 : CMatrix a))
      ((MatrixMap.traceEffectToUnit_traceNonincreasingCP
        (Matrix.PosSemidef.one : (1 : CMatrix a).PosSemidef) le_rfl).completelyPositive)
      alpha = 1 := by
  let K : a → Matrix PUnit a ℂ := fun k => fun (_ : PUnit) i =>
    (psdSqrt (1 : CMatrix a)) k i
  have hnorm_kraus :
      cbOneToAlphaNorm
          (MatrixMap.ofKraus K)
          (MatrixMap.ofKraus_completelyPositive K)
          alpha = 1 := by
    calc
      cbOneToAlphaNorm
          (MatrixMap.ofKraus K)
          (MatrixMap.ofKraus_completelyPositive K)
          alpha =
        alphaToAlphaNorm
          (MatrixMap.krausComplement K)
          (MatrixMap.krausComplement_isCompletelyPositive K)
          alpha :=
          by
            simpa [SchattenOrder.ofOneLt] using
              (MatrixMap.cbOneToAlphaNorm_eq_krausComplement_alphaToAlphaNorm
                K halpha)
      _ =
        alphaToAlphaNorm
          (Channel.idChannel a).map
          (Channel.idChannel a).completelyPositive
          alpha := by
            exact alphaToAlphaNorm_congr_map_self
              (show MatrixMap.krausComplement K = (Channel.idChannel a).map by
                simpa [K] using traceEffectToUnit_one_krausComplement_eq_id (a := a))
              (MatrixMap.krausComplement_isCompletelyPositive K)
              (Channel.idChannel a).completelyPositive
              alpha
      _ = 1 := alphaToAlphaNorm_id_eq_one (a := a)
  calc
    cbOneToAlphaNorm
      (MatrixMap.traceEffectToUnit (1 : CMatrix a))
      ((MatrixMap.traceEffectToUnit_traceNonincreasingCP
        (Matrix.PosSemidef.one : (1 : CMatrix a).PosSemidef) le_rfl).completelyPositive)
      alpha =
      cbOneToAlphaNorm
          (MatrixMap.ofKraus K)
          (MatrixMap.ofKraus_completelyPositive K)
          alpha := by
            exact cbOneToAlphaNorm_congr_map_unit
              (by rfl)
              ((MatrixMap.traceEffectToUnit_traceNonincreasingCP
                (Matrix.PosSemidef.one : (1 : CMatrix a).PosSemidef) le_rfl).completelyPositive)
              (MatrixMap.ofKraus_completelyPositive K)
              alpha
    _ = 1 := hnorm_kraus

private theorem psdSchattenPNorm_isometry_conj
    {r : Type v} [Fintype r] [DecidableEq r]
    (V : Matrix r a ℂ) {A : CMatrix a} (hA : A.PosSemidef)
    (hV : Matrix.conjTranspose V * V = (1 : CMatrix a))
    (p : SchattenOrder) :
    psdSchattenPNorm (V * A * Matrix.conjTranspose V)
        (hA.mul_mul_conjTranspose_same V) p =
      psdSchattenPNorm A hA p := by
  simp only [psdSchattenPNorm, Internal.psdSchattenExpression]
  rw [psdTracePower_isometry_conj V hA hV p.property]

/-- Canonical purification amplitude for an arbitrary `Y_RA`, arranged as
`R | (A,S)`.

This is the finite-dimensional purification used in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2102-2140], specifically
source lines 2131-2135. -/
private def cbOneToAlphaPurificationAmp
    (Y : CMatrix (Prod a a)) : Prod a (Prod a (Prod a a)) → ℂ :=
  fun x => psdSqrt Y (x.1, x.2.1) x.2.2

private theorem partialTraceB_rankOne_cbOneToAlphaPurificationAmp
    {Y : CMatrix (Prod a a)} (hY : Y.PosSemidef) :
    partialTraceB (a := a) (b := Prod a (Prod a a))
        (rankOneMatrix (cbOneToAlphaPurificationAmp Y)) =
      partialTraceB (a := a) (b := a) Y := by
  let S : CMatrix (Prod a a) := psdSqrt Y
  have hSsq : S * S = Y := by
    simpa [S] using psdSqrt_mul_self_of_posSemidef hY
  have hSherm : S.IsHermitian := by
    simpa [S] using psdSqrt_isHermitian Y
  ext r r'
  calc
    partialTraceB (a := a) (b := Prod a (Prod a a))
        (rankOneMatrix (cbOneToAlphaPurificationAmp Y)) r r'
        = ∑ x : Prod a (Prod a a),
            S (r, x.1) x.2 * star (S (r', x.1) x.2) := by
          change (∑ x : Prod a (Prod a a),
            rankOneMatrix (cbOneToAlphaPurificationAmp Y) (r, x) (r', x)) =
              ∑ x : Prod a (Prod a a),
                S (r, x.1) x.2 * star (S (r', x.1) x.2)
          simp [rankOneMatrix_apply, cbOneToAlphaPurificationAmp, S]
    _ = ∑ av : a, ∑ s : Prod a a,
            S (r, av) s * star (S (r', av) s) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ av : a, ∑ s : Prod a a,
            S (r, av) s * S s (r', av) := by
          refine Finset.sum_congr rfl fun av _ => ?_
          refine Finset.sum_congr rfl fun s _ => ?_
          have hstar : star (S (r', av) s) = S s (r', av) := by
            simpa using hSherm.apply s (r', av)
          rw [hstar]
    _ = ∑ av : a, (S * S) (r, av) (r', av) := by
          refine Finset.sum_congr rfl fun av _ => ?_
          simp [Matrix.mul_apply]
    _ = ∑ av : a, Y (r, av) (r', av) := by
          refine Finset.sum_congr rfl fun av _ => ?_
          rw [hSsq]
    _ = partialTraceB (a := a) (b := a) Y r r' := by
          rfl

private theorem traceEffectToUnit_one_single_apply
    {s : Type w} [Fintype s] [DecidableEq s] (p q : s) :
    MatrixMap.traceEffectToUnit (1 : CMatrix s) (Matrix.single p q (1 : ℂ))
        PUnit.unit PUnit.unit = if q = p then 1 else 0 := by
  have h := MatrixMap.traceEffectToUnit_apply_of_posSemidef
    (a := s) (E := (1 : CMatrix s)) (X := Matrix.single p q (1 : ℂ))
    Matrix.PosSemidef.one
  have happ := congrFun (congrFun h PUnit.unit) PUnit.unit
  calc
    MatrixMap.traceEffectToUnit (1 : CMatrix s) (Matrix.single p q (1 : ℂ))
        PUnit.unit PUnit.unit =
        ((Matrix.single p q (1 : ℂ) * (1 : CMatrix s)).trace) := happ
    _ = (Matrix.single p q (1 : ℂ)).trace := by rw [Matrix.mul_one]
    _ = if q = p then 1 else 0 := by
          by_cases hqp : q = p
          · subst q
            simp [Matrix.trace, Matrix.single]
          · simp [Matrix.trace, Matrix.single, hqp]

private def padOutputRightUnit
    {η : Type w} [Inhabited η] (A : CMatrix (Prod a b)) :
    CMatrix (Prod a (Prod b η)) :=
  fun x y => A (x.1, x.2.1) (y.1, y.2.1)

private def outputRightUnitEquiv
    {η : Type w} [Inhabited η] [Subsingleton η] :
    Prod a b ≃ Prod a (Prod b η) where
  toFun x := (x.1, (x.2, default))
  invFun x := (x.1, x.2.1)
  left_inv x := rfl
  right_inv x := by
    rcases x with ⟨ra, bout, e⟩
    simp [Subsingleton.elim default e]

private def outputRightUnitIsometry
    {η : Type w} [DecidableEq η] [Inhabited η] [Subsingleton η] :
    Matrix (Prod a (Prod b η)) (Prod a b) ℂ :=
  fun x y => if x = outputRightUnitEquiv y then 1 else 0

private theorem outputRightUnitIsometry_isometry
    {η : Type w} [Fintype η] [DecidableEq η] [Inhabited η] [Subsingleton η] :
    Matrix.conjTranspose (outputRightUnitIsometry (a := a) (b := b) (η := η)) *
        outputRightUnitIsometry =
      (1 : CMatrix (Prod a b)) := by
  ext x y
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (outputRightUnitEquiv (η := η) x)]
  · by_cases hxy : x = y
    · subst y
      simp [outputRightUnitIsometry]
    · have hne :
          (outputRightUnitEquiv (η := η)) x ≠
            (outputRightUnitEquiv (η := η)) y := by
        intro h
        exact hxy ((outputRightUnitEquiv (η := η)).injective h)
      simp [outputRightUnitIsometry, hxy, hne]
  · intro z _ hz
    have hzx : z ≠ (outputRightUnitEquiv (η := η)) x := hz
    by_cases hzy : z = (outputRightUnitEquiv (η := η)) y
    · subst z
      simp [outputRightUnitIsometry, hz]
    · simp [outputRightUnitIsometry, hzx, hzy]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

private theorem padOutputRightUnit_eq_isometry_conj
    {η : Type w} [Fintype η] [DecidableEq η] [Inhabited η] [Subsingleton η]
    (A : CMatrix (Prod a b)) :
    padOutputRightUnit A =
      outputRightUnitIsometry * A *
        Matrix.conjTranspose (outputRightUnitIsometry (a := a) (b := b) (η := η)) := by
  ext x y
  rcases x with ⟨ra, bout, ux⟩
  rcases y with ⟨ra', bout', uy⟩
  have hux : ux = default := Subsingleton.elim ux default
  have huy : uy = default := Subsingleton.elim uy default
  subst ux
  subst uy
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (ra', bout')]
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (ra, bout)]
    · simp [padOutputRightUnit, outputRightUnitIsometry, outputRightUnitEquiv]
    · intro z _ hz
      have hzx : (ra, (bout, (default : η))) ≠
          (outputRightUnitEquiv (η := η)) z := by
        intro hx
        apply hz
        simpa [outputRightUnitEquiv] using
          (congrArg (fun x : Prod a (Prod b η) => (x.1, x.2.1)) hx).symm
      simp [outputRightUnitIsometry, hzx]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · intro z _ hz
    rw [Matrix.mul_apply]
    have hyz : (ra', (bout', (default : η))) ≠
        (outputRightUnitEquiv (η := η)) z := by
      intro hy
      apply hz
      simpa [outputRightUnitEquiv] using
        (congrArg (fun x : Prod a (Prod b η) => (x.1, x.2.1)) hy).symm
    simp [outputRightUnitIsometry, hyz]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

private theorem psdSchattenPNorm_padOutputRightUnit
    {η : Type w} [Fintype η] [DecidableEq η] [Inhabited η] [Subsingleton η]
    {A : CMatrix (Prod a b)} (hA : A.PosSemidef)
    (hPad : (padOutputRightUnit (η := η) A).PosSemidef)
    (p : SchattenOrder) :
    psdSchattenPNorm (padOutputRightUnit (η := η) A) hPad p =
      psdSchattenPNorm A hA p := by
  let V : Matrix (Prod a (Prod b η)) (Prod a b) ℂ :=
    outputRightUnitIsometry
  let hConj : (V * A * Matrix.conjTranspose V).PosSemidef :=
    hA.mul_mul_conjTranspose_same V
  calc
    psdSchattenPNorm (padOutputRightUnit (η := η) A) hPad p =
        psdSchattenPNorm (V * A * Matrix.conjTranspose V) hConj p := by
          exact psdSchattenPNorm_congr
            (by simpa [V] using padOutputRightUnit_eq_isometry_conj (η := η) (A := A))
            hPad hConj p
    _ = psdSchattenPNorm A hA p := by
          exact psdSchattenPNorm_isometry_conj V hA
            (by simpa [V] using outputRightUnitIsometry_isometry (a := a) (b := b) (η := η))
            p

private theorem kron_traceEffectToUnit_one_apply
    {s : Type w} [Fintype s] [DecidableEq s]
    (Phi : MatrixMap a b) (X : CMatrix (Prod a s)) (bout bout' : b) :
    MatrixMap.kron Phi (MatrixMap.traceEffectToUnit (1 : CMatrix s)) X
        (bout, PUnit.unit) (bout', PUnit.unit) =
      Phi (partialTraceB (a := a) (b := s) X) bout bout' := by
  have hPhi := congrFun
    (congrFun (MatrixMap.map_eq_sum_single Phi
      (partialTraceB (a := a) (b := s) X)) bout) bout'
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hPhi
  calc
    MatrixMap.kron Phi (MatrixMap.traceEffectToUnit (1 : CMatrix s)) X
        (bout, PUnit.unit) (bout', PUnit.unit)
        =
      ∑ j : s, ∑ i : a, ∑ i' : a,
        X (i, j) (i', j) *
          Phi (Matrix.single i i' (1 : ℂ)) bout bout' := by
          simp [MatrixMap.kron, traceEffectToUnit_one_single_apply]
    _ =
      ∑ i : a, ∑ j : s, ∑ i' : a,
        X (i, j) (i', j) *
          Phi (Matrix.single i i' (1 : ℂ)) bout bout' := by
          rw [Finset.sum_comm]
    _ =
      ∑ i : a, ∑ i' : a, ∑ j : s,
        X (i, j) (i', j) *
          Phi (Matrix.single i i' (1 : ℂ)) bout bout' := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
    _ =
      ∑ i : a, ∑ i' : a,
        (∑ j : s, X (i, j) (i', j)) *
          Phi (Matrix.single i i' (1 : ℂ)) bout bout' := by
          simp [Finset.sum_mul]
    _ =
      ∑ i : a, ∑ i' : a,
        partialTraceB (a := a) (b := s) X i i' *
          Phi (Matrix.single i i' (1 : ℂ)) bout bout' := by
          rfl
    _ = Phi (partialTraceB (a := a) (b := s) X) bout bout' := by
          exact hPhi.symm

private theorem partialTraceB_cbOneToAlphaPurificationAmp_slice
    {Y : CMatrix (Prod a a)} (hY : Y.PosSemidef) (r r' : a) :
    partialTraceB (a := a) (b := Prod a a)
        (fun j j' : Prod a (Prod a a) =>
          rankOneMatrix (cbOneToAlphaPurificationAmp Y) (r, j) (r', j')) =
      fun i i' => Y (r, i) (r', i') := by
  let S : CMatrix (Prod a a) := psdSqrt Y
  have hSsq : S * S = Y := by
    simpa [S] using psdSqrt_mul_self_of_posSemidef hY
  have hSherm : S.IsHermitian := by
    simpa [S] using psdSqrt_isHermitian Y
  ext i i'
  calc
    partialTraceB (a := a) (b := Prod a a)
        (fun j j' : Prod a (Prod a a) =>
          rankOneMatrix (cbOneToAlphaPurificationAmp Y) (r, j) (r', j')) i i'
        = ∑ s : Prod a a, S (r, i) s * star (S (r', i') s) := by
          change (∑ s : Prod a a,
            rankOneMatrix (cbOneToAlphaPurificationAmp Y) (r, (i, s)) (r', (i', s))) =
              ∑ s : Prod a a, S (r, i) s * star (S (r', i') s)
          simp [rankOneMatrix_apply, cbOneToAlphaPurificationAmp, S]
    _ = ∑ s : Prod a a, S (r, i) s * S s (r', i') := by
          refine Finset.sum_congr rfl fun s _ => ?_
          have hstar : star (S (r', i') s) = S s (r', i') := by
            simpa using hSherm.apply s (r', i')
          rw [hstar]
    _ = (S * S) (r, i) (r', i') := by
          simp [Matrix.mul_apply]
    _ = Y (r, i) (r', i') := by
          rw [hSsq]

private theorem kron_id_kron_trace_purification_eq_pad_referenceLift
    (Phi : MatrixMap a b) {Y : CMatrix (Prod a a)} (hY : Y.PosSemidef) :
    MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.kron Phi (MatrixMap.traceEffectToUnit (1 : CMatrix (Prod a a))))
        (rankOneMatrix (cbOneToAlphaPurificationAmp Y)) =
      padOutputRightUnit (Phi.referenceLift Y) := by
  ext x y
  rcases x with ⟨r, bout, ux⟩
  rcases y with ⟨r', bout', uy⟩
  cases ux
  cases uy
  calc
    MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.kron Phi (MatrixMap.traceEffectToUnit (1 : CMatrix (Prod a a))))
        (rankOneMatrix (cbOneToAlphaPurificationAmp Y))
        (r, (bout, PUnit.unit)) (r', (bout', PUnit.unit))
        =
      MatrixMap.kron Phi (MatrixMap.traceEffectToUnit (1 : CMatrix (Prod a a)))
        (fun j j' : Prod a (Prod a a) =>
          rankOneMatrix (cbOneToAlphaPurificationAmp Y) (r, j) (r', j'))
        (bout, PUnit.unit) (bout', PUnit.unit) := by
          rw [MatrixMap.kron_idChannel_left_apply_slice]
    _ =
      Phi
        (partialTraceB (a := a) (b := Prod a a)
          (fun j j' : Prod a (Prod a a) =>
            rankOneMatrix (cbOneToAlphaPurificationAmp Y) (r, j) (r', j')))
        bout bout' := by
          rw [kron_traceEffectToUnit_one_apply]
    _ = Phi (fun i i' => Y (r, i) (r', i')) bout bout' := by
          rw [partialTraceB_cbOneToAlphaPurificationAmp_slice hY r r']
    _ = Phi.referenceLift Y (r, bout) (r', bout') := by
          rw [MatrixMap.referenceLift]
          rw [MatrixMap.kron_idChannel_left_apply_slice]
    _ =
      padOutputRightUnit (Phi.referenceLift Y)
        (r, (bout, PUnit.unit)) (r', (bout', PUnit.unit)) := by
          rfl

/-- Each alternate-expression quotient is bounded by the source CB norm.

This formalizes the purification and `M \otimes Tr` argument from
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2102-2140], specifically
source lines 2131-2140. -/
theorem cbOneToAlphaAlternateValue_le_cbOneToAlphaNorm
    [Nonempty a]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (Y : CBOneToAlphaAlternateDomain a alpha) :
    cbOneToAlphaAlternateValue Phi hPhi Y ≤
      cbOneToAlphaNorm Phi hPhi alpha := by
  let s := Prod a a
  let TrS : MatrixMap s PUnit.{1} :=
    MatrixMap.traceEffectToUnit (1 : CMatrix s)
  let hTrS : MatrixMap.IsCompletelyPositive TrS :=
    ((MatrixMap.traceEffectToUnit_traceNonincreasingCP
      (Matrix.PosSemidef.one : (1 : CMatrix s).PosSemidef) le_rfl).completelyPositive)
  let Theta : MatrixMap (Prod a s) (Prod b PUnit.{1}) :=
    MatrixMap.kron Phi TrS
  let hTheta : MatrixMap.IsCompletelyPositive Theta :=
    MatrixMap.isCompletelyPositive_kron Phi TrS hPhi hTrS
  let psi : Prod a (Prod a s) → ℂ :=
    cbOneToAlphaPurificationAmp Y.matrix
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have hDenMatrix :
      partialTraceB (a := a) (b := Prod a s) (rankOneMatrix psi) =
        partialTraceB (a := a) (b := a) Y.matrix := by
    simpa [psi, s] using
      partialTraceB_rankOne_cbOneToAlphaPurificationAmp
        (a := a) (Y := Y.matrix) Y.pos
  have hDenNorm :
      psdSchattenPNorm
          (partialTraceB (a := a) (b := Prod a s) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi)) alpha =
        psdSchattenPNorm
          (partialTraceB (a := a) (b := a) Y.matrix)
          (partialTraceB_posSemidef Y.pos) alpha := by
    exact psdSchattenPNorm_congr hDenMatrix
      (partialTraceB_posSemidef (rankOneMatrix_pos psi))
      (partialTraceB_posSemidef Y.pos) alpha
  have hDenPos :
      0 < psdSchattenPNorm
          (partialTraceB (a := a) (b := Prod a s) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi)) alpha := by
    rw [hDenNorm]
    exact Y.marginal_norm_pos
  have hPure :
      psdSchattenPNorm
          (MatrixMap.kron (Channel.idChannel a).map Theta (rankOneMatrix psi))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.kron (Channel.idChannel a).map Theta)
            (MatrixMap.isCompletelyPositive_kron
              (Channel.idChannel a).map Theta
              (Channel.idChannel a).completelyPositive hTheta)
            (rankOneMatrix psi) (rankOneMatrix_pos psi))
          alpha /
        psdSchattenPNorm
          (partialTraceB (a := a) (b := Prod a s) (rankOneMatrix psi))
          (partialTraceB_posSemidef (rankOneMatrix_pos psi))
          alpha ≤
        cbOneToAlphaNorm Theta hTheta alpha := by
    exact cbOneToAlphaPureRankOneValueWithRef_le_cbOneToAlphaNorm
      (a := Prod a s) (b := Prod b PUnit.{1}) (r := a)
      Theta hTheta halpha psi hDenPos
  let hAltNum : (Phi.referenceLift Y.matrix).PosSemidef :=
    Phi.referenceLift_mapsPositive hPhi Y.pos
  let hPad : (padOutputRightUnit (η := PUnit.{1}) (Phi.referenceLift Y.matrix)).PosSemidef := by
    rw [padOutputRightUnit_eq_isometry_conj (η := PUnit.{1})
      (A := Phi.referenceLift Y.matrix)]
    exact hAltNum.mul_mul_conjTranspose_same
      (outputRightUnitIsometry (a := a) (b := b) (η := PUnit.{1}))
  have hNumMatrix :
      MatrixMap.kron (Channel.idChannel a).map Theta (rankOneMatrix psi) =
        padOutputRightUnit (η := PUnit.{1}) (Phi.referenceLift Y.matrix) := by
    simpa [Theta, TrS, psi, s] using
      kron_id_kron_trace_purification_eq_pad_referenceLift
        (a := a) (b := b) Phi (Y := Y.matrix) Y.pos
  have hNumNorm :
      psdSchattenPNorm
          (MatrixMap.kron (Channel.idChannel a).map Theta (rankOneMatrix psi))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.kron (Channel.idChannel a).map Theta)
            (MatrixMap.isCompletelyPositive_kron
              (Channel.idChannel a).map Theta
              (Channel.idChannel a).completelyPositive hTheta)
            (rankOneMatrix psi) (rankOneMatrix_pos psi))
          alpha =
        psdSchattenPNorm (Phi.referenceLift Y.matrix) hAltNum alpha := by
    calc
      psdSchattenPNorm
          (MatrixMap.kron (Channel.idChannel a).map Theta (rankOneMatrix psi))
          (MatrixMap.isCompletelyPositive_mapsPositive
            (MatrixMap.kron (Channel.idChannel a).map Theta)
            (MatrixMap.isCompletelyPositive_kron
              (Channel.idChannel a).map Theta
              (Channel.idChannel a).completelyPositive hTheta)
            (rankOneMatrix psi) (rankOneMatrix_pos psi))
          alpha =
        psdSchattenPNorm
          (padOutputRightUnit (η := PUnit.{1}) (Phi.referenceLift Y.matrix))
          hPad alpha := by
            exact psdSchattenPNorm_congr hNumMatrix _ hPad alpha
      _ = psdSchattenPNorm (Phi.referenceLift Y.matrix) hAltNum alpha := by
            exact psdSchattenPNorm_padOutputRightUnit hAltNum hPad alpha
  have hValueEq :
      cbOneToAlphaAlternateValue Phi hPhi Y =
        psdSchattenPNorm
            (MatrixMap.kron (Channel.idChannel a).map Theta (rankOneMatrix psi))
            (MatrixMap.isCompletelyPositive_mapsPositive
              (MatrixMap.kron (Channel.idChannel a).map Theta)
              (MatrixMap.isCompletelyPositive_kron
                (Channel.idChannel a).map Theta
                (Channel.idChannel a).completelyPositive hTheta)
              (rankOneMatrix psi) (rankOneMatrix_pos psi))
            alpha /
          psdSchattenPNorm
            (partialTraceB (a := a) (b := Prod a s) (rankOneMatrix psi))
            (partialTraceB_posSemidef (rankOneMatrix_pos psi))
            alpha := by
    unfold cbOneToAlphaAlternateValue
    rw [hNumNorm, hDenNorm]
  have hThetaNorm :
      cbOneToAlphaNorm Theta hTheta alpha =
        cbOneToAlphaNorm Phi hPhi alpha *
          cbOneToAlphaNorm TrS hTrS alpha := by
    simpa [SchattenOrder.ofOneLt] using
      (cbOneToAlphaNorm_kron_eq_mul Phi hPhi TrS hTrS halpha)
  have hTrNorm :
      cbOneToAlphaNorm TrS hTrS alpha = 1 := by
    simpa [TrS, hTrS, s] using
      cbOneToAlphaNorm_traceEffectToUnit_one (a := s) halpha
  calc
    cbOneToAlphaAlternateValue Phi hPhi Y =
        psdSchattenPNorm
            (MatrixMap.kron (Channel.idChannel a).map Theta (rankOneMatrix psi))
            (MatrixMap.isCompletelyPositive_mapsPositive
              (MatrixMap.kron (Channel.idChannel a).map Theta)
              (MatrixMap.isCompletelyPositive_kron
                (Channel.idChannel a).map Theta
                (Channel.idChannel a).completelyPositive hTheta)
              (rankOneMatrix psi) (rankOneMatrix_pos psi))
            alpha /
          psdSchattenPNorm
            (partialTraceB (a := a) (b := Prod a s) (rankOneMatrix psi))
            (partialTraceB_posSemidef (rankOneMatrix_pos psi))
            alpha := hValueEq
    _ ≤ cbOneToAlphaNorm Theta hTheta alpha := hPure
    _ = cbOneToAlphaNorm Phi hPhi alpha := by
          rw [hThetaNorm, hTrNorm, mul_one]

private def CBOneToAlphaAlternateDomain.one
    [Nonempty a] (alpha : SchattenOrder) : CBOneToAlphaAlternateDomain a alpha where
  matrix := 1
  pos := Matrix.PosSemidef.one
  marginal_norm_pos := by
    have hne :
        partialTraceB (a := a) (b := a) (1 : CMatrix (Prod a a)) ≠ 0 := by
      classical
      obtain ⟨i⟩ := ‹Nonempty a›
      intro hzero
      have hentry := congrFun (congrFun hzero i) i
      have hcard_pos : 0 < Fintype.card a := Fintype.card_pos_iff.mpr ‹Nonempty a›
      have hcard_ne : ((Fintype.card a : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hcard_pos)
      have hdiag :
          partialTraceB (a := a) (b := a) (1 : CMatrix (Prod a a)) i i =
            (Fintype.card a : ℂ) := by
        change (∑ j : a, (1 : CMatrix (Prod a a)) (i, j) (i, j)) =
          (Fintype.card a : ℂ)
        simp
      have hentry_zero :
          partialTraceB (a := a) (b := a) (1 : CMatrix (Prod a a)) i i = 0 := by
        simpa using hentry
      have hcard_zero : (Fintype.card a : ℂ) = 0 := by
        rw [← hdiag]
        exact hentry_zero
      exact hcard_ne hcard_zero
    exact psdSchattenPNorm_pos_of_ne_zero
      (partialTraceB (a := a) (b := a) (1 : CMatrix (Prod a a)))
      (partialTraceB_posSemidef (Matrix.PosSemidef.one :
        (1 : CMatrix (Prod a a)).PosSemidef))
      hne

theorem cbOneToAlphaAlternateExpression_le_cbOneToAlphaNorm
    [Nonempty a]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real)) :
    cbOneToAlphaAlternateExpression Phi hPhi alpha ≤
      cbOneToAlphaNorm Phi hPhi alpha := by
  unfold cbOneToAlphaAlternateExpression
  refine csSup_le ?_ ?_
  · let Y0 := CBOneToAlphaAlternateDomain.one (a := a) alpha
    exact ⟨cbOneToAlphaAlternateValue Phi hPhi Y0, ⟨Y0, rfl⟩⟩
  · rintro x ⟨Y, rfl⟩
    exact cbOneToAlphaAlternateValue_le_cbOneToAlphaNorm Phi hPhi halpha Y

/-- Source alternate expression for the CB `1 -> alpha` norm.

This is the theorem statement in
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:2102-2140], specifically
source lines 2105-2107, with the two inequalities formalizing the source proof
in lines 2110-2140. -/
theorem cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    [Nonempty a]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real)) :
    cbOneToAlphaNorm Phi hPhi alpha =
      cbOneToAlphaAlternateExpression Phi hPhi alpha := by
  have hbdd : BddAbove (cbOneToAlphaAlternateValueSet Phi hPhi alpha) :=
    ⟨cbOneToAlphaNorm Phi hPhi alpha, by
      rintro x ⟨Y, rfl⟩
      exact cbOneToAlphaAlternateValue_le_cbOneToAlphaNorm
        Phi hPhi halpha Y⟩
  exact le_antisymm
    (cbOneToAlphaNorm_le_cbOneToAlphaAlternateExpression_of_bddAbove
      Phi hPhi halpha hbdd)
    (cbOneToAlphaAlternateExpression_le_cbOneToAlphaNorm
      Phi hPhi halpha)

end MatrixMap

end

end QIT
