/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Concavity

/-!
# Identity-reference collapse for the positive `alpha -> alpha` norm

This module proves the Khatri--Wilde source collapse step for completely
positive maps:
`||id_R ⊗ Phi||_{alpha -> alpha} = ||Phi||_{alpha -> alpha}`.

Source alignment:
* KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2242-2280 prove
  the collapse lemma by product-input restriction for the lower bound and by
  reference twirling plus concavity for the upper bound.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x

noncomputable section

open State

variable {r : Type w} {a : Type u} {b : Type v}
variable [Fintype r] [DecidableEq r]
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace MatrixMap

private theorem maximallyMixed_matrix_ne_zero [Nonempty r] :
    (maximallyMixed r).matrix ≠ 0 := by
  intro hzero
  have htrace := congrArg Complex.re (maximallyMixed r).trace_eq_one
  rw [hzero, Matrix.trace_zero] at htrace
  norm_num at htrace

theorem maximallyMixed_schatten_norm_pos [Nonempty r] (alpha : SchattenOrder) :
    0 < psdSchattenPNorm (maximallyMixed r).matrix (maximallyMixed r).pos alpha :=
  psdSchattenPNorm_pos_of_ne_zero (maximallyMixed r).matrix
    (maximallyMixed r).pos (maximallyMixed_matrix_ne_zero (r := r))

theorem posSemidef_unitary_conj_forward
    {n : Type x} [Fintype n] [DecidableEq n]
    {A : CMatrix n} (hA : A.PosSemidef) (U : Matrix.unitaryGroup n ℂ) :
    ((U : CMatrix n) * A * star (U : CMatrix n)).PosSemidef := by
  simpa using posSemidef_unitary_conj hA U⁻¹

theorem cMatrix_rpow_unitary_conj_forward
    {n : Type x} [Fintype n] [DecidableEq n]
    {A : CMatrix n} (hA : A.PosSemidef) (U : Matrix.unitaryGroup n ℂ)
    {s : Real} (hs : 0 <= s) :
    CFC.rpow ((U : CMatrix n) * A * star (U : CMatrix n)) s =
      (U : CMatrix n) * CFC.rpow A s * star (U : CMatrix n) := by
  simpa using cMatrix_rpow_unitary_conj hA U⁻¹ hs

theorem psdSchattenPNorm_unitary_conj_forward
    {n : Type x} [Fintype n] [DecidableEq n]
    {A : CMatrix n} (hA : A.PosSemidef) (U : Matrix.unitaryGroup n ℂ)
    (p : SchattenOrder) :
    psdSchattenPNorm ((U : CMatrix n) * A * star (U : CMatrix n))
        (posSemidef_unitary_conj_forward hA U) p =
      psdSchattenPNorm A hA p := by
  rw [psdSchattenPNorm, psdSchattenPNorm, Internal.psdSchattenExpression,
    Internal.psdSchattenExpression]
  rw [show
      psdTracePower ((U : CMatrix n) * A * star (U : CMatrix n))
          (posSemidef_unitary_conj_forward hA U) p =
        psdTracePower A hA p by
        simpa using psdTracePower_unitary_conj U⁻¹ hA p.property.le]

def cpValueOnPSD
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) (X : CMatrix a) : Real := by
  classical
  exact if hX : X.PosSemidef then cpPsdSchattenRpowValue Phi hPhi alpha X hX else 0

theorem cpValueOnPSD_of_pos
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) {X : CMatrix a} (hX : X.PosSemidef) :
    cpValueOnPSD Phi hPhi alpha X =
      cpPsdSchattenRpowValue Phi hPhi alpha X hX := by
  classical
  simp [cpValueOnPSD, hX]

omit [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
private theorem posSemidefSet_convex :
    {n : Type x} → Convex Real ({X : CMatrix n | X.PosSemidef}) := by
  intro n X hX Y hY s t hs ht _hst
  exact Matrix.PosSemidef.add
    (Matrix.PosSemidef.smul hX hs)
    (Matrix.PosSemidef.smul hY ht)

private theorem cpValueOnPSD_concaveOn
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real)) :
    ConcaveOn Real ({X : CMatrix a | X.PosSemidef})
      (cpValueOnPSD Phi hPhi alpha) := by
  refine ⟨posSemidefSet_convex (n := a), ?_⟩
  intro X hX Y hY s t hs ht hst
  have ht_eq : t = 1 - s := by linarith
  subst t
  have hs_le_one : s <= 1 := by linarith
  have hmix : (s • X + (1 - s) • Y : CMatrix a).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hX hs)
      (Matrix.PosSemidef.smul hY ht)
  rw [cpValueOnPSD_of_pos Phi hPhi alpha hX,
    cpValueOnPSD_of_pos Phi hPhi alpha hY,
    cpValueOnPSD_of_pos Phi hPhi alpha hmix]
  exact cp_psdSchatten_rpow_value_concave Phi hPhi halpha hs hs_le_one hX hY

theorem cpValueOnPSD_uniform_average_le
    {ι : Type x} [Fintype ι] [Nonempty ι]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (X : ι → CMatrix a) (hX : ∀ i, (X i).PosSemidef) :
    (∑ i : ι, (Fintype.card ι : Real)⁻¹ *
        cpValueOnPSD Phi hPhi alpha (X i)) <=
      cpValueOnPSD Phi hPhi alpha
        (∑ i : ι, (Fintype.card ι : Real)⁻¹ • X i) := by
  classical
  let w : ι → Real := fun _ => (Fintype.card ι : Real)⁻¹
  have hcard_pos : 0 < (Fintype.card ι : Real) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 <= w i := by
    intro i hi
    exact inv_nonneg.mpr (le_of_lt hcard_pos)
  have hw_sum : ∑ i ∈ (Finset.univ : Finset ι), w i = 1 := by
    simp [w]
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), X i ∈ ({X : CMatrix a | X.PosSemidef}) := by
    intro i hi
    exact hX i
  have hjensen :=
    (cpValueOnPSD_concaveOn Phi hPhi halpha).le_map_sum
      (t := (Finset.univ : Finset ι)) (w := w) (p := X)
      hw_nonneg hw_sum hmem
  simpa [w, smul_eq_mul] using hjensen

private def collapseLocalReferenceUnitary (U : Matrix.unitaryGroup r ℂ) :
    Matrix.unitaryGroup (Prod r a) ℂ :=
  ⟨Matrix.kronecker (U : CMatrix r) (1 : CMatrix a), by
    let I : Matrix.unitaryGroup a ℂ := ⟨1, by simp⟩
    simpa using Matrix.kronecker_mem_unitary U.2 I.2⟩

@[simp] private theorem collapseLocalReferenceUnitary_coe
    (U : Matrix.unitaryGroup r ℂ) :
    (collapseLocalReferenceUnitary (a := a) U : CMatrix (Prod r a)) =
      Matrix.kronecker (U : CMatrix r) (1 : CMatrix a) := rfl

private theorem collapseDiagonalSignReferenceUnitary_conj_apply
    (ε : r → Bool) (X : CMatrix (Prod r a)) (i i' : r) (j j' : a) :
    (((collapseLocalReferenceUnitary (a := a) (diagonalSignUnitary ε) :
          CMatrix (Prod r a)) *
        X * star (collapseLocalReferenceUnitary (a := a) (diagonalSignUnitary ε) :
          CMatrix (Prod r a))) (i, j) (i', j')) =
      boolSignComplex (ε i) * X (i, j) (i', j') * boolSignComplex (ε i') := by
  simp only [collapseLocalReferenceUnitary_coe, diagonalSignUnitary_coe,
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

private theorem collapsePermutationReferenceUnitary_conj_apply
    (π : Equiv.Perm r) (X : CMatrix (Prod r a)) (i i' : r) (j j' : a) :
    (((collapseLocalReferenceUnitary (a := a) (permutationUnitary π) :
          CMatrix (Prod r a)) *
        X * star (collapseLocalReferenceUnitary (a := a) (permutationUnitary π) :
          CMatrix (Prod r a))) (i, j) (i', j')) =
      X (π i, j) (π i', j') := by
  simp only [collapseLocalReferenceUnitary_coe, permutationUnitary_coe,
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

private theorem collapseLocalReferenceUnitary_mul
    (U V : Matrix.unitaryGroup r ℂ) :
    (collapseLocalReferenceUnitary (a := a) (U * V) : CMatrix (Prod r a)) =
      (collapseLocalReferenceUnitary (a := a) U : CMatrix (Prod r a)) *
        (collapseLocalReferenceUnitary (a := a) V : CMatrix (Prod r a)) := by
  rw [collapseLocalReferenceUnitary_coe, collapseLocalReferenceUnitary_coe,
    collapseLocalReferenceUnitary_coe]
  simpa using
    (Matrix.mul_kronecker_mul (U : CMatrix r) (V : CMatrix r)
      (1 : CMatrix a) (1 : CMatrix a))

private theorem collapseLocalReferenceSignPermutationUnitary_conj_apply
    (ε : r → Bool) (π : Equiv.Perm r) (X : CMatrix (Prod r a))
    (i i' : r) (j j' : a) :
    (((collapseLocalReferenceUnitary (a := a)
          (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a)) *
        X *
        star (collapseLocalReferenceUnitary (a := a)
          (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a))) (i, j) (i', j')) =
      boolSignComplex (ε (π i)) * X (π i, j) (π i', j') *
        boolSignComplex (ε (π i')) := by
  classical
  let P : CMatrix (Prod r a) :=
    collapseLocalReferenceUnitary (a := a) (permutationUnitary π)
  let D : CMatrix (Prod r a) :=
    collapseLocalReferenceUnitary (a := a) (diagonalSignUnitary ε)
  have hmul :
      (collapseLocalReferenceUnitary (a := a)
          (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a)) = P * D := by
    simpa [P, D] using
      collapseLocalReferenceUnitary_mul (a := a) (U := permutationUnitary π)
        (V := diagonalSignUnitary ε)
  calc
    (((collapseLocalReferenceUnitary (a := a)
          (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a)) *
        X *
        star (collapseLocalReferenceUnitary (a := a)
          (permutationUnitary π * diagonalSignUnitary ε) :
          CMatrix (Prod r a))) (i, j) (i', j')) =
        (P * (D * X * star D) * star P) (i, j) (i', j') := by
          rw [hmul, star_mul]
          simp [P, D, mul_assoc]
    _ = (D * X * star D) (π i, j) (π i', j') := by
          simpa [P] using
            collapsePermutationReferenceUnitary_conj_apply (a := a) π
              (D * X * star D) i i' j j'
    _ = boolSignComplex (ε (π i)) * X (π i, j) (π i', j') *
          boolSignComplex (ε (π i')) := by
          simpa [D] using
            collapseDiagonalSignReferenceUnitary_conj_apply (a := a) ε X
              (π i) (π i') j j'

private def collapseReferenceDepolarizingTwirl [Nonempty r]
    (X : CMatrix (Prod r a)) : CMatrix (Prod r a) :=
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

private theorem collapseReferenceTwirl_eq_maximallyMixed_tensor_partialTrace
    [Nonempty r] (X : CMatrix (Prod r a)) :
    collapseReferenceDepolarizingTwirl (r := r) (a := a) X =
      Matrix.kronecker (maximallyMixed r).matrix
        (partialTraceA (a := r) (b := a) X) := by
  classical
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  unfold collapseReferenceDepolarizingTwirl
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp_rw [← collapseLocalReferenceUnitary_coe (a := a)]
  simp_rw [collapseLocalReferenceSignPermutationUnitary_conj_apply]
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
        simp [QIT.partialTraceA, maximallyMixed_matrix, Matrix.kronecker,
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
    simp [QIT.partialTraceA, maximallyMixed_matrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, hii']

private theorem id_kron_signPermutation_conj
    (Phi : MatrixMap a b)
    (ε : r → Bool) (π : Equiv.Perm r) (X : CMatrix (Prod r a)) :
    MatrixMap.kron (Channel.idChannel r).map Phi
        ((collapseLocalReferenceUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (Prod r a)) *
          X *
          star (collapseLocalReferenceUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (Prod r a))) =
      (collapseLocalReferenceUnitary (a := b)
          (permutationUnitary π * diagonalSignUnitary ε) :
            CMatrix (Prod r b)) *
        (MatrixMap.kron (Channel.idChannel r).map Phi X) *
          star (collapseLocalReferenceUnitary (a := b)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (Prod r b)) := by
  ext rb rb'
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (fun j j' =>
        (((collapseLocalReferenceUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (Prod r a)) *
          X *
          star (collapseLocalReferenceUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (Prod r a))) (rb.1, j) (rb'.1, j'))) =
        (boolSignComplex (ε (π rb.1)) * boolSignComplex (ε (π rb'.1))) •
          (fun j j' => X (π rb.1, j) (π rb'.1, j')) := by
    ext j j'
    rw [collapseLocalReferenceSignPermutationUnitary_conj_apply]
    simp [mul_assoc, mul_comm]
  rw [hslice]
  let c : ℂ := boolSignComplex (ε (π rb.1)) * boolSignComplex (ε (π rb'.1))
  let S : CMatrix a := fun j j' => X (π rb.1, j) (π rb'.1, j')
  have hmap := congrFun (congrFun
    (LinearMap.map_smul Phi
      c S) rb.2) rb'.2
  change Phi (c • S) rb.2 rb'.2 =
    ((collapseLocalReferenceUnitary (a := b)
        (permutationUnitary π * diagonalSignUnitary ε) : CMatrix (Prod r b)) *
      MatrixMap.kron (Channel.idChannel r).map Phi X *
      star (collapseLocalReferenceUnitary (a := b)
        (permutationUnitary π * diagonalSignUnitary ε) : CMatrix (Prod r b))) rb rb'
  calc
    Phi (c • S) rb.2 rb'.2 = (c • Phi S) rb.2 rb'.2 := hmap
    _ =
        ((collapseLocalReferenceUnitary (a := b)
            (permutationUnitary π * diagonalSignUnitary ε) : CMatrix (Prod r b)) *
          MatrixMap.kron (Channel.idChannel r).map Phi X *
          star (collapseLocalReferenceUnitary (a := b)
            (permutationUnitary π * diagonalSignUnitary ε) : CMatrix (Prod r b))) rb rb' := by
          rw [collapseLocalReferenceSignPermutationUnitary_conj_apply]
          rw [MatrixMap.kron_idChannel_left_apply_slice]
          simp [c, S, Matrix.smul_apply, mul_assoc, mul_left_comm, mul_comm]

private theorem id_kron_signPermutation_cpValue_eq
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (ε : r → Bool) (π : Equiv.Perm r)
    (Y : CMatrix (Prod r a)) (hY : Y.PosSemidef) :
    cpValueOnPSD
        (MatrixMap.kron (Channel.idChannel r).map Phi)
        (MatrixMap.isCompletelyPositive_kron
          (Channel.idChannel r).map Phi
          (Channel.idChannel r).completelyPositive hPhi)
        alpha
        ((collapseLocalReferenceUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (Prod r a)) *
          Y *
          star (collapseLocalReferenceUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (Prod r a))) =
      cpValueOnPSD
        (MatrixMap.kron (Channel.idChannel r).map Phi)
        (MatrixMap.isCompletelyPositive_kron
          (Channel.idChannel r).map Phi
          (Channel.idChannel r).completelyPositive hPhi)
        alpha Y := by
  let K : MatrixMap (Prod r a) (Prod r b) :=
    MatrixMap.kron (Channel.idChannel r).map Phi
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.isCompletelyPositive_kron
      (Channel.idChannel r).map Phi
      (Channel.idChannel r).completelyPositive hPhi
  let Uin : Matrix.unitaryGroup (Prod r a) ℂ :=
    collapseLocalReferenceUnitary (a := a) (permutationUnitary π * diagonalSignUnitary ε)
  let Uout : Matrix.unitaryGroup (Prod r b) ℂ :=
    collapseLocalReferenceUnitary (a := b) (permutationUnitary π * diagonalSignUnitary ε)
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have hinv_nonneg : 0 <= 1 / (alpha : Real) :=
    one_div_nonneg.mpr (le_of_lt halpha_pos)
  have hconj_pos : ((Uin : CMatrix (Prod r a)) * Y * star (Uin : CMatrix (Prod r a))).PosSemidef :=
    posSemidef_unitary_conj_forward hY Uin
  rw [cpValueOnPSD_of_pos K hK alpha hconj_pos,
    cpValueOnPSD_of_pos K hK alpha hY]
  unfold cpPsdSchattenRpowValue
  have hrpow :
      CFC.rpow ((Uin : CMatrix (Prod r a)) * Y * star (Uin : CMatrix (Prod r a)))
          (1 / (alpha : Real)) =
        (Uin : CMatrix (Prod r a)) * CFC.rpow Y (1 / (alpha : Real)) *
          star (Uin : CMatrix (Prod r a)) :=
    cMatrix_rpow_unitary_conj_forward hY Uin hinv_nonneg
  have hmap :
      K (CFC.rpow ((Uin : CMatrix (Prod r a)) * Y * star (Uin : CMatrix (Prod r a)))
          (1 / (alpha : Real))) =
        (Uout : CMatrix (Prod r b)) * K (CFC.rpow Y (1 / (alpha : Real))) *
          star (Uout : CMatrix (Prod r b)) := by
    rw [hrpow]
    simpa [K, Uin, Uout] using
      id_kron_signPermutation_conj (r := r) (a := a) (b := b)
        Phi ε π (CFC.rpow Y (1 / (alpha : Real)))
  have hKY : (K (CFC.rpow Y (1 / (alpha : Real)))).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive K hK
      (CFC.rpow Y (1 / (alpha : Real)))
      (cMatrix_rpow_posSemidef (A := Y) (s := 1 / (alpha : Real)) hY)
  have hKYconj :
      ((Uout : CMatrix (Prod r b)) * K (CFC.rpow Y (1 / (alpha : Real))) *
        star (Uout : CMatrix (Prod r b))).PosSemidef :=
    posSemidef_unitary_conj_forward hKY Uout
  calc
    psdSchattenPNorm
        (K (CFC.rpow ((Uin : CMatrix (Prod r a)) * Y * star (Uin : CMatrix (Prod r a)))
          (1 / (alpha : Real)))) _ alpha =
      psdSchattenPNorm
        ((Uout : CMatrix (Prod r b)) * K (CFC.rpow Y (1 / (alpha : Real))) *
          star (Uout : CMatrix (Prod r b)))
        hKYconj alpha := by
          exact psdSchattenPNorm_congr hmap _ hKYconj alpha
    _ = psdSchattenPNorm (K (CFC.rpow Y (1 / (alpha : Real)))) hKY alpha :=
          psdSchattenPNorm_unitary_conj_forward hKY Uout alpha

private def AlphaToAlphaTraceDomain.partialTraceReference
    {alpha : SchattenOrder}
    (Y : AlphaToAlphaTraceDomain (Prod r a) alpha) :
    AlphaToAlphaTraceDomain a alpha where
  matrix := partialTraceA (a := r) (b := a) Y.matrix
  pos := partialTraceA_posSemidef (a := r) (b := a) Y.pos
  trace_le_one := by
    have htrace := congrArg Complex.re
      (partialTraceA_trace (a := r) (b := a) Y.matrix)
    simpa [htrace] using Y.trace_le_one

theorem maximallyMixed_rpow_schatten_norm_eq_one
    [Nonempty r] {alpha : SchattenOrder} (halpha : 1 < (alpha : Real)) :
    psdSchattenPNorm
        (CFC.rpow (maximallyMixed r).matrix (1 / (alpha : Real)))
        (cMatrix_rpow_posSemidef
          (A := (maximallyMixed r).matrix) (s := 1 / (alpha : Real))
          (maximallyMixed r).pos)
        alpha = 1 := by
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have halpha_nonneg : 0 <= (alpha : Real) := le_of_lt halpha_pos
  have hinv_nonneg : 0 <= 1 / (alpha : Real) := one_div_nonneg.mpr halpha_nonneg
  have hpower :
      psdTracePower
          (CFC.rpow (maximallyMixed r).matrix (1 / (alpha : Real)))
          (cMatrix_rpow_posSemidef
            (A := (maximallyMixed r).matrix) (s := 1 / (alpha : Real))
            (maximallyMixed r).pos)
          alpha = 1 := by
    rw [psdTracePower_eq]
    have hpow :
        CFC.rpow (CFC.rpow (maximallyMixed r).matrix (1 / (alpha : Real)))
            (alpha : Real) =
          CFC.rpow (maximallyMixed r).matrix 1 := by
      exact cMatrix_rpow_rpow_of_nonneg (maximallyMixed r).pos
        hinv_nonneg halpha_nonneg (by field_simp [ne_of_gt halpha_pos])
    rw [hpow]
    have hone :
        CFC.rpow (maximallyMixed r).matrix 1 = (maximallyMixed r).matrix :=
      CFC.rpow_one (maximallyMixed r).matrix
        (ha := Matrix.nonneg_iff_posSemidef.mpr (maximallyMixed r).pos)
    rw [hone]
    exact congrArg Complex.re (maximallyMixed r).trace_eq_one
  rw [psdSchattenPNorm, Internal.psdSchattenExpression, hpower]
  exact Real.one_rpow _

private theorem id_kron_traceValue_maximallyMixed_tensor
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (Y : AlphaToAlphaTraceDomain a alpha) :
    cpValueOnPSD
        (MatrixMap.kron (Channel.idChannel r).map Phi)
        (MatrixMap.isCompletelyPositive_kron
          (Channel.idChannel r).map Phi
          (Channel.idChannel r).completelyPositive hPhi)
        alpha
        (Matrix.kronecker (maximallyMixed r).matrix Y.matrix) =
      alphaToAlphaTraceValue Phi hPhi Y := by
  let K : MatrixMap (Prod r a) (Prod r b) :=
    MatrixMap.kron (Channel.idChannel r).map Phi
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.isCompletelyPositive_kron
      (Channel.idChannel r).map Phi
      (Channel.idChannel r).completelyPositive hPhi
  have hprod : (Matrix.kronecker (maximallyMixed r).matrix Y.matrix).PosSemidef :=
    (maximallyMixed r).pos.kronecker Y.pos
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have hinv_nonneg : 0 <= 1 / (alpha : Real) :=
    one_div_nonneg.mpr (le_of_lt halpha_pos)
  rw [cpValueOnPSD_of_pos K hK alpha hprod]
  unfold cpPsdSchattenRpowValue alphaToAlphaTraceValue
  have hpow :
      CFC.rpow (Matrix.kronecker (maximallyMixed r).matrix Y.matrix)
          (1 / (alpha : Real)) =
        Matrix.kronecker
          (CFC.rpow (maximallyMixed r).matrix (1 / (alpha : Real)))
          (CFC.rpow Y.matrix (1 / (alpha : Real))) :=
    cMatrix_rpow_kronecker_nonneg (maximallyMixed r).pos Y.pos hinv_nonneg
  let Rpow : CMatrix r :=
    CFC.rpow (maximallyMixed r).matrix (1 / (alpha : Real))
  let Ypow : CMatrix a := CFC.rpow Y.matrix (1 / (alpha : Real))
  have hRpow : Rpow.PosSemidef :=
    cMatrix_rpow_posSemidef
      (A := (maximallyMixed r).matrix) (s := 1 / (alpha : Real))
      (maximallyMixed r).pos
  have hYpow : Ypow.PosSemidef :=
    cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos
  have hPhiYpow : (Phi Ypow).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Ypow hYpow
  have hmap :
      K (CFC.rpow (Matrix.kronecker (maximallyMixed r).matrix Y.matrix)
          (1 / (alpha : Real))) =
        Matrix.kronecker Rpow (Phi Ypow) := by
    rw [hpow]
    change MatrixMap.kron (Channel.idChannel r).map Phi
        (Matrix.kronecker Rpow Ypow) =
      Matrix.kronecker Rpow (Phi Ypow)
    rw [MatrixMap.kron_apply_kronecker, Channel.idChannel_map]
  have hKpow : (K (CFC.rpow (Matrix.kronecker (maximallyMixed r).matrix Y.matrix)
          (1 / (alpha : Real)))).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive K hK
      (CFC.rpow (Matrix.kronecker (maximallyMixed r).matrix Y.matrix)
          (1 / (alpha : Real)))
      (cMatrix_rpow_posSemidef
        (A := Matrix.kronecker (maximallyMixed r).matrix Y.matrix)
        (s := 1 / (alpha : Real)) hprod)
  calc
    psdSchattenPNorm
        (K (CFC.rpow (Matrix.kronecker (maximallyMixed r).matrix Y.matrix)
          (1 / (alpha : Real)))) _ alpha =
      psdSchattenPNorm (Matrix.kronecker Rpow (Phi Ypow))
        (hRpow.kronecker hPhiYpow) alpha := by
          exact psdSchattenPNorm_congr hmap hKpow
            (hRpow.kronecker hPhiYpow) alpha
    _ =
      psdSchattenPNorm Rpow hRpow alpha *
        psdSchattenPNorm (Phi Ypow) hPhiYpow alpha := by
          rw [psdSchattenPNorm_kronecker hRpow hPhiYpow alpha]
    _ = psdSchattenPNorm (Phi Ypow) hPhiYpow alpha := by
          rw [maximallyMixed_rpow_schatten_norm_eq_one (r := r) halpha]
          simp

private theorem id_kron_traceValue_le_partialTrace_traceValue
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (Y : AlphaToAlphaTraceDomain (Prod r a) alpha) :
    alphaToAlphaTraceValue
        (MatrixMap.kron (Channel.idChannel r).map Phi)
        (MatrixMap.isCompletelyPositive_kron
          (Channel.idChannel r).map Phi
          (Channel.idChannel r).completelyPositive hPhi)
        Y <=
      alphaToAlphaTraceValue Phi hPhi (Y.partialTraceReference (r := r)) := by
  classical
  let K : MatrixMap (Prod r a) (Prod r b) :=
    MatrixMap.kron (Channel.idChannel r).map Phi
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.isCompletelyPositive_kron
      (Channel.idChannel r).map Phi
      (Channel.idChannel r).completelyPositive hPhi
  let ι := (r → Bool) × Equiv.Perm r
  let U : ι → Matrix.unitaryGroup r ℂ :=
    fun idx => permutationUnitary idx.2 * diagonalSignUnitary idx.1
  let X : ι → CMatrix (Prod r a) := fun idx =>
    (Matrix.kronecker ((U idx : Matrix.unitaryGroup r ℂ) : CMatrix r)
        (1 : CMatrix a)) *
      Y.matrix *
      star (Matrix.kronecker ((U idx : Matrix.unitaryGroup r ℂ) : CMatrix r)
        (1 : CMatrix a))
  have hX : ∀ idx : ι, (X idx).PosSemidef := by
    intro idx
    simpa [X, U, collapseLocalReferenceUnitary_coe] using
      posSemidef_unitary_conj_forward Y.pos
        (collapseLocalReferenceUnitary (a := a) (U idx))
  have hvalue_eq : ∀ idx : ι,
      cpValueOnPSD K hK alpha (X idx) =
        alphaToAlphaTraceValue K hK Y := by
    intro idx
    rcases idx with ⟨ε, π⟩
    rw [show X (ε, π) =
        (collapseLocalReferenceUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (Prod r a)) *
          Y.matrix *
          star (collapseLocalReferenceUnitary (a := a)
            (permutationUnitary π * diagonalSignUnitary ε) :
              CMatrix (Prod r a)) by
        simp [X, U, collapseLocalReferenceUnitary_coe]]
    rw [id_kron_signPermutation_cpValue_eq
      (r := r) (a := a) (b := b) Phi hPhi halpha ε π Y.matrix Y.pos]
    rw [cpValueOnPSD_of_pos K hK alpha Y.pos]
    rfl
  have hcard_pos : 0 < (Fintype.card ι : Real) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hsum_weights : ∑ _idx : ι, (Fintype.card ι : Real)⁻¹ = 1 := by
    simp
  have hstart :
      alphaToAlphaTraceValue K hK Y =
        ∑ idx : ι, (Fintype.card ι : Real)⁻¹ *
          cpValueOnPSD K hK alpha (X idx) := by
    calc
      alphaToAlphaTraceValue K hK Y =
          (∑ _idx : ι, (Fintype.card ι : Real)⁻¹) *
            alphaToAlphaTraceValue K hK Y := by rw [hsum_weights, one_mul]
      _ = ∑ idx : ι, (Fintype.card ι : Real)⁻¹ *
            alphaToAlphaTraceValue K hK Y := by
            rw [Finset.sum_mul]
      _ = ∑ idx : ι, (Fintype.card ι : Real)⁻¹ *
            cpValueOnPSD K hK alpha (X idx) := by
            refine Finset.sum_congr rfl fun idx _ => ?_
            rw [hvalue_eq idx]
  have hjensen :
      (∑ idx : ι, (Fintype.card ι : Real)⁻¹ *
          cpValueOnPSD K hK alpha (X idx)) <=
        cpValueOnPSD K hK alpha
          (∑ idx : ι, (Fintype.card ι : Real)⁻¹ • X idx) :=
    cpValueOnPSD_uniform_average_le K hK halpha X hX
  have hcoef :
      ((((Fintype.card ι : Real)⁻¹ : Real) : ℂ)) =
        (Fintype.card ι : ℂ)⁻¹ := by
    norm_num [show (Fintype.card ι : Real) ≠ 0 from ne_of_gt hcard_pos]
  have htwirl_sum :
      (∑ idx : ι, (Fintype.card ι : Real)⁻¹ • X idx) =
        collapseReferenceDepolarizingTwirl (r := r) (a := a) Y.matrix := by
    change (∑ idx : ι,
        ((((Fintype.card ι : Real)⁻¹ : Real) : ℂ) • X idx)) =
      collapseReferenceDepolarizingTwirl (r := r) (a := a) Y.matrix
    rw [hcoef]
    dsimp [collapseReferenceDepolarizingTwirl, X, U, ι]
  have htwirl :
      collapseReferenceDepolarizingTwirl (r := r) (a := a) Y.matrix =
        Matrix.kronecker (maximallyMixed r).matrix
          (partialTraceA (a := r) (b := a) Y.matrix) :=
    collapseReferenceTwirl_eq_maximallyMixed_tensor_partialTrace (r := r) (a := a)
      Y.matrix
  have hproduct :
      cpValueOnPSD K hK alpha
        (Matrix.kronecker (maximallyMixed r).matrix
          (partialTraceA (a := r) (b := a) Y.matrix)) =
      alphaToAlphaTraceValue Phi hPhi (Y.partialTraceReference (r := r)) :=
    id_kron_traceValue_maximallyMixed_tensor
      (r := r) (a := a) (b := b) Phi hPhi halpha
      (Y.partialTraceReference (r := r))
  calc
    alphaToAlphaTraceValue K hK Y =
        ∑ idx : ι, (Fintype.card ι : Real)⁻¹ *
          cpValueOnPSD K hK alpha (X idx) := hstart
    _ <= cpValueOnPSD K hK alpha
          (∑ idx : ι, (Fintype.card ι : Real)⁻¹ • X idx) := hjensen
    _ = cpValueOnPSD K hK alpha
          (collapseReferenceDepolarizingTwirl (r := r) (a := a) Y.matrix) := by
          rw [htwirl_sum]
    _ = cpValueOnPSD K hK alpha
          (Matrix.kronecker (maximallyMixed r).matrix
            (partialTraceA (a := r) (b := a) Y.matrix)) := by
          rw [htwirl]
    _ = alphaToAlphaTraceValue Phi hPhi (Y.partialTraceReference (r := r)) := hproduct

theorem alphaToAlphaTraceValue_eq_zero_or_le_positiveValue
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real))
    (Y : AlphaToAlphaTraceDomain a alpha) :
    alphaToAlphaTraceValue Phi hPhi Y = 0 ∨
      ∃ p ∈ alphaToAlphaPositiveValueSet Phi hPhi alpha,
        alphaToAlphaTraceValue Phi hPhi Y <= p := by
  let Z : CMatrix a := CFC.rpow Y.matrix (1 / (alpha : Real))
  let hZ : Z.PosSemidef :=
    cMatrix_rpow_posSemidef (A := Y.matrix) (s := 1 / (alpha : Real)) Y.pos
  let normZ : Real := psdSchattenPNorm Z hZ alpha
  have hnormZ_nonneg : 0 <= normZ := psdSchattenPNorm_nonneg Z hZ alpha
  by_cases hnormZ_zero : normZ = 0
  · left
    have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
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
            exact psdSchattenPNorm_congr hPhiZzero hPhiZpos
              Matrix.PosSemidef.zero alpha
      _ = 0 := psdSchattenPNorm_zero alpha
  · right
    have hnormZ_pos : 0 < normZ :=
      lt_of_le_of_ne hnormZ_nonneg (Ne.symm hnormZ_zero)
    let X : AlphaToAlphaPositiveDomain a alpha :=
      { matrix := Z, pos := hZ, norm_pos := hnormZ_pos }
    refine ⟨alphaToAlphaPositiveValue Phi hPhi X, ⟨X, rfl⟩, ?_⟩
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
      alphaToAlphaTraceValue Phi hPhi Y =
          normZ * alphaToAlphaPositiveValue Phi hPhi X := htrace_eq_mul
      _ <= alphaToAlphaPositiveValue Phi hPhi X :=
          mul_le_of_le_one_left hratio_nonneg hnorm_le_one

private theorem alphaToAlphaPositiveValueSet_subset_id_kron
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real)) :
    alphaToAlphaPositiveValueSet Phi hPhi alpha ⊆
      alphaToAlphaPositiveValueSet
        (MatrixMap.kron (Channel.idChannel r).map Phi)
        (MatrixMap.isCompletelyPositive_kron
          (Channel.idChannel r).map Phi
          (Channel.idChannel r).completelyPositive hPhi)
        alpha := by
  rintro x ⟨Z, rfl⟩
  let K : MatrixMap (Prod r a) (Prod r b) :=
    MatrixMap.kron (Channel.idChannel r).map Phi
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.isCompletelyPositive_kron
      (Channel.idChannel r).map Phi
      (Channel.idChannel r).completelyPositive hPhi
  let R : CMatrix r := (maximallyMixed r).matrix
  let hR : R.PosSemidef := (maximallyMixed r).pos
  have halpha_pos : 0 < (alpha : Real) := lt_trans zero_lt_one halpha
  have hRnorm_pos : 0 < psdSchattenPNorm R hR alpha := by
    simpa [R, hR] using maximallyMixed_schatten_norm_pos (r := r) alpha
  let X : AlphaToAlphaPositiveDomain (Prod r a) alpha :=
    { matrix := Matrix.kronecker R Z.matrix,
      pos := hR.kronecker Z.pos,
      norm_pos := by
        rw [psdSchattenPNorm_kronecker hR Z.pos alpha]
        exact mul_pos hRnorm_pos Z.norm_pos }
  refine ⟨X, ?_⟩
  have hPhiZ : (Phi Z.matrix).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Z.matrix Z.pos
  have hKprod :
      K (Matrix.kronecker R Z.matrix) = Matrix.kronecker R (Phi Z.matrix) := by
    dsimp [K]
    change MatrixMap.kron (Channel.idChannel r).map Phi
        (Matrix.kronecker R Z.matrix) =
      Matrix.kronecker R (Phi Z.matrix)
    rw [MatrixMap.kron_apply_kronecker, Channel.idChannel_map]
  have hKpos : (K (Matrix.kronecker R Z.matrix)).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive K hK
      (Matrix.kronecker R Z.matrix) (hR.kronecker Z.pos)
  have hnum :
      psdSchattenPNorm (K (Matrix.kronecker R Z.matrix)) hKpos alpha =
        psdSchattenPNorm (Matrix.kronecker R (Phi Z.matrix))
          (hR.kronecker hPhiZ) alpha :=
    psdSchattenPNorm_congr hKprod hKpos (hR.kronecker hPhiZ) alpha
  unfold alphaToAlphaPositiveValue
  change
    psdSchattenPNorm (K (Matrix.kronecker R Z.matrix)) _ alpha /
      psdSchattenPNorm (Matrix.kronecker R Z.matrix) _ alpha =
    psdSchattenPNorm (Phi Z.matrix)
        (MatrixMap.isCompletelyPositive_mapsPositive Phi hPhi Z.matrix Z.pos)
        alpha /
      psdSchattenPNorm Z.matrix Z.pos alpha
  rw [hnum]
  rw [psdSchattenPNorm_kronecker hR hPhiZ alpha,
    psdSchattenPNorm_kronecker hR Z.pos alpha]
  field_simp [ne_of_gt hRnorm_pos]

private theorem id_kron_positiveValue_eq_zero_or_le_positiveValue
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real)) :
    ∀ x ∈
      alphaToAlphaPositiveValueSet
        (MatrixMap.kron (Channel.idChannel r).map Phi)
        (MatrixMap.isCompletelyPositive_kron
          (Channel.idChannel r).map Phi
          (Channel.idChannel r).completelyPositive hPhi)
        alpha,
      x = 0 ∨ ∃ p ∈ alphaToAlphaPositiveValueSet Phi hPhi alpha, x <= p := by
  intro x hx
  rcases hx with ⟨Z, rfl⟩
  let K : MatrixMap (Prod r a) (Prod r b) :=
    MatrixMap.kron (Channel.idChannel r).map Phi
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.isCompletelyPositive_kron
      (Channel.idChannel r).map Phi
      (Channel.idChannel r).completelyPositive hPhi
  let Y : AlphaToAlphaTraceDomain (Prod r a) alpha := Z.toTraceDomain halpha
  have htrace_eq :
      alphaToAlphaTraceValue K hK Y = alphaToAlphaPositiveValue K hK Z :=
    alphaToAlphaTraceValue_toTraceDomain_eq_positiveValue K hK halpha Z
  have hle :
      alphaToAlphaPositiveValue K hK Z <=
        alphaToAlphaTraceValue Phi hPhi (Y.partialTraceReference (r := r)) := by
    rw [← htrace_eq]
    exact id_kron_traceValue_le_partialTrace_traceValue
      (r := r) (a := a) (b := b) Phi hPhi halpha Y
  rcases alphaToAlphaTraceValue_eq_zero_or_le_positiveValue Phi hPhi halpha
      (Y.partialTraceReference (r := r)) with hzero | ⟨p, hp, hyp⟩
  · left
    have hx_nonneg : 0 <= alphaToAlphaPositiveValue K hK Z :=
      alphaToAlphaPositiveValue_nonneg K hK Z
    exact le_antisymm (by simpa [hzero] using hle) hx_nonneg
  · right
    exact ⟨p, hp, hle.trans hyp⟩

private theorem alphaToAlphaNorm_id_kron_compare
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (halpha : 1 < (alpha : Real)) :
    alphaToAlphaNorm Phi hPhi alpha <=
        alphaToAlphaNorm
          (MatrixMap.kron (Channel.idChannel r).map Phi)
          (MatrixMap.isCompletelyPositive_kron
            (Channel.idChannel r).map Phi
            (Channel.idChannel r).completelyPositive hPhi)
          alpha ∧
      alphaToAlphaNorm
          (MatrixMap.kron (Channel.idChannel r).map Phi)
          (MatrixMap.isCompletelyPositive_kron
            (Channel.idChannel r).map Phi
            (Channel.idChannel r).completelyPositive hPhi)
          alpha <=
        alphaToAlphaNorm Phi hPhi alpha := by
  let K : MatrixMap (Prod r a) (Prod r b) :=
    MatrixMap.kron (Channel.idChannel r).map Phi
  let hK : MatrixMap.IsCompletelyPositive K :=
    MatrixMap.isCompletelyPositive_kron
      (Channel.idChannel r).map Phi
      (Channel.idChannel r).completelyPositive hPhi
  let P : Set Real := alphaToAlphaPositiveValueSet Phi hPhi alpha
  let T : Set Real := alphaToAlphaPositiveValueSet K hK alpha
  have hP_nonneg : ∀ x ∈ P, 0 <= x := by
    rintro x ⟨Y, rfl⟩
    exact alphaToAlphaPositiveValue_nonneg Phi hPhi Y
  have hT_nonneg : ∀ x ∈ T, 0 <= x := by
    rintro x ⟨Y, rfl⟩
    exact alphaToAlphaPositiveValue_nonneg K hK Y
  have hP_subset_T : P ⊆ T := by
    simpa [P, T, K, hK] using
      alphaToAlphaPositiveValueSet_subset_id_kron
        (r := r) (a := a) (b := b) Phi hPhi halpha
  have hT_le_zero_or_P : ∀ x ∈ T, x = 0 ∨ ∃ p ∈ P, x <= p := by
    simpa [P, T, K, hK] using
      id_kron_positiveValue_eq_zero_or_le_positiveValue
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
  change sSup P <= sSup T ∧ sSup T <= sSup P
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

/-- Product-input restriction gives the easy direction of the source collapse
lemma. -/
theorem alphaToAlphaNorm_le_id_kron
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : Real} (halpha : 1 < alpha) :
    alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) <=
      alphaToAlphaNorm
        (MatrixMap.kron (Channel.idChannel r).map Phi)
        (MatrixMap.isCompletelyPositive_kron
          (Channel.idChannel r).map Phi
          (Channel.idChannel r).completelyPositive hPhi)
        (SchattenOrder.ofOneLt halpha) :=
  (alphaToAlphaNorm_id_kron_compare (r := r) Phi hPhi halpha).1

/-- Reference twirling gives the nontrivial direction of the source collapse
lemma. -/
theorem id_kron_alphaToAlphaNorm_le
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : Real} (halpha : 1 < alpha) :
    alphaToAlphaNorm
        (MatrixMap.kron (Channel.idChannel r).map Phi)
        (MatrixMap.isCompletelyPositive_kron
          (Channel.idChannel r).map Phi
          (Channel.idChannel r).completelyPositive hPhi)
        (SchattenOrder.ofOneLt halpha) <=
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
  exact (alphaToAlphaNorm_id_kron_compare (r := r) Phi hPhi halpha).2

/-- Tensoring a completely positive map with an identity reference does not
change the positive `alpha -> alpha` norm. -/
theorem alphaToAlphaNorm_id_kron_eq
    [Nonempty r]
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : Real} (halpha : 1 < alpha) :
    alphaToAlphaNorm
        (MatrixMap.kron (Channel.idChannel r).map Phi)
        (MatrixMap.isCompletelyPositive_kron
          (Channel.idChannel r).map Phi
          (Channel.idChannel r).completelyPositive hPhi)
        (SchattenOrder.ofOneLt halpha) =
      alphaToAlphaNorm Phi hPhi (SchattenOrder.ofOneLt halpha) := by
  exact le_antisymm
    (id_kron_alphaToAlphaNorm_le (r := r) Phi hPhi halpha)
    (alphaToAlphaNorm_le_id_kron (r := r) Phi hPhi halpha)


end MatrixMap

end

end QIT
