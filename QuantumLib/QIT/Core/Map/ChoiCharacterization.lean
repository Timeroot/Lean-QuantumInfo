/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Core.Map

/-!
# Choi characterizations of matrix-map properties

Source-shaped characterizations of trace preservation, Hermiticity
preservation, and complete positivity of a finite-dimensional matrix map in
terms of its Choi matrix.

Convention: `choi Phi` is indexed by `input × output`, with
`choi Phi (i, j) (k, l) = Phi (Matrix.single i k 1) j l`. The source
[Chiribella2009Networks, comblong-pub.tex:181-199] indexes its
Choi-Jamiolkowski operator by `output × input` instead. With the input-first
convention used here, the trace-preserving characterization reads
`Matrix.traceRight (choi Phi) = 1` (the partial trace over the output factor is
the identity on the input factor), the Hermiticity-preserving
characterization reads `(choi Phi).IsHermitian`, and the complete-positivity
characterization equates Choi positivity with positivity of `Phi ⊗ id` on
every finite ancilla system.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace MatrixMap

/-- `ofChoiMatrix` is also a left inverse to the Choi construction: every
matrix map is the map induced by its own Choi matrix. -/
theorem ofChoiMatrix_choi (Phi : MatrixMap a b) : ofChoiMatrix (choi Phi) = Phi :=
  choi_inj (choi_ofChoiMatrix (choi Phi))

section TracePreserving

/-- The `(i, i')` entry of the output partial trace of the Choi matrix is the
trace of the image of the `(i, i')` matrix unit. -/
theorem traceRight_choi_apply (Phi : MatrixMap a b) (i i' : a) :
    Matrix.traceRight (choi Phi) i i' =
      (Phi (Matrix.single i i' (1 : ℂ))).trace := by
  simp [Matrix.traceRight, Matrix.trace, Matrix.diag, choi]

/-- Trace preservation is equivalent to the output partial trace of the Choi
matrix being the identity on the input system
[Chiribella2009Networks, comblong-pub.tex:204-209]. -/
theorem isTracePreserving_iff_traceRight_choi (Phi : MatrixMap a b) :
    MatrixMap.IsTracePreserving Phi ↔ Matrix.traceRight (choi Phi) = 1 := by
  constructor
  · intro hTP
    ext i i'
    rw [traceRight_choi_apply, hTP (Matrix.single i i' (1 : ℂ)),
      trace_single_one, Matrix.one_apply]
  · intro h X
    rw [trace_map_eq_sum_single Phi X]
    have hkey : ∀ i i' : a,
        (Phi (Matrix.single i i' (1 : ℂ))).trace =
          (1 : CMatrix a) i i' := by
      intro i i'
      rw [← traceRight_choi_apply, h]
    calc
      (∑ i : a, ∑ i' : a, X i i' *
          (Phi (Matrix.single i i' (1 : ℂ))).trace) =
        ∑ i : a, ∑ i' : a, X i i' * (1 : CMatrix a) i i' := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [hkey i i']
      _ = (X * 1).trace := by
        rw [Matrix.trace]
        refine Finset.sum_congr rfl fun i _ => ?_
        show (∑ i' : a, X i i' * (1 : CMatrix a) i i') = (X * (1 : CMatrix a)) i i
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun i' _ => ?_
        by_cases hii : i = i'
        · subst hii
          simp
        · have hne : i' ≠ i := fun h' => hii h'.symm
          simp [hii, hne]
      _ = X.trace := by rw [Matrix.mul_one]

end TracePreserving

section HermitianPreserving

/-- Hermiticity preservation is equivalent to commutation with the adjoint
(star) operation, via the Hermitian decomposition of an arbitrary matrix. -/
theorem isHermitianPreserving_iff_map_star (Phi : MatrixMap a b) :
    MatrixMap.IsHermitianPreserving Phi ↔
      (∀ X : CMatrix a, Phi (star X) = star (Phi X)) := by
  constructor
  · intro hHP X
    symm
    set A : CMatrix a := (2 : ℂ)⁻¹ • (X + star X) with hAdef
    set B : CMatrix a := ((2 : ℂ) * Complex.I)⁻¹ • (X - star X) with hBdef
    have hstarI : star (Complex.I : ℂ) = -Complex.I := by
      simp
    have hI2I : Complex.I * ((2 : ℂ) * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by
      rw [mul_inv]
      calc Complex.I * ((2 : ℂ)⁻¹ * Complex.I⁻¹)
          = (2 : ℂ)⁻¹ * (Complex.I * Complex.I⁻¹) := by ring
        _ = (2 : ℂ)⁻¹ := by
          rw [mul_inv_cancel₀ Complex.I_ne_zero, mul_one]
    have htwo : ∀ Y : CMatrix a, (2 : ℂ) • Y = Y + Y := by
      intro Y
      rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
    have hA : A.IsHermitian := by
      rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, hAdef]
      rw [star_smul, star_add, star_star, star_inv₀, star_ofNat, add_comm]
    have hB : B.IsHermitian := by
      rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, hBdef]
      rw [star_smul, star_sub, star_star, star_inv₀, star_mul, star_ofNat, hstarI,
        neg_mul, mul_comm Complex.I (2 : ℂ), ← neg_inv, neg_smul,
        ← smul_neg, neg_sub]
    have hXdecomp : X = A + Complex.I • B := by
      rw [hAdef, hBdef, smul_smul, hI2I, ← smul_add]
      have h2X : (X + star X) + (X - star X) = (2 : ℂ) • X := by
        rw [htwo X]
        abel
      rw [h2X, smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]
    have hstarXdecomp : star X = A - Complex.I • B := by
      rw [hAdef, hBdef, smul_smul, hI2I, ← smul_sub]
      have h2sX : (X + star X) - (X - star X) = (2 : ℂ) • star X := by
        rw [htwo (star X)]
        abel
      rw [h2sX, smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]
    calc star (Phi X) = star (Phi (A + Complex.I • B)) := by rw [hXdecomp]
      _ = star (Phi A + Complex.I • Phi B) := by
        rw [map_add Phi A (Complex.I • B), map_smul Phi Complex.I B]
      _ = star (Phi A) + star (Complex.I • Phi B) := by rw [star_add]
      _ = Phi A + star (Complex.I • Phi B) := by
        rw [Matrix.star_eq_conjTranspose (Phi A), (hHP hA).eq]
      _ = Phi A + star Complex.I • star (Phi B) := by rw [star_smul]
      _ = Phi A + (-Complex.I) • Phi B := by
        rw [hstarI, Matrix.star_eq_conjTranspose (Phi B), (hHP hB).eq]
      _ = Phi A - Complex.I • Phi B := by
        rw [sub_eq_add_neg (Phi A) (Complex.I • Phi B), neg_smul Complex.I (Phi B)]
      _ = Phi (A - Complex.I • B) := by
        rw [map_sub Phi A (Complex.I • B), map_smul Phi Complex.I B]
      _ = Phi (star X) := by rw [hstarXdecomp]
  · intro hstar X hX
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, ← hstar X,
      Matrix.star_eq_conjTranspose X, hX.eq]

/-- Commutation with the adjoint is equivalent to the Choi matrix being
Hermitian. -/
theorem map_star_iff_choi_isHermitian (Phi : MatrixMap a b) :
    (∀ X : CMatrix a, Phi (star X) = star (Phi X)) ↔
      (choi Phi).IsHermitian := by
  constructor
  · intro hstar
    rw [Matrix.IsHermitian]
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨k, l⟩
    have hsingle : Matrix.single k i (1 : ℂ) =
        star (Matrix.single i k (1 : ℂ)) := by
      rw [Matrix.star_eq_conjTranspose]
      ext p q
      by_cases hp : k = p <;> by_cases hq : i = q <;>
        simp [Matrix.conjTranspose_apply, Matrix.single, hp, hq]
    calc Matrix.conjTranspose (choi Phi) (i, j) (k, l)
        = star (choi Phi (k, l) (i, j)) := Matrix.conjTranspose_apply _ _ _
      _ = star ((Phi (Matrix.single k i (1 : ℂ))) l j) := rfl
      _ = star ((Phi (star (Matrix.single i k (1 : ℂ)))) l j) := by
        rw [hsingle]
      _ = star ((star (Phi (Matrix.single i k (1 : ℂ)))) l j) := by
        rw [hstar]
      _ = star (star ((Phi (Matrix.single i k (1 : ℂ))) j l)) := by
        rw [Matrix.star_apply]
      _ = (Phi (Matrix.single i k (1 : ℂ))) j l := star_star _
      _ = choi Phi (i, j) (k, l) := rfl
  · intro hJ X
    ext j l
    have hJentry : ∀ (p p' : a) (q q' : b),
        star ((Phi (Matrix.single p' p (1 : ℂ))) q' q) =
          (Phi (Matrix.single p p' (1 : ℂ))) q q' := by
      intro p p' q q'
      have h := congrFun (congrFun hJ.eq (p, q)) (p', q')
      rw [Matrix.conjTranspose_apply] at h
      exact h
    have hL : (Phi (star X)) j l =
        ∑ i : a, ∑ i' : a, star (X i' i) *
          (Phi (Matrix.single i i' (1 : ℂ))) j l := by
      have h := congrFun (congrFun (map_eq_sum_single Phi (star X)) j) l
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.star_apply] at h
      exact h
    have hR : (star (Phi X)) j l =
        ∑ i : a, ∑ i' : a, star (X i i') *
          star ((Phi (Matrix.single i i' (1 : ℂ))) l j) := by
      have h := congrFun (congrFun (map_eq_sum_single Phi X) l) j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
      rw [Matrix.star_apply, h]
      simp only [star_sum, star_mul']
    rw [hL, hR]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hJentry p q j l]

/-- A matrix map is Hermiticity preserving if and only if its Choi matrix is
Hermitian [Chiribella2009Networks, comblong-pub.tex:220-221]. -/
theorem isHermitianPreserving_iff_choi_isHermitian (Phi : MatrixMap a b) :
    MatrixMap.IsHermitianPreserving Phi ↔ (choi Phi).IsHermitian :=
  (isHermitianPreserving_iff_map_star Phi).trans
    (map_star_iff_choi_isHermitian Phi)

end HermitianPreserving

section CompletePositivity

/-- Arbitrary-ancilla positivity: tensoring the map with the identity map on
any finite ancilla index type preserves positive semidefiniteness. This is
the standard positivity-based formulation of complete positivity. -/
def MapsPositiveUnderAncilla (Phi : MatrixMap a b) : Prop :=
  ∀ (r : Type w) [Fintype r] [DecidableEq r] (X : CMatrix (a × r)),
    X.PosSemidef → (MatrixMap.kron Phi LinearMap.id X).PosSemidef

variable {r : Type w} {s : Type x}
variable [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- The Choi matrix of the identity map is the unnormalized maximally
entangled rank-one projector. -/
theorem choi_id :
    choi (LinearMap.id : MatrixMap r r) =
      Matrix.vecMulVec
        (fun x : r × r => if x.1 = x.2 then (1 : ℂ) else 0)
        (star fun x : r × r => if x.1 = x.2 then (1 : ℂ) else 0) := by
  ext ij kl
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  simp only [choi, LinearMap.id_coe, id_eq, Matrix.single_apply, Matrix.vecMulVec,
    Matrix.of_apply, Pi.star_apply]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> simp [hij, hkl]

/-- The Choi matrix of the identity map, the unnormalized maximally entangled
projector, is positive semidefinite. -/
theorem choi_id_posSemidef :
    (choi (LinearMap.id : MatrixMap r r)).PosSemidef := by
  rw [choi_id]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- The identity matrix map is completely positive. -/
theorem isCompletelyPositive_id :
    MatrixMap.IsCompletelyPositive (LinearMap.id : MatrixMap r r) :=
  (isCompletelyPositive_iff_choi _).mpr choi_id_posSemidef

/-- Tensoring with the identity map commutes with reindexing the ancilla
factor of the input matrix. -/
theorem kron_id_submatrix (Phi : MatrixMap a b) (X : CMatrix (a × r))
    (f : s → r) :
    MatrixMap.kron Phi LinearMap.id (X.submatrix (Prod.map id f) (Prod.map id f)) =
      (MatrixMap.kron Phi LinearMap.id X).submatrix (Prod.map id f) (Prod.map id f) := by
  ext bd bd'
  rcases bd with ⟨j, s1⟩
  rcases bd' with ⟨l, s2⟩
  simp only [Matrix.submatrix_apply, Prod.map_apply, id_eq]
  rw [kron_id_apply Phi X j l (f s1) (f s2),
    kron_id_apply Phi (X.submatrix (Prod.map id f) (Prod.map id f)) j l s1 s2]
  simp only [Matrix.submatrix_apply, Prod.map_apply, id_eq]

/-- The unnormalized maximally entangled input is mapped by `Phi ⊗ id` to the
factor-swapped Choi matrix. -/
theorem kron_id_choi_id (Phi : MatrixMap a b) :
    MatrixMap.kron Phi LinearMap.id (choi (LinearMap.id : MatrixMap a a)) =
      (choi Phi).submatrix (Equiv.prodComm b a) (Equiv.prodComm b a) := by
  ext bd bd'
  rcases bd with ⟨j, i0⟩
  rcases bd' with ⟨l, k0⟩
  simp only [Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [kron_id_apply]
  rw [Finset.sum_eq_single i0]
  · rw [Finset.sum_eq_single k0]
    · simp [choi, Matrix.single]
    · intro i' _ hi'
      simp [choi, Matrix.single, hi']
    · intro hnot
      simp at hnot
  · intro i _ hi
    refine Finset.sum_eq_zero fun i' _ => ?_
    simp [choi, Matrix.single, hi]
  · intro hnot
    simp at hnot

/-- Complete positivity implies positivity under tensoring with the identity on an arbitrary
finite ancilla, via tensor stability and the Kraus-form positivity of the resulting map. -/
theorem isCompletelyPositive_mapsPositiveUnderAncilla {Phi : MatrixMap a b}
    (hPhi : MatrixMap.IsCompletelyPositive Phi) : MapsPositiveUnderAncilla Phi := by
  intro r _ _ X hX
  exact isCompletelyPositive_mapsPositive _
    (MatrixMap.IsCompletelyPositive.kron hPhi isCompletelyPositive_id) X hX

/-- Positivity under tensoring with the identity on an ancilla of the input
index type itself forces the Choi matrix to be positive semidefinite: the
unnormalized maximally entangled state is positive, and its image is the
factor-swapped Choi matrix. -/
theorem isCompletelyPositive_of_mapsPositiveUnderAncilla (Phi : MatrixMap a b)
    (h : MapsPositiveUnderAncilla.{u, v, u} Phi) : MatrixMap.IsCompletelyPositive Phi := by
  have hW := h a (choi (LinearMap.id : MatrixMap a a)) choi_id_posSemidef
  rw [kron_id_choi_id] at hW
  exact (isCompletelyPositive_iff_choi Phi).mpr
    ((Matrix.posSemidef_submatrix_equiv (Equiv.prodComm b a)).mp hW)

/-- Complete positivity is equivalent to positivity under tensoring with the
identity map on arbitrary finite ancilla systems indexed by types in the input universe
[Chiribella2009Networks, comblong-pub.tex:236-237]. -/
theorem isCompletelyPositive_iff_mapsPositiveUnderAncilla (Phi : MatrixMap a b) :
    MatrixMap.IsCompletelyPositive Phi ↔ MapsPositiveUnderAncilla.{u, v, u} Phi :=
  ⟨fun hPhi => isCompletelyPositive_mapsPositiveUnderAncilla hPhi,
    fun h => isCompletelyPositive_of_mapsPositiveUnderAncilla Phi h⟩

/-- Complete positivity is also equivalent to positivity under tensoring with
the identity map on `Fin n`-indexed ancillas of every finite dimension. -/
theorem isCompletelyPositive_iff_mapsPositiveUnderAncilla_fin (Phi : MatrixMap a b) :
    MatrixMap.IsCompletelyPositive Phi ↔
      (∀ (n : ℕ) (X : CMatrix (a × Fin n)),
        X.PosSemidef → (MatrixMap.kron Phi LinearMap.id X).PosSemidef) := by
  constructor
  · intro hPhi n X hX
    exact isCompletelyPositive_mapsPositiveUnderAncilla hPhi (Fin n) X hX
  · intro h
    classical
    have hW : (choi (LinearMap.id : MatrixMap a a)).PosSemidef :=
      choi_id_posSemidef
    have hW' : ((choi (LinearMap.id : MatrixMap a a)).submatrix
        (Prod.map id (Fintype.equivFin a).symm)
        (Prod.map id (Fintype.equivFin a).symm)).PosSemidef :=
      hW.submatrix _
    have hstep := h (Fintype.card a) _ hW'
    rw [kron_id_submatrix] at hstep
    have hcomp : (Prod.map id (Fintype.equivFin a).symm :
          b × Fin (Fintype.card a) → b × a) ∘
        (Prod.map id (Fintype.equivFin a) :
          b × a → b × Fin (Fintype.card a)) = id := by
      funext y
      rcases y with ⟨p, q⟩
      simp [Prod.map]
    have hback : ((MatrixMap.kron Phi LinearMap.id (choi (LinearMap.id : MatrixMap a a))).submatrix
        (Prod.map id (Fintype.equivFin a).symm)
        (Prod.map id (Fintype.equivFin a).symm)).submatrix
        (Prod.map id (Fintype.equivFin a)) (Prod.map id (Fintype.equivFin a)) =
        MatrixMap.kron Phi LinearMap.id (choi (LinearMap.id : MatrixMap a a)) := by
      rw [Matrix.submatrix_submatrix, hcomp, Matrix.submatrix_id_id]
    have hM : (MatrixMap.kron Phi LinearMap.id
        (choi (LinearMap.id : MatrixMap a a))).PosSemidef := by
      rw [← hback]
      exact hstep.submatrix _
    have hswap : (Equiv.prodComm b a : b × a → a × b) ∘
        (Equiv.prodComm a b : a × b → b × a) = id := by
      funext y
      rcases y with ⟨p, q⟩
      rfl
    have hchoi : choi Phi =
        (MatrixMap.kron Phi LinearMap.id (choi (LinearMap.id : MatrixMap a a))).submatrix
          (Equiv.prodComm a b) (Equiv.prodComm a b) := by
      rw [kron_id_choi_id, Matrix.submatrix_submatrix, hswap,
        Matrix.submatrix_id_id]
    rw [isCompletelyPositive_iff_choi, hchoi]
    exact hM.submatrix _

end CompletePositivity

end MatrixMap

end

end QIT
