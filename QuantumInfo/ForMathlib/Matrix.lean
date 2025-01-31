import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Algebra.Algebra.Quasispectrum

import QuantumInfo.ForMathlib.Other

open BigOperators
open Classical

variable {n 𝕜 : Type*}
variable [RCLike 𝕜]

namespace RCLike

theorem isSelfAdjoint_re_iff {c : 𝕜} : IsSelfAdjoint c ↔ RCLike.re c = c  :=
  RCLike.conj_eq_iff_re

theorem isSelfAdjoint_im_zero_iff {c : 𝕜} : IsSelfAdjoint c ↔ RCLike.im c = 0  :=
  RCLike.conj_eq_iff_im

open ComplexOrder

theorem inv_nonneg' {x : 𝕜} (h : 0 ≤ x) : 0 ≤ x⁻¹ := by
  by_cases h0 : x = 0
  · subst x
    simp only [_root_.inv_zero, le_refl]
  · exact (RCLike.inv_pos.mpr (lt_of_le_of_ne h (Ne.symm h0))).le

@[simp]
theorem inv_nonneg {x : 𝕜} : 0 ≤ x⁻¹ ↔ 0 ≤ x :=
  ⟨by simpa only [inv_inv] using inv_nonneg' (x := x⁻¹), inv_nonneg'⟩

end RCLike

namespace Matrix

theorem zero_rank_eq_zero {A : Matrix n n 𝕜} [Fintype n] (hA : A.rank = 0) : A = 0 := by
  have h : ∀ v, A.mulVecLin v = 0 := by
    intro v
    rw [Matrix.rank, Module.finrank_zero_iff] at hA
    have := hA.elim ⟨A.mulVecLin v, ⟨v, rfl⟩⟩ ⟨0, ⟨0, by rw [mulVecLin_apply, mulVec_zero]⟩⟩
    simpa only [Subtype.mk.injEq] using this
  rw [← LinearEquiv.map_eq_zero_iff toLin']
  exact LinearMap.ext h

namespace IsHermitian

variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

include hA in
theorem smul_selfAdjoint {c : 𝕜} (hc : _root_.IsSelfAdjoint c) : (c • A).IsHermitian := by
  rw [IsHermitian, Matrix.conjTranspose_smul, hc, hA]

include hA in
theorem smul_im_zero {c : 𝕜} (h : RCLike.im c = 0) : (c • A).IsHermitian :=
  hA.smul_selfAdjoint (RCLike.isSelfAdjoint_im_zero_iff.mpr h)

include hA in
theorem smul_real (c : ℝ) : (c • A).IsHermitian := by
  convert hA.smul_im_zero (RCLike.ofReal_im c) using 1
  ext
  simp only [smul_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul]

def HermitianSubspace (n 𝕜 : Type*) [Fintype n] [RCLike 𝕜] : Subspace ℝ (Matrix n n 𝕜) where
  carrier := { A : Matrix n n 𝕜 | A.IsHermitian }
  add_mem' _ _ := by simp_all only [Set.mem_setOf_eq, IsHermitian.add]
  zero_mem' := by simp only [Set.mem_setOf_eq, isHermitian_zero]
  smul_mem' c A := by
    simp only [Set.mem_setOf_eq]
    intro hA
    exact IsHermitian.smul_real hA c

variable [Fintype n]

include hA in
@[simp]
theorem re_trace_eq_trace : RCLike.re (A.trace) = A.trace := by
  rw [trace, map_sum, RCLike.ofReal_sum, IsHermitian.coe_re_diag hA]

/-- The trace of a Hermitian matrix, as a real number. -/
def rtrace {A : Matrix n n 𝕜} (_ : A.IsHermitian) : ℝ :=
  RCLike.re (A.trace)

include hA in
@[simp]
theorem rtrace_eq_trace : (hA.rtrace : 𝕜) = A.trace :=
  hA.re_trace_eq_trace

section eigenvalues

/-- The sum of the eigenvalues of a Hermitian matrix is equal to its trace. -/
theorem sum_eigenvalues_eq_trace : ∑ i, hA.eigenvalues i = A.trace := by
  nth_rewrite 2 [hA.spectral_theorem]
  rw [Matrix.trace_mul_comm]
  rw [← mul_assoc]
  simp [Matrix.trace_diagonal]

theorem sum_eigenvalues_eq_rtrace : ∑ i, hA.eigenvalues i = hA.rtrace := by
  rw [rtrace, ←@RCLike.ofReal_inj 𝕜, sum_eigenvalues_eq_trace hA, re_trace_eq_trace hA]

/-- If all eigenvalues are equal to zero, then the matrix is zero. -/
theorem eigenvalues_zero_eq_zero (h : ∀ i, hA.eigenvalues i = 0) : A = 0 := by
  suffices A.rank = 0 from zero_rank_eq_zero this
  simp only [hA.rank_eq_card_non_zero_eigs, h, ne_eq, not_true_eq_false, Fintype.card_eq_zero]

end eigenvalues

end IsHermitian

section Kronecker

open Kronecker

variable [CommRing R] [StarRing R]
variable (A : Matrix m m R) (B : Matrix n n R)

theorem kroneckerMap_conjTranspose : (A ⊗ₖ B)ᴴ = (Aᴴ ⊗ₖ Bᴴ) := by
  ext; simp

variable {A : Matrix m m R} {B : Matrix n n R}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

include hA hB in
theorem kroneckerMap_IsHermitian : (A ⊗ₖ B).IsHermitian := by
  exact (hA ▸ hB ▸ kroneckerMap_conjTranspose A B : _ = _)

end Kronecker

namespace PosSemidef

open Classical
open Kronecker
open scoped ComplexOrder

variable {m n 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike 𝕜] [DecidableEq n]

section
variable {A : Matrix m m 𝕜} {B : Matrix m m 𝕜}
variable (hA : A.PosSemidef) (hB : B.PosSemidef)

include hA in
theorem diag_nonneg : ∀i, 0 ≤ A.diag i := by
  intro i
  simpa [Matrix.mulVec, dotProduct] using hA.2 (fun j ↦ if i = j then 1 else 0)

include hA in
theorem trace_nonneg : 0 ≤ A.trace := by
  rw [Matrix.trace]
  apply Finset.sum_nonneg
  simp_rw [Finset.mem_univ, forall_true_left]
  exact hA.diag_nonneg

include hA in
theorem trace_zero : A.trace = 0 → A = 0 := by
  intro h
  rw [← hA.isHermitian.sum_eigenvalues_eq_trace, RCLike.ofReal_eq_zero] at h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hA.eigenvalues_nonneg i)] at h
  simp only [Finset.mem_univ, diag_apply, forall_const] at h
  exact hA.isHermitian.eigenvalues_zero_eq_zero h

include hA in
@[simp]
theorem trace_zero_iff : A.trace = 0 ↔ A = 0 :=
  ⟨trace_zero hA, (by simp [·])⟩

theorem rtrace_nonneg : 0 ≤ hA.1.rtrace := by
  have := hA.trace_nonneg
  rwa [← hA.1.rtrace_eq_trace, RCLike.ofReal_nonneg] at this

@[simp]
theorem rtrace_zero_iff : hA.1.rtrace = 0 ↔ A = 0 :=
  ⟨fun h ↦ hA.trace_zero_iff.mp (RCLike.ext
    (by simp [show RCLike.re A.trace = 0 from h])
    (by simp [RCLike.nonneg_iff.mp hA.trace_nonneg])),
  (by simp [·, IsHermitian.rtrace])⟩

include hA in
theorem smul {c : 𝕜} (h : 0 ≤ c) : (c • A).PosSemidef := by
  constructor
  · apply hA.1.smul_im_zero (RCLike.nonneg_iff.mp h).2
  · intro x
    rw [Matrix.smul_mulVec_assoc, Matrix.dotProduct_smul]
    exact mul_nonneg h (hA.2 x)

include hA hB in
theorem convex_cone {c₁ c₂ : 𝕜} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) : (c₁ • A + c₂ • B).PosSemidef :=
  (hA.smul hc₁).add (hB.smul hc₂)

set_option trace.split.failure true

/-- A standard basis matrix (with a positive entry) is positive semidefinite iff the entry is on the diagonal. -/
theorem stdBasisMatrix_iff_eq (i j : m) {c : 𝕜} (hc : 0 < c) : (Matrix.stdBasisMatrix i j c).PosSemidef ↔ i = j := by
  constructor
  · intro ⟨hherm, _⟩
    rw [IsHermitian, ←Matrix.ext_iff] at hherm
    replace hherm := hherm i j
    simp only [stdBasisMatrix, conjTranspose_apply, of_apply, true_and, RCLike.star_def, if_true] at hherm
    apply_fun (starRingEnd 𝕜) at hherm
    have hcstar := RCLike.conj_eq_iff_im.mpr (RCLike.pos_iff.mp hc).right
    rw [starRingEnd_self_apply, hcstar, ite_eq_left_iff] at hherm
    contrapose! hherm
    have hcnezero : 0 ≠ c := by
      by_contra hczero
      subst hczero
      exact (lt_self_iff_false 0).mp hc
    exact ⟨fun _ => hherm.symm, hcnezero⟩
  · intro hij
    subst hij
    constructor
    · ext x y
      simp only [conjTranspose_apply, RCLike.star_def, Matrix.stdBasisMatrix, of_apply]
      split_ifs <;> try tauto
      · exact RCLike.conj_eq_iff_im.mpr (RCLike.pos_iff.1 hc).2
      · exact RingHom.map_zero (starRingEnd 𝕜)
    · intro x
      simp only [dotProduct, Matrix.stdBasisMatrix, of_apply, mulVec]
      convert_to 0 ≤ (star x i) * c * (x i)
      · simp only [Finset.mul_sum]
        rw [←Fintype.sum_prod_type']
        have h₀ : ∀ x_1 : m × m, x_1 ≠ ⟨i, i⟩ → star x x_1.1 * ((if i = x_1.1 ∧ i = x_1.2 then c else 0) * x x_1.2) = 0 := fun z hz => by
          have h₁ : ¬(i = z.1 ∧ i = z.2) := by
            rw [ne_eq, Prod.mk.inj_iff] at hz
            by_contra hz'
            apply hz
            exact ⟨hz'.left.symm, hz'.right.symm⟩
          rw [ite_cond_eq_false _ _ (eq_false h₁)]
          ring
        rw [Fintype.sum_eq_single ⟨i, i⟩ h₀]
        simp only [RCLike.star_def, and_self, reduceIte, mul_assoc]
      · rw [mul_comm, ←mul_assoc]
        have hpos : 0 ≤ x i * star x i := by simp only [Pi.star_apply, RCLike.star_def,
          RCLike.mul_conj, RCLike.ofReal_nonneg, norm_nonneg, pow_nonneg]
        exact (mul_nonneg hpos (le_of_lt hc))

end

variable {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
variable (hA : A.PosSemidef) (hB : B.PosSemidef)

include hA hB in
theorem PosSemidef_kronecker : (A ⊗ₖ B).PosSemidef := by
  rw [hA.left.spectral_theorem, hB.left.spectral_theorem]
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
  rw [← kroneckerMap_conjTranspose]
  rw [Matrix.diagonal_kronecker_diagonal]
  apply mul_mul_conjTranspose_same
  rw [posSemidef_diagonal_iff]
  rintro ⟨i₁, i₂⟩
  convert mul_nonneg (hA.eigenvalues_nonneg i₁) (hB.eigenvalues_nonneg i₂)
  rw [RCLike.nonneg_iff]
  simp

lemma sqrt_eq {A B : Matrix m m 𝕜} (h : A = B) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hA.sqrt = hB.sqrt := by
  congr!

lemma sqrt_eq' {A B : Matrix m m 𝕜} (h : A = B) (hA : A.PosSemidef) :
    hA.sqrt = (h ▸ hA).sqrt := by
  congr!

@[simp]
theorem sqrt_0 : (Matrix.PosSemidef.zero (n := n) (R := 𝕜)).sqrt = 0 :=
  Eq.symm $ eq_sqrt_of_sq_eq Matrix.PosSemidef.zero _ (by simp)

@[simp]
theorem sqrt_1 : (Matrix.PosSemidef.one (n := n) (R := 𝕜)).sqrt = 1 :=
  Eq.symm $ eq_sqrt_of_sq_eq Matrix.PosSemidef.one _ (by simp)

theorem nonneg_smul {c : 𝕜} (hA : A.PosSemidef) (hc : 0 ≤ c) : (c • A).PosSemidef := by
  constructor
  · simp only [IsHermitian, conjTranspose_smul, RCLike.star_def]
    congr
    exact RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hc).2
    exact hA.1
  · intro x
    rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
    exact Left.mul_nonneg hc (hA.2 x)

theorem pos_smul {c : 𝕜} (hA : (c • A).PosSemidef) (hc : 0 < c) : A.PosSemidef := by
  have : 0 < 1/c := by
    rw [RCLike.pos_iff] at hc ⊢
    aesop
  convert hA.nonneg_smul (c := 1/c) this.le
  rw [smul_smul, one_div, inv_mul_cancel₀ hc.ne', one_smul]

theorem nonneg_smul_Real_smul {c : ℝ} (hA : A.PosSemidef) (hc : 0 ≤ c) : (c • A).PosSemidef := by
  rw [(RCLike.real_smul_eq_coe_smul c A : c • A = (c : 𝕜) • A)]
  exact nonneg_smul hA (RCLike.ofReal_nonneg.mpr hc)

theorem pos_Real_smul {c : ℝ} (hA : (c • A).PosSemidef) (hc : 0 < c) : A.PosSemidef := by
  rw [(RCLike.real_smul_eq_coe_smul c A : c • A = (c : 𝕜) • A)] at hA
  exact pos_smul hA (RCLike.ofReal_pos.mpr hc)

theorem sqrt_nonneg_smul {c : 𝕜} (hA : (c^2 • A).PosSemidef) (hc : 0 < c) :
    hA.sqrt = c • (hA.pos_smul (sq_pos_of_pos hc) : A.PosSemidef).sqrt := by
  apply Eq.symm
  apply eq_sqrt_of_sq_eq
  · apply nonneg_smul ?_ hc.le
    apply posSemidef_sqrt
  rw [pow_two, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, sqrt_mul_self, pow_two, smul_smul]

include hA in
theorem zero_dotProduct_zero_iff : (∀ x : m → 𝕜, 0 = star x ⬝ᵥ A.mulVec x) ↔ A = 0 := by
  constructor
  · intro h0
    replace h0 := fun x ↦(PosSemidef.dotProduct_mulVec_zero_iff hA x).mp (h0 x).symm
    ext i j
    specialize h0 (Pi.single j 1)
    rw [mulVec_single] at h0
    replace h0 := congrFun h0 i
    simp_all only [mul_one, Pi.zero_apply, zero_apply]
    convert h0 using 1
    sorry
  · intro h0
    rw [h0]
    simp only [zero_mulVec, dotProduct_zero, implies_true]

theorem zero_posSemidef_neg_posSemidef_iff : A.PosSemidef ∧ (-A).PosSemidef ↔ A = 0 := by
  constructor
  · intro ⟨hA, hNegA⟩
    have h0 : ∀ x : m → 𝕜, 0 = star x ⬝ᵥ A.mulVec x := fun x ↦ by
      have hNegA' := hNegA.right x
      rw [neg_mulVec, dotProduct_neg, le_neg, neg_zero] at hNegA'
      exact le_antisymm (hA.right x) hNegA'
    exact (zero_dotProduct_zero_iff hA).mp h0
  · intro h0
    rw [h0]
    simp only [neg_zero, and_self, PosSemidef.zero]

end PosSemidef

namespace PosSemidef
section partialOrder
open scoped ComplexOrder

variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

/-- Loewner partial order of square matrices induced by positive-semi-definiteness:
`A ≤ B ↔ (B - A).PosSemidef` alongside properties that make it an "OrderedCancelAddCommMonoid"
TODO : Equivalence to CStarAlgebra.spectralOrder -/
instance instOrderedCancelAddCommMonoid : OrderedCancelAddCommMonoid (Matrix n n 𝕜) where
  le A B := (B - A).PosSemidef
  le_refl A := by simp only [sub_self, PosSemidef.zero]
  le_trans A B C hAB hBC := by
    simp_all only
    rw [←sub_add_sub_cancel _ B _]
    exact PosSemidef.add hBC hAB
  le_antisymm A B hAB hBA := by
    simp_all only
    rw [←neg_sub] at hAB
    rw [←sub_eq_zero]
    exact zero_posSemidef_neg_posSemidef_iff.mp ⟨hBA, hAB⟩
  add_le_add_left A B hAB C := by simp_all only [add_sub_add_left_eq_sub]
  le_of_add_le_add_left A B C hABAC:= by simp_all only [add_sub_add_left_eq_sub]

theorem le_iff_sub_posSemidef : A ≤ B ↔ (B - A).PosSemidef := by rfl

theorem zero_le_iff_posSemidef : 0 ≤ A ↔ A.PosSemidef := by
  apply Iff.trans (le_iff_sub_posSemidef)
  rw [sub_zero]

/-- Basically, the instance states A ≤ B ↔ B = A + Sᴴ * S  -/
instance instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
  StarOrderedRing.of_nonneg_iff'
    (add_le_add_left)
    (fun _ ↦ Iff.trans zero_le_iff_posSemidef Matrix.posSemidef_iff_eq_transpose_mul_self)

/-- Basically, the instance states 0 ≤ A → ∀ x ∈ spectrum ℝ A, 0 ≤ x  -/
instance instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n 𝕜) := by
  apply NonnegSpectrumClass.of_spectrum_nonneg
  intro A hA x hx
  rw [IsHermitian.eigenvalues_eq_spectrum_real (zero_le_iff_posSemidef.mp hA).1, Set.mem_range] at hx
  obtain ⟨i, hi⟩ := hx
  rw [←hi]
  exact Matrix.PosSemidef.eigenvalues_nonneg (zero_le_iff_posSemidef.mp hA) i

theorem le_iff_sub_nonneg : A ≤ B ↔ 0 ≤ B - A := Iff.trans le_iff_sub_posSemidef zero_le_iff_posSemidef.symm

theorem le_of_nonneg_imp {R : Type*} [OrderedAddCommGroup R] (f : Matrix n n 𝕜 →+ R) (h : ∀ A, A.PosSemidef → 0 ≤ f A) :
  (A ≤ B → f A ≤ f B) := by
  intro hAB
  rw [←sub_nonneg, ←map_sub]
  exact h (B - A) <| le_iff_sub_posSemidef.mp hAB

theorem le_of_nonneg_imp' {R : Type*} [OrderedAddCommGroup R] {x y : R} (f : R →+ Matrix n n 𝕜) (h : ∀ x, 0 ≤ x → (f x).PosSemidef) :
  (x ≤ y → f x ≤ f y) := by
  intro hxy
  rw [le_iff_sub_nonneg, ←map_sub]
  rw [←sub_nonneg] at hxy
  exact zero_le_iff_posSemidef.mpr <| h (y - x) hxy

theorem diag_monotone : Monotone (diag : Matrix n n 𝕜 → (n → 𝕜)) := fun _ _ ↦
  le_of_nonneg_imp (diagAddMonoidHom n 𝕜) (fun _ ↦ diag_nonneg)

theorem diag_mono : A ≤ B → ∀ i, A.diag i ≤ B.diag i := diag_monotone.imp

theorem trace_monotone : Monotone (@trace n 𝕜 _ _) := fun _ _ ↦
  le_of_nonneg_imp (traceAddMonoidHom n 𝕜) (fun _ ↦ trace_nonneg)

theorem trace_mono : A ≤ B → A.trace ≤ B.trace := trace_monotone.imp

theorem mul_mul_conjTranspose_mono {m : Type*} [Fintype m] (C : Matrix m n 𝕜) :
  A ≤ B → C * A * C.conjTranspose ≤ C * B * C.conjTranspose := fun hAB ↦ by
    rw [le_iff_sub_posSemidef]
    have hDistrib : C * B * Cᴴ - C * A * Cᴴ = C * (B - A) * Cᴴ := by
      ext i j
      simp only [sub_apply, mul_apply, conjTranspose_apply, RCLike.star_def, Finset.sum_mul,
        ←Finset.sum_sub_distrib, mul_sub_left_distrib, mul_sub_right_distrib]
    rw [hDistrib]
    exact mul_mul_conjTranspose_same (le_iff_sub_posSemidef.mp hAB) C

theorem conjTranspose_mul_mul_mono {m : Type*} [Fintype m] (C : Matrix n m 𝕜) :
  A ≤ B → C.conjTranspose * A * C ≤ C.conjTranspose * B * C := fun hAB ↦ by
    rw [le_iff_sub_posSemidef]
    have hDistrib : Cᴴ * B * C - Cᴴ * A * C = Cᴴ * (B - A) * C := by
      ext i j
      simp only [sub_apply, mul_apply, conjTranspose_apply, RCLike.star_def, Finset.sum_mul,
        ←Finset.sum_sub_distrib, mul_sub_left_distrib, mul_sub_right_distrib]
    rw [hDistrib]
    exact conjTranspose_mul_mul_same (le_iff_sub_posSemidef.mp hAB) C

theorem diagonal_monotone : Monotone (diagonal : (n → 𝕜) → _) := fun _ _ ↦
  le_of_nonneg_imp' (diagonalAddMonoidHom n 𝕜) (fun _ ↦ PosSemidef.diagonal)

theorem diagonal_mono {d₁ d₂ : n → 𝕜} : d₁ ≤ d₂ → diagonal d₁ ≤ diagonal d₂ := diagonal_monotone.imp

theorem diagonal_le_iff {d₁ d₂ : n → 𝕜} : d₁ ≤ d₂ ↔ diagonal d₁ ≤ diagonal d₂ := ⟨diagonal_mono, by
  intro hd
  rw [le_iff_sub_posSemidef, diagonal_sub, posSemidef_diagonal_iff] at hd
  simp only [sub_nonneg] at hd
  exact hd⟩

theorem le_smul_one_of_eigenvalues_iff (hA : A.PosSemidef) (c : ℝ) :
  (∀ i, hA.1.eigenvalues i ≤ c) ↔ A ≤ c • (1 : Matrix n n 𝕜) := by
  let U : Matrix n n 𝕜 := ↑hA.1.eigenvectorUnitary
  have hU : U.conjTranspose = star U := by simp only [star]
  have hU' : U * star U = 1 := by
    simp only [SetLike.coe_mem, unitary.mul_star_self_of_mem, U]
  have hc : c • (1 : Matrix n n 𝕜) = U * (c • 1) * U.conjTranspose := by
    simp only [Algebra.mul_smul_comm, mul_one, hU, Algebra.smul_mul_assoc, hU']
  have hc' : c • (1 : Matrix n n 𝕜) = Matrix.diagonal (RCLike.ofReal ∘ fun _ : n ↦ c) := by
    ext i j
    simp only [smul_apply, one_apply, smul_ite, RCLike.real_smul_eq_coe_mul, mul_one, smul_zero,
      diagonal, Function.comp_apply, of_apply]
  have hAST : A = U * diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) * U.conjTranspose := by
    rw [hU]
    exact IsHermitian.spectral_theorem hA.1
  constructor
  · intro h
    rw [hc, hc', hAST]
    apply mul_mul_conjTranspose_mono
    apply diagonal_mono
    intro i
    simp only [Function.comp_apply, algebraMap_le_algebraMap, h i]
  intro hAc i
  replace hAc := conjTranspose_mul_mul_mono U hAc
  have hU'CT : star U * U = 1 := by
    simp only [SetLike.coe_mem, unitary.star_mul_self_of_mem, U]
  have hcCT : U.conjTranspose * (c • 1) * U = c • (1 : Matrix n n 𝕜) := by
    simp only [Algebra.mul_smul_comm, mul_one, hU, Algebra.smul_mul_assoc, hU'CT]
  have hASTCT : U.conjTranspose * A * U = diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) := by
    rw [hU]
    exact IsHermitian.star_mul_self_mul_eq_diagonal hA.1
  rw [hcCT, hc', hASTCT, ←diagonal_le_iff] at hAc
  specialize hAc i
  simp only [Function.comp_apply, algebraMap_le_algebraMap] at hAc
  exact hAc

theorem le_trace_smul_one (hA : A.PosSemidef) : A ≤ hA.1.rtrace • 1 := by
  have h : ∀ i, hA.1.eigenvalues i ≤ hA.1.rtrace := fun i ↦ by
    rw [←IsHermitian.sum_eigenvalues_eq_rtrace hA.1]
    convert @Finset.sum_le_sum_of_subset_of_nonneg n ℝ _ hA.1.eigenvalues {i} Finset.univ _ _
    · rw [Finset.sum_singleton]
    · exact Finset.subset_univ {i}
    · exact fun j _ _ ↦ eigenvalues_nonneg hA j
  exact (le_smul_one_of_eigenvalues_iff hA hA.1.rtrace).mp h

end partialOrder

end PosSemidef

section frobenius_inner_product
open scoped ComplexOrder
variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜} {C : Matrix n n 𝕜} [Fintype n]

namespace IsHermitian
open scoped ComplexOrder

variable (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)

/-- Real inner product of two square matrices. Only defined for Hermitian matrices,
  as this lets us meaningfully interpret it as a real. -/
def rinner (_ : A.IsHermitian) (_ : B.IsHermitian) : ℝ :=
  RCLike.re (A * B).trace

/-- The inner product for Hermtian matrices is equal to the trace of
  the product. -/
theorem rinner_eq_trace_mul : hA.rinner hB = (A * B).trace := by
  have h₁ := (RCLike.is_real_TFAE (A * B).trace).out 2 0
  rw [rinner, h₁]
  nth_rewrite 1 1 [← hA, ← hB]
  simp [Matrix.trace, Matrix.mul_apply, Finset.sum_comm (f := fun x y ↦ A x y * _)]

theorem rinner_symm : hA.rinner hB = hB.rinner hA := by
  rw [rinner, rinner, Matrix.trace_mul_comm]

@[simp]
theorem rinner_zero_mul : hA.rinner Matrix.isHermitian_zero = 0 := by
  simp [rinner]

@[simp]
theorem rinner_mul_zero : Matrix.isHermitian_zero.rinner hA = 0 := by
  simp [rinner]

variable [DecidableEq n] in
@[simp]
theorem rinner_mul_one : hA.rinner Matrix.isHermitian_one = hA.rtrace := by
  simp only [rinner, mul_one, rtrace]

variable [DecidableEq n] in
@[simp]
theorem one_rinner_mul : Matrix.isHermitian_one.rinner hA = hA.rtrace := by
  simp only [rinner, one_mul, rtrace]

theorem rinner_smul_selfAdjoint {c : 𝕜} (hc : _root_.IsSelfAdjoint c) :
    (hA.smul_selfAdjoint hc).rinner hB = c * hA.rinner hB := by
  simp [rinner, RCLike.conj_eq_iff_re.mp hc, RCLike.conj_eq_iff_im.mp hc]

theorem smul_rinner_selfAdjoint {c : 𝕜} (hc : _root_.IsSelfAdjoint c) :
    hA.rinner (hB.smul_selfAdjoint hc) = c * hA.rinner hB := by
  rwa [rinner_symm, rinner_symm hA, rinner_smul_selfAdjoint]

@[simp]
theorem rinner_smul_real {c : ℝ} :
    (hA.smul_real c).rinner hB = c * hA.rinner hB := by
  simp [rinner, RCLike.smul_re]

@[simp]
theorem smul_inner_real {c : ℝ} :
    hA.rinner (hB.smul_real c) = c * hA.rinner hB := by
  simp [rinner, RCLike.smul_re]

@[simp]
theorem rinner_add : hA.rinner (IsHermitian.add hB hC) = hA.rinner hB + hA.rinner hC := by
  unfold rinner
  rw [left_distrib, trace_add, map_add]

@[simp]
theorem rinner_sub : hA.rinner (IsHermitian.sub hB hC) = hA.rinner hB - hA.rinner hC := by
  unfold rinner
  rw [sub_eq_add_neg, left_distrib, trace_add, map_add, mul_neg, trace_neg, map_neg, ←sub_eq_add_neg]

end IsHermitian
namespace PosSemidef

variable (hA : A.PosSemidef) (hB : B.PosSemidef)

/-- The inner product for PSD matrices is nonnegative. -/
theorem rinner_ge_zero : 0 ≤ hA.1.rinner hB.1 := by
  rw [IsHermitian.rinner, ← hA.sqrt_mul_self, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  nth_rewrite 1 [← hA.posSemidef_sqrt.left]
  exact (RCLike.nonneg_iff.mp (hB.conjTranspose_mul_mul_same _).trace_nonneg).left

theorem rinner_mono {A B C : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.IsHermitian) (hC : C.IsHermitian) :
  B ≤ C → hA.1.rinner hB ≤ hA.1.rinner hC := fun hBC ↦ by
  rw [le_iff_sub_posSemidef] at hBC
  have hTr : 0 ≤ hA.1.rinner (IsHermitian.sub hC hB) := rinner_ge_zero hA hBC
  rw [IsHermitian.rinner_sub] at hTr
  linarith

set_option pp.proofs.withType true in
include hA hB in
/-- The inner product for PSD matrices is at most the product of their traces. -/
theorem rinner_le_mul_trace : hA.1.rinner hB.1 ≤ hA.1.rtrace * hB.1.rtrace := by
  convert rinner_mono hA hB.1 (IsHermitian.smul_real isHermitian_one hB.1.rtrace) (le_trace_smul_one hB)
  rw [IsHermitian.smul_inner_real hA.1 isHermitian_one, IsHermitian.rinner_mul_one, mul_comm]

-- /-- The InnerProductSpace on Matrix n n 𝕜 defined by the Frobenius inner product, `Matrix.inner`.-/
-- def MatrixInnerProduct :=
--   InnerProductSpace.ofCore (𝕜 := ℝ) (F := Matrix n n 𝕜) {
--     inner := rinner
--     conj_symm := fun x y ↦ by
--       simp [inner, starRingEnd_apply, ← Matrix.trace_conjTranspose,
--         conjTranspose_mul, conjTranspose_conjTranspose]
--     nonneg_re := fun x ↦ by
--       simp only [inner]
--       exact (RCLike.nonneg_iff.mp x.posSemidef_conjTranspose_mul_self.trace_nonneg).1
--     add_left := by simp [inner, add_mul]
--     smul_left := by simp [inner]
--     definite := sorry
--   }

end PosSemidef
end frobenius_inner_product

section mat_trace

variable [AddCommMonoid R] [Fintype d]

def _root_.Matrix.traceLeft (m : Matrix (d × d₁) (d × d₂) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₁ j₁ ↦ ∑ i₂, m (i₂, i₁) (i₂, j₁)

def _root_.Matrix.traceRight (m : Matrix (d₁ × d) (d₂ × d) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₂ j₂ ↦ ∑ i₁, m (i₂, i₁) (j₂, i₁)

variable [Fintype d₁] [Fintype d₂] in
@[simp]
theorem _root_.Matrix.trace_of_traceLeft (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.traceLeft.trace = A.trace := by
  convert (Fintype.sum_prod_type_right _).symm
  rfl

variable [Fintype d₁] [Fintype d₂] in
@[simp]
theorem _root_.Matrix.trace_of_traceRight (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.traceRight.trace = A.trace := by
  convert (Fintype.sum_prod_type _).symm
  rfl

open ComplexOrder

variable [RCLike R] {A : Matrix (d₁ × d₂) (d₁ × d₂) R} [Fintype d₂] [Fintype d₁]

theorem _root_.Matrix.PosSemidef.traceLeft (hA : A.PosSemidef) : A.traceLeft.PosSemidef :=
  sorry

theorem _root_.Matrix.PosSemidef.traceRight (hA : A.PosSemidef) : A.traceRight.PosSemidef :=
  sorry

end mat_trace
