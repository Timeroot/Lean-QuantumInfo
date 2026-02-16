/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Multiset.Functor --Can't believe I'm having to import this
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.IsDiag

import Mathlib.Tactic.Bound

import QuantumInfo.ForMathlib.Misc

noncomputable section

open BigOperators

variable {n 𝕜 : Type*}
variable [RCLike 𝕜] [DecidableEq n]

namespace Matrix

theorem zero_rank_eq_zero {A : Matrix n n 𝕜} [Fintype n] (hA : A.rank = 0) : A = 0 := by
  have h : ∀ v, A.mulVecLin v = 0 := by
    intro v
    rw [rank, Module.finrank_zero_iff] at hA
    have := hA.elim ⟨A.mulVecLin v, ⟨v, rfl⟩⟩ ⟨0, ⟨0, by rw [mulVecLin_apply, mulVec_zero]⟩⟩
    simpa only [Subtype.mk.injEq] using this
  rw [← LinearEquiv.map_eq_zero_iff toLin']
  exact LinearMap.ext h

namespace IsHermitian

variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

include hA in
omit [DecidableEq n] in
theorem smul_selfAdjoint {c : 𝕜} (hc : _root_.IsSelfAdjoint c) : (c • A).IsHermitian := by
  exact IsSelfAdjoint.smul hc hA

include hA in
omit [DecidableEq n] in
theorem smul_im_zero {c : 𝕜} (h : RCLike.im c = 0) : (c • A).IsHermitian :=
  hA.smul_selfAdjoint (RCLike.conj_eq_iff_im.mpr h)

include hA in
omit [DecidableEq n] in
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
omit [DecidableEq n] in
@[simp]
theorem re_trace_eq_trace : RCLike.re (A.trace) = A.trace := by
  rw [trace, map_sum, RCLike.ofReal_sum, IsHermitian.coe_re_diag hA]

section eigenvalues

/-- The sum of the eigenvalues of a Hermitian matrix is equal to its trace. -/
theorem sum_eigenvalues_eq_trace : ∑ i, hA.eigenvalues i = A.trace := by
  nth_rewrite 2 [hA.spectral_theorem]
  rw [trace_mul_comm, ← mul_assoc]
  simp [trace_diagonal]

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

omit [DecidableEq n] in
theorem kroneckerMap_conjTranspose : (A ⊗ₖ B)ᴴ = (Aᴴ ⊗ₖ Bᴴ) := by
  ext; simp

variable {A : Matrix m m R} {B : Matrix n n R}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

include hA hB in
omit [DecidableEq n] in
theorem kroneckerMap_IsHermitian : (A ⊗ₖ B).IsHermitian := by
  exact (hA ▸ hB ▸ kroneckerMap_conjTranspose A B : _ = _)

end Kronecker

namespace PosSemidef

open Kronecker
open scoped ComplexOrder

variable {m n 𝕜 : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike 𝕜] [dn : DecidableEq n]

section
variable {A : Matrix m m 𝕜} {B : Matrix m m 𝕜}
variable (hA : A.PosSemidef) (hB : B.PosSemidef)

include hA in
theorem diag_nonneg : ∀i, 0 ≤ A.diag i := by
  intro i
  classical simpa [mulVec, dotProduct] using hA.2 (fun j ↦ if i = j then 1 else 0)

include hA in
theorem trace_zero : A.trace = 0 → A = 0 := by
  open Classical in
  intro h
  rw [← hA.isHermitian.sum_eigenvalues_eq_trace, RCLike.ofReal_eq_zero] at h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hA.eigenvalues_nonneg i)] at h
  simp only [Finset.mem_univ, forall_const] at h
  exact hA.isHermitian.eigenvalues_zero_eq_zero h

include hA in
@[simp]
theorem trace_zero_iff : A.trace = 0 ↔ A = 0 :=
  ⟨trace_zero hA, (by simp [·])⟩

--belongs somewhere else. compare with `Complex.normSq_eq_conj_mul_self`.
open ComplexConjugate in
theorem _root_.RCLike.normSq_eq_conj_mul_self {z : 𝕜} : RCLike.normSq z = conj z * z := by
  rw [RCLike.ext_iff]
  simp [RCLike.normSq]
  ring_nf

omit dn in
open ComplexConjugate in
theorem outer_self_conj (v : n → 𝕜) : PosSemidef (vecMulVec v (conj v)) := by
  constructor
  · ext
    simp [vecMulVec_apply, mul_comm]
  · intro x
    simp_rw [dotProduct, Pi.star_apply, RCLike.star_def, mulVec, dotProduct,
      vecMulVec_apply, mul_assoc, ← Finset.mul_sum, ← mul_assoc, ← Finset.sum_mul]
    change
      0 ≤ (∑ i : n, conj (x i) * v i) * ∑ i : n, conj (v i) * x i
    have : (∑ i : n, conj (x i) * v i) =
        (∑ i : n, conj (conj (v i) * x i)) := by
          simp only [mul_comm (conj (x _)) (v _), map_mul,
          RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [this, ← map_sum, ← RCLike.normSq_eq_conj_mul_self, RCLike.ofReal_nonneg]
    exact RCLike.normSq_nonneg _

include hA hB in
theorem convex_cone {c₁ c₂ : 𝕜} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) : (c₁ • A + c₂ • B).PosSemidef :=
  (hA.smul hc₁).add (hB.smul hc₂)

variable [dm : DecidableEq m]

/-- A standard basis matrix (with a positive entry) is positive semidefinite iff the entry is on the diagonal. -/
theorem stdBasisMatrix_iff_eq (i j : m) {c : 𝕜} (hc : 0 < c) : (single i j c).PosSemidef ↔ i = j := by
  constructor
  · intro ⟨hherm, _⟩
    rw [IsHermitian, ← ext_iff] at hherm
    replace hherm := hherm i j
    simp only [single, conjTranspose_apply, of_apply, true_and, RCLike.star_def, if_true] at hherm
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
      simp only [conjTranspose_apply, RCLike.star_def, single, of_apply]
      split_ifs <;> try tauto
      · exact RCLike.conj_eq_iff_im.mpr (RCLike.pos_iff.1 hc).2
      · exact RingHom.map_zero (starRingEnd 𝕜)
    · intro x
      simp only [dotProduct, single, of_apply, mulVec]
      convert_to 0 ≤ (star x i) * c * (x i)
      · simp only [Finset.mul_sum]
        rw [←Fintype.sum_prod_type']
        have h₀ : ∀ x_1 : m × m, x_1 ≠ ⟨i, i⟩ → star x x_1.1 * ((if i = x_1.1 ∧ i = x_1.2 then c else 0) * x x_1.2) = 0 := fun z hz => by
          have h₁ : ¬(i = z.1 ∧ i = z.2) := by
            rw [ne_eq, Prod.mk_inj] at hz
            by_contra hz'
            apply hz
            exact ⟨hz'.left.symm, hz'.right.symm⟩
          rw [ite_cond_eq_false _ _ (eq_false h₁)]
          ring
        rw [Fintype.sum_eq_single ⟨i, i⟩ h₀]
        simp [mul_assoc]
      · rw [mul_comm, ←mul_assoc]
        have hpos : 0 ≤ x i * star x i := by simp only [Pi.star_apply, RCLike.star_def,
          RCLike.mul_conj, RCLike.ofReal_nonneg, norm_nonneg, pow_nonneg]
        exact (mul_nonneg hpos (le_of_lt hc))

end

variable {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
variable (hA : A.PosSemidef) (hB : B.PosSemidef)

include hA hB in
theorem PosSemidef_kronecker : (A ⊗ₖ B).PosSemidef := by
  open Classical in
  rw [hA.left.spectral_theorem, hB.left.spectral_theorem]
  rw [mul_kronecker_mul, mul_kronecker_mul]
  rw [star_eq_conjTranspose, star_eq_conjTranspose]
  rw [← kroneckerMap_conjTranspose]
  rw [diagonal_kronecker_diagonal]
  apply mul_mul_conjTranspose_same
  rw [posSemidef_diagonal_iff]
  rintro ⟨i₁, i₂⟩
  convert mul_nonneg (hA.eigenvalues_nonneg i₁) (hB.eigenvalues_nonneg i₂)
  rw [RCLike.nonneg_iff]
  simp

variable [dm : DecidableEq m]

open MatrixOrder
open ComplexOrder

omit [DecidableEq m]

include hA in
theorem zero_dotProduct_zero_iff : (∀ x : m → 𝕜, 0 = star x ⬝ᵥ A.mulVec x) ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have h₂ := fun x ↦ (PosSemidef.dotProduct_mulVec_zero_iff hA x).mp (h x).symm
    classical have : DecidableEq m := inferInstance
    convert congrFun (h₂ (Pi.single j 1)) i using 1
    simp
  · rintro rfl
    simp

theorem nonneg_smul {c : 𝕜} (hA : A.PosSemidef) (hc : 0 ≤ c) : (c • A).PosSemidef := by
  constructor
  · simp only [IsHermitian, conjTranspose_smul, RCLike.star_def]
    congr
    exact RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hc).2
    exact hA.1
  · intro x
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
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

theorem zero_posSemidef_neg_posSemidef_iff : A.PosSemidef ∧ (-A).PosSemidef ↔ A = 0 := by
  constructor
  · intro ⟨hA, hNegA⟩
    have h0 : ∀ x : m → 𝕜, 0 = star x ⬝ᵥ A.mulVec x := fun x ↦ by
      have hNegA' := hNegA.right x
      rw [neg_mulVec, dotProduct_neg, le_neg, neg_zero] at hNegA'
      exact le_antisymm (hA.right x) hNegA'
    exact (zero_dotProduct_zero_iff hA).mp h0
  · rintro rfl
    simp [PosSemidef.zero]

end PosSemidef


namespace PosDef
open scoped ComplexOrder

variable {n m 𝕜 : Type*}
variable [Fintype n] [RCLike 𝕜] [DecidableEq n]
variable {A : Matrix n n 𝕜}

theorem toLin_ker_eq_bot (hA : A.PosDef) : LinearMap.ker A.toLin' = ⊥ := by
  ext v
  have := hA.right v
  grind [mulVec_zero, dotProduct_zero, LinearMap.mem_ker, toLin'_apply, Submodule.mem_bot]

theorem of_toLin_ker_eq_bot (hA : LinearMap.ker A.toLin' = ⊥) (hA₂ : A.PosSemidef) : A.PosDef := by
  rwa [hA₂.posDef_iff_isUnit, ← Matrix.isUnit_toLin'_iff, LinearMap.isUnit_iff_ker_eq_bot]

theorem ker_range_antitone {d : Type*} [Fintype d] [DecidableEq d] {A B : Matrix d d ℂ}
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
    LinearMap.ker A.toEuclideanLin ≤ LinearMap.ker B.toEuclideanLin ↔
    LinearMap.range B.toEuclideanLin ≤ LinearMap.range A.toEuclideanLin
     := by
  rw [Matrix.isHermitian_iff_isSymmetric] at hA hB
  exact ContinuousLinearMap.ker_le_ker_iff_range_le_range
    (T := Matrix.toEuclideanCLM.toFun B) (U := Matrix.toEuclideanCLM.toFun A) hB hA

end PosDef

namespace PosSemidef
section partialOrder
open scoped ComplexOrder
open scoped MatrixOrder

variable {n m 𝕜 : Type*}
variable [Fintype n] [Fintype m] [RCLike 𝕜] [DecidableEq m]
variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

instance instOrderedCancelAddCommMonoid : IsOrderedCancelAddMonoid (Matrix n n 𝕜) where
  add_le_add_left A B hAB C := by
    rw [Matrix.le_iff]
    rwa [add_sub_add_left_eq_sub]
  le_of_add_le_add_left A B C hABAC:= by
    rw [Matrix.le_iff] at hABAC
    rwa [add_sub_add_left_eq_sub] at hABAC

/-- Basically, the instance states A ≤ B ↔ B = A + Sᴴ * S  -/
instance instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
  StarOrderedRing.of_nonneg_iff'
    (add_le_add_left)
    (fun _ ↦ by classical apply CStarAlgebra.nonneg_iff_eq_star_mul_self)

theorem le_of_nonneg_imp {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (f : Matrix n n 𝕜 →+ R) (h : ∀ A, A.PosSemidef → 0 ≤ f A) :
    (A ≤ B → f A ≤ f B) := by
  intro hAB
  rw [←sub_nonneg, ←map_sub]
  exact h (B - A) <| by rwa [← Matrix.le_iff]

theorem le_of_nonneg_imp' {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    {x y : R} (f : R →+ Matrix n n 𝕜) (h : ∀ x, 0 ≤ x → (f x).PosSemidef) :
    (x ≤ y → f x ≤ f y) := by
  intro hxy
  rw [← sub_nonneg, ← map_sub, Matrix.nonneg_iff_posSemidef]
  rw [← sub_nonneg] at hxy
  exact h (y - x) hxy

omit [DecidableEq m] in
theorem mul_mul_conjTranspose_mono (C : Matrix m n 𝕜) :
  A ≤ B → C * A * C.conjTranspose ≤ C * B * C.conjTranspose := fun hAB ↦ by
    rw [Matrix.le_iff] at hAB ⊢
    have hDistrib : C * B * Cᴴ - C * A * Cᴴ = C * (B - A) * Cᴴ := by
      ext i j
      simp only [sub_apply, mul_apply, conjTranspose_apply, RCLike.star_def, Finset.sum_mul,
        ←Finset.sum_sub_distrib, mul_sub_left_distrib, mul_sub_right_distrib]
    rw [hDistrib]
    exact mul_mul_conjTranspose_same hAB C

omit [DecidableEq m] in
theorem conjTranspose_mul_mul_mono (C : Matrix n m 𝕜) :
  A ≤ B → C.conjTranspose * A * C ≤ C.conjTranspose * B * C := fun hAB ↦ by
    convert mul_mul_conjTranspose_mono Cᴴ hAB
    <;> rw [conjTranspose_conjTranspose]

theorem nonneg_iff_eigenvalue_nonneg [DecidableEq n] : 0 ≤ A ↔ ∀ x, 0 ≤ hA.eigenvalues x :=
  Iff.trans Matrix.nonneg_iff_posSemidef hA.posSemidef_iff_eigenvalues_nonneg

theorem diag_monotone : Monotone (diag : Matrix n n 𝕜 → (n → 𝕜)) := fun _ _ ↦
  le_of_nonneg_imp (diagAddMonoidHom n 𝕜) (fun _ ↦ diag_nonneg)

theorem diag_mono : A ≤ B → ∀ i, A.diag i ≤ B.diag i := diag_monotone.imp

theorem trace_monotone : Monotone (@trace n 𝕜 _ _) := fun _ _ ↦
  le_of_nonneg_imp (traceAddMonoidHom n 𝕜) (fun _ ↦ trace_nonneg)

theorem trace_mono : A ≤ B → A.trace ≤ B.trace := trace_monotone.imp

variable [DecidableEq n]

theorem diagonal_monotone : Monotone (diagonal : (n → 𝕜) → _) := fun _ _ ↦
  le_of_nonneg_imp' (diagonalAddMonoidHom n 𝕜) (fun _ ↦ PosSemidef.diagonal)

theorem diagonal_mono {d₁ d₂ : n → 𝕜} : d₁ ≤ d₂ → diagonal d₁ ≤ diagonal d₂ := diagonal_monotone.imp

theorem diagonal_le_iff {d₁ d₂ : n → 𝕜} : d₁ ≤ d₂ ↔ diagonal d₁ ≤ diagonal d₂ := ⟨diagonal_mono, by
  intro hd
  rw [Matrix.le_iff, diagonal_sub, posSemidef_diagonal_iff] at hd
  simp only [sub_nonneg] at hd
  exact hd⟩

theorem le_smul_one_of_eigenvalues_iff (hA : A.IsHermitian) (c : ℝ) :
  (∀ i, hA.eigenvalues i ≤ c) ↔ A ≤ c • (1 : Matrix n n 𝕜) := by
  let U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  have hU : U.conjTranspose = star U := by simp only [star]
  have hU' : U * star U = 1 := by
    simp only [SetLike.coe_mem, unitary.mul_star_self_of_mem, U]
  have hc : c • (1 : Matrix n n 𝕜) = U * (c • 1) * U.conjTranspose := by
    simp only [Algebra.mul_smul_comm, mul_one, hU, Algebra.smul_mul_assoc, hU']
  have hc' : c • (1 : Matrix n n 𝕜) = diagonal (RCLike.ofReal ∘ fun _ : n ↦ c) := by
    ext i j
    simp only [smul_apply, one_apply, smul_ite, RCLike.real_smul_eq_coe_mul, mul_one, smul_zero,
      diagonal, Function.comp_apply, of_apply]
  have hAST : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * U.conjTranspose := by
    rw [hU]
    exact IsHermitian.spectral_theorem hA
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
  have hASTCT : U.conjTranspose * A * U = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [hU]
    exact IsHermitian.star_mul_self_mul_eq_diagonal hA
  rw [hcCT, hc', hASTCT, ←diagonal_le_iff] at hAc
  specialize hAc i
  simp only [Function.comp_apply, algebraMap_le_algebraMap] at hAc
  exact hAc

theorem smul_one_le_of_eigenvalues_iff (hA : A.IsHermitian) (c : ℝ) :
  (∀ i, c ≤ hA.eigenvalues i) ↔ c • (1 : Matrix n n 𝕜) ≤ A := by
  -- I did the lazy thing and just copied the previous proof
  let U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  have hU : U.conjTranspose = star U := by simp only [star]
  have hU' : U * star U = 1 := by
    simp only [SetLike.coe_mem, unitary.mul_star_self_of_mem, U]
  have hc : c • (1 : Matrix n n 𝕜) = U * (c • 1) * U.conjTranspose := by
    simp only [Algebra.mul_smul_comm, mul_one, hU, Algebra.smul_mul_assoc, hU']
  have hc' : c • (1 : Matrix n n 𝕜) = diagonal (RCLike.ofReal ∘ fun _ : n ↦ c) := by
    ext i j
    simp only [smul_apply, one_apply, smul_ite, RCLike.real_smul_eq_coe_mul, mul_one, smul_zero,
      diagonal, Function.comp_apply, of_apply]
  have hAST : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * U.conjTranspose := by
    rw [hU]
    exact IsHermitian.spectral_theorem hA
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
  have hASTCT : U.conjTranspose * A * U = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [hU]
    exact IsHermitian.star_mul_self_mul_eq_diagonal hA
  rw [hcCT, hc', hASTCT, ←diagonal_le_iff] at hAc
  specialize hAc i
  simp only [Function.comp_apply, algebraMap_le_algebraMap] at hAc
  exact hAc

end partialOrder

end PosSemidef

-- noncomputable section frobenius_inner_product
-- open scoped ComplexOrder
-- variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜} {C : Matrix n n 𝕜} [Fintype n]

-- /-- The InnerProductSpace on Matrix n n 𝕜 defined by the real part of the
--  Frobenius inner product. -/
-- def InnerProductCore : InnerProductSpace.Core (𝕜 := ℝ) (F := Matrix n n 𝕜):=
--    {
--     inner A B := RCLike.re (Aᴴ * B).trace
--     conj_inner_symm := fun x y ↦ by
--       simpa [inner, starRingEnd_apply, ← trace_conjTranspose] using
--         RCLike.conj_re (xᴴ * y).trace
--     re_inner_nonneg := fun x ↦
--       (RCLike.nonneg_iff.mp x.posSemidef_conjTranspose_mul_self.trace_nonneg).1
--     add_left := by simp [inner, add_mul]
--     smul_left x y r := by
--       simpa using RCLike.smul_re _ (xᴴ * y).trace
--     definite x h := by
--       ext i j
--       replace h : ∑ j, ∑ i, (RCLike.re (x i j) ^ 2 + RCLike.im (x i j) ^ 2) = 0 := by
--         simpa [trace, mul_apply, ← pow_two] using h
--       rw [Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)] at h
--       replace h := congrFun h j
--       rw [Pi.zero_apply, Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)] at h
--       replace h := congrFun h i
--       dsimp at h
--       rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff] at h
--       apply RCLike.ext (h.left.trans RCLike.zero_re.symm) (h.right.trans (map_zero _).symm)
--   }

-- def instNormed : NormedAddCommGroup (Matrix n n 𝕜) :=
--   InnerProductCore.toNormedAddCommGroup

-- scoped[Frobenius] attribute [instance] Matrix.instNormed

-- open scoped Frobenius in
-- def instInnerProductSpace : InnerProductSpace ℝ (Matrix n n 𝕜) :=
--   InnerProductSpace.ofCore InnerProductCore

-- scoped[Frobenius] attribute [instance] Matrix.instInnerProductSpace

-- instance : Inner ℝ (Matrix n n 𝕜) :=
--   instInnerProductSpace.toInner

-- /-- The InnerProductSpace on Matrix n n 𝕜 defined by the Frobenius inner product. -/
-- def CInnerProductCore : InnerProductSpace.Core (𝕜 := ℂ) (F := Matrix n n ℂ):=
--    {
--     inner A B := (Aᴴ * B).trace
--     conj_inner_symm := fun x y ↦ by
--       simp [inner, starRingEnd_apply, ← Matrix.trace_conjTranspose]
--     re_inner_nonneg := fun x ↦
--       (RCLike.nonneg_iff.mp x.posSemidef_conjTranspose_mul_self.trace_nonneg).1
--     add_left := by simp [inner, add_mul]
--     smul_left x y r := by simp
--     definite x h := by
--       ext i j
--       replace h : ∑ j, ∑ i, ((x i j).re ^ 2 + (x i j).im ^ 2) = (0 : ℂ) := by
--         convert h
--         simp only [Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_pow, trace, diag_apply,
--           mul_apply, conjTranspose_apply, RCLike.star_def]
--         congr! 2
--         norm_cast
--         rw [Complex.conj_mul', ← Complex.sq_norm_sub_sq_re]
--         norm_cast
--         abel
--       rw [Complex.ofReal_eq_zero,
--         Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)] at h
--       replace h := congrFun h j
--       rw [Pi.zero_apply, Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)] at h
--       replace h := congrFun h i
--       dsimp at h
--       rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff] at h
--       apply RCLike.ext (h.left.trans RCLike.zero_re.symm) (h.right.trans (map_zero _).symm)
--   }

-- open scoped Frobenius in
-- def instCInnerProductSpace : InnerProductSpace ℂ (Matrix n n ℂ) :=
--   InnerProductSpace.ofCore CInnerProductCore

-- scoped[Frobenius] attribute [instance] Matrix.instCInnerProductSpace

-- instance : Inner ℂ (Matrix n n ℂ) :=
--   instCInnerProductSpace.toInner

--Makes the `Inner ℝ` instance is globally accessible, but the norm instances
--require `open scoped Frobenius`. e.g.

-- open scoped Frobenius in
-- #synth InnerProductSpace ℝ (Matrix (Fin 5) (Fin 5) ℝ)

-- (no `open` needed):
-- #synth Inner ℝ (Matrix (Fin 5) (Fin 5) ℝ)

-- end frobenius_inner_product

section partial_trace

variable [AddCommMonoid R] [Fintype d]

def traceLeft (m : Matrix (d × d₁) (d × d₂) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₁ j₁ ↦ ∑ i₂, m (i₂, i₁) (i₂, j₁)

def traceRight (m : Matrix (d₁ × d) (d₂ × d) R) : Matrix d₁ d₂ R :=
  Matrix.of fun i₂ j₂ ↦ ∑ i₁, m (i₂, i₁) (j₂, i₁)

variable [Fintype d₁] [Fintype d₂] in
@[simp]
theorem traceLeft_trace (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.traceLeft.trace = A.trace := by
  convert (Fintype.sum_prod_type_right _).symm
  rfl

variable [Fintype d₁] [Fintype d₂] in
@[simp]
theorem traceRight_trace (A : Matrix (d₁ × d₂) (d₁ × d₂) R) : A.traceRight.trace = A.trace := by
  convert (Fintype.sum_prod_type _).symm
  rfl

variable [StarAddMonoid R] in
theorem IsHermitian.traceLeft {A : Matrix (d × d₁) (d × d₁) R} (hA : A.IsHermitian) : A.traceLeft.IsHermitian := by
  ext
  simp only [Matrix.traceLeft, conjTranspose_apply, of_apply, star_sum]
  congr!
  exact congrFun₂ hA _ _

variable [StarAddMonoid R] in
theorem IsHermitian.traceRight {A : Matrix (d₁ × d) (d₁ × d) R} (hA : A.IsHermitian) : A.traceRight.IsHermitian := by
  ext
  simp only [Matrix.traceRight, conjTranspose_apply, of_apply, star_sum]
  congr!
  exact congrFun₂ hA _ _

variable [DecidableEq dB] [Fintype dA] [Fintype dB] in
open scoped Kronecker in
/--
`Tr(M (A ⊗ I)) = Tr(Tr_B(M) A)`
-/
theorem trace_mul_kron_one_right {R : Type*} [Ring R]
    (M : Matrix (dA × dB) (dA × dB) R) (A : Matrix dA dA R) :
    (M * (A ⊗ₖ (1 : Matrix dB dB R))).trace = (M.traceRight * A).trace := by
  simp [trace, mul_apply, kroneckerMap_apply, traceRight, one_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

variable [DecidableEq dA] [Fintype dA] [Fintype dB] in
open scoped Kronecker in
/--
`Tr(M (I ⊗ B)) = Tr(Tr_A(M) B)`
-/
theorem trace_mul_one_kron_right {R : Type*} [Ring R]
    (M : Matrix (dA × dB) (dA × dB) R) (B : Matrix dB dB R) :
    (M * ((1 : Matrix dA dA R) ⊗ₖ B)).trace = (M.traceLeft * B).trace := by
  simp [trace, mul_apply, kroneckerMap_apply, traceLeft, one_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

open ComplexOrder

variable {d₁ d₂ : Type*} {A : Matrix (d₁ × d₂) (d₁ × d₂) 𝕜}
variable [Fintype d₂] [Fintype d₁]

theorem PosSemidef.traceLeft [DecidableEq d₁] (hA : A.PosSemidef) : A.traceLeft.PosSemidef := by
  constructor
  · exact hA.1.traceLeft
  · intro x
    convert Finset.sum_nonneg' (s := .univ) (fun (i : d₁) ↦ hA.2 (fun (j,k) ↦ if i = j then x k else 0))
    simp_rw [Matrix.traceLeft, dotProduct_mulVec]
    simpa [dotProduct, vecMul_eq_sum, ite_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
      apply_ite] using Finset.sum_comm_cycle

theorem PosSemidef.traceRight [DecidableEq d₂] (hA : A.PosSemidef) : A.traceRight.PosSemidef := by
  constructor
  · exact hA.1.traceRight
  · intro x
    convert Finset.sum_nonneg' (s := .univ) (fun (i : d₂) ↦ hA.2 (fun (j,k) ↦ if i = k then x j else 0))
    simp_rw [Matrix.traceRight, dotProduct_mulVec]
    simpa [dotProduct, vecMul_eq_sum, ite_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
      apply_ite] using Finset.sum_comm_cycle

end partial_trace

section posdef

open ComplexOrder
open Kronecker

theorem PosDef.kron {d₁ d₂ 𝕜 : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]
    {A : Matrix d₁ d₁ 𝕜} {B : Matrix d₂ d₂ 𝕜} (hA : A.PosDef) (hB : B.PosDef) : (A ⊗ₖ B).PosDef := by
  rw [hA.left.spectral_theorem, hB.left.spectral_theorem]
  rw [mul_kronecker_mul, mul_kronecker_mul]
  rw [star_eq_conjTranspose, star_eq_conjTranspose]
  rw [← kroneckerMap_conjTranspose]
  rw [diagonal_kronecker_diagonal]
  apply mul_mul_conjTranspose_same
  · rw [posDef_diagonal_iff]
    rintro ⟨i₁, i₂⟩
    convert mul_pos (hA.eigenvalues_pos i₁) (hB.eigenvalues_pos i₂)
    rw [RCLike.pos_iff]
    simp
  · apply Matrix.vecMul_injective_of_isUnit
    rw [isUnit_iff_exists]
    use (star hA.left.eigenvectorUnitary.val) ⊗ₖ (star hB.left.eigenvectorUnitary.val)
    simp [← Matrix.mul_kronecker_mul]

theorem PosDef.submatrix {d₁ d₂ 𝕜 : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]
    {M : Matrix d₁ d₁ 𝕜} (hM : M.PosDef) {e : d₂ → d₁} (he : Function.Injective e) : (M.submatrix e e).PosDef := by
  use hM.left.submatrix e
  intro x hx
  let y : d₁ → 𝕜 := fun i ↦ ∑ j ∈ { j | e j = i}, x j
  have hy : y ≠ 0 := by
    contrapose! hx
    simp only [funext_iff] at hx ⊢
    intro i
    simpa [y, he.eq_iff, Finset.sum_eq_single_of_mem] using hx (e i)
  convert hM.right y hy
  dsimp [Matrix.mulVec, dotProduct, y]
  simp only [map_sum]
  simp only [Finset.sum_mul, Finset.sum_filter, Finset.mul_sum]
  simp [← Finset.mul_sum, Finset.sum_comm]

theorem PosDef.reindex {d₁ d₂ 𝕜 : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]
    {M : Matrix d₁ d₁ 𝕜} (hM : M.PosDef) (e : d₁ ≃ d₂) : (M.reindex e e).PosDef :=
  hM.submatrix e.symm.injective

@[simp]
theorem PosDef.reindex_iff {d₁ d₂ 𝕜 : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]
    {M : Matrix d₁ d₁ 𝕜} (e : d₁ ≃ d₂) : (M.reindex e e).PosDef ↔ M.PosDef := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reindex e⟩
  convert h.reindex e.symm
  simp

theorem PosSemidef.rsmul {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (c • M).PosSemidef := by
  constructor
  · exact hM.1.smul_real c
  · peel hM.2
    rw [smul_mulVec, dotProduct_smul]
    positivity

theorem PosDef.Convex {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] : Convex ℝ (Matrix.PosDef (n := n) (R := 𝕜)) := by
  intro A hA B hB a b ha hb hab
  rcases ha.lt_or_eq with ha | rfl
  · apply (hA.smul ha).add_posSemidef
    exact hB.posSemidef.smul hb
  · apply Matrix.PosDef.posSemidef_add
    · simp [Matrix.PosSemidef.zero]
    · exact hB.smul (by linarith)

end posdef

section eigenvalues

open ComplexOrder

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]

theorem PosDef_iff_eigenvalues' (M : Matrix d d 𝕜) :
    M.PosDef ↔ ∃ (h : M.IsHermitian), ∀ i, 0 < h.eigenvalues i :=
  ⟨fun h ↦ ⟨h.left, h.left.posDef_iff_eigenvalues_pos.mp h⟩,
    fun ⟨w, h⟩ ↦ w.posDef_iff_eigenvalues_pos.mpr h⟩

--PR'ed: #27118
theorem IsHermitian.charpoly_roots_eq_eigenvalues {M : Matrix d d 𝕜} (hM : M.IsHermitian) :
    M.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hM.eigenvalues) Finset.univ.val := by
  -- Since M is Hermitian, its characteristic polynomial splits into linear factors over the reals.
  have h_split : M.charpoly = Multiset.prod (Multiset.map (fun (e : ℝ) => Polynomial.X - Polynomial.C (RCLike.ofReal e)) (Multiset.map (fun (i : d) => hM.eigenvalues i) Finset.univ.val)) := by
    -- Since M is Hermitian, it is diagonalizable, and its characteristic polynomial splits into linear factors over the reals.
    have h_diag : ∃ P : Matrix d d 𝕜, P.det ≠ 0 ∧ ∃ D : Matrix d d 𝕜, D = Matrix.diagonal (fun i => RCLike.ofReal (hM.eigenvalues i)) ∧ M = P * D * P⁻¹ := by
      have := hM.spectral_theorem;
      refine' ⟨ hM.eigenvectorUnitary, _, _ ⟩
      · -- Since the eigenvector unitary is a unitary matrix, its determinant is a unit, hence non-zero.
        have h_det_unitary : IsUnit (Matrix.det (hM.eigenvectorUnitary : Matrix d d 𝕜)) := by
          exact UnitaryGroup.det_isUnit hM.eigenvectorUnitary
        exact h_det_unitary.ne_zero
      · refine' ⟨ _, rfl, this.trans _ ⟩
        rw [ Matrix.inv_eq_left_inv ]
        congr!
        bound
    -- Since M is similar to D, their characteristic polynomials are the same.
    have h_char_poly : M.charpoly = Matrix.charpoly (Matrix.diagonal (fun i => RCLike.ofReal (hM.eigenvalues i))) := by
      rcases h_diag with ⟨P, left, ⟨D, left_1, rfl⟩⟩
      rw [ ← left_1, Matrix.charpoly, Matrix.charpoly ];
      simp +decide [ Matrix.charmatrix, Matrix.mul_assoc ];
      -- Since $w$ is invertible, we can simplify the determinant.
      have h_inv : (P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * (P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) = 1 := by
        simp [ ← Matrix.map_mul, left ];
      -- Since $w$ is invertible, we can simplify the determinant using the fact that the determinant of a product is the product of the determinants.
      have h_det_prod : Matrix.det ((Matrix.diagonal (fun _ => Polynomial.X) - P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜) * (D.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜) * P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)))) = Matrix.det ((P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * (Matrix.diagonal (fun _ => Polynomial.X) - D.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * (P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜))) := by
        simp only [ mul_sub, sub_mul, Matrix.mul_assoc ];
        -- Since Matrix.diagonal (fun _ => Polynomial.X) is a scalar matrix, it commutes with any matrix.
        have h_comm : Matrix.diagonal (fun _ => Polynomial.X) * P⁻¹.map Polynomial.C = P⁻¹.map Polynomial.C * Matrix.diagonal (fun _ => Polynomial.X) := by
          ext i j; by_cases hi : i = j <;> simp [ hi ];
        simp only [ h_comm ];
        simp [ ← mul_assoc, h_inv ];
      rw [ h_det_prod, Matrix.det_mul, Matrix.det_mul ];
      -- Since the determinant of the product of two matrices is the product of their determinants, and the determinant of the identity matrix is 1, we have:
      have h_det_identity : Matrix.det (P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * Matrix.det (P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) = 1 := by
        rw [ ← Matrix.det_mul, h_inv, Matrix.det_one ];
      rw [ mul_right_comm, h_det_identity, one_mul ];
    rw [h_char_poly];
    simp [ Matrix.charpoly, Matrix.det_diagonal ];
  rw [ h_split, Polynomial.roots_multiset_prod ];
  -- Case 1
  · erw [ Multiset.bind_map ];
    aesop;
  -- Case 2
  · -- Since the eigenvalues are real, and we're working over the complex numbers (since 𝕜 is a real closed field), the polynomial X - C(e) would be zero only if e is zero. But if e is zero, then the polynomial would be X, which isn't zero. So 0 can't be in the multiset.
    simp [Polynomial.X_sub_C_ne_zero]

--These is disgusting atm. There's cleaner versions of them headed to Mathlib. See #29526 and follow-ups
theorem IsHermitian.cfc_eigenvalues {M : Matrix d d 𝕜} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    ∃ (e : d ≃ d), Matrix.IsHermitian.eigenvalues (cfc_predicate f M) = f ∘ hM.eigenvalues ∘ e := by
  have h_eigenvalues : Multiset.map hM.eigenvalues Finset.univ.val = Multiset.map (fun i => hM.eigenvalues i) Finset.univ.val := by
    rfl
  generalize_proofs at *;
  have h_eigenvalues_cfc : (IsHermitian.cfc hM f).charpoly.roots = Multiset.map (fun i => (f (hM.eigenvalues i) : 𝕜)) Finset.univ.val := by
    rw [ Matrix.IsHermitian.cfc, Matrix.charpoly ];
    -- Since $U$ is unitary, we have $U^* U = I$, and thus the characteristic polynomial of $U D U^*$ is the same as the characteristic polynomial of $D$.
    have h_charpoly : Matrix.det ((hM.eigenvectorUnitary : Matrix d d 𝕜) * Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues) * Star.star (hM.eigenvectorUnitary : Matrix d d 𝕜)).charmatrix = Matrix.det (Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues)).charmatrix := by
      -- Since $U$ is unitary, we have $U^* U = I$, and thus the characteristic polynomial of $U D U^*$ is the same as the characteristic polynomial of $D$ by the properties of determinants.
      have h_char_poly : ∀ (t : 𝕜), Matrix.det (t • 1 - (hM.eigenvectorUnitary : Matrix d d 𝕜) * Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues) * star (hM.eigenvectorUnitary : Matrix d d 𝕜)) = Matrix.det (t • 1 - Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues)) := by
        intro t;
        -- Since $U$ is unitary, we have $U^* U = I$, and thus the determinant of $tI - UDU^*$ is the same as the determinant of $tI - D$.
        have h_det : Matrix.det (t • 1 - (hM.eigenvectorUnitary : Matrix d d 𝕜) * Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues) * star (hM.eigenvectorUnitary : Matrix d d 𝕜)) = Matrix.det ((hM.eigenvectorUnitary : Matrix d d 𝕜) * (t • 1 - Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues)) * star (hM.eigenvectorUnitary : Matrix d d 𝕜)) := by
          simp [ mul_sub, sub_mul, mul_assoc ];
        rw [ h_det, Matrix.det_mul, Matrix.det_mul ];
        rw [ mul_right_comm, ← Matrix.det_mul, mul_comm ];
        norm_num +zetaDelta at *;
      refine' Polynomial.funext fun t => _;
      convert h_char_poly t using 1;
      · simp [ Matrix.det_apply', Polynomial.eval_finset_sum ];
        simp [ Matrix.one_apply, Polynomial.eval_prod ];
        congr! 3;
        aesop;
      · simp [ Matrix.det_apply', Polynomial.eval_finset_sum ];
        simp [ Matrix.one_apply, Polynomial.eval_prod ];
        exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;
    simp_all [ Matrix.charmatrix, Matrix.det_diagonal ];
    rw [ Polynomial.roots_prod ];
    · bound;
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _;
  have := IsHermitian.charpoly_roots_eq_eigenvalues (cfc_predicate f M);
  rw [← Matrix.IsHermitian.cfc_eq] at h_eigenvalues_cfc
  rw [ h_eigenvalues_cfc ] at this;
  simp [ Function.comp ] at this;
  rw [ Multiset.map_univ_eq_iff ] at this;
  obtain ⟨ e, he ⟩ := this;
  use e.symm
  ext x
  have := congr_fun he ( e.symm x );
  simp_all only [Function.comp_apply, Equiv.apply_symm_apply, algebraMap.coe_inj]


set_option maxHeartbeats 0 in
--Should be combined the above...? TODO Cleanup
/--
If a Hermitian matrix A is unitarily similar to a diagonal matrix with real entries f, then the eigenvalues of A are a permutation of f.
-/
lemma IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal {d 𝕜 : Type*}
    [Fintype d] [DecidableEq d] [RCLike 𝕜]
    {A : Matrix d d 𝕜} (hA : A.IsHermitian)
    {U : Matrix d d 𝕜} (hU : U ∈ Matrix.unitaryGroup d 𝕜)
    {f : d → ℝ}
    (h : A = U * Matrix.diagonal (fun i => (RCLike.ofReal (f i) : 𝕜)) * Matrix.conjTranspose U) :
    ∃ σ : d ≃ d, hA.eigenvalues ∘ σ = f := by
  -- Since A is unitarily similar to D, they have the same characteristic polynomial.
  have h_char_poly : Matrix.charpoly A = Matrix.charpoly (Matrix.diagonal fun i => (f i : 𝕜)) := by
    have h_char_poly : Matrix.charpoly (U * Matrix.diagonal (fun i => (f i : 𝕜)) * Uᴴ) = Matrix.charpoly (Matrix.diagonal (fun i => (f i : 𝕜))) := by
      have h_det : ∀ (t : 𝕜), Matrix.det (t • 1 - U * Matrix.diagonal (fun i => (f i : 𝕜)) * Uᴴ) = Matrix.det (t • 1 - Matrix.diagonal (fun i => (f i : 𝕜))) := by
        intro t
        have h_det : Matrix.det (t • 1 - U * Matrix.diagonal (fun i => (f i : 𝕜)) * Uᴴ) = Matrix.det (U * (t • 1 - Matrix.diagonal (fun i => (f i : 𝕜))) * Uᴴ) := by
          simp [ mul_sub, sub_mul, Matrix.mul_assoc ];
          rw [ show U * Uᴴ = 1 from by simpa [ Matrix.mul_eq_one_comm ] using hU.2 ];
        have := congr_arg Matrix.det hU.2; norm_num at this; simp_all [ mul_assoc, mul_comm ] ;
        simp_all [ ← mul_assoc ];
        simp_all [ Star.star ]
      refine' Polynomial.funext fun t => _;
      convert h_det t using 1 <;> simp [ Matrix.charpoly, Matrix.det_apply' ];
      · simp [ Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod, Matrix.one_apply ];
        exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;
      · simp [ Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod, Matrix.one_apply ];
        exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;
    rw [ h, h_char_poly ];
  -- The roots of the characteristic polynomial of A are its eigenvalues (by `IsHermitian.charpoly_roots_eq_eigenvalues`).
  have h_eigenvalues : (Matrix.charpoly A).roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val := by
    exact Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hA;
  -- The roots of the characteristic polynomial of D are the diagonal entries f.
  have h_diag_roots : (Matrix.charpoly (Matrix.diagonal fun i => (f i : 𝕜))).roots = Multiset.map (fun i => (f i : 𝕜)) Finset.univ.val := by
    simp [ Matrix.charpoly, Matrix.det_diagonal ];
    rw [ Polynomial.roots_prod ];
    · aesop;
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _;
  have := Multiset.map_univ_eq_iff ( RCLike.ofReal ∘ hA.eigenvalues ) f
  subst h
  simp_all only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, CompTriple.comp_eq]
  refine' this.mp _ |> fun ⟨ e, he ⟩ => ⟨ e.symm, _ ⟩
  · simpa [ Function.comp ] using congr_arg ( Multiset.map ( RCLike.re : 𝕜 → ℝ ) ) h_eigenvalues.symm
  · exact funext fun x => by simpa using congr_fun he ( e.symm x ) ;

end eigenvalues

section

variable {α n : Type*} [RCLike α] [Fintype n] [DecidableEq n]

@[simp]
theorem toEuclideanLin_one : Matrix.toEuclideanLin (1 : Matrix n n α) = .id := by
  ext1 x
  simp [Matrix.toEuclideanLin]

end

section more_cfc

open ComplexOrder

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]

@[simp]
theorem cfc_diagonal (g : d → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun x ↦ (g x : 𝕜))) = diagonal (RCLike.ofReal ∘ f ∘ g) := by
  --Thanks Aristotle
  have h_self_adjoint : _root_.IsSelfAdjoint (diagonal (fun x => (g x : 𝕜))) := by
      change Matrix.conjTranspose _ = _
      simp [Matrix.conjTranspose]
  --TODO cfc_cont_tac
  rw [cfc, dif_pos ⟨h_self_adjoint, continuousOn_iff_continuous_restrict.mpr <| by fun_prop⟩]
  rw [cfcHom_eq_of_continuous_of_map_id]
  rotate_left
  · refine' { .. }
    use fun f ↦ Matrix.diagonal fun x ↦ f ⟨g x, (by
      simpa [algebraMap_eq_diagonal, diagonal_apply] using
        congr_arg (· x x) ·.exists_left_inv.choose_spec
      )⟩
    · simp
    · simp [diagonal, ← Matrix.ext_iff, mul_apply]
      grind
    · simp
    · simp [diagonal, funext_iff]
      grind [add_zero]
    · simp [← ext_iff, diagonal]
      exact fun r i j ↦ rfl
    · simp [← ext_iff, diagonal]
      grind [RCLike.conj_ofReal, map_zero]
  · dsimp [diagonal]
    continuity
  · simp [diagonal]
  · simp [diagonal]

theorem PosSemidef.pos_of_mem_spectrum {A : Matrix d d 𝕜} (hA : A.PosSemidef) (r : ℝ) :
    r ∈ spectrum ℝ A → 0 ≤ r := by
  intro hr
  rw [hA.left.spectrum_real_eq_range_eigenvalues] at hr
  rcases hr with ⟨i, rfl⟩
  exact hA.eigenvalues_nonneg i

theorem PosSemidef.pow_add {A : Matrix d d 𝕜} (hA : A.PosSemidef) {x y : ℝ} (hxy : x + y ≠ 0) :
    cfc (· ^ (x + y) : ℝ → ℝ) A = cfc (fun r ↦ r ^ x * r ^ y : ℝ → ℝ) A := by
  refine cfc_congr fun r hr ↦ ?_
  exact Real.rpow_add' (hA.pos_of_mem_spectrum r hr) hxy

theorem PosSemidef.pow_mul {A : Matrix d d 𝕜} {x y : ℝ} (hA : A.PosSemidef) :
    cfc (· ^ (x * y) : ℝ → ℝ) A = cfc (fun r ↦ (r ^ x) ^ y : ℝ → ℝ) A := by
  refine cfc_congr fun r hr ↦ ?_
  exact Real.rpow_mul (hA.pos_of_mem_spectrum r hr) x y

end more_cfc

section subm

variable {α : Type*} [AddCommMonoid α]
variable {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂]

@[simp]
theorem trace_submatrix
  (A : Matrix d₁ d₁ α) (e : d₂ ≃ d₁) :
    (A.submatrix e e).trace = A.trace := by
  simpa [Matrix.trace] using e.sum_comp (fun x ↦ A x x)

end subm

section spectrum_kron

--This is really really ugly, and already *after* trying to clean it up a bit.
set_option maxHeartbeats 7200000

open Kronecker
open scoped Pointwise

private lemma spectrum_prod_complex {d d₂ : Type*}
  [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
  {A : Matrix d d 𝕜} {B : Matrix d₂ d₂ 𝕜}
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∀ x : 𝕜, x ∈ spectrum 𝕜 (A ⊗ₖ B) → ∃ a ∈ spectrum 𝕜 A, ∃ b ∈ spectrum 𝕜 B, x = a * b := by
  intro x hx
  have h_det : Matrix.det (A ⊗ₖ B - x • 1) = 0 := by
    rw [ spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det ] at hx;
    rw [ ← neg_sub, Matrix.det_neg ]
    simp_all only [isUnit_iff_ne_zero, ne_eq, Decidable.not_not, Fintype.card_prod,
      mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, not_or, false_and, false_or]
    convert hx using 1;
    congr! 1;
    ext ⟨ i, j ⟩ ⟨ i', j' ⟩;
    simp [ Algebra.smul_def ]
  -- Since $A$ and $B$ are Hermitian, they are diagonalizable. Let $P$ and $Q$ be unitary matrices such that $P^*AP$ and $Q^*BQ$ are diagonal.
  obtain ⟨P, hP₁, ⟨D, hD⟩⟩ : ∃ P : Matrix d d 𝕜, P.det ≠ 0 ∧ ∃ D : Matrix d d 𝕜, D.IsDiag ∧ P⁻¹ * A * P = D := by
    refine' ⟨ hA.eigenvectorUnitary, _, Matrix.diagonal ( RCLike.ofReal ∘ hA.eigenvalues ), _, _ ⟩;
    · intro h_det_zero;
      exact absurd h_det_zero <| isUnit_iff_ne_zero.mp <| UnitaryGroup.det_isUnit hA.eigenvectorUnitary
    · exact isDiag_diagonal (RCLike.ofReal ∘ hA.eigenvalues);
    · -- Since $U$ is unitary, $U⁻¹ = U*$, and thus $U⁻¹ * U = I$.
      have h_unitary : (hA.eigenvectorUnitary : Matrix d d 𝕜)⁻¹ = star (hA.eigenvectorUnitary : Matrix d d 𝕜) := by
        rw [ Matrix.inv_eq_left_inv ];
        simp
      -- Substitute h_unitary into the equation.
      rw [h_unitary];
      exact Matrix.IsHermitian.star_mul_self_mul_eq_diagonal hA
  obtain ⟨Q, hQ₁, ⟨E, hE⟩⟩ : ∃ Q : Matrix d₂ d₂ 𝕜, Q.det ≠ 0 ∧ ∃ E : Matrix d₂ d₂ 𝕜, E.IsDiag ∧ Q⁻¹ * B * Q = E := by
    have := Matrix.IsHermitian.spectral_theorem hB;
    -- By the spectral theorem, since B is Hermitian, there exists a unitary matrix Q and a diagonal matrix D such that B = Q * D * Q⁻¹.
    obtain ⟨Q, hQ_unitary, D, hD_diag, hQ⟩ : ∃ Q : Matrix d₂ d₂ 𝕜, Q.det ≠ 0 ∧ ∃ D : Matrix d₂ d₂ 𝕜, D.IsDiag ∧ B = Q * D * Q⁻¹ := by
      refine' ⟨ hB.eigenvectorUnitary, _, Matrix.diagonal ( RCLike.ofReal ∘ hB.eigenvalues ), _, _ ⟩;
      · intro h_det_zero;
        -- Since the eigenvector unitary matrix is unitary, its determinant is non-zero.
        have h_unitary_det : ∀ (U : Matrix d₂ d₂ 𝕜), U * star U = 1 → U.det ≠ 0 :=
          fun U hU => Matrix.det_ne_zero_of_right_inverse hU;
        exact h_unitary_det _ ( by simp) h_det_zero;
      · exact isDiag_diagonal (RCLike.ofReal ∘ hB.eigenvalues);
      · convert this using 1;
        rw [ Matrix.inv_eq_left_inv ];
        simp
    refine ⟨ Q, hQ_unitary, D, hD_diag, ?_ ⟩
    simp [ hQ, mul_assoc, hQ_unitary, isUnit_iff_ne_zero ];
  -- Then $(P \otimes Q)^{-1}(A \otimes B)(P \otimes Q) = D \otimes E$, where $D$ and $E$ are diagonal matrices.
  have h_diag : (P.kronecker Q)⁻¹ * (A ⊗ₖ B) * (P.kronecker Q) = D ⊗ₖ E := by
    -- Using the properties of the Kronecker product and the fact that $P$ and $Q$ are invertible, we can simplify the expression.
    have h_kronecker : (P.kronecker Q)⁻¹ * (A.kronecker B) * (P.kronecker Q) = (P⁻¹ * A * P).kronecker (Q⁻¹ * B * Q) := by
      have h_kronecker : ∀ (X Y : Matrix d d 𝕜) (Z W : Matrix d₂ d₂ 𝕜), (X.kronecker Z) * (Y.kronecker W) = (X * Y).kronecker (Z * W) := by
        intro X Y Z W; ext i j; simp [ Matrix.mul_apply ] ;
        simp only [mul_left_comm, mul_comm, Finset.mul_sum _ _ _];
        exact Fintype.sum_prod_type_right _
      rw [Matrix.inv_eq_right_inv, h_kronecker, h_kronecker];
      convert h_kronecker P P⁻¹ Q Q⁻¹ using 1;
      simp [ hP₁, hQ₁, isUnit_iff_ne_zero ];
    aesop;
  -- Since $D$ and $E$ are diagonal matrices, the determinant of $(D \otimes E - xI)$ is the product of the determinants of $(D - xI)$ and $(E - xI)$.
  have h_det_diag : Matrix.det (D ⊗ₖ E - x • 1) = 0 := by
    have h_det_diag : Matrix.det ((P.kronecker Q)⁻¹ * (A ⊗ₖ B - x • 1) * (P.kronecker Q)) = Matrix.det (D ⊗ₖ E - x • 1) := by
      simp [ ← h_diag, mul_sub, sub_mul ];
      simp [ Matrix.det_kronecker, hP₁, hQ₁ ];
    simp_all [ Matrix.det_mul ];
  -- Since $D$ and $E$ are diagonal matrices, the determinant of $(D \otimes E - xI)$ is the product of the determinants of $(D - xI)$ and $(E - xI)$. Therefore, there must be some $i$ and $j$ such that $D_{ii} * E_{jj} = x$.
  obtain ⟨i, j, hij⟩ : ∃ i : d, ∃ j : d₂, D i i * E j j = x := by
    contrapose! h_det_diag;
    have h_det_diag : Matrix.det (D ⊗ₖ E - x • 1) = ∏ i : d, ∏ j : d₂, (D i i * E j j - x) := by
      have h_det_diag : Matrix.det (D ⊗ₖ E - x • 1) = Matrix.det (Matrix.diagonal (fun p : d × d₂ => D p.1 p.1 * E p.2 p.2 - x)) := by
        congr with p q
        simp_all only [ne_eq, kronecker, sub_apply,
          kroneckerMap_apply, smul_apply, smul_eq_mul]
        obtain ⟨fst, snd⟩ := p
        obtain ⟨fst_1, snd_1⟩ := q
        obtain ⟨left, rfl⟩ := hD
        obtain ⟨left_1, rfl⟩ := hE
        simp_all only
        by_cases h : fst = fst_1 <;> by_cases h' : snd = snd_1 <;> simp [ h, h', Matrix.one_apply ];
        · exact Or.inr ( left_1 ( by aesop ) );
        · exact Or.inl ( left h );
        · exact Or.inl ( left h );
      simp_all [ Matrix.det_diagonal ];
      exact Fintype.prod_prod_type fun (x_2 : d × d₂) => D x_2.1 x_2.1 * E x_2.2 x_2.2 - x
    exact h_det_diag.symm ▸ Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero_of_ne <| by solve_by_elim;
  refine' ⟨ D i i, _, E j j, _, _ ⟩
  · simp_all [ spectrum.mem_iff ];
    simp_all [ Matrix.isUnit_iff_isUnit_det ];
    have h_det_diag : Matrix.det (P⁻¹ * (D i i • 1 - A) * P) = 0 := by
      simp_all [ mul_sub, sub_mul, mul_assoc ];
      rw [ Matrix.det_eq_zero_of_row_eq_zero i ]
      intro j_1
      subst hij
      simp_all only [map_mul, sub_apply, smul_apply, smul_eq_mul]
      obtain ⟨left, rfl⟩ := hD
      obtain ⟨left_1, rfl⟩ := hE
      by_cases hij : i = j_1 <;> simp_all [ Matrix.one_apply ];
      exact left hij;
    simp_all [ Matrix.det_mul];
    convert h_det_diag using 1;
    exact congr_arg Matrix.det ( by ext i j; by_cases hi : i = j <;> simp [ hi, Algebra.smul_def ] );
  · simp_all [ spectrum.mem_iff ];
    -- Since $E$ is diagonal, $E j j - B$ is singular, hence not invertible.
    have h_singular : Matrix.det (E j j • 1 - B) = 0 := by
      have h_singular : Matrix.det (Q⁻¹ * (E j j • 1 - B) * Q) = 0 := by
        simp [ mul_sub, sub_mul, hE.2 ];
        rw [ Matrix.det_eq_zero_of_row_eq_zero j ]
        intro j_1
        subst hij
        simp_all only [map_mul, isUnit_iff_ne_zero, ne_eq, not_false_eq_true, nonsing_inv_mul, sub_apply,
          smul_apply, smul_eq_mul]
        obtain ⟨left, rfl⟩ := hD
        obtain ⟨left_1, rfl⟩ := hE
        by_cases h : j = j_1 <;> aesop;
      simp_all [ Matrix.det_mul ];
    simp_all [ Matrix.isUnit_iff_isUnit_det ];
    convert h_singular using 1;
    simp [ Algebra.smul_def ];
  · simp_all [ spectrum.mem_iff ];

private lemma spectrum_prod_le {d d₂ : Type*}
  [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
  {A : Matrix d d 𝕜} {B : Matrix d₂ d₂ 𝕜}
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
    spectrum ℝ (A ⊗ₖ B) ⊆ spectrum ℝ A * spectrum ℝ B := by
  intro x hx
  suffices h : ∃ a ∈ spectrum ℝ A, ∃ b ∈ spectrum ℝ B, x = a * b by
    rcases h with ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  obtain ⟨_, ha, _, hb, h₁, ⟨a', rfl⟩, ⟨b', rfl⟩⟩ : ∃ a ∈ spectrum 𝕜 A, ∃ b ∈ spectrum 𝕜 B,
      x = a * b ∧
      a ∈ Set.range (algebraMap ℝ 𝕜) ∧ b ∈ Set.range (algebraMap ℝ 𝕜) := by
    obtain ⟨a, ha, b, hb, hx_eq⟩ := spectrum_prod_complex hA hB x (by convert hx using 1);
    have ha' := ha
    have hb' := hb
    rw [hA.spectrum_eq_image_range] at ha
    rw [hB.spectrum_eq_image_range] at hb
    grind
  use a', ha, b', hb
  simp only [RCLike.algebraMap_eq_ofReal] at h₁
  exact_mod_cast h₁

set_option maxHeartbeats 800000
open Kronecker in
open scoped Pointwise in
theorem spectrum_prod {d d₂ : Type*}
  [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
  {A : Matrix d d 𝕜} {B : Matrix d₂ d₂ 𝕜}
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
    spectrum ℝ (A ⊗ₖ B) = spectrum ℝ A * spectrum ℝ B := by
  apply subset_antisymm
  · exact spectrum_prod_le hA hB
  · rintro x ⟨ y, hy, z, hz, rfl ⟩;
    -- Since $y$ is an eigenvalue of $A$ and $z$ is an eigenvalue of $B$, there exist eigenvectors $v$ and $w$ such that $A*v = y*v$ and $B*w = z*w$.
    obtain ⟨v, hv⟩ : ∃ v : d → 𝕜, v ≠ 0 ∧ A.mulVec v = y • v := by
      rw [ spectrum.mem_iff ] at hy;
      simp_all [ Matrix.isUnit_iff_isUnit_det ];
      have := Matrix.exists_mulVec_eq_zero_iff.mpr hy;
      simp_all [ funext_iff, Matrix.mulVec, dotProduct ];
      simp_all [ sub_mul, Matrix.one_apply, Algebra.algebraMap_eq_smul_one ];
      exact ⟨ this.choose, this.choose_spec.1, fun x => by linear_combination -this.choose_spec.2 x ⟩
    obtain ⟨w, hw⟩ : ∃ w : d₂ → 𝕜, w ≠ 0 ∧ B.mulVec w = z • w := by
      rw [ spectrum.mem_iff ] at hz;
      simp_all [ Matrix.isUnit_iff_isUnit_det ];
      have := Matrix.exists_mulVec_eq_zero_iff.mpr hz;
      simp_all [ Matrix.sub_mulVec ];
      obtain ⟨ w, hw, hw' ⟩ := this; use w; simp_all [ sub_eq_zero, Algebra.algebraMap_eq_smul_one ] ;
      simp_all [ funext_iff, Matrix.mulVec, dotProduct ];
      simp_all [ Matrix.one_apply];
    refine' spectrum.mem_iff.mpr _;
    -- Consider the vector $v \otimes w$.
    set v_tensor_w : (d × d₂) → 𝕜 := fun p => v p.1 * w p.2;
    -- We need to show that $v \otimes w$ is an eigenvector of $A \otimes B$ with eigenvalue $yz$.
    have h_eigenvector : (Matrix.kroneckerMap (· * ·) A B).mulVec v_tensor_w = (y * z) • v_tensor_w := by
      ext ⟨ i, j ⟩ ;
      simp [ Matrix.mulVec, dotProduct] at *
      simp [ funext_iff, Matrix.mulVec, dotProduct ] at hv hw ⊢
      erw [ Finset.sum_product ]
      simp_all only [v_tensor_w]
      obtain ⟨left, right⟩ := hv
      obtain ⟨left_1, right_1⟩ := hw
      -- By separating the sums, we can apply the given equalities.
      have h_separate : ∑ x, ∑ x_1, A i x * B j x_1 * (v x * w x_1) = (∑ x : d, A i x * v x) * (∑ x_1 : d₂, B j x_1 * w x_1) := by
        simp only [mul_left_comm, mul_comm, Finset.mul_sum _ _ _];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      rw [ h_separate, right, right_1 ]
      simp [RCLike.real_smul_eq_coe_mul]
      ring_nf
    -- Since $v \otimes w$ is an eigenvector of $A \otimes B$ with eigenvalue $yz$, we have $(A \otimes B - yzI)(v \otimes w) = 0$.
    have h_eigenvector_zero : ((A ⊗ₖ B) - (y * z) • 1) *ᵥ v_tensor_w = 0 := by
      simp [ h_eigenvector, Matrix.sub_mulVec ];
      simp [ Matrix.mulVec, funext_iff ];
      simp [ Matrix.one_apply, dotProduct ];
    -- Since $v \otimes w$ is non-zero, we have $(A \otimes B - yzI)(v \otimes w) = 0$ implies that $A \otimes B - yzI$ is not invertible.
    have h_not_invertible : ¬IsUnit (A ⊗ₖ B - (y * z) • 1) := by
      simp only [ne_eq, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Decidable.not_not, v_tensor_w] at *
      rw [ ← Matrix.exists_mulVec_eq_zero_iff ]
      refine' ⟨ v_tensor_w, _, h_eigenvector_zero ⟩;
      simp [ funext_iff ] at hv hw ⊢
      obtain ⟨left, right⟩ := hv
      obtain ⟨left_1, right_1⟩ := hw
      exact ⟨left.choose, left_1.choose, mul_ne_zero left.choose_spec left_1.choose_spec⟩
    rw [← IsUnit.neg_iff, neg_sub]
    convert h_not_invertible using 4
    simp [ Algebra.smul_def ]

end spectrum_kron

open ComplexOrder in
open MatrixOrder in
theorem PosDef.zero_lt {n : Type*} [Nonempty n] [Fintype n] {A : Matrix n n ℂ} (hA : A.PosDef) : 0 < A := by
  apply lt_of_le_of_ne
  · replace hA := hA.posSemidef
    rwa [Matrix.nonneg_iff_posSemidef]
  · rintro rfl
    --wtf do better. TODO
    have : ¬(0 < 0) := by trivial
    classical rw [← Matrix.posDef_natCast_iff (n := n) (R := ℂ)] at this
    revert hA
    convert this
    ext; simp
    trans ((0 : ℕ) : ℂ)
    · simp
    classical
    change _ = ite _ _ _
    simp


lemma IsHermitian.spectrum_eq_image_eigenvalues [Fintype n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    spectrum ℝ A = Finset.univ.image hA.eigenvalues := by
  simpa using hA.spectrum_real_eq_range_eigenvalues

/- This lemma looks "wrong" in the sense that it's specifically about `Fintype.card foo = Finset.card bar`,
why not just use the underyling fact `foo = ↑bar`? It turns out this actually gives annoying issues
with dependent rewrites, given the necessary `Fintype` instance. Using the above theorem for example,
trying `rw [hA.spectrum_eq_image_eigenvalues]` fails because of dependent types. -/
lemma IsHermitian.card_spectrum_eq_image [Fintype n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
  [Fintype (spectrum ℝ A)] :
    Fintype.card (spectrum ℝ A) = (Finset.univ.image hA.eigenvalues).card := by
  trans (Set.univ.image hA.eigenvalues).toFinset.card
  · symm
    convert Set.toFinset_card _
    rw [Set.image_univ]
    exact Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hA
  · simp

section iInf_iSup
namespace IsHermitian

variable {d : Type*} [Fintype d] [DecidableEq d] {A B : Matrix d d ℂ}

open ComplexOrder

lemma sub_iInf_eignevalues (hA : A.IsHermitian) :
    (A - iInf hA.eigenvalues • 1).PosSemidef := by
  constructor
  · simpa [ Matrix.IsHermitian, sub_eq_add_neg ] using hA
  · intro x
    have h_eigenvalue : ∀ i, hA.eigenvalues i ≥ iInf hA.eigenvalues := by
      -- By definition of infimum, for any eigenvalue $i$, we have $hA.eigenvalues i \geq iInf hA.eigenvalues$.
      intros i
      apply le_of_forall_le
      intro j a
      exact le_trans a (ciInf_le ( Finite.bddBelow_range hA.eigenvalues ) i );
    -- Since $A$ is Hermitian, we can diagonalize it as $A = Q \Lambda Q^*$, where $Q$ is unitary and $\Lambda$ is diagonal with the eigenvalues on the diagonal.
    obtain ⟨Q, Λ, hQ, hΛ⟩ : ∃ Q : Matrix d d ℂ, ∃ Λ : d → ℂ, Q.conjTranspose * Q = 1 ∧ A = Q * Matrix.diagonal Λ * Q.conjTranspose ∧ ∀ i, Λ i = Matrix.IsHermitian.eigenvalues hA i := by
      have := hA.spectral_theorem;
      refine' ⟨ _, _, _, this, _ ⟩;
      · simp [ ← Matrix.ext_iff ];
        intro i j; erw [ Matrix.mul_apply ] ; simp [ Matrix.one_apply ] ;
        have := hA.eigenvectorBasis.orthonormal;
        rw [ orthonormal_iff_ite ] at this;
        rw [← this i j]
        simp [PiLp.inner_apply, mul_comm]
      · simp
    -- Since $Q$ is unitary, we have $Q^* Q = I$, and thus $Q^* (A - \lambda_{\min} I) Q = \Lambda - \lambda_{\min} I$.
    have h_diag : Q.conjTranspose * (A - (iInf (Matrix.IsHermitian.eigenvalues hA)) • 1) * Q = Matrix.diagonal (fun i => Λ i - (iInf (Matrix.IsHermitian.eigenvalues hA))) := by
      simp [ hΛ, mul_sub, sub_mul, mul_assoc, hQ ];
      simp [ ← mul_assoc, hQ];
      ext i j ; by_cases hij : i = j <;> aesop;
    -- Since $Q$ is unitary, we have $Q^* (A - \lambda_{\min} I) Q = \Lambda - \lambda_{\min} I$, and thus $x^* (A - \lambda_{\min} I) x = (Q^* x)^* (\Lambda - \lambda_{\min} I) (Q^* x)$.
    have h_quad_form : Star.star x ⬝ᵥ (A - (iInf (Matrix.IsHermitian.eigenvalues hA)) • 1).mulVec x = Star.star (Q.conjTranspose.mulVec x) ⬝ᵥ (Matrix.diagonal (fun i => Λ i - (iInf (Matrix.IsHermitian.eigenvalues hA)))).mulVec (Q.conjTranspose.mulVec x) := by
      rw [ ← h_diag ];
      simp [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.mul_eq_one_comm.mp hQ];
      simp only [mulVec_conjTranspose, star_star, vecMul_vecMul];
      rw [ ← Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp hQ, one_mul ];
    simp_all only [ge_iff_le, dotProduct, Pi.star_apply, RCLike.star_def, mulVec, sub_apply,
      smul_apply, Complex.real_smul, conjTranspose_apply, star_sum, star_mul',
      RingHomCompTriple.comp_apply, RingHom.id_apply];
    simp_all only [implies_true, and_self, diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, ↓reduceIte];
    -- Since the eigenvalues are real and the sums involving Q and x are complex, the product of a complex number and its conjugate is non-negative.
    have h_nonneg : ∀ i, 0 ≤ (∑ x_2, Q x_2 i * star (x x_2)) * (∑ x_2, star (Q x_2 i) * x x_2) := by
      intro i
      have h_nonneg : 0 ≤ (∑ x_2, Q x_2 i * star (x x_2)) * star (∑ x_2, Q x_2 i * star (x x_2)) := by
        exact mul_star_self_nonneg (∑ x_2, Q x_2 i * star (x x_2))
      convert h_nonneg using 1;
      simp [ mul_comm, Finset.mul_sum _ _ _];
    -- Since each term in the sum is a product of a non-negative number and a non-negative eigenvalue difference, the entire sum is non-negative.
    have h_sum_nonneg : ∀ i, 0 ≤ (∑ x_2, Q x_2 i * star (x x_2)) * (((↑(hA.eigenvalues i) : ℂ) - (↑(iInf hA.eigenvalues) : ℂ)) * ∑ x_2, star (Q x_2 i) * x x_2) := by
      intro i
      specialize h_nonneg i
      simp_all only [mul_assoc, mul_comm, mul_left_comm, RCLike.star_def] ;
      rw [ ← mul_assoc ];
      exact mul_nonneg h_nonneg ( sub_nonneg_of_le <| mod_cast h_eigenvalue i );
    convert Finset.sum_nonneg fun i _ => h_sum_nonneg i;
    rw [ hΛ.1 ]

lemma iInf_eigenvalues_le_dotProduct_mulVec (hA : A.IsHermitian) (v : d → ℂ) :
    iInf hA.eigenvalues * (star v ⬝ᵥ v) ≤ star v ⬝ᵥ A *ᵥ v := by
  conv_lhs =>
    equals (star v ⬝ᵥ (iInf hA.eigenvalues • 1) *ᵥ v) =>
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, mul_comm, mulVec]
      simp [Matrix.one_apply, mul_assoc, mul_left_comm, Finset.mul_sum]
  rw [← sub_nonneg, ← dotProduct_sub, ← Matrix.sub_mulVec]
  exact (sub_iInf_eignevalues hA).right v

lemma iInf_eigenvalues_le_of_posSemidef
  (hAB : (B - A).PosSemidef) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    iInf hA.eigenvalues ≤ iInf hB.eigenvalues := by
  rcases isEmpty_or_nonempty d
  · simp
  contrapose! hAB
  rw [PosSemidef]
  push_neg
  intro _
  apply exists_lt_of_ciInf_lt at hAB
  rcases hAB with ⟨i, hi⟩
  use WithLp.ofLp (hB.eigenvectorBasis i)
  simp only [sub_mulVec, dotProduct_sub, sub_nonneg]
  rw [hB.mulVec_eigenvectorBasis i]
  simp only [dotProduct_smul, Complex.real_smul]
  nth_rw 2 [dotProduct_comm]
  rw [← EuclideanSpace.inner_eq_star_dotProduct]
  intro h
  replace h := (iInf_eigenvalues_le_dotProduct_mulVec hA _).trans h
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [OrthonormalBasis.inner_eq_one, mul_one, Complex.real_le_real] at h
  order

open MatrixOrder in
lemma iInf_eigenvalues_le (hAB : A ≤ B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    iInf hA.eigenvalues ≤ iInf hB.eigenvalues :=
  iInf_eigenvalues_le_of_posSemidef hAB hA hB

open MatrixOrder in
lemma iInf_eigenvalues_smul_one_le (hA : A.IsHermitian) : iInf hA.eigenvalues • 1 ≤ A :=
  (PosSemidef.smul_one_le_of_eigenvalues_iff hA (iInf hA.eigenvalues)).mp
    (ciInf_le (Finite.bddBelow_range _))

end IsHermitian
end iInf_iSup

section matrix_order

--Shortcut instances. Having these around speeds things out considerably, in some cases?
open MatrixOrder

variable {d : Type*} [Fintype d]

lemma _shortcut_posSMulMono : PosSMulMono ℝ (Matrix d d ℂ) :=
  inferInstance

lemma _shortcut_posSmulReflectLE : PosSMulReflectLE ℝ (Matrix d d ℂ) :=
  inferInstance

scoped[MatrixOrder] attribute [instance] Matrix._shortcut_posSMulMono
scoped[MatrixOrder] attribute [instance] Matrix._shortcut_posSmulReflectLE

end matrix_order

open ComplexOrder in
theorem IsHermitian.spectrum_subset_Ici_of_sub {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A x : Matrix d d 𝕜} (hA : A.IsHermitian) (hl : (x - A).PosSemidef) :
    spectrum ℝ x ⊆ Set.Ici (⨅ i, hA.eigenvalues i) := by
  --Thanks Aristotle
  intro μ hμ
  obtain ⟨v, hv₁, hv₂⟩ : ∃ v : d → 𝕜, v ≠ 0 ∧ x.mulVec v = μ • v := by
    have h_singular : ∃ v : d → 𝕜, v ≠ 0 ∧ (μ • 1 - x).mulVec v = 0 := by
      simp only [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq, Decidable.not_not] at hμ
      convert Matrix.exists_mulVec_eq_zero_iff.mpr hμ;
      simp [Algebra.smul_def]
    refine h_singular.imp fun v h ↦ ⟨h.left, ?_⟩
    simp_all [Matrix.sub_mulVec, sub_eq_iff_eq_add, funext_iff, Matrix.mulVec, dotProduct, Matrix.one_apply]
  -- Since $x - A$ is positive semidefinite, for any eigenvalue $\lambda$ of $x$, we have $\lambda \geq \min(\text{eigenvalues of } A)$.
  have h_lower_bound : ∀ (v : d → 𝕜), v ≠ 0 → (star v ⬝ᵥ (x.mulVec v)) ≥ (⨅ i, (hA.eigenvalues i)) * (star v ⬝ᵥ v) := by
    intro v hv_nonzero
    have h_eigenvalue : (star v ⬝ᵥ (A.mulVec v)) ≥ (⨅ i, (hA.eigenvalues i)) * (star v ⬝ᵥ v) := by
      have h_expand : (star v ⬝ᵥ (A.mulVec v)) = ∑ i, (hA.eigenvalues i) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) := by
        change (star v ⬝ᵥ (A.mulVec v)) = ∑ i, (hA.eigenvalues i) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i))
        have h_decomp : A = ∑ i, (hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k)))) := by
          convert Matrix.IsHermitian.spectral_theorem hA using 1;
          ext i j
          simp only [RCLike.star_def, Matrix.smul_of, Matrix.sum_apply, Matrix.of_apply,
            Pi.smul_apply, Matrix.diagonal, Function.comp_apply, Matrix.mul_apply,
            Matrix.IsHermitian.eigenvectorUnitary_apply, PiLp.ofLp_apply, mul_ite, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.star_apply];
          simp [ mul_comm, mul_left_comm, Algebra.smul_def ]
        -- Substitute the decomposition of $A$ into the expression $(star v ⬝ᵥ (A.mulVec v))$.
        have h_subst : (star v ⬝ᵥ (A.mulVec v)) = ∑ i, (hA.eigenvalues i) * (star v ⬝ᵥ (Matrix.mulVec (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k)))) v)) := by
          -- Substitute the decomposition of $A$ into the expression $(star v ⬝ᵥ (A.mulVec v))$ and use the linearity of matrix multiplication.
          have h_subst : (star v ⬝ᵥ (A.mulVec v)) = (star v ⬝ᵥ ((∑ i, (hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k))))).mulVec v)) := by
            rw [ ← h_decomp ];
          -- By the linearity of matrix multiplication and the dot product, we can distribute the sum over the dot product.
          have h_distribute : (star v ⬝ᵥ (∑ i, (hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k))))).mulVec v) = ∑ i, (star v ⬝ᵥ ((hA.eigenvalues i) • (Matrix.of (fun j k => (hA.eigenvectorBasis i j) * (star (hA.eigenvectorBasis i k))))).mulVec v) := by
            -- By the linearity of matrix multiplication and the dot product, we can distribute the sum over the dot product. This follows from the fact that matrix multiplication is linear.
            have h_distribute : ∀ (M N : Matrix d d 𝕜) (v : d → 𝕜), Star.star v ⬝ᵥ (M + N).mulVec v = Star.star v ⬝ᵥ M.mulVec v + Star.star v ⬝ᵥ N.mulVec v := by
              simp [ Matrix.add_mulVec, dotProduct_add ];
            -- By induction on the number of terms in the sum, we can apply the distributive property repeatedly.
            have h_induction : ∀ (n : ℕ) (M : Fin n → Matrix d d 𝕜) (v : d → 𝕜), Star.star v ⬝ᵥ (∑ i, M i).mulVec v = ∑ i, Star.star v ⬝ᵥ (M i).mulVec v := by
              intro n M v
              induction n
              · simp [*]
              · simp [Fin.sum_univ_succ, *]
            convert h_induction ( Fintype.card d ) ( fun i => Matrix.of ( hA.eigenvalues ( Fintype.equivFin d |>.symm i ) • fun j k => hA.eigenvectorBasis ( Fintype.equivFin d |>.symm i ) j * starRingEnd 𝕜 ( hA.eigenvectorBasis ( Fintype.equivFin d |>.symm i ) k ) ) ) v using 1;
            · rw [ ← Equiv.sum_comp ( Fintype.equivFin d ) ];
              simp [ Fintype.equivFin ];
            · rw [ ← Equiv.sum_comp ( Fintype.equivFin d ) ];
              simp [ Fintype.equivFin ];
          convert h_distribute using 1;
          simp only [dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec, Matrix.of_apply,
            Finset.mul_sum _ _ _, Matrix.smul_apply, Algebra.smul_mul_assoc,
            Algebra.mul_smul_comm];
          simp [ Algebra.smul_def ];
        convert h_subst using 2;
        simp only [dotProduct, Pi.star_apply, RCLike.star_def, mul_comm, mul_assoc, Matrix.mulVec,
          Matrix.of_apply, mul_eq_mul_left_iff, map_eq_zero];
        simp [ mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      -- Since $\lambda_i \geq \inf(\text{eigenvalues of } A)$ for all $i$, we can bound each term in the sum.
      have h_bound : ∀ i, (hA.eigenvalues i) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) ≥ (⨅ i, (hA.eigenvalues i)) * (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) := by
        intro i
        have h_eigenvalue_bound : (hA.eigenvalues i) ≥ (⨅ i, (hA.eigenvalues i)) :=
          ciInf_le (Set.finite_range _).bddBelow _
        -- Since the product of the inner products is real and non-negative, multiplying both sides of the inequality by this product preserves the inequality.
        have h_nonneg : 0 ≤ (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) := by
          -- Since the inner product is conjugate symmetric, we have star v ⬝ᵥ (hA.eigenvectorBasis i) = conjugate(star (hA.eigenvectorBasis i) ⬝ᵥ v).
          have h_conj_symm : star v ⬝ᵥ (hA.eigenvectorBasis i) = star (star (hA.eigenvectorBasis i) ⬝ᵥ v) := by
            simp [ dotProduct, mul_comm];
          rw [ h_conj_symm ];
          exact mul_star_self_nonneg (star (hA.eigenvectorBasis i) ⬝ᵥ v);
        norm_num [ mul_assoc ];
        exact mul_le_mul_of_nonneg_right ( mod_cast h_eigenvalue_bound ) h_nonneg;
      -- Since $\sum_{i} (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) = star v ⬝ᵥ v$, we can factor out $(⨅ i, (hA.eigenvalues i))$ from the sum.
      have h_sum : ∑ i, (star (hA.eigenvectorBasis i) ⬝ᵥ v) * (star v ⬝ᵥ (hA.eigenvectorBasis i)) = star v ⬝ᵥ v := by
        have h_sum : ∑ i, (star (hA.eigenvectorBasis i) ⬝ᵥ v) • (hA.eigenvectorBasis i) = v := by
          have := hA.eigenvectorBasis.sum_repr v;
          convert this using 1;
          simp only [dotProduct, Pi.star_apply, RCLike.star_def, mul_comm,
            hA.eigenvectorBasis.repr_apply_apply, PiLp.inner_apply, RCLike.inner_apply];
        -- Taking the inner product of both sides of h_sum with star v, we get the desired equality.
        have h_inner : star v ⬝ᵥ (∑ i, (star (hA.eigenvectorBasis i) ⬝ᵥ v) • (hA.eigenvectorBasis i)) = star v ⬝ᵥ v := by
          rw [h_sum];
        convert h_inner using 1;
        simp [ dotProduct, Finset.mul_sum _ _ _ ];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      rw [ h_expand ];
      refine' le_trans _ ( Finset.sum_le_sum fun i _ => h_bound i );
      simp only [ mul_assoc];
      rw [ ← Finset.mul_sum _ _ _, h_sum ];
    have := hl.2 v; simp_all [ Matrix.sub_mulVec ] ;
    exact le_trans h_eigenvalue this;
  change (⨅ i, hA.eigenvalues i) ≤ μ
  have := h_lower_bound v hv₁
  simp_all only [ne_eq, star, RCLike.star_def, Matrix.dotProduct_mulVec, ge_iff_le,
    dotProduct_smul];
  simp_all only [dotProduct, mul_comm, RCLike.mul_conj];
  rw [ Algebra.smul_def ] at this;
  -- Since the sum of the squares of the norms of v is positive, we can divide both sides of the inequality by it.
  have h_sum_pos : 0 < ∑ x : d, (‖v x‖ : ℝ) ^ 2 := by
    contrapose! hv₁;
    simp_all only [funext_iff, Pi.zero_apply, not_forall, forall_exists_index, Matrix.mulVec, Pi.smul_apply]
    intro i
    rw [← norm_eq_zero]
    simpa [ sq_nonneg ] using le_antisymm ( le_trans ( Finset.single_le_sum ( fun a _ => sq_nonneg ( ‖v a‖ ) ) ( Finset.mem_univ i ) ) hv₁ ) ( sq_nonneg ( ‖v i‖ ) )
  norm_cast at this;
  nlinarith

open ComplexOrder in
theorem IsHermitian.spectrum_subset_Iic_of_sub {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A x : Matrix d d 𝕜} (hA : A.IsHermitian) (hl : (A - x).PosSemidef) :
    spectrum ℝ x ⊆ Set.Iic (⨆ i, hA.eigenvalues i) := by
  have h := spectrum_subset_Ici_of_sub hA.neg (x := -x) ?_
  · rcases isEmpty_or_nonempty d
    · simp
    rw [← spectrum.neg_eq] at h
    intro μ hμ
    specialize h (Set.neg_mem_neg.mpr hμ)
    rw [← Set.mem_neg, Set.neg_Ici] at h
    convert h
    rw [iInf, iSup, ← spectrum_real_eq_range_eigenvalues, ← spectrum_real_eq_range_eigenvalues]
    rw [← spectrum.neg_eq, csInf_neg ?_ (A.finite_real_spectrum.bddAbove), neg_neg]
    exact IsSelfAdjoint.spectrum_nonempty hA
  · convert hl using 1
    abel

open ComplexOrder in
theorem IsHermitian.spectrum_subset_of_mem_Icc {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A B x : Matrix d d 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
  (hl : (x - A).PosSemidef) (hr : (B - x).PosSemidef) :
    spectrum ℝ x ⊆ Set.Icc (⨅ i, hA.eigenvalues i) (⨆ i, hB.eigenvalues i) := by
  rw [← Set.Ici_inter_Iic]
  exact Set.subset_inter (hA.spectrum_subset_Ici_of_sub hl) (hB.spectrum_subset_Iic_of_sub hr)

/--
The right partial trace of a matrix is equal to the left partial trace of the matrix reindexed by swapping the tensor factors.
-/
theorem traceRight_eq_traceLeft_reindex {n m R : Type*} [Fintype m] [AddCommMonoid R]
  (M : Matrix (n × m) (n × m) R) :
    M.traceRight = (M.reindex (.prodComm ..) (.prodComm ..)).traceLeft := by
  rfl

open ComplexOrder in
theorem PosSemidef.trace_pos {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≠ 0) : 0 < A.trace := by
  apply hA.trace_nonneg.lt_of_ne'
  classical
  rw [hA.left.trace_eq_sum_eigenvalues]
  suffices ∑ i, hA.left.eigenvalues i ≠ 0 from mod_cast this
  rwa [ne_eq, Fintype.sum_eq_zero_iff_of_nonneg hA.eigenvalues_nonneg,
    hA.left.eigenvalues_eq_zero_iff]

section traceLeftRight

variable {m α : Type*} [AddCommGroup α] [Fintype m]
omit [DecidableEq n]

variable {A B : Matrix (m × n) (m × n) α}
@[simp]
theorem traceLeft_add : (A + B).traceLeft = A.traceLeft + B.traceLeft := by
  ext : 2
  simp [Matrix.traceLeft, Finset.sum_add_distrib]

@[simp]
theorem traceLeft_neg : (-A).traceLeft = -A.traceLeft := by
  ext : 2; simp [Matrix.traceLeft]

@[simp]
theorem traceLeft_sub : (A - B).traceLeft = A.traceLeft - B.traceLeft := by
  simp [sub_eq_add_neg]

variable {A B : Matrix (n × m) (n × m) α}

@[simp]
theorem traceRight_add : (A + B).traceRight = A.traceRight + B.traceRight := by
  ext : 2
  simp [Matrix.traceRight, Finset.sum_add_distrib]

@[simp]
theorem traceRight_neg : (-A).traceRight = -A.traceRight := by
  ext : 2; simp [Matrix.traceRight]

@[simp]
theorem traceRight_sub : (A - B).traceRight = A.traceRight - B.traceRight := by
  simp [sub_eq_add_neg]

variable {R : Type*} [DistribSMul R α]
@[simp]
theorem traceLeft_smul {A : Matrix (m × n) (m × n) α} (r : R) :
    (r • A).traceLeft = r • A.traceLeft := by
  ext : 2; simp [Matrix.traceLeft, ← Finset.smul_sum]

@[simp]
theorem traceRight_smul {A : Matrix (n × m) (n × m) α} (r : R) :
    (r • A).traceRight = r • A.traceRight := by
  ext : 2; simp [Matrix.traceRight, ← Finset.smul_sum]

end traceLeftRight

theorem unitaryGroup_row_norm [Fintype n] (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, ‖U j i‖^2 = 1 := by
  suffices ∑ j, ‖U j i‖^2 = (1 : ℂ) by exact_mod_cast this
  simpa [Matrix.mul_apply, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    using congr($(U.prop.left) i i)

section finprod

variable {ι : Type*} {d : ι → Type*} [fι : Fintype ι]
variable {R : Type*}

def piProd [CommMonoid R] (A : ∀ i, Matrix (d i) (d i) R) : Matrix (∀ i, d i) (∀ i, d i) R :=
  Matrix.of (fun j k : (∀ i, d i) ↦ ∏ i, A i (j i) (k i))

variable {A : ∀ i, Matrix (d i) (d i) R}

theorem IsHermitian.piProd [CommSemiring R] [StarRing R] (hA : ∀ i, (A i).IsHermitian) :
    (piProd A).IsHermitian := by
  ext j k
  simp [Matrix.piProd]
  exact Finset.prod_congr rfl fun i _ => by simpa using congr_fun ( congr_fun ( hA i ) ( j i ) ) ( k i ) ;

variable [DecidableEq ι] [∀ i, Fintype (d i)] --[∀ i, DecidableEq (d i)]

theorem trace_piProd [CommSemiring R] :
    (piProd A).trace = ∏ i, (A i).trace := by
  symm
  simp [trace, piProd, Fintype.prod_sum]

open ComplexOrder in
set_option maxHeartbeats 400000 in
theorem PosSemidef.piProd [RCLike R] (hA : ∀ i, (A i).PosSemidef) :
    (piProd A).PosSemidef := by
  -- Let B i be the square root of A i. Let BigB be the pi-product of B i. Show that BigB.conjTranspose * BigB equals the pi-product of A i using Fintype.prod_sum. Then use Matrix.PosSemidef.conjTranspose_mul_self to conclude the proof.
  obtain ⟨B, hB⟩ : ∃ B : ∀ i, Matrix (d i) (d i) R, ∀ i, (A i) = B i * star (B i) := by
    -- By definition of positive semi-definite matrices, each $A_i$ can be written as $B_i^* B_i$ for some matrix $B_i$.
    have h_decomp : ∀ i, ∃ B : Matrix (d i) (d i) R, A i = B * star B := by
      intro i
      obtain ⟨B, hB⟩ : ∃ B : Matrix (d i) (d i) R, A i = B.conjTranspose * B := by
        exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp (hA i)
      use B.conjTranspose;
      convert hB using 1;
      simp [ Matrix.star_eq_conjTranspose ];
    exact ⟨ fun i => Classical.choose ( h_decomp i ), fun i => Classical.choose_spec ( h_decomp i ) ⟩;
  have hBigB_conjTranspose_mul_BigB : Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i * star (B i)) (j i) (k i)) = Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i) (j i) (k i)) * star (Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i) (j i) (k i))) := by
    ext j k; simp [ Matrix.mul_apply]
    simp only [Finset.prod_sum, ← Finset.prod_mul_distrib];
    refine' Finset.sum_bij ( fun p hp => fun i => p i ( Finset.mem_univ i ) ) _ _ _ _ <;> simp +decide;
    · simp [ funext_iff ];
    · exact fun b => ⟨ fun i _ => b i, rfl ⟩;
  simp_all [ Matrix.PosSemidef, Matrix.piProd ]
  constructor
  · ext1
    simp [Matrix.mul_apply, mul_comm]
  · intro x
    set y := star (Matrix.of (fun j k : (∀ i, d i) => ∏ i, B i (j i) (k i))) *ᵥ x
    convert dotProduct_star_self_nonneg y using 1
    simp [ Matrix.dotProduct_mulVec]
    simp [ Matrix.dotProduct_mulVec, y ];
    simp [ Matrix.vecMul, dotProduct, mul_comm ];
    simp [ Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

end finprod

--TODO: Can this be used for `Matrix.reindex_eq_conj` cleanup?
theorem submatrix_eq_mul_mul {d d₂ d₃ R : Type*} [DecidableEq d] [Fintype d] [Semiring R]
  (A : Matrix d d R) (e : d₂ → d) (f : d₃ → d) :
    A.submatrix e f = (submatrix (α := R) 1 e id : Matrix d₂ d R) * A * (submatrix (α := R) 1 id f) := by
  rw [show id = Equiv.refl d by rfl, Matrix.mul_submatrix_one, Matrix.one_submatrix_mul]
  simp

open scoped Matrix Kronecker in
/--
The conjugate of a Kronecker product by a Kronecker product is the Kronecker product of the conjugates (for matrices).
-/
lemma kronecker_conj_eq {m n p q α : Type*} [CommSemiring α] [StarRing α] [Fintype m] [Fintype n]
    (A : Matrix m m α) (B : Matrix n n α) (C : Matrix p m α) (D : Matrix q n α) :
    (C ⊗ₖ D) * (A ⊗ₖ B) * (C ⊗ₖ D)ᴴ = (C * A * Cᴴ) ⊗ₖ (D * B * Dᴴ) := by
  rw [← Matrix.mul_kronecker_mul]
  ext1
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, star_mul']
  simp only [← starRingEnd_apply, mul_comm, Finset.mul_sum, mul_left_comm]
  simp only [Finset.sum_mul, mul_assoc, Finset.mul_sum, mul_left_comm]
  rw [Fintype.sum_prod_type_right]

end Matrix
