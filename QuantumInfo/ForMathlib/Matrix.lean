import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.Tactic.Bound

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
theorem trace_nonneg : 0 ≤ A.trace := by
  rw [trace]
  apply Finset.sum_nonneg
  simp_rw [Finset.mem_univ, forall_true_left]
  exact hA.diag_nonneg

include hA in
theorem trace_zero : A.trace = 0 → A = 0 := by
  open Classical in
  intro h
  rw [← hA.isHermitian.sum_eigenvalues_eq_trace, RCLike.ofReal_eq_zero] at h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hA.eigenvalues_nonneg i)] at h
  simp only [Finset.mem_univ, diag_apply, forall_const] at h
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

include hA in
theorem smul {c : 𝕜} (h : 0 ≤ c) : (c • A).PosSemidef := by
  constructor
  · apply hA.1.smul_im_zero (RCLike.nonneg_iff.mp h).2
  · intro x
    rw [smul_mulVec_assoc, dotProduct_smul]
    exact mul_nonneg h (hA.2 x)

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

lemma sqrt_eq {A B : Matrix m m 𝕜} (h : A = B) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hA.sqrt = hB.sqrt := by
  congr!

lemma sqrt_eq' {A B : Matrix m m 𝕜} (h : A = B) (hA : A.PosSemidef) :
    hA.sqrt = (h ▸ hA).sqrt := by
  congr!

@[simp]
theorem sqrt_0 : (PosSemidef.zero (n := n) (R := 𝕜)).sqrt = 0 :=
  (sqrt_eq_zero_iff PosSemidef.zero).mpr rfl

@[simp]
theorem sqrt_1 : (PosSemidef.one (n := n) (R := 𝕜)).sqrt = 1 :=
  (sqrt_eq_one_iff PosSemidef.one).mpr rfl

theorem posSemidef_iff_eigenvalues_nonneg {hA : A.IsHermitian} : A.PosSemidef ↔ ∀ x, 0 ≤ hA.eigenvalues x :=
  ⟨PosSemidef.eigenvalues_nonneg, IsHermitian.posSemidef_of_eigenvalues_nonneg hA⟩

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
    rw [smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
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

include dm in
theorem sqrt_nonneg_smul {c : 𝕜} (hA : (c^2 • A).PosSemidef) (hc : 0 < c) :
    hA.sqrt = c • (hA.pos_smul (sq_pos_of_pos hc) : A.PosSemidef).sqrt := by
  apply Eq.symm
  apply (eq_sqrt_iff_sq_eq ?_ hA).mpr
  · rw [pow_two, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, sqrt_mul_self, pow_two, smul_smul]
  · apply nonneg_smul ?_ hc.le
    apply posSemidef_sqrt

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
  sorry

theorem of_toLin_ker_eq_bot (hA : LinearMap.ker A.toLin' = ⊥) (hA₂ : A.PosSemidef) : A.PosDef := by
  sorry

-- see https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/More.20stuff.20about.20kernels.2Franges.20of.20matrices/with/521587161
-- --Doesn't require [FiniteDimensional] so it's on its own
-- theorem LinearMap.ker_le_ker_of_range_antitone {V 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
--     {A B : V →ₗ[𝕜] V} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (h : range A ≤ range B) :
--     ker B ≤ ker A := by
--   intro v hv
--   rw [mem_ker] at hv ⊢
--   obtain ⟨y, hy⟩ : ∃ y, B y = A (A v) := by simpa using @h (A (A v))
--   rw [← inner_self_eq_zero (𝕜 := 𝕜), ← hA, ← hy, hB, hv, inner_zero_right]

-- theorem LinearMap.ker_range_antitone {V 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
--   [FiniteDimensional 𝕜 V] {A B : V →ₗ[𝕜] V} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
--     range A ≤ range B ↔ ker B ≤ ker A := by
--   use ker_le_ker_of_range_antitone hA hB
--   rintro h z ⟨y, rfl⟩
--   let b := hB.eigenvectorBasis rfl
--   have h₂ := OrthonormalBasis.sum_repr' b (A y)
--   simp_rw [← hA _ y, ← Finset.sum_add_sum_compl (s := { i | hB.eigenvalues rfl i = 0 })] at h₂
--   conv at h₂ =>
--     enter [1]
--     congr
--     · rw [← Finset.sum_attach]
--       enter [2, i]
--       equals 0 =>
--         obtain ⟨i, hi⟩ := i
--         suffices B (b i) = 0 by simp [show A (b i) = 0 from h this]
--         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
--         simp [b, hi]
--     · rw [Finset.compl_filter, ← Finset.sum_attach (Finset.filter _ _)]
--       enter [2, i, 2]
--       equals (hB.eigenvalues rfl i : 𝕜)⁻¹ • B (b i) =>
--         obtain ⟨i, hi⟩ := i
--         rw [hB.apply_eigenvectorBasis rfl i, inv_smul_smul₀]
--         simpa using hi
--   simp only [Finset.sum_const_zero, smul_smul, zero_add, ← LinearMapClass.map_smul, ← map_sum] at h₂
--   exact ⟨_, h₂⟩

theorem ker_range_antitone {d : Type*} [Fintype d] [DecidableEq d] {A B : Matrix d d ℂ}
  (hA : A.IsHermitian) (hB : B.IsHermitian) :
    LinearMap.ker A.toEuclideanLin ≤ LinearMap.ker A.toEuclideanLin ↔
    LinearMap.range A.toEuclideanLin ≤ LinearMap.range B.toEuclideanLin
     := by
  convert ContinuousLinearMap.ker_le_ker_iff_range_le_range
    (T := Matrix.toEuclideanCLM.toFun A) (U := Matrix.toEuclideanCLM.toFun B) ?_ ?_
  · sorry
  · sorry
  · sorry

end PosDef

namespace PosSemidef
section partialOrder
open scoped ComplexOrder

variable {n m 𝕜 : Type*}
variable [Fintype n] [Fintype m] [RCLike 𝕜] [DecidableEq m]
variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜}
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

/-- Loewner partial order of square matrices induced by positive-semi-definiteness:
`A ≤ B ↔ (B - A).PosSemidef` alongside properties that make it an "OrderedCancelAddCommMonoid"
TODO : Equivalence to CStarAlgebra.spectralOrder -/
instance loewnerOrder : PartialOrder (Matrix n n 𝕜) where
  le A B := (B - A).PosSemidef
  le_refl A := by simp only [sub_self, PosSemidef.zero]
  le_trans A B C hAB hBC := by
    rw [←sub_add_sub_cancel _ B _]
    exact PosSemidef.add hBC hAB
  le_antisymm A B hAB hBA := by
    rw [←neg_sub] at hAB
    rw [←sub_eq_zero]
    exact zero_posSemidef_neg_posSemidef_iff.mp ⟨hBA, hAB⟩

instance instOrderedCancelAddCommMonoid : IsOrderedCancelAddMonoid (Matrix n n 𝕜) where
  add_le_add_left A B hAB C := by
    dsimp [loewnerOrder]
    rwa [add_sub_add_left_eq_sub]
  le_of_add_le_add_left A B C hABAC:= by
    dsimp [loewnerOrder] at hABAC
    rwa [add_sub_add_left_eq_sub] at hABAC

theorem le_iff_sub_posSemidef : A ≤ B ↔ (B - A).PosSemidef := by rfl

theorem zero_le_iff_posSemidef : 0 ≤ A ↔ A.PosSemidef := by
  apply Iff.trans (le_iff_sub_posSemidef)
  rw [sub_zero]

/-- Basically, the instance states A ≤ B ↔ B = A + Sᴴ * S  -/
instance instStarOrderedRing : StarOrderedRing (Matrix n n 𝕜) :=
  StarOrderedRing.of_nonneg_iff'
    (add_le_add_left)
    (fun _ ↦ zero_le_iff_posSemidef.trans posSemidef_iff_eq_conjTranspose_mul_self)

theorem le_iff_sub_nonneg : A ≤ B ↔ 0 ≤ B - A := Iff.trans le_iff_sub_posSemidef zero_le_iff_posSemidef.symm

theorem le_of_nonneg_imp {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (f : Matrix n n 𝕜 →+ R) (h : ∀ A, A.PosSemidef → 0 ≤ f A) :
    (A ≤ B → f A ≤ f B) := by
  intro hAB
  rw [←sub_nonneg, ←map_sub]
  exact h (B - A) <| le_iff_sub_posSemidef.mp hAB

theorem le_of_nonneg_imp' {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    {x y : R} (f : R →+ Matrix n n 𝕜) (h : ∀ x, 0 ≤ x → (f x).PosSemidef) :
    (x ≤ y → f x ≤ f y) := by
  intro hxy
  rw [le_iff_sub_nonneg, ←map_sub]
  rw [←sub_nonneg] at hxy
  exact zero_le_iff_posSemidef.mpr <| h (y - x) hxy

omit [DecidableEq m] in
theorem mul_mul_conjTranspose_mono (C : Matrix m n 𝕜) :
  A ≤ B → C * A * C.conjTranspose ≤ C * B * C.conjTranspose := fun hAB ↦ by
    rw [le_iff_sub_posSemidef]
    have hDistrib : C * B * Cᴴ - C * A * Cᴴ = C * (B - A) * Cᴴ := by
      ext i j
      simp only [sub_apply, mul_apply, conjTranspose_apply, RCLike.star_def, Finset.sum_mul,
        ←Finset.sum_sub_distrib, mul_sub_left_distrib, mul_sub_right_distrib]
    rw [hDistrib]
    exact mul_mul_conjTranspose_same (le_iff_sub_posSemidef.mp hAB) C

omit [DecidableEq m] in
theorem conjTranspose_mul_mul_mono (C : Matrix n m 𝕜) :
  A ≤ B → C.conjTranspose * A * C ≤ C.conjTranspose * B * C := fun hAB ↦ by
    rw [le_iff_sub_posSemidef]
    have hDistrib : Cᴴ * B * C - Cᴴ * A * C = Cᴴ * (B - A) * C := by
      ext i j
      simp only [sub_apply, mul_apply, conjTranspose_apply, RCLike.star_def, Finset.sum_mul,
        ←Finset.sum_sub_distrib, mul_sub_left_distrib, mul_sub_right_distrib]
    rw [hDistrib]
    exact conjTranspose_mul_mul_same (le_iff_sub_posSemidef.mp hAB) C

/-- Basically, the instance states 0 ≤ A → ∀ x ∈ spectrum ℝ A, 0 ≤ x  -/
instance instNonnegSpectrumClass : NonnegSpectrumClass ℝ (Matrix n n 𝕜) := by
  open Classical in
  apply NonnegSpectrumClass.of_spectrum_nonneg
  intro A hA x hx
  rw [IsHermitian.eigenvalues_eq_spectrum_real (zero_le_iff_posSemidef.mp hA).1, Set.mem_range] at hx
  obtain ⟨i, hi⟩ := hx
  rw [←hi]
  exact (zero_le_iff_posSemidef.mp hA).eigenvalues_nonneg i

theorem nonneg_iff_eigenvalue_nonneg [DecidableEq n] : 0 ≤ A ↔ ∀ x, 0 ≤ hA.eigenvalues x :=
  Iff.trans zero_le_iff_posSemidef posSemidef_iff_eigenvalues_nonneg

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
  have hc' : c • (1 : Matrix n n 𝕜) = diagonal (RCLike.ofReal ∘ fun _ : n ↦ c) := by
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
  simp only [Finset.sum_mul, Finset.sum_filter, mul_assoc, Finset.mul_sum]
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

theorem PosDef.smul {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • M).PosDef := by
  constructor
  · exact hM.1.smul_real c
  · peel hM.2
    rw [smul_mulVec_assoc, dotProduct_smul]
    positivity

theorem PosSemidef.rsmul {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (c • M).PosSemidef := by
  constructor
  · exact hM.1.smul_real c
  · peel hM.2
    rw [smul_mulVec_assoc, dotProduct_smul]
    positivity

theorem PosDef.Convex {n : Type*} [Fintype n] : Convex ℝ (Matrix.PosDef (n := n) (R := ℂ)) := by
  intro A hA B hB a b ha hb hab
  rcases ha.eq_or_lt with (rfl | ha)
  · simp_all
  rcases hb.eq_or_lt with (rfl | hb)
  · simp_all
  exact (hA.smul ha).add (hB.smul hb)

end posdef

section eigenvalues

open ComplexOrder

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]

theorem PosDef_iff_eigenvalues {M : Matrix d d 𝕜} (hM : M.IsHermitian) :
    M.PosDef ↔ ∀ i, 0 < hM.eigenvalues i := by
  constructor
  · exact PosDef.eigenvalues_pos
  · intro a
    have := Matrix.IsHermitian.spectral_theorem hM;
    -- Since the diagonal matrix of eigenvalues is positive definite, and the product of a unitary matrix, a positive definite matrix, and the conjugate transpose of the unitary matrix is positive definite, we can conclude that M is positive definite.
    have h_pos_def : PosDef (Matrix.diagonal (fun i => (hM.eigenvalues i : 𝕜))) := by
      simpa [ Complex.ext_iff ] using a;
    rw [ this ];
    convert h_pos_def.conjTranspose_mul_mul_same _;
    all_goals try infer_instance;
    -- Case 1
    · ext i j;
      simp ( config := { decide := Bool.true } ) [ Matrix.map_apply, Complex.ext_iff ];
    -- Case 2
    · -- The matrix $Q$ is unitary, so its conjugate transpose is also unitary.
      have h_unitary : (Star.star (↑hM.eigenvectorUnitary : Matrix d d 𝕜)) * (↑hM.eigenvectorUnitary : Matrix d d 𝕜) = 1 := by
        field_simp;
      exact fun x y hxy => by simpa [ h_unitary ] using congr_arg ( fun z => ( ↑hM.eigenvectorUnitary : Matrix d d 𝕜 ).mulVec z ) hxy

theorem PosDef_iff_eigenvalues' (M : Matrix d d 𝕜) :
    M.PosDef ↔ ∃ (h : M.IsHermitian), ∀ i, 0 < h.eigenvalues i :=
  ⟨fun h ↦ ⟨h.left, (PosDef_iff_eigenvalues h.left).mp h⟩,
    fun ⟨w, h⟩ ↦ (PosDef_iff_eigenvalues w).mpr h⟩


theorem IsHermitian.charpoly_roots_eq_eigenvalues {M : Matrix d d 𝕜} (hM : M.IsHermitian) :
    M.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hM.eigenvalues) Finset.univ.val := by
  -- Since M is Hermitian, its characteristic polynomial splits into linear factors over the reals.
  have h_split : M.charpoly = Multiset.prod (Multiset.map (fun (e : ℝ) => Polynomial.X - Polynomial.C (RCLike.ofReal e)) (Multiset.map (fun (i : d) => hM.eigenvalues i) Finset.univ.val)) := by
    -- Since M is Hermitian, it is diagonalizable, and its characteristic polynomial splits into linear factors over the reals.
    have h_diag : ∃ P : Matrix d d 𝕜, P.det ≠ 0 ∧ ∃ D : Matrix d d 𝕜, D = Matrix.diagonal (fun i => RCLike.ofReal (hM.eigenvalues i)) ∧ M = P * D * P⁻¹ := by
      have := hM.spectral_theorem;
      refine' ⟨ hM.eigenvectorUnitary, _, _ ⟩;
      -- Case 1
      · -- Since the eigenvector unitary is a unitary matrix, its determinant is a unit, hence non-zero.
        have h_det_unitary : IsUnit (Matrix.det (hM.eigenvectorUnitary : Matrix d d 𝕜)) := by
          exact UnitaryGroup.det_isUnit hM.eigenvectorUnitary
        exact h_det_unitary.ne_zero;
      -- Case 2
      · refine' ⟨ _, rfl, this.trans _ ⟩;
        rw [ Matrix.inv_eq_left_inv ];
        congr!;
        bound;
    -- Since M is similar to D, their characteristic polynomials are the same.
    have h_char_poly : M.charpoly = Matrix.charpoly (Matrix.diagonal (fun i => RCLike.ofReal (hM.eigenvalues i))) := by
      rcases h_diag with ⟨P, left, ⟨D, left_1, rfl⟩⟩
      rw [ ← left_1, Matrix.charpoly, Matrix.charpoly ];
      simp +decide [ Matrix.charmatrix, Matrix.mul_assoc ];
      -- Since $w$ is invertible, we can simplify the determinant.
      have h_inv : (P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * (P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) = 1 := by
        simp ( config := { decide := Bool.true } ) [ ← Matrix.map_mul, left ];
      -- Since $w$ is invertible, we can simplify the determinant using the fact that the determinant of a product is the product of the determinants.
      have h_det_prod : Matrix.det ((Matrix.diagonal (fun _ => Polynomial.X) - P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜) * (D.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜) * P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)))) = Matrix.det ((P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * (Matrix.diagonal (fun _ => Polynomial.X) - D.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * (P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜))) := by
        simp ( config := { decide := Bool.true } ) only [ mul_sub, sub_mul, Matrix.mul_assoc, h_inv ];
        -- Since Matrix.diagonal (fun _ => Polynomial.X) is a scalar matrix, it commutes with any matrix.
        have h_comm : Matrix.diagonal (fun _ => Polynomial.X) * P⁻¹.map Polynomial.C = P⁻¹.map Polynomial.C * Matrix.diagonal (fun _ => Polynomial.X) := by
          ext i j; by_cases hi : i = j <;> simp ( config := { decide := Bool.true } ) [ hi ];
        simp ( config := { decide := Bool.true } ) only [ h_comm, Matrix.mul_assoc ];
        simp ( config := { decide := Bool.true } ) [ ← mul_assoc, h_inv ];
      rw [ h_det_prod, Matrix.det_mul, Matrix.det_mul ];
      -- Since the determinant of the product of two matrices is the product of their determinants, and the determinant of the identity matrix is 1, we have:
      have h_det_identity : Matrix.det (P.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) * Matrix.det (P⁻¹.map (⇑Polynomial.C : 𝕜 → Polynomial 𝕜)) = 1 := by
        rw [ ← Matrix.det_mul, h_inv, Matrix.det_one ];
      rw [ mul_right_comm, h_det_identity, one_mul ];
    rw [h_char_poly];
    simp ( config := { decide := Bool.true } ) [ Matrix.charpoly, Matrix.det_diagonal ];
  rw [ h_split, Polynomial.roots_multiset_prod ];
  -- Case 1
  · erw [ Multiset.bind_map ];
    aesop;
  -- Case 2
  · -- Since the eigenvalues are real, and we're working over the complex numbers (since 𝕜 is a real closed field), the polynomial X - C(e) would be zero only if e is zero. But if e is zero, then the polynomial would be X, which isn't zero. So 0 can't be in the multiset.
    simp [Polynomial.X_sub_C_ne_zero]

theorem IsHermitian.cfc_eigenvalues {M : Matrix d d 𝕜} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    ∃ (e : d ≃ d), IsHermitian.eigenvalues (cfc_predicate f M) = f ∘ hM.eigenvalues ∘ e := by
  sorry

end eigenvalues

section

variable {α n : Type*} [RCLike α] [Fintype n] [DecidableEq n]

@[simp]
theorem toEuclideanLin_one : Matrix.toEuclideanLin (1 : Matrix n n α) = .id := by
  ext1 x
  simp [Matrix.toEuclideanLin]

end
