/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import QuantumInfo.ForMathlib.HermitianMat.CFC
import QuantumInfo.ForMathlib.HermitianMat.Order
import QuantumInfo.ForMathlib.Misc

/-!
Facts connecting matrices, their ordering, and when they commute or not. This probably could be
reorganized to belong in other files better, but in the absence of a clear import hierarchy this
seems okay for now.
-/

theorem Commute.exists_HermitianMat_cfc {d : Type*} [Fintype d] [DecidableEq d]
  (A B : HermitianMat d ℂ) (hAB : Commute A.toMat B.toMat) :
    ∃ C : HermitianMat d ℂ, (∃ f : ℝ → ℝ, A = C.cfc f) ∧ (∃ g : ℝ → ℝ, B = C.cfc g) := by
  obtain ⟨C, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := hAB.exists_cfc A.H B.H
  by_cases hC : C.IsHermitian
  · use ⟨C, hC⟩
    constructor
    · exact ⟨g₁, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨g₂, by simp [HermitianMat.ext_iff, hg₂]⟩
  · change ¬(IsSelfAdjoint C) at hC
    rw [cfc_apply_of_not_predicate C hC] at hg₁ hg₂
    use 0
    constructor
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₂]⟩

namespace HermitianMat

open ComplexOrder

theorem cfc_le_cfc_of_PosDef {d : Type*} [Fintype d] [DecidableEq d]
  {f g : ℝ → ℝ} (hfg : ∀ i, 0 < i → f i ≤ g i) (A : HermitianMat d ℂ) (hA : A.toMat.PosDef) :
    A.cfc f ≤ A.cfc g := by
  rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
  intro i
  rw [Pi.sub_apply, sub_nonneg]
  rw [A.H.posDef_iff_eigenvalues_pos] at hA
  apply hfg
  apply hA

theorem cfc_commute {d : Type*} [Fintype d] [DecidableEq d]
  (A B : HermitianMat d ℂ) (f g : ℝ → ℝ) (hAB : Commute A.toMat B.toMat) :
    Commute (A.cfc f).toMat (B.cfc g).toMat := by
  obtain ⟨C, ⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩ := hAB.exists_HermitianMat_cfc
  rw [commute_iff_eq, ← HermitianMat.cfc_comp, ← HermitianMat.cfc_comp, ← HermitianMat.coe_cfc_mul, ← HermitianMat.coe_cfc_mul, mul_comm (f ∘ h₁) (g ∘ h₂)]

theorem cfc_self_commute {d : Type*} [Fintype d] [DecidableEq d]
  (A : HermitianMat d ℂ) (f g : ℝ → ℝ) :
    Commute (A.cfc f).toMat (A.cfc g).toMat := by
  rw [commute_iff_eq, ← HermitianMat.coe_cfc_mul, ← HermitianMat.coe_cfc_mul, mul_comm f g]

/- TODO: Write a version of this that holds more broadly for some sets. Esp closed intervals of reals,
which correspond nicely to closed intervals of matrices. Write the specialization to Set.univ (Monotone
instead of MonotoneOn). Also a version that works for StrictMonoOn. -/
theorem cfc_le_cfc_of_commute_monoOn {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Ioi 0)) {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat)
  (hAB₂ : A ≤ B) (hA : A.toMat.PosDef) (hB : B.toMat.PosDef) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, C.zero_le_cfc] at hAB₂ ⊢
  intro i
  simp only [HermitianMat.val_eq_coe, Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  · rw [HermitianMat.cfc_PosDef] at hA
    exact hA i
  · rw [HermitianMat.cfc_PosDef] at hB
    exact hB i
  · simpa using hAB₂ i

/-- TODO: See above -/
theorem cfc_le_cfc_of_commute {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf : Monotone f) {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat)
  (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, C.zero_le_cfc] at hAB₂ ⊢
  intro i
  simp only [HermitianMat.val_eq_coe, Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  simpa using hAB₂ i

--This is the more general version that requires operator concave functions but doesn't require the inputs
-- to commute. Requires the correct statement of operator convexity though, which we don't have right now.
proof_wanted cfc_monoOn_pos_of_monoOn_posDef {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf_is_operator_convex : False) :
    MonotoneOn (HermitianMat.cfc · f) { A : HermitianMat d ℂ | A.toMat.PosDef }

proof_wanted log_monoOn_posDef {d : Type*} [Fintype d] [DecidableEq d] :
    MonotoneOn HermitianMat.log { A : HermitianMat d ℂ | A.toMat.PosDef }

/-- Monotonicity of log on commuting operators. -/
theorem log_le_log_of_commute {d : Type*} [Fintype d] [DecidableEq d]
  {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat) (hAB₂ : A ≤ B) (hA : A.toMat.PosDef) :
    A.log ≤ B.log := by
  refine HermitianMat.cfc_le_cfc_of_commute_monoOn ?_ hAB₁ hAB₂ hA ?_
  · exact Real.strictMonoOn_log.monotoneOn
  · --The fact that `A ≤ B` and `A.PosDef` implies `B.PosDef`. Should be a theorem, TODO
    -- This almost works but not quite:
    -- rw [← Matrix.isStrictlyPositive_iff_posDef] at hA ⊢
    -- exact hA.of_le hAB₂
    simpa using Matrix.PosDef.add_posSemidef hA hAB₂ --ew. abuse

/-- Monotonicity of exp on commuting operators. -/
theorem exp_le_exp_of_commute {d : Type*} [Fintype d] [DecidableEq d]
  {A B : HermitianMat d ℂ} (hAB₁ : Commute A.toMat B.toMat) (hAB₂ : A.cfc Real.exp ≤ B.cfc Real.exp) :
    A ≤ B := by
  have hA : A = (A.cfc Real.exp).cfc Real.log := by simp [← HermitianMat.cfc_comp]
  have hB : B = (B.cfc Real.exp).cfc Real.log := by simp [← HermitianMat.cfc_comp]
  rw [hA, hB]
  apply HermitianMat.log_le_log_of_commute
  · apply HermitianMat.cfc_commute
    exact hAB₁
  · exact hAB₂
  · rw [HermitianMat.cfc_PosDef]
    intro
    positivity

section uncategorized_cleanup

theorem inv_eq_rpow_neg_one {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A : HermitianMat n 𝕜) (hA : A.toMat.PosDef) : A⁻¹ = A ^ (-1 : ℝ) := by
  -- Since the matrix is invertible, we can apply the fact that the inverse of a matrix is equal to its -1 power.
  have h_inv : A.toMat⁻¹ = cfc A (fun x => x⁻¹) := by
    rw [ Matrix.inv_eq_left_inv ];
    have h_inv : (cfc A (fun x => x⁻¹)).toMat * A.toMat = cfc A (fun x => x⁻¹ * x) := by
      have h_inv : (cfc A (fun x => x⁻¹)).toMat * A.toMat = cfc A (fun x => x⁻¹ * x) := by
        have h_inv : ∀ (f g : ℝ → ℝ), (cfc A f).toMat * (cfc A g).toMat = cfc A (fun x => f x * g x) := by
          intro f g;
          convert coe_cfc_mul A f g using 1;
          · exact Eq.symm (coe_cfc_mul A f g);
          · convert coe_cfc_mul A f g using 1
        convert h_inv ( fun x => x⁻¹ ) ( fun x => x ) using 1 ; aesop;
      exact h_inv;
    rw [ h_inv, cfc_congr_of_posDef hA ];
    rotate_right;
    exacts [ fun x => 1, by simp +decide [ cfc_const ], fun x hx => by simp +decide [ hx.out.ne' ] ];
  -- Since the matrix is invertible, we can apply the fact that the inverse of a matrix is equal to its -1 power in the functional calculus.
  have h_inv : A⁻¹ = cfc A (fun x => x⁻¹) := by
    exact HermitianMat.ext h_inv;
  rw [ h_inv, pow_eq_cfc, show ( fun x : ℝ => x⁻¹ ) = fun x : ℝ => x ^ ( -1 : ℝ ) by ext; norm_num [ Real.rpow_neg_one ] ]

theorem inv_ge_one_of_le_one {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A : HermitianMat n 𝕜} (hA : A.toMat.PosDef) (h : A ≤ 1) : 1 ≤ A⁻¹ := by
  have h_inv_ge_one : A⁻¹ = cfc A (fun x => x⁻¹) := by
    convert inv_eq_rpow_neg_one A hA;
    rw [ pow_eq_cfc ];
    norm_num [ Real.rpow_neg_one ];
  have h_inv_ge_one : ∀ i, 1 ≤ 1 / A.H.eigenvalues i := by
    intro i
    have h_eigenvalue : 0 < A.H.eigenvalues i := by
      exact hA.eigenvalues_pos i
    have h_eigenvalue_le_one : A.H.eigenvalues i ≤ 1 := by
      have h_eigenvalue_le_one : ∀ x : n → 𝕜, x ≠ 0 → (star x ⬝ᵥ A.toMat.mulVec x) / (star x ⬝ᵥ x) ≤ 1 := by
        intro x hx_nonzero
        have h_eigenvalue_le_one : (star x ⬝ᵥ A.toMat.mulVec x) ≤ (star x ⬝ᵥ x) := by
          have h_eigenvalue_le_one : ∀ x : n → 𝕜, x ≠ 0 → (star x ⬝ᵥ A.toMat.mulVec x) ≤ (star x ⬝ᵥ x) := by
            intro x hx_nonzero
            have h_eigenvalue_le_one : (star x ⬝ᵥ (1 - A.toMat).mulVec x) ≥ 0 := by
              have h_eigenvalue_le_one : (1 - A.toMat).PosSemidef := by
                exact h;
              exact h_eigenvalue_le_one.2 x
            simp_all +decide [ Matrix.sub_mulVec, dotProduct_sub ];
          exact h_eigenvalue_le_one x hx_nonzero
        generalize_proofs at *;
        convert div_le_one_of_le₀ h_eigenvalue_le_one _ using 1
        generalize_proofs at *;
        · exact PosMulReflectLT.toMulPosReflectLT;
        · exact dotProduct_star_self_nonneg x
      generalize_proofs at *;
      convert h_eigenvalue_le_one ( ‹Matrix.IsHermitian A.toMat›.eigenvectorBasis i ) ( by intro h; simpa [ h ] using ‹Matrix.IsHermitian A.toMat›.eigenvectorBasis.orthonormal.1 i ) using 1 ; simp +decide [ Matrix.mulVec, dotProduct ];
      rw [ show ( ∑ x, ( starRingEnd 𝕜 ) ( ‹Matrix.IsHermitian A.toMat›.eigenvectorBasis i x ) * ∑ x_1, A x x_1 * ‹Matrix.IsHermitian A.toMat›.eigenvectorBasis i x_1 ) = ( ‹Matrix.IsHermitian A.toMat›.eigenvalues i ) * ( ∑ x, ( starRingEnd 𝕜 ) ( ‹Matrix.IsHermitian A.toMat›.eigenvectorBasis i x ) * ‹Matrix.IsHermitian A.toMat›.eigenvectorBasis i x ) from ?_ ];
      · rw [ mul_div_cancel_right₀ ];
        · norm_cast;
        · have := ‹Matrix.IsHermitian A.toMat›.eigenvectorBasis.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
          specialize this i i ; simp_all +decide [ Inner.inner ];
          simp_all +decide [ mul_comm ];
      · have := ‹Matrix.IsHermitian A.toMat›.mulVec_eigenvectorBasis i; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
        replace this := congr_arg ( fun x => ∑ j, ( starRingEnd 𝕜 ) ( ‹Matrix.IsHermitian A.toMat›.eigenvectorBasis i j ) * x j ) this ; simp_all +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ] ;
        norm_num [ Algebra.smul_def ]
    exact one_le_one_div h_eigenvalue h_eigenvalue_le_one;
  have h_inv_ge_one : 0 ≤ A.cfc (fun x => x⁻¹ - 1) := by
    rw [ zero_le_cfc ];
    aesop;
  convert add_le_add_right h_inv_ge_one 1 using 1;
  · norm_num;
  · rw [ ‹A⁻¹ = A.cfc fun x => x⁻¹›, ← sub_eq_zero ];
    rw [ ← sub_sub, ← cfc_sub ];
    simp +decide [ Pi.sub_def ]

theorem sandwich_identity {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (B : HermitianMat n 𝕜) (hB : B.toMat.PosDef) :
    (B.conj (B ^ (-1/2 : ℝ)).toMat).toMat = 1 := by
  have hB_inv_sqrt : (B ^ (-1 / 2 : ℝ)).toMat * (B ^ (-1 / 2 : ℝ)).toMat = (B ^ (-1 : ℝ)).toMat := by
    rw [ ← coe_rpow_add ] <;> norm_num;
    -- Since B is positive definite, it is also positive semidefinite.
    have h_pos_semidef : B.toMat.PosSemidef := by
      exact hB.posSemidef;
    exact zero_le_iff.mpr h_pos_semidef;
  have hB_inv : (B ^ (-1 : ℝ)).toMat = B.toMat⁻¹ := by
    have := HermitianMat.inv_eq_rpow_neg_one B hB;
    exact this ▸ rfl;
  rw [ hB_inv ] at hB_inv_sqrt;
  simp +decide [mul_assoc];
  rw [ ← Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp ];
  rw [ ← Matrix.mul_assoc, hB_inv_sqrt, Matrix.nonsing_inv_mul _ ];
  exact isUnit_iff_ne_zero.mpr hB.det_pos.ne'

lemma rpow_inv_eq_neg_rpow {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] (A : HermitianMat n 𝕜) (hA : A.toMat.PosDef) (p : ℝ) : (A ^ p)⁻¹ = A ^ (-p) := by
  ext i j;
  have h_inv : (A ^ p).toMat * (A ^ (-p)).toMat = 1 := by
    have h_inv : (A ^ p).toMat * (A ^ (-p)).toMat = 1 := by
      have h_pow : (A ^ p).toMat = cfc A (fun x => x ^ p) := by
        exact rfl
      have h_pow_neg : (A ^ (-p)).toMat = cfc A (fun x => x ^ (-p)) := by
        exact rfl
      have h_inv : (A ^ p).toMat * (A ^ (-p)).toMat = cfc A (fun x => x ^ p * x ^ (-p)) := by
        rw [ h_pow, h_pow_neg, ← coe_cfc_mul ];
        rfl;
      have h_inv : (A ^ p).toMat * (A ^ (-p)).toMat = cfc A (fun x => 1) := by
        rw [ h_inv ];
        refine' congr_arg _ ( cfc_congr_of_posDef hA _ );
        exact fun x hx => by simp +decide [ ← Real.rpow_add hx ] ;
      rw [ h_inv, cfc_const ] ; norm_num;
    exact h_inv;
  -- By definition of matrix inverse, if $(A^p) * (A^{-p}) = 1$, then $(A^{-p})$ is the inverse of $(A^p)$.
  have h_inv_def : (A ^ p).toMat⁻¹ = (A ^ (-p)).toMat := by
    exact Matrix.inv_eq_right_inv h_inv;
  convert congr_fun ( congr_fun h_inv_def i ) j using 1

lemma sandwich_le_one {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A B : HermitianMat n 𝕜) (hB : B.toMat.PosDef) (h : A ≤ B) :
    (A.conj (B ^ (-1/2 : ℝ)).toMat) ≤ 1 := by
  have h_sandwich : (B.conj (B ^ (-1/2 : ℝ)).toMat).toMat = 1 := by
    exact sandwich_identity B hB;
  convert conj_mono _ h using 1;
  exact HermitianMat.ext (id (Eq.symm h_sandwich))

lemma rpow_neg_mul_rpow_self {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] (A : HermitianMat n 𝕜) (hA : A.toMat.PosDef) (p : ℝ) : (A ^ (-p)).toMat * (A ^ p).toMat = 1 := by
  have := rpow_inv_eq_neg_rpow A hA p;
  rw [ ← this ];
  -- Since $A$ is positive definite, $A^p$ is also positive definite.
  have h_pos_def : (A ^ p).toMat.PosDef := by
    have h_pos_def : ∀ p : ℝ, A.toMat.PosDef → (A ^ p).toMat.PosDef := by
      intro p hA_pos_def
      have h_eigenvalues_pos : ∀ i, 0 < (A.H.eigenvalues i) ^ p := by
        exact fun i => Real.rpow_pos_of_pos ( by exact Matrix.PosDef.eigenvalues_pos hA i ) _;
      have h_eigenvalues_pos : (A ^ p).toMat.PosDef ↔ ∀ i, 0 < (A ^ p).H.eigenvalues i := by
        exact Matrix.IsHermitian.posDef_iff_eigenvalues_pos (H (A ^ p));
      have h_eigenvalues_pos : ∃ e : n ≃ n, (A ^ p).H.eigenvalues = fun i => (A.H.eigenvalues (e i)) ^ p := by
        exact Matrix.IsHermitian.cfc_eigenvalues (H A) fun x => x.rpow p;
      aesop;
    exact h_pos_def p hA;
  convert Matrix.nonsing_inv_mul _ _;
  exact isUnit_iff_ne_zero.mpr h_pos_def.det_pos.ne'

lemma isUnit_rpow_toMat {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A : HermitianMat n 𝕜) (hA : A.toMat.PosDef) (p : ℝ) : IsUnit (A ^ p).toMat := by
  have hA_inv : IsUnit (A ^ (-p)).toMat := by
    have hA_inv : (A ^ (-p)).toMat * (A ^ p).toMat = 1 := by
      exact rpow_neg_mul_rpow_self A hA p
    exact Matrix.isUnit_of_right_inverse hA_inv;
  -- Since $(A^{-p}) (A^p) = 1$, we have that $(A^p)$ is the inverse of $(A^{-p})$.
  have hA_inv : (A ^ p).toMat = (A ^ (-p)).toMat⁻¹ := by
    have hA_inv : (A ^ (-p)).toMat * (A ^ p).toMat = 1 := by
      exact rpow_neg_mul_rpow_self A hA p;
    exact Eq.symm (Matrix.inv_eq_right_inv hA_inv);
  aesop

lemma sandwich_inv {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A B : HermitianMat n 𝕜) (hB : B.toMat.PosDef) :
    (A.conj (B ^ (-1/2 : ℝ)).toMat)⁻¹ = A⁻¹.conj (B ^ (1/2 : ℝ)).toMat := by
  have hM : ∀ (M : Matrix n n 𝕜), IsUnit M → (A.conj M)⁻¹ = A⁻¹.conj (M⁻¹).conjTranspose := by
    exact fun M a => inv_conj A M a;
  rw [ hM ];
  · -- By definition of exponentiation, we know that $(B^{-1/2})^{-1} = B^{1/2}$.
    have h_inv : (B ^ (-1 / 2 : ℝ)).toMat⁻¹ = (B ^ (1 / 2 : ℝ)).toMat := by
      have h_inv : (B ^ (-1 / 2 : ℝ)).toMat * (B ^ (1 / 2 : ℝ)).toMat = 1 := by
        convert rpow_neg_mul_rpow_self B hB ( 1 / 2 ) using 1 ; norm_num;
      rw [ Matrix.inv_eq_right_inv h_inv ];
    aesop;
  · exact isUnit_rpow_toMat B hB (-1 / 2)

end uncategorized_cleanup
end HermitianMat
