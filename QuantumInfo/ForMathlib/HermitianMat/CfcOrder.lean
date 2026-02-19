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

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {f g : ℝ → ℝ}

theorem Commute.exists_HermitianMat_cfc (hAB : Commute A.mat B.mat) :
    ∃ C : HermitianMat d 𝕜, (∃ f : ℝ → ℝ, A = C.cfc f) ∧ (∃ g : ℝ → ℝ, B = C.cfc g) := by
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

theorem cfc_le_cfc_of_PosDef (hfg : ∀ i, 0 < i → f i ≤ g i) (hA : A.mat.PosDef) :
    A.cfc f ≤ A.cfc g := by
  rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
  intro i
  rw [Pi.sub_apply, sub_nonneg]
  rw [A.H.posDef_iff_eigenvalues_pos] at hA
  apply hfg
  apply hA

/- TODO: Write a version of this that holds more broadly for some sets. Esp closed intervals of reals,
which correspond nicely to closed intervals of matrices. Write the specialization to Set.univ (Monotone
instead of MonotoneOn). Also a version that works for StrictMonoOn. -/
theorem cfc_le_cfc_of_commute_monoOn (hf : MonotoneOn f (Set.Ioi 0))
  (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, C.zero_le_cfc] at hAB₂ ⊢
  intro i
  simp only [Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  · rw [HermitianMat.cfc_PosDef] at hA
    exact hA i
  · rw [HermitianMat.cfc_PosDef] at hB
    exact hB i
  · simpa using hAB₂ i

/-- TODO: See above -/
theorem cfc_le_cfc_of_commute (hf : Monotone f) (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, C.zero_le_cfc] at hAB₂ ⊢
  intro i
  simp only [Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  simpa using hAB₂ i

--This is the more general version that requires operator concave functions but doesn't require the inputs
-- to commute. Requires the correct statement of operator convexity though, which we don't have right now.
proof_wanted cfc_monoOn_pos_of_monoOn_posDef {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf_is_operator_convex : False) :
    MonotoneOn (HermitianMat.cfc · f) { A : HermitianMat d ℂ | A.mat.PosDef }

/-- Monotonicity of log on commuting operators. -/
theorem log_le_log_of_commute (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) (hA : A.mat.PosDef) :
    A.log ≤ B.log := by
  refine HermitianMat.cfc_le_cfc_of_commute_monoOn ?_ hAB₁ hAB₂ hA ?_
  · exact Real.strictMonoOn_log.monotoneOn
  · simpa using Matrix.PosDef.add_posSemidef hA hAB₂ --ew. abuse. TODO Cleanup

/-- Monotonicity of exp on commuting operators. -/
theorem le_of_exp_commute (hAB₁ : Commute A.mat B.mat) (hAB₂ : A.exp ≤ B.exp) :
    A ≤ B := by
  have hA : A = (A.exp).log := by simp [exp, log, ← HermitianMat.cfc_comp]
  have hB : B = (B.exp).log := by simp [exp, log, ← HermitianMat.cfc_comp]
  rw [hA, hB]
  apply HermitianMat.log_le_log_of_commute
  · apply HermitianMat.cfc_commute
    exact hAB₁
  · exact hAB₂
  · rw [exp, HermitianMat.cfc_PosDef]
    intro
    positivity

section uncategorized_cleanup

theorem rpow_nonneg (hA : 0 ≤ A) {p : ℝ} : 0 ≤ A ^ p := by
  convert zero_le_cfc_of_zero_le hA _
  exact fun i hi => Real.rpow_nonneg hi p

theorem inv_eq_rpow_neg_one (hA : A.mat.PosDef) : A⁻¹ = A ^ (-1 : ℝ) := by
  have := nonSingular_of_posDef hA
  rw [← cfc_inv, pow_eq_cfc, show ( fun x : ℝ => x⁻¹ ) = fun x : ℝ => x ^ ( -1 : ℝ ) by ext; norm_num [ Real.rpow_neg_one ] ]

theorem inv_ge_one_of_le_one (hA : A.mat.PosDef) (h : A ≤ 1) : 1 ≤ A⁻¹ := by
  --TODO Cleanup
  have := nonSingular_of_posDef hA
  have h_inv_ge_one : ∀ i, 1 ≤ 1 / A.H.eigenvalues i := by
    intro i
    have h_eigenvalue : 0 < A.H.eigenvalues i := by
      exact hA.eigenvalues_pos i
    have h_eigenvalue_le_one : A.H.eigenvalues i ≤ 1 := by
      have h_eigenvalue_le_one : ∀ x : d → 𝕜, x ≠ 0 → (star x ⬝ᵥ A.mat.mulVec x) / (star x ⬝ᵥ x) ≤ 1 := by
        intro x hx_nonzero
        have h_eigenvalue_le_one : (star x ⬝ᵥ A.mat.mulVec x) ≤ (star x ⬝ᵥ x) := by
          have h_eigenvalue_le_one : ∀ x : d → 𝕜, x ≠ 0 → (star x ⬝ᵥ A.mat.mulVec x) ≤ (star x ⬝ᵥ x) := by
            intro x hx_nonzero
            have h_eigenvalue_le_one : (star x ⬝ᵥ (1 - A.mat).mulVec x) ≥ 0 := by
              exact h.2 x
            simp_all +decide [ Matrix.sub_mulVec, dotProduct_sub ];
          exact h_eigenvalue_le_one x hx_nonzero
        generalize_proofs at *;
        convert div_le_one_of_le₀ h_eigenvalue_le_one _ using 1
        generalize_proofs at *;
        · exact PosMulReflectLT.toMulPosReflectLT;
        · exact dotProduct_star_self_nonneg x
      generalize_proofs at *;
      convert h_eigenvalue_le_one ( A.H.eigenvectorBasis i ) ( by intro h; simpa [ h ] using A.H.eigenvectorBasis.orthonormal.1 i ) using 1 ; simp [ Matrix.mulVec, dotProduct ];
      rw [ show ( ∑ x, ( starRingEnd 𝕜 ) ( A.H.eigenvectorBasis i x ) * ∑ x_1, A x x_1 * A.H.eigenvectorBasis i x_1 ) = ( A.H.eigenvalues i ) * ( ∑ x, ( starRingEnd 𝕜 ) ( A.H.eigenvectorBasis i x ) * A.H.eigenvectorBasis i x ) from ?_ ];
      · rw [ mul_div_cancel_right₀ ];
        · norm_cast;
        · have := A.H.eigenvectorBasis.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
          specialize this i i ; simp_all +decide [ Inner.inner ];
          simp_all [ mul_comm ];
      · have := A.H.mulVec_eigenvectorBasis i; simp_all [ Matrix.mulVec, dotProduct ] ;
        replace this := congr_arg ( fun x => ∑ j, ( starRingEnd 𝕜 ) ( A.H.eigenvectorBasis i j ) * x j ) this ; simp_all [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ] ;
        norm_num [ Algebra.smul_def ]
    exact one_le_one_div h_eigenvalue h_eigenvalue_le_one;
  have h_inv_ge_one : 0 ≤ A.cfc (fun x => x⁻¹ - 1) := by
    rw [ zero_le_cfc ];
    aesop;
  convert add_le_add_right h_inv_ge_one 1 using 1;
  · norm_num;
  · rw [ ← cfc_inv, ← sub_eq_zero ];
    rw [ ← sub_sub, ← cfc_sub ];
    simp [ Pi.sub_def ]

theorem sandwich_self (hB : B.mat.PosDef) :
    (B.conj (B ^ (-1/2 : ℝ)).mat) = 1 := by
  have hB_inv_sqrt : (B ^ (-1 / 2 : ℝ)).mat * (B ^ (-1 / 2 : ℝ)).mat = (B ^ (-1 : ℝ)).mat := by
    rw [ ← mat_rpow_add ] <;> norm_num
    rw [zero_le_iff]
    exact hB.posSemidef
  have hB_inv : (B ^ (-1 : ℝ)).mat = B.mat⁻¹ := by
    rw [← inv_eq_rpow_neg_one hB, mat_inv]
  rw [ hB_inv ] at hB_inv_sqrt;
  ext1
  simp [mul_assoc];
  rw [ ← Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp ];
  rw [ ← Matrix.mul_assoc, hB_inv_sqrt, Matrix.nonsing_inv_mul _ ];
  exact isUnit_iff_ne_zero.mpr hB.det_pos.ne'

lemma rpow_inv_eq_neg_rpow (hA : A.mat.PosDef) (p : ℝ) : (A ^ p)⁻¹ = A ^ (-p) := by
  --TODO cleanup
  ext i j;
  have h_inv : (A ^ p).mat * (A ^ (-p)).mat = 1 := by
    have h_inv : (A ^ p).mat * (A ^ (-p)).mat = 1 := by
      have h_pow : (A ^ p).mat = cfc A (fun x => x ^ p) := by
        exact rfl
      have h_pow_neg : (A ^ (-p)).mat = cfc A (fun x => x ^ (-p)) := by
        exact rfl
      have h_inv : (A ^ p).mat * (A ^ (-p)).mat = cfc A (fun x => x ^ p * x ^ (-p)) := by
        rw [ h_pow, h_pow_neg, ← mat_cfc_mul ];
        rfl;
      have h_inv : (A ^ p).mat * (A ^ (-p)).mat = cfc A (fun x => 1) := by
        rw [ h_inv ];
        refine' congr_arg _ ( cfc_congr_of_posDef hA _ );
        exact fun x hx => by simp [ ← Real.rpow_add hx ] ;
      rw [ h_inv, cfc_const ] ; norm_num;
    exact h_inv;
  -- By definition of matrix inverse, if $(A^p) * (A^{-p}) = 1$, then $(A^{-p})$ is the inverse of $(A^p)$.
  have h_inv_def : (A ^ p).mat⁻¹ = (A ^ (-p)).mat := by
    exact Matrix.inv_eq_right_inv h_inv;
  convert congr_fun ( congr_fun h_inv_def i ) j using 1

lemma sandwich_le_one (hB : B.mat.PosDef) (h : A ≤ B) :
    (A.conj (B ^ (-1/2 : ℝ)).mat) ≤ 1 := by
  convert ← conj_mono h using 1
  exact sandwich_self hB

lemma rpow_neg_mul_rpow_self (hA : A.mat.PosDef) (p : ℝ) :
    (A ^ (-p)).mat * (A ^ p).mat = 1 := by
  have := rpow_inv_eq_neg_rpow hA p;
  rw [ ← this ];
  -- Since $A$ is positive definite, $A^p$ is also positive definite.
  have h_pos_def : (A ^ p).mat.PosDef := by
    have h_pos_def : ∀ p : ℝ, A.mat.PosDef → (A ^ p).mat.PosDef := by
      intro p hA_pos_def
      have h_eigenvalues_pos : ∀ i, 0 < (A.H.eigenvalues i) ^ p := by
        exact fun i => Real.rpow_pos_of_pos ( by exact Matrix.PosDef.eigenvalues_pos hA i ) _;
      have h_eigenvalues_pos : (A ^ p).mat.PosDef ↔ ∀ i, 0 < (A ^ p).H.eigenvalues i := by
        exact Matrix.IsHermitian.posDef_iff_eigenvalues_pos (H (A ^ p));
      have h_eigenvalues_pos : ∃ e : d ≃ d, (A ^ p).H.eigenvalues = fun i => (A.H.eigenvalues (e i)) ^ p := by
        exact Matrix.IsHermitian.cfc_eigenvalues (H A) fun x => x.rpow p;
      aesop;
    exact h_pos_def p hA;
  convert Matrix.nonsing_inv_mul _ _;
  exact isUnit_iff_ne_zero.mpr h_pos_def.det_pos.ne'

lemma isUnit_rpow_toMat (hA : A.mat.PosDef) (p : ℝ) : IsUnit (A ^ p).mat := by
  have hA_inv : IsUnit (A ^ (-p)).mat := by
    have hA_inv : (A ^ (-p)).mat * (A ^ p).mat = 1 := by
      exact rpow_neg_mul_rpow_self hA p
    exact Matrix.isUnit_of_right_inverse hA_inv;
  -- Since $(A^{-p}) (A^p) = 1$, we have that $(A^p)$ is the inverse of $(A^{-p})$.
  have hA_inv : (A ^ p).mat = (A ^ (-p)).mat⁻¹ := by
    have hA_inv : (A ^ (-p)).mat * (A ^ p).mat = 1 := by
      exact rpow_neg_mul_rpow_self hA p;
    exact Eq.symm (Matrix.inv_eq_right_inv hA_inv);
  aesop

lemma sandwich_inv (hB : B.mat.PosDef) :
    (A.conj (B ^ (-1/2 : ℝ)).mat)⁻¹ = A⁻¹.conj (B ^ (1/2 : ℝ)).mat := by
  rw [inv_conj]
  · have h_inv : (B ^ (-1 / 2 : ℝ)).mat⁻¹ = (B ^ (1 / 2 : ℝ)).mat := by
      have h_inv : (B ^ (-1 / 2 : ℝ)).mat * (B ^ (1 / 2 : ℝ)).mat = 1 := by
        convert rpow_neg_mul_rpow_self hB ( 1 / 2 ) using 1 ; norm_num;
      exact Matrix.inv_eq_right_inv h_inv;
    aesop;
  · apply isUnit_rpow_toMat hB

end uncategorized_cleanup
end HermitianMat
