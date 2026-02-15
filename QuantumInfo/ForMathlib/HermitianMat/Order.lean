/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Trace

namespace HermitianMat

open ComplexOrder
open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n m : Type*} [Fintype n] [Fintype m]
variable {A B C : HermitianMat n 𝕜}
variable {M : Matrix m n 𝕜} {N : Matrix n n 𝕜}

open MatrixOrder in
/-- The `MatrixOrder` instance for Matrix (the Loewner order) we keep open for
HermitianMat, always. -/
instance : PartialOrder (HermitianMat n 𝕜) :=
  inferInstanceAs (PartialOrder (selfAdjoint _))

open MatrixOrder in
instance : IsOrderedAddMonoid (HermitianMat n 𝕜) :=
  inferInstanceAs (IsOrderedAddMonoid (selfAdjoint _))

theorem le_iff : A ≤ B ↔ (B - A).mat.PosSemidef := by
  rfl

theorem zero_le_iff : 0 ≤ A ↔ A.mat.PosSemidef := by
  rw [le_iff, sub_zero]

theorem le_iff_mulVec_le : A ≤ B ↔
    ∀ x, star x ⬝ᵥ A.mat *ᵥ x ≤ star x ⬝ᵥ B.mat *ᵥ x := by
  simp [le_iff, Matrix.PosSemidef, B.H.sub A.H, Matrix.sub_mulVec]

instance [DecidableEq n] : ZeroLEOneClass (HermitianMat n 𝕜) where
  zero_le_one := by
    rw [zero_le_iff]
    exact Matrix.PosSemidef.one

theorem lt_iff_posdef : A < B ↔ (B - A).mat.PosSemidef ∧ A ≠ B :=
  lt_iff_le_and_ne

instance : IsStrictOrderedModule ℝ (HermitianMat n 𝕜) where
  smul_lt_smul_of_pos_left a ha b b₂ hb := by
    rw [HermitianMat.lt_iff_posdef] at hb ⊢
    simp only [← smul_sub, ne_eq, smul_right_inj ha.ne']
    exact ⟨hb.left.smul ha.le, hb.right⟩
  smul_lt_smul_of_pos_right a ha b b2 hb := by
    rw [HermitianMat.lt_iff_posdef] at ha ⊢
    rw [sub_zero] at ha
    rw [← sub_pos] at hb
    convert And.intro (ha.left.smul hb.le) ha.right using 1
    · simp [← sub_smul]
    simp only [ne_eq, not_iff_not]
    constructor
    · intro h
      rw [eq_comm, ← sub_eq_zero, ← sub_smul] at h
      simpa [eq_comm, hb.ne'] using h
    · rintro rfl; simp

theorem trace_pos {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]
    {A : HermitianMat n 𝕜} (hA : 0 < A) : 0 < A.trace := by
  open ComplexOrder in
  have hA' := hA.le
  rw [HermitianMat.zero_le_iff] at hA'
  have h_pos := Matrix.PosSemidef.trace_pos hA' (by simpa [HermitianMat.ext_iff] using hA.ne')
  rw [HermitianMat.trace_eq_re_trace]
  rw [RCLike.pos_iff] at h_pos
  exact h_pos.left

--Without these shortcut instances, `gcongr` fails to close certain goals...? Why? TODO
instance : PosSMulMono ℝ (HermitianMat n 𝕜) := inferInstance
instance : SMulPosMono ℝ (HermitianMat n 𝕜) := inferInstance

--Without explicitly giving this instance, Lean times out trying to find it sometimes.
instance : PosSMulReflectLE ℝ (HermitianMat n 𝕜) :=
  PosSMulMono.toPosSMulReflectLE

theorem le_trace_smul_one [DecidableEq n] (hA : 0 ≤ A) : A ≤ A.trace • 1 := by
  have hA' : A.mat.PosSemidef := zero_le_iff.mp hA
  refine (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hA'.1 A.trace).mp ?_
  rw [← A.sum_eigenvalues_eq_trace]
  intro i
  exact Finset.single_le_sum (fun j _ ↦ hA'.eigenvalues_nonneg j) (Finset.mem_univ i)

variable (M) in
theorem conj_le (hA : 0 ≤ A) : 0 ≤ A.conj M := by
  rw [zero_le_iff] at hA ⊢
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hA M

theorem convex_cone (hA : 0 ≤ A) (hB : 0 ≤ B) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    0 ≤ (c₁ • A + c₂ • B) := by
  rw [zero_le_iff] at hA hB ⊢
  exact (hA.smul hc₁).add (hB.smul hc₂)

theorem sq_nonneg [DecidableEq n] : 0 ≤ A ^ 2 := by
  simp [zero_le_iff, pow_two]
  nth_rewrite 1 [←Matrix.IsHermitian.eq A.H]
  exact Matrix.posSemidef_conjTranspose_mul_self A.mat

theorem ker_antitone [DecidableEq n] (hA : 0 ≤ A) : A ≤ B → B.ker ≤ A.ker := by
  intro h x hB
  replace h := (le_iff_mulVec_le.mp h) x
  rw [HermitianMat.mem_ker_iff_mulVec_zero] at hB ⊢
  rw [hB, dotProduct_zero] at h
  rw [zero_le_iff] at hA
  rw [← hA.dotProduct_mulVec_zero_iff]
  exact le_antisymm h (hA.right x)

theorem conj_mono (h : A ≤ B) : A.conj M ≤ B.conj M := by
  have h_conj_pos : (M * (B - A).mat * Mᴴ).PosSemidef :=
    Matrix.PosSemidef.mul_mul_conjTranspose_same h M
  constructor;
  · simp [conj, Matrix.IsHermitian, Matrix.mul_assoc]
  · simpa [Matrix.mul_sub, Matrix.sub_mul] using h_conj_pos.2

lemma conj_posDef [DecidableEq n] (hA : A.mat.PosDef) (hN : IsUnit N) :
    (A.conj N).mat.PosDef := by
  use HermitianMat.H _
  intro x hx_ne_zero
  open Matrix in
  have h_pos : 0 < star (Nᴴ *ᵥ x) ⬝ᵥ A *ᵥ (Nᴴ *ᵥ x) := by
    apply hA.2
    intro h
    apply hx_ne_zero
    simpa [ hN ] using Matrix.eq_zero_of_mulVec_eq_zero
      (by simpa [Matrix.det_conjTranspose] using hN.map Matrix.detMonoidHom) h
  convert h_pos using 1
  simp only [conj_apply_mat, mulVec_mulVec, Matrix.mul_assoc]
  simp [dotProduct_mulVec, mulVec_conjTranspose]

lemma inv_conj [DecidableEq n] {M : Matrix n n 𝕜} (hM : IsUnit M) :
    (A.conj M)⁻¹ = A⁻¹.conj (M⁻¹)ᴴ := by
  have h_inv : (M⁻¹)ᴴ * Mᴴ = 1 := by
    simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq] at hM
    simp [Matrix.conjTranspose_nonsing_inv, hM]
  ext1
  simp only [conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.conjTranspose_conjTranspose]
  simp only [mat_inv, mat_mk]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv h_inv, mul_assoc]
