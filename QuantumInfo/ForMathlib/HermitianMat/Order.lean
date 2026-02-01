/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Trace

namespace HermitianMat

open ComplexOrder

variable {α : Type*} [RCLike α]
variable {n : Type*} [Fintype n]
variable  {A B C : HermitianMat n α} {M N : Matrix n n α}

open MatrixOrder in
/-- The `MatrixOrder` instance for Matrix (the Loewner order) we keep open for
HermitianMat, always. -/
instance : PartialOrder (HermitianMat n α) :=
  inferInstance

theorem le_iff : A ≤ B ↔ (B - A).toMat.PosSemidef := by
  rfl

theorem zero_le_iff : 0 ≤ A ↔ A.toMat.PosSemidef := by
  rw [← propext_iff]
  apply congrArg Matrix.PosSemidef (sub_zero _)

theorem le_iff_mulVec_le : A ≤ B ↔ ∀ x, star x ⬝ᵥ A.toMat.mulVec x ≤ star x ⬝ᵥ B.toMat.mulVec x := by
  have hH : (B.toMat - A.toMat).IsHermitian := Matrix.IsHermitian.sub B.H A.H
  simp [le_iff, Matrix.PosSemidef, hH, Matrix.sub_mulVec]

instance [DecidableEq n] : ZeroLEOneClass (HermitianMat n ℂ) where
  zero_le_one := by
    rw [HermitianMat.zero_le_iff]
    exact Matrix.PosSemidef.one

theorem lt_iff_posdef : A < B ↔ (B - A).toMat.PosSemidef ∧ A ≠ B :=
  lt_iff_le_and_ne

instance : IsStrictOrderedModule ℝ (HermitianMat n α) where
    smul_lt_smul_of_pos_left a ha b b₂ hb := by
      rw [HermitianMat.lt_iff_posdef] at hb ⊢
      simp only [← smul_sub, selfAdjoint.val_smul, val_eq_coe, AddSubgroupClass.coe_sub, ne_eq,
        smul_right_inj ha.ne']
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

--Without these shortcut instances, `gcongr` fails to close certain goals...? Why? TODO
instance : PosSMulMono ℝ (HermitianMat n α) := inferInstance
instance : SMulPosMono ℝ (HermitianMat n α) := inferInstance

--Without explicitly giving this instance, Lean times out trying to find it sometimes.
instance {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜] :
    PosSMulReflectLE ℝ (HermitianMat d 𝕜) :=
  PosSMulMono.toPosSMulReflectLE

theorem le_trace_smul_one [DecidableEq n] (hA : 0 ≤ A) : A ≤ (A.trace : ℝ) • 1 := by
  have hA' : A.toMat.PosSemidef := zero_le_iff.mp hA
  refine (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hA'.1 A.trace).mp ?_
  rw [← A.sum_eigenvalues_eq_trace]
  intro i
  exact Finset.single_le_sum (fun j _ ↦ hA'.eigenvalues_nonneg j) (Finset.mem_univ i)

theorem conj_le (hA : 0 ≤ A) [Fintype m] (M : Matrix m n α) : 0 ≤ A.conj M := by
  rw [zero_le_iff] at hA ⊢
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hA M

theorem convex_cone (hA : 0 ≤ A) (hB : 0 ≤ B) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    : 0 ≤ (c₁ • A + c₂ • B) := by
  rw [zero_le_iff] at hA hB ⊢
  exact (hA.smul hc₁).add (hB.smul hc₂)

theorem sq_nonneg [DecidableEq n] : 0 ≤ A^2 := by
  simp [zero_le_iff, pow_two]
  nth_rewrite 1 [←Matrix.IsHermitian.eq A.H]
  exact Matrix.posSemidef_conjTranspose_mul_self A.toMat

theorem ker_antitone [DecidableEq n] (hA : 0 ≤ A) : A ≤ B → B.ker ≤ A.ker := fun h x hB ↦ by
  rw [HermitianMat.mem_ker_iff_mulVec_zero] at *
  replace h := (le_iff_mulVec_le.mp h) x
  rw [hB, dotProduct_zero] at h
  apply (Matrix.PosSemidef.dotProduct_mulVec_zero_iff (zero_le_iff.mp hA) x).mp
  exact eq_of_le_of_ge h ((zero_le_iff.mp hA).2 x)

section uncategorized_cleanup

open ComplexOrder

theorem conj_mono {n m 𝕜 : Type*} [Fintype n] [Fintype m] [DecidableEq n] [RCLike 𝕜]
    {A B : HermitianMat n 𝕜} (M : Matrix m n 𝕜) (h : A ≤ B) : A.conj M ≤ B.conj M := by
  -- Since $B - A \geq 0$, we have $M(B - A)M^* \geq 0$.
  have h_conj_pos : (M * (B - A).toMat * Matrix.conjTranspose M).PosSemidef := by
    exact Matrix.PosSemidef.mul_mul_conjTranspose_same h M;
  constructor;
  · unfold HermitianMat.conj; simp +decide [ Matrix.IsHermitian, Matrix.mul_assoc ] ;
  · intro x; have := h_conj_pos.2; simp_all +decide [ Matrix.mul_assoc, Matrix.dotProduct_mulVec]
    simpa only [ Matrix.mul_sub, Matrix.sub_mul ] using this x

lemma conj_posDef {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (A : HermitianMat n 𝕜) (hA : A.toMat.PosDef) (M : Matrix n n 𝕜) (hM : IsUnit M) :
    (A.conj M).toMat.PosDef := by
  refine' ⟨ _, _ ⟩;
  · simp +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
  · intro x hx_ne_zero
    have h_pos : 0 < star (M.conjTranspose.mulVec x) ⬝ᵥ A.toMat.mulVec (M.conjTranspose.mulVec x) := by
      apply hA.2;
      exact fun h => hx_ne_zero <| by simpa [ hM ] using Matrix.eq_zero_of_mulVec_eq_zero ( show M.conjTranspose.det ≠ 0 from by simpa [ Matrix.det_conjTranspose ] using hM.map ( Matrix.detMonoidHom ) ) h;
    convert h_pos using 1;
    simp [ Matrix.mul_assoc, Matrix.dotProduct_mulVec];
    simp [ Matrix.mulVec_conjTranspose ]

set_option maxHeartbeats 1000000 in
lemma inv_conj {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] (A : HermitianMat n 𝕜) (M : Matrix n n 𝕜) (hM : IsUnit M) :
    (A.conj M)⁻¹ = A⁻¹.conj (M⁻¹).conjTranspose := by
  -- Since $M$ is invertible, we have $M^{-1} * M = I$ and $(M^{-1})^* M^* = I$.
  have h_inv : (M⁻¹).conjTranspose * M.conjTranspose = 1 := by
    simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq] at hM
    simp [Matrix.conjTranspose_nonsing_inv, hM]
  unfold HermitianMat.conj;
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, val_eq_coe, Matrix.conjTranspose_conjTranspose]
  apply Subtype.ext
  field_simp
  convert Matrix.mul_inv_rev _ _ using 1;
  rw [ Matrix.mul_inv_rev, Matrix.inv_eq_left_inv h_inv, mul_assoc ];
  rfl
