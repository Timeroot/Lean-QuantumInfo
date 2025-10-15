/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.Matrix

open BigOperators
open Classical

namespace Matrix
noncomputable section traceNorm

open scoped ComplexOrder

variable {m n R : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike R]

/-- The trace norm of a matrix: Tr[√(A† A)]. -/
def traceNorm (A : Matrix m n R) : ℝ :=
  RCLike.re A.posSemidef_conjTranspose_mul_self.sqrt.trace

/-- The trace norm of the negative is equal to the trace norm. -/
@[simp]
theorem traceNorm_eq_neg_self (A : Matrix m n R) : traceNorm (-A) = traceNorm A := by
  unfold traceNorm
  congr! 3
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
  exact neg_neg _

--More generally sum of abs of singular values.
--Proposition 9.1.1 in Wilde
theorem traceNorm_Hermitian_eq_sum_abs_eigenvalues {A : Matrix n n R} (hA : A.IsHermitian) :
    A.traceNorm = ∑ i, abs (hA.eigenvalues i) :=
  sorry --Diagonalize A

/-- The trace norm is nonnegative. Property 9.1.1 in Wilde -/
theorem traceNorm_nonneg (A : Matrix m n R) : 0 ≤ A.traceNorm :=
  And.left $ RCLike.nonneg_iff.1
    A.posSemidef_conjTranspose_mul_self.posSemidef_sqrt.trace_nonneg

/-- The trace norm is zero only if the matrix is zero. -/
theorem traceNorm_zero_iff (A : Matrix m n R) : A.traceNorm = 0 ↔ A = 0 := by
  constructor
  · intro h
    have h₂ : ∀ i, A.posSemidef_conjTranspose_mul_self.posSemidef_sqrt.1.eigenvalues i = 0 :=
      sorry --sum of nonnegative values to zero
    have h₃ : A.posSemidef_conjTranspose_mul_self.sqrt = 0 :=
      sorry --all eigenvalues are zero iff matrix is zero
    have h₄ : Aᴴ * A = 0 :=
      sorry --sqrt is zero iff matrix is zero
    have h₅ : A = 0 :=
      sorry --conj_mul_self is zero iff A is zero
    exact h₅
  · intro hA
    subst hA
    have : (0 : Matrix m n R)ᴴ * (0 : Matrix m n R) = 0 := by simp
    rw [traceNorm, PosSemidef.sqrt_eq this _ Matrix.PosSemidef.zero]
    simp

/-- Trace norm is linear under scalar multiplication. Property 9.1.2 in Wilde -/
theorem traceNorm_smul (A : Matrix m n R) (c : R) : (c • A).traceNorm = ‖c‖ * A.traceNorm := by
  have h : (c • A)ᴴ * (c • A) = (‖c‖^2:R) • (Aᴴ * A) := by
    rw [conjTranspose_smul, RCLike.star_def, mul_smul, smul_mul, smul_smul]
    rw [RCLike.mul_conj c]
  rw [traceNorm, PosSemidef.sqrt_eq' h]
  have : RCLike.re (trace (‖c‖ • A.posSemidef_conjTranspose_mul_self.sqrt)) = ‖c‖ * traceNorm A := by
    simp [RCLike.smul_re]
    apply Or.inl
    rfl
  convert this
  rw [RCLike.real_smul_eq_coe_smul (K := R) ‖c‖]
  by_cases h : c = 0
  · nth_rewrite 8 [h]
    simp only [norm_zero, algebraMap.coe_zero, zero_smul]
    rw [← PosSemidef.sqrt_0]
    apply PosSemidef.sqrt_eq
    simp [h]
  · apply PosSemidef.sqrt_nonneg_smul _
    rw [RCLike.pos_iff_exists_ofReal]
    use ‖c‖
    simp [h]

/-- For square matrices, the trace norm is max Tr[U * A] over unitaries U.-/
theorem traceNorm_eq_max_tr_U (A : Matrix n n R) : IsGreatest {x | ∃ (U : unitaryGroup n R), (U.1 * A).trace = x} A.traceNorm := by
  sorry

/-- the trace norm satisfies the triangle inequality (for square matrices). TODO: Prove in general. -/
theorem traceNorm_triangleIneq (A B : Matrix n n R) : (A + B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  obtain ⟨Uab, h₁⟩ := (traceNorm_eq_max_tr_U (A + B)).left
  rw [Matrix.mul_add, Matrix.trace_add] at h₁
  obtain h₂ := (traceNorm_eq_max_tr_U A).right
  obtain h₃ := (traceNorm_eq_max_tr_U B).right
  simp only [upperBounds, Subtype.exists, exists_prop, Set.mem_setOf_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] at h₂ h₃
  replace h₂ := h₂ Uab.1 Uab.2
  replace h₃ := h₃ Uab.1 Uab.2
  rw [← RCLike.ofReal_le_ofReal (K := R)]
  simp only [RCLike.ofReal_add]
  calc _
    _ = _ + _ := h₁.symm
    _ ≤ ↑(traceNorm A) + trace (↑Uab * B) := by simp only [add_le_add_iff_right]; exact h₂
    _ ≤ _ := by simp only [add_le_add_iff_left]; exact h₃

theorem traceNorm_triangleIneq' (A B : Matrix n n R) : (A - B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  rw [sub_eq_add_neg A B, ←traceNorm_eq_neg_self B]
  exact traceNorm_triangleIneq A (-B)

theorem PosSemidef.traceNorm_PSD_eq_trace {A : Matrix m m R} (hA : A.PosSemidef) : A.traceNorm = A.trace := by
  have : Aᴴ * A = A^2 := by rw [hA.1, pow_two]
  rw [traceNorm, Matrix.PosSemidef.sqrt_eq' this, Matrix.PosSemidef.sqrt_sq hA, hA.1.re_trace_eq_trace]

end traceNorm

end Matrix
