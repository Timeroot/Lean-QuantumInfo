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
  open MatrixOrder in
  RCLike.re (CFC.sqrt (Aᴴ * A)).trace

@[simp]
theorem traceNorm_zero : traceNorm (0 : Matrix m n R) = 0 := by
  simp [traceNorm]

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
  open MatrixOrder in
  And.left $ RCLike.nonneg_iff.1
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg

/-- The trace norm is zero iff. the matrix is zero. -/
theorem traceNorm_zero_iff (A : Matrix m n R) : A.traceNorm = 0 ↔ A = 0 := by
  open MatrixOrder in
  set B := CFC.sqrt (Aᴴ * A) with hB_de
  have hB_posSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  have hB_hermitian : B.IsHermitian := hB_posSemidef.1
  have hB_pos : B.PosSemidef := ⟨hB_hermitian, hB_posSemidef.2⟩
  constructor
  · intro h
    have h₂ : ∀ i, hB_hermitian.eigenvalues i = 0 := by
      have h_sum : (↑(∑ j, hB_hermitian.eigenvalues j) : R) = 0 := by
        rw [hB_hermitian.sum_eigenvalues_eq_trace, ← hB_hermitian.re_trace_eq_trace]
        unfold traceNorm at h
        norm_cast
      have : ∑ j, hB_hermitian.eigenvalues j = 0 := by exact_mod_cast h_sum
      intro i
      exact Finset.sum_eq_zero_iff_of_nonneg (λ j _ => hB_pos.eigenvalues_nonneg j)
        |>.mp this i (Finset.mem_univ i)
    have h₃ : CFC.sqrt (Aᴴ * A) = 0 := hB_hermitian.eigenvalues_zero_eq_zero h₂
    have h₄ : Aᴴ * A = 0 := by
      simpa [h₃] using (
        CFC.nnrpow_sqrt_two (Aᴴ * A)
        (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self)
      ).symm
    rw [Matrix.conjTranspose_mul_self_eq_zero] at h₄
    exact h₄
  · rintro rfl
    simp

/-- Trace norm is linear under scalar multiplication. Property 9.1.2 in Wilde -/
theorem traceNorm_smul (A : Matrix m n R) (c : R) : (c • A).traceNorm = ‖c‖ * A.traceNorm := by
  have h : (c • A)ᴴ * (c • A) = (‖c‖^2:R) • (Aᴴ * A) := by
    rw [conjTranspose_smul, RCLike.star_def, mul_smul, smul_mul, smul_smul]
    rw [RCLike.mul_conj c]
  rw [traceNorm, h]
  open MatrixOrder in
  have : RCLike.re (trace (‖c‖ • CFC.sqrt (Aᴴ * A))) = ‖c‖ * traceNorm A := by
    simp [RCLike.smul_re]
    apply Or.inl
    rfl
  convert this using 3
  rw [RCLike.real_smul_eq_coe_smul (K := R) ‖c‖]
  by_cases h : c = 0
  · subst c
    simp
  · have hM_pd : (Aᴴ * A).PosSemidef := by apply posSemidef_conjTranspose_mul_self
    set M := (Aᴴ * A)
    rw [sq]
    simp [MulAction.mul_smul]
    apply CFC.sqrt_unique;
    · simp; rw [CFC.sqrt_mul_sqrt_self M hM_pd.nonneg]
    · exact le_trans ( by norm_num ) (
        smul_le_smul_of_nonneg_left ( show 0 ≤ CFC.sqrt M from by exact (CFC.sqrt_nonneg M) ) ( norm_nonneg c ) );

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
  open MatrixOrder in
  rw [traceNorm, this, CFC.sqrt_sq A, hA.1.re_trace_eq_trace]

end traceNorm

end Matrix
