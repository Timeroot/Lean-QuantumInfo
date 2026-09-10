/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.Purification.GramFactorization
public import QuantumLib.QIT.States.Purification.ReferenceUnitary
public import QuantumLib.QIT.States.TraceNorm.Spectral
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import QuantumLib.QIT.States.Purification.ReferenceIsometry
public import QuantumLib.QIT.States.TraceNorm.BlockMatrix

/-!
# Trace-norm variational witness

This module proves the finite-dimensional trace-norm variational route:
existence of an attaining matrix unitary, the universal upper bound for every
matrix unitary, and the `ReferenceUnitary` squared repackaging used downstream
by the Uhlmann leaf.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

noncomputable section
universe u v
variable {a : Type u} [Fintype a] [DecidableEq a]

open QIT

namespace QIT

theorem complex_normSq_le_sq_of_abs_le {z : ℂ} {r : ℝ}
    (h : ‖z‖ ≤ r) :
    Complex.normSq z ≤ r ^ 2 := by
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hnorm : ‖z‖ ≤ r := h
  have hr : 0 ≤ r := hz.trans hnorm
  rw [Complex.normSq_eq_norm_sq]
  exact (sq_le_sq₀ hz hr).2 hnorm

/-- For a positive semidefinite matrix, every unitary trace pairing is bounded
by the real trace. -/
theorem posSemidef_trace_mul_unitary_abs_le_trace_re
    (P : CMatrix a) (hP : P.PosSemidef) (U : Matrix.unitaryGroup a ℂ) :
     ‖(P * (U : CMatrix a)).trace‖ ≤ P.trace.re := by
  classical
  let E : Matrix.unitaryGroup a ℂ := hP.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ))
  let U' : Matrix.unitaryGroup a ℂ := E⁻¹ * U * E
  have hPdiag : P = (E : CMatrix a) * D * (E⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [E, D, Function.comp_def, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hP.1.spectral_theorem
  have htrace :
      (P * (U : CMatrix a)).trace = (D * (U' : CMatrix a)).trace := by
    calc
      (P * (U : CMatrix a)).trace =
          (((E : CMatrix a) * D * (E⁻¹ : Matrix.unitaryGroup a ℂ)) * U).trace := by
            simp [hPdiag]
      _ = ((E : CMatrix a) * D * ((E⁻¹ : Matrix.unitaryGroup a ℂ) * U)).trace := by
            simp [Matrix.mul_assoc]
      _ = (((E⁻¹ : Matrix.unitaryGroup a ℂ) * U) * (E : CMatrix a) * D).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = (D * (U' : CMatrix a)).trace := by
            rw [Matrix.trace_mul_comm]
            simp [U', Matrix.mul_assoc]
  have hdiag :
      (D * (U' : CMatrix a)).trace =
        ∑ i, ((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i := by
    simpa [D] using trace_diagonal_mul_eq_sum
      (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ)) (U' : CMatrix a)
  have hsum_abs :
       ‖(D * (U' : CMatrix a)).trace‖ ≤
        ∑ i, ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖ := by
    rw [hdiag]
    simpa using
      (norm_sum_le (s := Finset.univ)
        (f := fun i => ((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i))
  have hterm :
      (fun i => ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖) ≤
        fun i => hP.1.eigenvalues i := by
    intro i
    have hlambda : 0 ≤ hP.1.eigenvalues i := hP.eigenvalues_nonneg i
    have hentry : ‖(U' : CMatrix a) i i‖ ≤ (1 : ℝ) :=
      entry_norm_bound_of_unitary (show (U' : CMatrix a) ∈ Matrix.unitaryGroup a ℂ from U'.2) i i
    calc
      ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖ =
          hP.1.eigenvalues i * ‖(U' : CMatrix a) i i‖ := by
            simp [abs_of_nonneg hlambda]
      _ ≤ hP.1.eigenvalues i * 1 :=
            mul_le_mul_of_nonneg_left hentry hlambda
      _ = hP.1.eigenvalues i := by simp
  have hsum_le : (∑ i, ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖) ≤
      ∑ i, hP.1.eigenvalues i := by
    exact Finset.sum_le_sum fun i _ => hterm i
  have htrace_sum : P.trace.re = ∑ i, hP.1.eigenvalues i := by
    have h := hP.1.trace_eq_sum_eigenvalues
    exact (congrArg Complex.re h).trans (by simp)
  calc
     ‖(P * (U : CMatrix a)).trace‖ =
         ‖(D * (U' : CMatrix a)).trace‖ := by rw [htrace]
    _ ≤ ∑ i, ‖((hP.1.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖ := hsum_abs
    _ ≤ ∑ i, hP.1.eigenvalues i := hsum_le
    _ = P.trace.re := htrace_sum.symm

private theorem contraction_column_norm_sq_le_one
    (K : CMatrix a) (hK : Kᴴ * K ≤ 1) (j : a) :
    (Finset.univ.sum fun i : a => ‖K i j‖ ^ 2) ≤ (1 : ℝ) := by
  have hnon : 0 ≤ ((1 : CMatrix a) - Kᴴ * K) := sub_nonneg.mpr hK
  have hpos : ((1 : CMatrix a) - Kᴴ * K).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hnon
  have hq := hpos.dotProduct_mulVec_nonneg (Pi.single j (1 : ℂ))
  have heq :
      star (Pi.single j (1 : ℂ)) ⬝ᵥ
          (((1 : CMatrix a) - Kᴴ * K) *ᵥ Pi.single j (1 : ℂ)) =
        1 - Finset.univ.sum (fun i : a => star (K i j) * K i j) := by
    classical
    simp [dotProduct, Matrix.mulVec, Matrix.mul_apply, Pi.single_apply]
  rw [heq] at hq
  have hqre : 0 ≤ (1 - Finset.univ.sum (fun i : a => star (K i j) * K i j)).re :=
    hq.1
  have hterm : ∀ i : a, (star (K i j) * K i j).re = ‖K i j‖ ^ 2 := by
    intro i
    rw [← Complex.normSq_eq_norm_sq]
    have h := Complex.normSq_eq_conj_mul_self (z := K i j)
    exact (congrArg Complex.re h.symm).trans (by simp)
  have hsumre :
      (Finset.univ.sum (fun i : a => star (K i j) * K i j)).re =
        Finset.univ.sum (fun i : a => ‖K i j‖ ^ 2) := by
    calc
      (Finset.univ.sum (fun i : a => star (K i j) * K i j)).re =
          Finset.univ.sum (fun i : a => (star (K i j) * K i j).re) := by
            simp
      _ = Finset.univ.sum (fun i : a => ‖K i j‖ ^ 2) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
  have hqre' :
      0 ≤ (1 : ℝ) - Finset.univ.sum (fun i : a => ‖K i j‖ ^ 2) := by
    have hqre'' : 0 ≤ (1 : ℝ) -
        (Finset.univ.sum (fun i : a => star (K i j) * K i j)).re := by
      simpa [Complex.sub_re] using hqre
    have hsum_expand :
        Finset.univ.sum (fun i : a => ‖K i j‖ ^ 2) =
          Finset.univ.sum (fun i : a =>
            (K i j).re * (K i j).re + (K i j).im * (K i j).im) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← hterm i]
      simp
    simpa [hsum_expand] using hqre''
  linarith

private theorem contraction_entry_norm_bound
    (K : CMatrix a) (hK : Kᴴ * K ≤ 1) (i j : a) :
    ‖K i j‖ ≤ (1 : ℝ) := by
  have hsum := contraction_column_norm_sq_le_one K hK j
  have hterm_nonneg : 0 ≤ ‖K i j‖ ^ 2 := sq_nonneg _
  have hterm_le_sum :
      ‖K i j‖ ^ 2 ≤ Finset.univ.sum (fun x : a => ‖K x j‖ ^ 2) := by
    classical
    exact Finset.single_le_sum
      (fun x _ => sq_nonneg (‖K x j‖))
      (Finset.mem_univ i)
  have hsq : ‖K i j‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    simpa using le_trans hterm_le_sum hsum
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).1 hsq

/-- For a positive semidefinite matrix, every contraction trace pairing is
bounded by the real trace.  The contraction hypothesis is the finite matrix
order form `KᴴK ≤ I`. -/
theorem posSemidef_trace_mul_contraction_abs_le_trace_re
    (P : CMatrix a) (hP : P.PosSemidef) (K : CMatrix a) (hK : Kᴴ * K ≤ 1) :
     ‖(P * K).trace‖ ≤ P.trace.re := by
  classical
  let E : Matrix.unitaryGroup a ℂ := hP.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ))
  let K' : CMatrix a := ((E⁻¹ : Matrix.unitaryGroup a ℂ) : CMatrix a) * K * (E : CMatrix a)
  have hPdiag : P = (E : CMatrix a) * D * (E⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [E, D, Function.comp_def, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hP.1.spectral_theorem
  have hK' : K'ᴴ * K' ≤ 1 := by
    have hK'eq : K'ᴴ * K' = (E : CMatrix a)ᴴ * (Kᴴ * K) * (E : CMatrix a) := by
      calc
        K'ᴴ * K' =
            (((E : CMatrix a)ᴴ * K * (E : CMatrix a))ᴴ *
              ((E : CMatrix a)ᴴ * K * (E : CMatrix a))) := by
                simp [K', Matrix.star_eq_conjTranspose]
        _ = (E : CMatrix a)ᴴ * Kᴴ *
              ((E : CMatrix a) * ((E : CMatrix a)ᴴ * K * (E : CMatrix a))) := by
                simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (E : CMatrix a)ᴴ * Kᴴ *
              (((E : CMatrix a) * (E : CMatrix a)ᴴ) * K * (E : CMatrix a)) := by
                simp [Matrix.mul_assoc]
        _ = (E : CMatrix a)ᴴ * Kᴴ * (K * (E : CMatrix a)) := by
                rw [show (E : CMatrix a) * (E : CMatrix a)ᴴ = 1 by
                  exact Unitary.coe_mul_star_self E]
                simp [Matrix.mul_assoc]
        _ = (E : CMatrix a)ᴴ * (Kᴴ * K) * (E : CMatrix a) := by
                simp [Matrix.mul_assoc]
    rw [hK'eq]
    calc
      (E : CMatrix a)ᴴ * (Kᴴ * K) * (E : CMatrix a) ≤
          (E : CMatrix a)ᴴ * (1 : CMatrix a) * (E : CMatrix a) := by
            -- matrix-order conjugation by a fixed matrix preserves positivity
            have hnon : 0 ≤ (1 : CMatrix a) - Kᴴ * K := sub_nonneg.mpr hK
            have hconj : 0 ≤
                (E : CMatrix a)ᴴ * ((1 : CMatrix a) - Kᴴ * K) * (E : CMatrix a) :=
              Matrix.nonneg_iff_posSemidef.mpr
                ((Matrix.nonneg_iff_posSemidef.mp hnon).conjTranspose_mul_mul_same
                  (E : CMatrix a))
            have hdiff :
                (E : CMatrix a)ᴴ * ((1 : CMatrix a) - Kᴴ * K) * (E : CMatrix a) =
                  ((E : CMatrix a)ᴴ * (1 : CMatrix a) * (E : CMatrix a)) -
                    ((E : CMatrix a)ᴴ * (Kᴴ * K) * (E : CMatrix a)) := by
              noncomm_ring
            exact sub_nonneg.mp (by simpa [hdiff] using hconj)
      _ = 1 := by
            calc
              (E : CMatrix a)ᴴ * (1 : CMatrix a) * (E : CMatrix a) =
                  (E : CMatrix a)ᴴ * (E : CMatrix a) := by
                    simp
              _ = 1 := by
                    exact Unitary.coe_star_mul_self E
  have htrace :
      (P * K).trace = (D * K').trace := by
    calc
      (P * K).trace =
          (((E : CMatrix a) * D * (E⁻¹ : Matrix.unitaryGroup a ℂ)) * K).trace := by
            simp [hPdiag]
      _ = ((E : CMatrix a) * D *
            (((E⁻¹ : Matrix.unitaryGroup a ℂ) : CMatrix a) * K)).trace := by
            simp [Matrix.mul_assoc]
      _ = ((((E⁻¹ : Matrix.unitaryGroup a ℂ) : CMatrix a) * K) *
            (E : CMatrix a) * D).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = (D * K').trace := by
            simpa [K', Matrix.mul_assoc] using
              (Matrix.trace_mul_comm ((((E⁻¹ : Matrix.unitaryGroup a ℂ) : CMatrix a) * K) *
                (E : CMatrix a)) D)
  have hdiag :
      (D * K').trace =
        ∑ i, ((hP.1.eigenvalues i : ℝ) : ℂ) * K' i i := by
    simpa [D] using trace_diagonal_mul_eq_sum
      (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ)) K'
  have hsum_abs :
       ‖(D * K').trace‖ ≤
        ∑ i, ‖((hP.1.eigenvalues i : ℝ) : ℂ) * K' i i‖ := by
    rw [hdiag]
    simpa using
      (norm_sum_le (s := Finset.univ)
        (f := fun i => ((hP.1.eigenvalues i : ℝ) : ℂ) * K' i i))
  have hterm :
      (fun i => ‖((hP.1.eigenvalues i : ℝ) : ℂ) * K' i i‖) ≤
        fun i => hP.1.eigenvalues i := by
    intro i
    have hlambda : 0 ≤ hP.1.eigenvalues i := hP.eigenvalues_nonneg i
    have hentry : ‖K' i i‖ ≤ (1 : ℝ) :=
      contraction_entry_norm_bound K' hK' i i
    calc
      ‖((hP.1.eigenvalues i : ℝ) : ℂ) * K' i i‖ =
          hP.1.eigenvalues i * ‖K' i i‖ := by
            simp [abs_of_nonneg hlambda]
      _ ≤ hP.1.eigenvalues i * 1 :=
            mul_le_mul_of_nonneg_left hentry hlambda
      _ = hP.1.eigenvalues i := by simp
  have hsum_le :
      (∑ i, ‖((hP.1.eigenvalues i : ℝ) : ℂ) * K' i i‖) ≤
        ∑ i, hP.1.eigenvalues i := by
    exact Finset.sum_le_sum fun i _ => hterm i
  have htrace_sum : P.trace.re = ∑ i, hP.1.eigenvalues i := by
    have h := hP.1.trace_eq_sum_eigenvalues
    exact (congrArg Complex.re h).trans (by simp)
  calc
     ‖(P * K).trace‖ =
         ‖(D * K').trace‖ := by rw [htrace]
    _ ≤ ∑ i, ‖((hP.1.eigenvalues i : ℝ) : ℂ) * K' i i‖ := hsum_abs
    _ ≤ ∑ i, hP.1.eigenvalues i := hsum_le
    _ = P.trace.re := htrace_sum.symm

/-- Two square matrices with the same Gram matrix `X Xᴴ = S Sᴴ` differ by a
unitary factor on the right. -/
theorem exists_unitary_eq_mul_of_mul_conjTranspose_eq (X S : CMatrix a)
    (hGram : X * Xᴴ = S * Sᴴ) :
    ∃ U : Matrix.unitaryGroup a ℂ, S = X * (U : CMatrix a) := by
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := X) (B := S) hGram (Nat.le_refl _)
  exact ⟨⟨Matrix.transpose V.matrix, V.transpose_matrix_mem_unitary⟩, hV⟩

/-- The square root of a Hermitian conjugation `E A E` factors through the
square root of `A`: it equals `E √A U` for some unitary `U`. -/
theorem exists_unitary_psdSqrt_conj_eq (E A : CMatrix a) (hA : A.PosSemidef)
    (hEherm : E.IsHermitian) :
    ∃ U : Matrix.unitaryGroup a ℂ,
      psdSqrt (E * A * E) = E * psdSqrt A * (U : CMatrix a) := by
  have hEA : (E * A * E).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same E
    rw [hEherm.eq] at h
    simpa [Matrix.mul_assoc] using h
  refine exists_unitary_eq_mul_of_mul_conjTranspose_eq (E * psdSqrt A)
    (psdSqrt (E * A * E)) ?_
  rw [Matrix.conjTranspose_mul, hEherm.eq, psdSqrt_isHermitian A,
    psdSqrt_isHermitian (E * A * E), psdSqrt_mul_self_of_posSemidef hEA]
  calc
    E * psdSqrt A * (psdSqrt A * E) = E * (psdSqrt A * psdSqrt A) * E := by
      simp [Matrix.mul_assoc]
    _ = E * A * E := by rw [psdSqrt_mul_self_of_posSemidef hA]

/-- The unitary-attainment half of the finite-dimensional trace-norm
variational characterization: there is a unitary matrix attaining
`|Tr(MU)| = ‖M‖₁`. -/
theorem traceNorm_variational_exists_unitary_abs_trace (M : CMatrix a) :
    ∃ U : Matrix.unitaryGroup a ℂ,
       ‖(M * (U : Matrix a a ℂ)).trace‖ = traceNorm M := by
  classical
  let P : CMatrix a := psdSqrt (Mᴴ * M)
  have hP_hm : P.IsHermitian := psdSqrt_isHermitian (Mᴴ * M)
  have hP_sq : P * P = Mᴴ * M :=
    psdSqrt_mul_self_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self M)
  have hGram : P * Pᴴ = Mᴴ * (Mᴴ)ᴴ := by
    rw [hP_hm.eq, hP_sq, Matrix.conjTranspose_conjTranspose]
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := P) (B := Mᴴ) hGram (Nat.le_refl _)
  let W : Matrix a a ℂ := Matrix.transpose V.matrix
  have hW_unit : W ∈ Matrix.unitaryGroup a ℂ := by
    simpa [W] using V.transpose_matrix_mem_unitary
  refine ⟨⟨W, hW_unit⟩, ?_⟩
  have hM : M = Wᴴ * P := by
    have h := congrArg Matrix.conjTranspose hV
    simpa [W, hP_hm.eq, Matrix.conjTranspose_mul] using h
  have htrace : (M * W).trace = P.trace := by
    calc
      (M * W).trace = (Wᴴ * P * W).trace := by simp [hM, Matrix.mul_assoc]
      _ = (W * Wᴴ * P).trace := by
        rw [Matrix.trace_mul_cycle]
      _ = P.trace := by
        change ((W * star W) * P).trace = P.trace
        rw [(Matrix.mem_unitaryGroup_iff.mp hW_unit)]
        simp
  have hP_trace_nonneg : 0 ≤ P.trace :=
    Matrix.PosSemidef.trace_nonneg (psdSqrt_pos (Mᴴ * M))
  calc
     ‖(M * W).trace‖ = ‖P.trace‖ := by rw [htrace]
    _ = traceNorm M := by
      have hnorm : ‖P.trace‖ = P.trace.re := by
        have hcoe := Complex.eq_coe_norm_of_nonneg hP_trace_nonneg
        have hre : P.trace.re = ‖P.trace‖ := by
          exact (congrArg Complex.re hcoe).trans (by simp)
        exact hre.symm
      simpa [P, traceNorm] using hnorm

/-- The universal upper-bound half of the finite-dimensional trace-norm
variational characterization: every unitary matrix gives
`|Tr(MU)| ≤ ‖M‖₁`. -/
theorem traceNorm_variational_unitary_abs_trace_le
    (M : CMatrix a) (U : Matrix.unitaryGroup a ℂ) :
     ‖(M * (U : Matrix a a ℂ)).trace‖ ≤ traceNorm M := by
  classical
  let P : CMatrix a := psdSqrt (Mᴴ * M)
  have hP_hm : P.IsHermitian := psdSqrt_isHermitian (Mᴴ * M)
  have hP_sq : P * P = Mᴴ * M :=
    psdSqrt_mul_self_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self M)
  have hGram : P * Pᴴ = Mᴴ * (Mᴴ)ᴴ := by
    rw [hP_hm.eq, hP_sq, Matrix.conjTranspose_conjTranspose]
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := P) (B := Mᴴ) hGram (Nat.le_refl _)
  let W : Matrix.unitaryGroup a ℂ :=
    ⟨Matrix.transpose V.matrix, V.transpose_matrix_mem_unitary⟩
  have hM : M = (W : CMatrix a)ᴴ * P := by
    have h := congrArg Matrix.conjTranspose hV
    simpa [W, hP_hm.eq, Matrix.conjTranspose_mul] using h
  let Z : Matrix.unitaryGroup a ℂ := U * W⁻¹
  have htrace : (M * (U : CMatrix a)).trace = (P * (Z : CMatrix a)).trace := by
    calc
      (M * (U : CMatrix a)).trace = ((W : CMatrix a)ᴴ * P * U).trace := by
        simp [hM, Matrix.mul_assoc]
      _ = (P * ((U : CMatrix a) * star (W : CMatrix a))).trace := by
        rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
        simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      _ = (P * (Z : CMatrix a)).trace := by
        simp [Z]
  have hP_trace_abs_le :=
    posSemidef_trace_mul_unitary_abs_le_trace_re P (psdSqrt_pos (Mᴴ * M)) Z
  calc
     ‖(M * (U : CMatrix a)).trace‖ =
         ‖(P * (Z : CMatrix a)).trace‖ := by rw [htrace]
    _ ≤ P.trace.re := hP_trace_abs_le
    _ = traceNorm M := by rfl

/-- The trace-norm variational upper bound for contractions.

This extends `traceNorm_variational_unitary_abs_trace_le` from unitary test
matrices to arbitrary finite-dimensional contractions, stated as `KᴴK ≤ I` in
the matrix order. -/
theorem traceNorm_variational_contraction_abs_trace_le
    (M K : CMatrix a) (hK : Kᴴ * K ≤ 1) :
     ‖(M * K).trace‖ ≤ traceNorm M := by
  classical
  let P : CMatrix a := psdSqrt (Mᴴ * M)
  have hP_hm : P.IsHermitian := psdSqrt_isHermitian (Mᴴ * M)
  have hP_sq : P * P = Mᴴ * M :=
    psdSqrt_mul_self_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self M)
  have hGram : P * Pᴴ = Mᴴ * (Mᴴ)ᴴ := by
    rw [hP_hm.eq, hP_sq, Matrix.conjTranspose_conjTranspose]
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := P) (B := Mᴴ) hGram (Nat.le_refl _)
  let W : Matrix.unitaryGroup a ℂ :=
    ⟨Matrix.transpose V.matrix, V.transpose_matrix_mem_unitary⟩
  have hM : M = (W : CMatrix a)ᴴ * P := by
    have h := congrArg Matrix.conjTranspose hV
    simpa [W, hP_hm.eq, Matrix.conjTranspose_mul] using h
  let Z : CMatrix a := K * (W : CMatrix a)ᴴ
  have hZ : Zᴴ * Z ≤ 1 := by
    have hZeq : Zᴴ * Z = (W : CMatrix a) * (Kᴴ * K) * (W : CMatrix a)ᴴ := by
      simp [Z, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hZeq]
    calc
      (W : CMatrix a) * (Kᴴ * K) * (W : CMatrix a)ᴴ ≤
          (W : CMatrix a) * (1 : CMatrix a) * (W : CMatrix a)ᴴ := by
            have hnon : 0 ≤ (1 : CMatrix a) - Kᴴ * K := sub_nonneg.mpr hK
            have hconj : 0 ≤
                (W : CMatrix a) * ((1 : CMatrix a) - Kᴴ * K) * (W : CMatrix a)ᴴ :=
              by
                have h :=
                  (Matrix.nonneg_iff_posSemidef.mp hnon).conjTranspose_mul_mul_same
                    ((W : CMatrix a)ᴴ)
                simpa [Matrix.conjTranspose_conjTranspose] using
                  (Matrix.nonneg_iff_posSemidef.mpr h)
            have hdiff :
                (W : CMatrix a) * ((1 : CMatrix a) - Kᴴ * K) * (W : CMatrix a)ᴴ =
                  ((W : CMatrix a) * (1 : CMatrix a) * (W : CMatrix a)ᴴ) -
                    ((W : CMatrix a) * (Kᴴ * K) * (W : CMatrix a)ᴴ) := by
              noncomm_ring
            exact sub_nonneg.mp (by simpa [hdiff] using hconj)
      _ = 1 := by
            rw [Matrix.mul_one]
            change (W : CMatrix a) * star (W : CMatrix a) = 1
            exact (Matrix.mem_unitaryGroup_iff.mp W.2)
  have htrace : (M * K).trace = (P * Z).trace := by
    calc
      (M * K).trace = ((W : CMatrix a)ᴴ * P * K).trace := by
        simp [hM, Matrix.mul_assoc]
      _ = ((W : CMatrix a)ᴴ * (P * K)).trace := by
        exact congrArg Matrix.trace
          (Matrix.mul_assoc ((W : CMatrix a)ᴴ) P K)
      _ = ((P * K) * (W : CMatrix a)ᴴ).trace := by
        exact Matrix.trace_mul_comm ((W : CMatrix a)ᴴ) (P * K)
      _ = (P * (K * (W : CMatrix a)ᴴ)).trace := by
        simp [Matrix.mul_assoc]
      _ = (P * Z).trace := rfl
  calc
     ‖(M * K).trace‖ = ‖(P * Z).trace‖ := by rw [htrace]
    _ ≤ P.trace.re :=
          posSemidef_trace_mul_contraction_abs_le_trace_re P
            (psdSqrt_pos (Mᴴ * M)) Z hZ
    _ = traceNorm M := by rfl

/-- Matrix-level packaging of the finite-dimensional trace-norm variational
characterization: an attaining unitary exists and every unitary is bounded by
the trace norm. -/
theorem traceNorm_eq_max_unitary_abs_trace (M : CMatrix a) :
    (∃ U : Matrix.unitaryGroup a ℂ,
       ‖(M * (U : Matrix a a ℂ)).trace‖ = traceNorm M) ∧
      ∀ U : Matrix.unitaryGroup a ℂ,
         ‖(M * (U : Matrix a a ℂ)).trace‖ ≤ traceNorm M :=
  ⟨traceNorm_variational_exists_unitary_abs_trace M,
    traceNorm_variational_unitary_abs_trace_le M⟩

private theorem kronecker_one_right_mem_unitaryGroup
    {b : Type v} [Fintype b] [DecidableEq b] (U : Matrix.unitaryGroup b ℂ) :
    (1 : CMatrix a) ⊗ₖ (U : CMatrix b) ∈
      Matrix.unitaryGroup (a × b) ℂ := by
  let I : Matrix.unitaryGroup a ℂ := ⟨1, by simp⟩
  simpa using Matrix.kronecker_mem_unitary I.2 U.2

private theorem referenceIsometry_matrix_mul_conjTranspose
    {b : Type v} [Fintype b] [DecidableEq b] (V : ReferenceIsometry b b) :
    V.matrix * Matrix.conjTranspose V.matrix = 1 := by
  exact (Matrix.mul_eq_one_comm_of_card_eq b b ℂ rfl).mp V.isometry

private theorem referenceIsometry_matrix_mem_unitary
    {b : Type v} [Fintype b] [DecidableEq b] (V : ReferenceIsometry b b) :
    V.matrix ∈ Matrix.unitaryGroup b ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact referenceIsometry_matrix_mul_conjTranspose V

private theorem applyMatrixRight_eq_kronecker_conj
    {b : Type v} [Fintype b] [DecidableEq b]
    (V : ReferenceIsometry b b) (X : CMatrix (a × b)) :
    V.applyMatrixRight X =
      ((1 : CMatrix a) ⊗ₖ V.matrix) * X *
        Matrix.conjTranspose ((1 : CMatrix a) ⊗ₖ V.matrix) := by
  ext x y
  simp only [ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, one_mul]
  have hinner : ∀ z : a, ∀ t : b,
      (∑ z' : a, ∑ u : b,
          (if x.1 = z' then V.matrix x.2 u * X (z', u) (z, t) else 0)) =
        ∑ u : b, V.matrix x.2 u * X (x.1, u) (z, t) := by
    intro z t
    rw [Finset.sum_eq_single x.1]
    · simp
    · intro z' _ hz'
      have hne : x.1 ≠ z' := hz'.symm
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ x.1))
  simp_rw [hinner]
  let L : ℂ := ∑ t : b,
    (∑ u : b, V.matrix x.2 u * X (x.1, u) (y.1, t)) * star (V.matrix y.2 t)
  have hcollapse :
      (∑ z : a,
        ∑ t : b,
          (∑ u : b, V.matrix x.2 u * X (x.1, u) (z, t)) *
            star (if y.1 = z then V.matrix y.2 t else 0)) = L := by
    rw [Finset.sum_eq_single y.1]
    · simp [L]
    · intro z _ hz
      have hne : y.1 ≠ z := hz.symm
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ y.1))
  rw [hcollapse]

private theorem kronecker_one_referenceIsometry_mem_unitary
    {b : Type v} [Fintype b] [DecidableEq b] (V : ReferenceIsometry b b) :
    (1 : CMatrix a) ⊗ₖ V.matrix ∈ Matrix.unitaryGroup (a × b) ℂ := by
  let I : Matrix.unitaryGroup a ℂ := ⟨1, by simp⟩
  exact Matrix.kronecker_mem_unitary I.2 (referenceIsometry_matrix_mem_unitary V)

/-- Trace norm is contractive under tracing out the first subsystem.  This
standalone trace-norm theorem is the non-circular contraction step used by
post-selection reductions and by Fuchs--van de Graaf style arguments. -/
theorem traceNorm_traceLeft_le_matrix
    {b : Type v} [Fintype b] [DecidableEq b] (X : CMatrix (a × b)) :
    traceNorm (Matrix.traceLeft X) ≤ traceNorm X := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace
    (Matrix.traceLeft X)
  let Ubig : Matrix.unitaryGroup (a × b) ℂ :=
    ⟨(1 : CMatrix a) ⊗ₖ (U : CMatrix b),
      kronecker_one_right_mem_unitaryGroup U⟩
  calc
    traceNorm (Matrix.traceLeft X)
        = ‖((Matrix.traceLeft X) * (U : CMatrix b)).trace‖ :=
          hU.symm
    _ = ‖(X * (Ubig : CMatrix (a × b))).trace‖ := by
          congr 1
          simpa [Ubig] using
            traceLeft_mul_trace_eq_trace_mul_kronecker_one_right X
              (U : CMatrix b)
    _ ≤ traceNorm X := traceNorm_variational_unitary_abs_trace_le X Ubig

private theorem kronecker_one_left_mem_unitaryGroup
    {b : Type v} [Fintype b] [DecidableEq b] (U : Matrix.unitaryGroup a ℂ) :
    (U : CMatrix a) ⊗ₖ (1 : CMatrix b) ∈
      Matrix.unitaryGroup (a × b) ℂ := by
  let I : Matrix.unitaryGroup b ℂ := ⟨1, by simp⟩
  simpa using Matrix.kronecker_mem_unitary U.2 I.2

/-- Trace norm is contractive under tracing out the second subsystem. -/
theorem traceNorm_traceRight_le_matrix
    {b : Type v} [Fintype b] [DecidableEq b] (X : CMatrix (a × b)) :
    traceNorm (Matrix.traceRight X) ≤ traceNorm X := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace
    (Matrix.traceRight X)
  let Ubig : Matrix.unitaryGroup (a × b) ℂ :=
    ⟨(U : CMatrix a) ⊗ₖ (1 : CMatrix b),
      kronecker_one_left_mem_unitaryGroup U⟩
  calc
    traceNorm (Matrix.traceRight X)
        = ‖((Matrix.traceRight X) * (U : CMatrix a)).trace‖ :=
          hU.symm
    _ = ‖(X * (Ubig : CMatrix (a × b))).trace‖ := by
          congr 1
          simpa [Ubig] using
            (trace_mul_kronecker_one_right_eq_traceRight X
              (U : CMatrix a)).symm
    _ ≤ traceNorm X := traceNorm_variational_unitary_abs_trace_le X Ubig

/-- Drop a terminal unit register from a matrix. -/
def dropRightUnitMatrix {α : Type u} [Fintype α] [DecidableEq α]
    (X : CMatrix (α × PUnit)) : CMatrix α :=
  fun i j => X (i, PUnit.unit) (j, PUnit.unit)

/-- Dropping a terminal unit register is a partial trace over that unit
register, hence it does not increase trace norm. -/
theorem traceNorm_dropRightUnitMatrix_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (X : CMatrix (α × PUnit)) :
    traceNorm (dropRightUnitMatrix X) ≤ traceNorm X := by
  have hdrop :
      dropRightUnitMatrix X = Matrix.traceRight X := by
    ext i j
    simp [dropRightUnitMatrix, Matrix.traceRight]
  rw [hdrop]
  exact traceNorm_traceRight_le_matrix X

/-- A square reference isometry acting on the right/reference tensor factor
does not increase the trace norm.  Since the source and target reference
dimensions agree, the isometry is unitary, so this is unitary conjugation
invariance expressed in the input-first convention used by CKR reductions. -/
theorem traceNorm_applyMatrixRight_le
    {b : Type v} [Fintype b] [DecidableEq b]
    (V : ReferenceIsometry b b) (X : CMatrix (a × b)) :
    traceNorm (V.applyMatrixRight X) ≤ traceNorm X := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (V.applyMatrixRight X)
  let K : Matrix.unitaryGroup (a × b) ℂ :=
    ⟨(1 : CMatrix a) ⊗ₖ V.matrix,
      kronecker_one_referenceIsometry_mem_unitary (a := a) V⟩
  let Uin : Matrix.unitaryGroup (a × b) ℂ := K⁻¹ * U * K
  have htrace : ((V.applyMatrixRight X) * (U : CMatrix (a × b))).trace =
      (X * (Uin : CMatrix (a × b))).trace := by
    rw [applyMatrixRight_eq_kronecker_conj]
    change (((K : CMatrix (a × b)) * X * star (K : CMatrix (a × b))) * U).trace =
      (X * (Uin : CMatrix (a × b))).trace
    calc
      (((K : CMatrix (a × b)) * X * star (K : CMatrix (a × b))) * U).trace
          = ((K : CMatrix (a × b)) * X * (star (K : CMatrix (a × b)) * U)).trace := by
            simp [Matrix.mul_assoc]
      _ = (X * (star (K : CMatrix (a × b)) * U) * (K : CMatrix (a × b))).trace := by
            rw [Matrix.trace_mul_cycle]
            rw [Matrix.trace_mul_comm]
            simp [Matrix.mul_assoc]
      _ = (X * (Uin : CMatrix (a × b))).trace := by
            simp [Uin, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  calc
    traceNorm (V.applyMatrixRight X) =
         ‖((V.applyMatrixRight X) * (U : CMatrix (a × b))).trace‖ := hU.symm
    _ = ‖(X * (Uin : CMatrix (a × b))).trace‖ := by rw [htrace]
    _ ≤ traceNorm X := traceNorm_variational_unitary_abs_trace_le X Uin

/-- Trace norm triangle inequality, proved from the finite-dimensional
variational characterization. -/
theorem traceNorm_add_le (A B : CMatrix a) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (A + B)
  have htri : ‖((A + B) * (U : CMatrix a)).trace‖ ≤
       ‖(A * (U : CMatrix a)).trace‖ +
         ‖(B * (U : CMatrix a)).trace‖ := by
    rw [Matrix.add_mul, Matrix.trace_add]
    simpa using norm_add_le ((A * (U : CMatrix a)).trace)
      ((B * (U : CMatrix a)).trace)
  calc
    traceNorm (A + B) = ‖((A + B) * (U : CMatrix a)).trace‖ := hU.symm
    _ ≤ ‖(A * (U : CMatrix a)).trace‖ +
         ‖(B * (U : CMatrix a)).trace‖ := htri
    _ ≤ traceNorm A + traceNorm B := add_le_add
      (traceNorm_variational_unitary_abs_trace_le A U)
      (traceNorm_variational_unitary_abs_trace_le B U)

/-- Triangle inequality for matrix trace distance. -/
theorem traceNormDistance_triangle (A B C : CMatrix a) :
    traceNormDistance A C ≤
      traceNormDistance A B + traceNormDistance B C := by
  have hdiff : A - C = (A - B) + (B - C) := by
    ext i j
    simp [Matrix.sub_apply, Matrix.add_apply]
  calc
    traceNormDistance A C = traceNorm ((A - B) + (B - C)) := by
      rw [traceNormDistance, hdiff]
    _ ≤ traceNorm (A - B) + traceNorm (B - C) := traceNorm_add_le (A - B) (B - C)
    _ = traceNormDistance A B + traceNormDistance B C := rfl

/-- Triangle inequality for matrix normalized trace distance. -/
theorem normalizedTraceDistance_triangle (A B C : CMatrix a) :
    normalizedTraceDistance A C ≤
      normalizedTraceDistance A B + normalizedTraceDistance B C := by
  have hdiff : A - C = (A - B) + (B - C) := by
    ext i j
    simp [Matrix.sub_apply, Matrix.add_apply]
  have htri : traceNorm (A - C) ≤ traceNorm (A - B) + traceNorm (B - C) := by
    rw [hdiff]
    exact traceNorm_add_le (A - B) (B - C)
  calc
    normalizedTraceDistance A C =
        (1 / 2 : ℝ) * traceNorm (A - C) := rfl
    _ ≤ (1 / 2 : ℝ) * (traceNorm (A - B) + traceNorm (B - C)) :=
        mul_le_mul_of_nonneg_left htri (by norm_num)
    _ = normalizedTraceDistance A B + normalizedTraceDistance B C := by
        simp [normalizedTraceDistance, traceNormDistance, mul_add]

end QIT

namespace MState

/-- Triangle inequality for state normalized trace distance. -/
theorem normalizedTraceDistance_triangle (ρ σ τ : MState a) :
    ρ.normalizedTraceDistance τ ≤
      ρ.normalizedTraceDistance σ + σ.normalizedTraceDistance τ :=
  QIT.normalizedTraceDistance_triangle ρ.m σ.m τ.m

end MState

namespace QIT

/-- Trace norm is positively homogeneous for nonnegative real scalars, in the
one-sided form needed for finite averaging arguments. -/
theorem traceNorm_real_smul_le {c : ℝ} (hc : 0 ≤ c) (M : CMatrix a) :
    traceNorm (((c : ℂ) • M)) ≤ c * traceNorm M := by
  classical
  obtain ⟨U, hU⟩ :=
    traceNorm_variational_exists_unitary_abs_trace (((c : ℂ) • M))
  have htrace : ((((c : ℂ) • M) * (U : CMatrix a)).trace) =
      (c : ℂ) * ((M * (U : CMatrix a)).trace) := by
    rw [Matrix.smul_mul, Matrix.trace_smul]
    simp [smul_eq_mul]
  calc
    traceNorm (((c : ℂ) • M)) =
         ‖(((c : ℂ) • M) * (U : CMatrix a)).trace‖ := hU.symm
    _ = c * ‖(M * (U : CMatrix a)).trace‖ := by
      rw [htrace]
      simp [Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ c * traceNorm M := mul_le_mul_of_nonneg_left
      (traceNorm_variational_unitary_abs_trace_le M U) hc

theorem trace_abs_le_traceNorm {a : Type u} [Fintype a] [DecidableEq a]
    (M : CMatrix a) :
     ‖M.trace‖ ≤ traceNorm M := by
  simpa using traceNorm_variational_unitary_abs_trace_le M (1 : Matrix.unitaryGroup a ℂ)

/-- Trace norm is invariant under conjugate transpose. -/
theorem traceNorm_conjTranspose {a : Type u} [Fintype a] [DecidableEq a]
    (A : CMatrix a) :
    traceNorm (Matrix.conjTranspose A) = traceNorm A := by
  apply le_antisymm
  · obtain ⟨U, hU⟩ :=
      traceNorm_variational_exists_unitary_abs_trace (Matrix.conjTranspose A)
    let V : Matrix.unitaryGroup a ℂ := U⁻¹
    have hcoe : (V : CMatrix a) = star (U : CMatrix a) := by rfl
    have hstar : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
      rw [← Matrix.star_eq_conjTranspose, star_star]
    have htrace :
        ((Matrix.conjTranspose A * (U : CMatrix a)).trace) =
          star ((A * (V : CMatrix a)).trace) := by
      rw [hcoe]
      calc
        (Matrix.conjTranspose A * (U : CMatrix a)).trace =
            ((U : CMatrix a) * Matrix.conjTranspose A).trace := by
              rw [Matrix.trace_mul_comm]
        _ = (Matrix.conjTranspose (A * star (U : CMatrix a))).trace := by
            rw [Matrix.conjTranspose_mul, hstar]
        _ = star ((A * star (U : CMatrix a)).trace) :=
            Matrix.trace_conjTranspose _
    calc
      traceNorm (Matrix.conjTranspose A) =
           ‖(Matrix.conjTranspose A * (U : CMatrix a)).trace‖ := hU.symm
      _ = ‖(A * (V : CMatrix a)).trace‖ := by simp [htrace]
      _ ≤ traceNorm A := traceNorm_variational_unitary_abs_trace_le A V
  · obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace A
    let V : Matrix.unitaryGroup a ℂ := U⁻¹
    have hcoe : (V : CMatrix a) = star (U : CMatrix a) := by rfl
    have hstar : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
      rw [← Matrix.star_eq_conjTranspose, star_star]
    have htrace :
        ((A * (U : CMatrix a)).trace) =
          star ((Matrix.conjTranspose A * (V : CMatrix a)).trace) := by
      rw [hcoe]
      calc
        (A * (U : CMatrix a)).trace =
            ((U : CMatrix a) * A).trace := by rw [Matrix.trace_mul_comm]
        _ = (Matrix.conjTranspose (Matrix.conjTranspose A * star (U : CMatrix a))).trace := by
            rw [Matrix.conjTranspose_mul, hstar, Matrix.conjTranspose_conjTranspose]
        _ = star ((Matrix.conjTranspose A * star (U : CMatrix a)).trace) :=
            Matrix.trace_conjTranspose _
    calc
      traceNorm A = ‖(A * (U : CMatrix a)).trace‖ := hU.symm
      _ = ‖(Matrix.conjTranspose A * (V : CMatrix a)).trace‖ := by
            simp [htrace]
      _ ≤ traceNorm (Matrix.conjTranspose A) :=
          traceNorm_variational_unitary_abs_trace_le (Matrix.conjTranspose A) V

theorem traceNorm_real_smul_eq {a : Type u} [Fintype a] [DecidableEq a]
    {c : ℝ} (hc : 0 ≤ c) (M : CMatrix a) :
    traceNorm (((c : ℂ) • M)) = c * traceNorm M := by
  by_cases hcz : c = 0
  · simp [hcz]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
    apply le_antisymm
    · exact traceNorm_real_smul_le hc M
    · have hInvNonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr hc
      have hle := traceNorm_real_smul_le hInvNonneg (((c : ℂ) • M))
      have hscale : (((c⁻¹ : ℝ) : ℂ) • ((c : ℂ) • M)) = M := by
        rw [smul_smul]
        have hcC : ((c : ℂ) ≠ 0) := by exact_mod_cast hcz
        simp [hcC]
      rw [hscale] at hle
      have hmul := mul_le_mul_of_nonneg_left hle hc
      have htrace_nonneg : 0 ≤ traceNorm (((c : ℂ) • M)) :=
        traceNorm_nonneg _
      have hc_inv : c * c⁻¹ = 1 := mul_inv_cancel₀ hcz
      nlinarith

theorem traceNorm_eq_trace_psdSqrt_mul_conjTranspose (A : CMatrix a) :
    traceNorm A = (psdSqrt (A * Matrix.conjTranspose A)).trace.re := by
  rw [← traceNorm_conjTranspose A]
  simp [traceNorm, Matrix.conjTranspose_conjTranspose]

theorem traceNorm_eq_of_mul_conjTranspose_eq {A B : CMatrix a}
    (h : A * Matrix.conjTranspose A = B * Matrix.conjTranspose B) :
    traceNorm A = traceNorm B := by
  rw [traceNorm_eq_trace_psdSqrt_mul_conjTranspose A,
    traceNorm_eq_trace_psdSqrt_mul_conjTranspose B, h]

theorem traceNorm_eq_of_conjTranspose_mul_eq {A B : CMatrix a}
    (h : Matrix.conjTranspose A * A = Matrix.conjTranspose B * B) :
    traceNorm A = traceNorm B := by
  rw [← traceNorm_conjTranspose A, ← traceNorm_conjTranspose B]
  apply traceNorm_eq_of_mul_conjTranspose_eq
  simpa [Matrix.conjTranspose_conjTranspose] using h

/-- Fidelity-style rewriting of a product of square roots: `‖√A √B‖₁` is the
trace of `√(√B A √B)`. -/
theorem traceNorm_psdSqrt_mul_psdSqrt_eq_trace_psdSqrt_sandwich
    (A B : CMatrix a) (hA : A.PosSemidef) :
    traceNorm (psdSqrt A * psdSqrt B) =
      (psdSqrt (psdSqrt B * A * psdSqrt B)).trace.re := by
  rw [← traceNorm_conjTranspose (psdSqrt A * psdSqrt B)]
  rw [Matrix.conjTranspose_mul, psdSqrt_isHermitian A,
    psdSqrt_isHermitian B]
  rw [traceNorm_eq_trace_psdSqrt_mul_conjTranspose]
  rw [Matrix.conjTranspose_mul, psdSqrt_isHermitian A,
    psdSqrt_isHermitian B]
  have hinside :
      psdSqrt B * psdSqrt A * (psdSqrt A * psdSqrt B) =
        psdSqrt B * A * psdSqrt B := by
    calc
      psdSqrt B * psdSqrt A * (psdSqrt A * psdSqrt B) =
          psdSqrt B * (psdSqrt A * psdSqrt A) * psdSqrt B := by
            simp [Matrix.mul_assoc]
      _ = psdSqrt B * A * psdSqrt B := by
            rw [psdSqrt_mul_self_of_posSemidef hA]
  rw [hinside]

/-- If `E` acts as the identity on both sides of `√A`, then compressing the
second factor by `E` leaves `‖√A √R‖₁` unchanged. -/
theorem traceNorm_psdSqrt_mul_psdSqrt_conj_eq
    (A R E : CMatrix a) (hR : R.PosSemidef)
    (hER : (E * R * E).PosSemidef)
    (hleft : psdSqrt A * E = psdSqrt A)
    (hright : E * psdSqrt A = psdSqrt A) :
    traceNorm (psdSqrt A * psdSqrt R) =
      traceNorm (psdSqrt A * psdSqrt (E * R * E)) := by
  have hsand : psdSqrt A * R * psdSqrt A =
      psdSqrt A * (E * R * E) * psdSqrt A := by
    calc
      psdSqrt A * R * psdSqrt A =
          (psdSqrt A * E) * R * (E * psdSqrt A) := by rw [hleft, hright]
      _ = psdSqrt A * (E * R * E) * psdSqrt A := by simp [Matrix.mul_assoc]
  calc
    traceNorm (psdSqrt A * psdSqrt R) =
        traceNorm (psdSqrt R * psdSqrt A) := by
      rw [← traceNorm_conjTranspose]
      rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian R).eq,
        (psdSqrt_isHermitian A).eq]
    _ = (psdSqrt (psdSqrt A * R * psdSqrt A)).trace.re :=
      traceNorm_psdSqrt_mul_psdSqrt_eq_trace_psdSqrt_sandwich R A hR
    _ = (psdSqrt (psdSqrt A * (E * R * E) * psdSqrt A)).trace.re := by rw [hsand]
    _ = traceNorm (psdSqrt (E * R * E) * psdSqrt A) :=
      (traceNorm_psdSqrt_mul_psdSqrt_eq_trace_psdSqrt_sandwich
        (E * R * E) A hER).symm
    _ = traceNorm (psdSqrt A * psdSqrt (E * R * E)) := by
      rw [← traceNorm_conjTranspose]
      rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian A).eq,
        (psdSqrt_isHermitian (E * R * E)).eq]

private theorem traceNorm_submatrix_equiv_le {b : Type v} [Fintype b] [DecidableEq b]
    (e : a ≃ b) (M : CMatrix b) :
    traceNorm (M.submatrix e e) ≤ traceNorm M := by
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (M.submatrix e e)
  let Ubig : Matrix.unitaryGroup b ℂ :=
    ⟨(U : CMatrix a).submatrix e.symm e.symm, cMatrix_reindex_mem_unitary e U⟩
  calc
    traceNorm (M.submatrix e e) =
         ‖((M.submatrix e e) * (U : CMatrix a)).trace‖ := hU.symm
    _ = ‖(M * (Ubig : CMatrix b)).trace‖ := by
          congr 1
          simpa [Ubig] using (trace_mul_submatrix_equiv e M (Ubig : CMatrix b))
    _ ≤ traceNorm M := traceNorm_variational_unitary_abs_trace_le M Ubig

/-- The trace norm is invariant under simultaneous reindexing by a finite
equivalence. -/
theorem traceNorm_submatrix_equiv {b : Type v} [Fintype b] [DecidableEq b]
    (e : a ≃ b) (M : CMatrix b) :
    traceNorm (M.submatrix e e) = traceNorm M := by
  apply le_antisymm
  · exact traceNorm_submatrix_equiv_le e M
  · have h := traceNorm_submatrix_equiv_le e.symm (M.submatrix e e)
    simpa using h

/-- Trace distance is invariant under simultaneous reindexing by a finite
equivalence. -/
theorem traceNormDistance_submatrix_equiv {b : Type v} [Fintype b] [DecidableEq b]
    (e : a ≃ b) (M N : CMatrix b) :
    traceNormDistance (M.submatrix e e) (N.submatrix e e) = traceNormDistance M N := by
  have hsub : M.submatrix e e - N.submatrix e e = (M - N).submatrix e e := by
    ext i j
    rfl
  rw [traceNormDistance, traceNormDistance, hsub, traceNorm_submatrix_equiv]

namespace ReferenceIsometry

universe w

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- Distributing a product over a sum on the right:
`(a × extra) ⊕ (a × b) ≃ a × (extra ⊕ b)`. -/
def prodSumRightEquiv
    (a : Type u) (extra : Type w) (b : Type v) :
    ((a × extra) ⊕ (a × b)) ≃ (a × (extra ⊕ b)) where
  toFun x := match x with
    | Sum.inl ae => (ae.1, Sum.inl ae.2)
    | Sum.inr ab => (ab.1, Sum.inr ab.2)
  invFun x := match x.2 with
    | Sum.inl e => Sum.inl (x.1, e)
    | Sum.inr y => Sum.inr (x.1, y)
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x with | mk i s => cases s <;> rfl

omit [Fintype a] [DecidableEq a] in
theorem applyMatrixRight_sumInr_submatrix_prodSumRightEquiv
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    (X : CMatrix (a × b)) :
    ((ReferenceIsometry.sumInr extra b).applyMatrixRight X).submatrix
      (prodSumRightEquiv a extra b) (prodSumRightEquiv a extra b) =
        (Matrix.fromBlocks (0 : CMatrix (a × extra)) 0 0 X :
          CMatrix ((a × extra) ⊕ (a × b))) := by
  ext x y
  cases x <;> cases y <;>
    simp [prodSumRightEquiv, ReferenceIsometry.applyMatrixRight,
      ReferenceIsometry.rightBlock, ReferenceIsometry.sumInr, Matrix.mul_apply]

/-- Concrete right-summand reference padding preserves trace norm. -/
theorem traceNorm_applyMatrixRight_sumInr
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    (X : CMatrix (a × b)) :
    traceNorm ((ReferenceIsometry.sumInr extra b).applyMatrixRight X) =
      traceNorm X := by
  let e := prodSumRightEquiv a extra b
  have htn := traceNorm_submatrix_equiv e
    ((ReferenceIsometry.sumInr extra b).applyMatrixRight X)
  rw [applyMatrixRight_sumInr_submatrix_prodSumRightEquiv (a := a)
    (b := b) (extra := extra) X] at htn
  rw [← htn]
  rw [Matrix.traceNorm_fromBlocks_diagonal]
  simp
end ReferenceIsometry

/-- Finite subadditivity of the trace norm. -/
theorem traceNorm_sum_le_sum_traceNorm {ι : Type v} (s : Finset ι)
    (f : ι → CMatrix a) :
    traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceNorm (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro i s his ih
    rw [Finset.sum_insert his, Finset.sum_insert his]
    calc
      traceNorm (f i + ∑ x ∈ s, f x) ≤ traceNorm (f i) + traceNorm (∑ x ∈ s, f x) :=
        traceNorm_add_le _ _
      _ ≤ traceNorm (f i) + ∑ x ∈ s, traceNorm (f x) := add_le_add (le_refl _) ih

/-- The trace-norm variational maximum can be attained by a `ReferenceUnitary`
in the transposed matrix convention used by the Uhlmann route. -/
theorem traceNorm_variational_exists_referenceUnitary_sq (M : CMatrix a) :
    ∃ U : ReferenceUnitary a,
      Complex.normSq ((M * Matrix.transpose U.matrix).trace) = (traceNorm M) ^ 2 := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace M
  let V : ReferenceUnitary a := ⟨Matrix.UnitaryGroup.transpose U⟩
  refine ⟨V, ?_⟩
  have hAbs :
       ‖(M * Matrix.transpose V.matrix).trace‖ = traceNorm M := by
    simpa [V] using hU
  simp [Complex.normSq_eq_norm_sq, hAbs]

/-- Every `ReferenceUnitary` gives a squared trace expression bounded by the
squared trace norm, in the transposed matrix convention used downstream. -/
theorem traceNorm_variational_referenceUnitary_sq_le
    (M : CMatrix a) (U : ReferenceUnitary a) :
    Complex.normSq ((M * Matrix.transpose U.matrix).trace) ≤ (traceNorm M) ^ 2 := by
  classical
  have hAbs :
       ‖(M * Matrix.transpose U.matrix).trace‖ ≤ traceNorm M := by
    simpa using traceNorm_variational_unitary_abs_trace_le M
      (Matrix.UnitaryGroup.transpose U.matrix)
  exact complex_normSq_le_sq_of_abs_le hAbs

end QIT

namespace MState

/-- Normalized trace distance is invariant under state reindexing. -/
theorem normalizedTraceDistance_reindex_equiv {b : Type v} [Fintype b] [DecidableEq b]
    (ρ σ : MState a) (e : a ≃ b) :
    (ρ.reindex e).normalizedTraceDistance (σ.reindex e) = ρ.normalizedTraceDistance σ := by
  simp only [MState.normalizedTraceDistance, QIT.normalizedTraceDistance, MState.reindex_matrix]
  rw [QIT.traceNormDistance_submatrix_equiv e.symm ρ.m σ.m]

end MState
