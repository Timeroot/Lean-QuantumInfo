/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.RelativeEntropyDPI
public import QIT.Information.Entropy.Entropy
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Information.BinaryHypothesisTest

/-!
# Mutual information data processing

This module develops the local-channel rewrite layer needed for the
Khatri--Wilde quantum mutual information data-processing statement
[KhatriWilde2024Principles, Chapters/entropies.tex:1081-1130].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z

noncomputable section

namespace Matrix

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The zero roots contributed by powers of `X` do not affect `xlog2` spectral
sums. -/
theorem roots_X_pow_map_re_xlog2_sum_zero (n : ℕ) :
    ((Polynomial.X ^ n : Polynomial ℂ).roots.map (fun z : ℂ => xlog2 z.re)).sum = 0 := by
  rw [Polynomial.roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton]
  simp [xlog2]

/-- If two characteristic-polynomial identities differ only by powers of `X`,
then the `xlog2` spectral sums over their nonzero roots agree. -/
theorem roots_re_xlog2_sum_eq_of_X_pow_mul_eq
    {P Q : Polynomial ℂ} {m n : ℕ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : Polynomial.X ^ m * P = Polynomial.X ^ n * Q) :
    (P.roots.map (fun z : ℂ => xlog2 z.re)).sum =
      (Q.roots.map (fun z : ℂ => xlog2 z.re)).sum := by
  have hXm : (Polynomial.X ^ m : Polynomial ℂ) ≠ 0 := by simp
  have hXn : (Polynomial.X ^ n : Polynomial ℂ) ≠ 0 := by simp
  have hleft_ne : (Polynomial.X ^ m : Polynomial ℂ) * P ≠ 0 := mul_ne_zero hXm hP
  have hright_ne : (Polynomial.X ^ n : Polynomial ℂ) * Q ≠ 0 := mul_ne_zero hXn hQ
  have hroots := congrArg Polynomial.roots h
  rw [Polynomial.roots_mul hleft_ne, Polynomial.roots_mul hright_ne] at hroots
  have hsum :=
    congrArg (fun s : Multiset ℂ => (s.map (fun z : ℂ => xlog2 z.re)).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add] at hsum
  rw [roots_X_pow_map_re_xlog2_sum_zero m,
    roots_X_pow_map_re_xlog2_sum_zero n] at hsum
  simpa using hsum

/-- Trace pairing against a diagonal operator in a unitary basis only reads the
diagonal entries of the other operator in that basis. -/
theorem trace_mul_unitary_conj_diagonal_right_re
    (U : Matrix.unitaryGroup α ℂ) (B : CMatrix α) (e : α → ℝ) :
    ((B * ((U : CMatrix α) * (Matrix.diagonal fun i => ((e i : ℝ) : ℂ)) *
      star (U : CMatrix α))).trace).re =
      ∑ i : α, ((star (U : CMatrix α) * B * (U : CMatrix α)) i i).re * e i := by
  let D : CMatrix α := Matrix.diagonal fun i => ((e i : ℝ) : ℂ)
  have htrace :
      (B * ((U : CMatrix α) * D * star (U : CMatrix α))).trace =
        ((star (U : CMatrix α) * B * (U : CMatrix α)) * D).trace := by
    calc
      (B * ((U : CMatrix α) * D * star (U : CMatrix α))).trace =
          (((B * (U : CMatrix α)) * D) * star (U : CMatrix α)).trace := by
            simp [Matrix.mul_assoc]
      _ = (star (U : CMatrix α) * ((B * (U : CMatrix α)) * D)).trace := by
            rw [Matrix.trace_mul_comm]
      _ = ((star (U : CMatrix α) * B * (U : CMatrix α)) * D).trace := by
            simp [Matrix.mul_assoc]
  rw [htrace]
  simp [D, Matrix.trace, Matrix.diagonal, Matrix.mul_apply, Complex.mul_re]

end Matrix

namespace Channel

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The identity channel has the identity matrix map. -/
theorem idChannel_map_eq_linearMap_id :
    (idChannel α).map = (LinearMap.id : MatrixMap α α) := by
  ext X i j
  simp [idChannel, MatrixMap.ofKraus]

end Channel

namespace State

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Compressing a state to the positive spectral support of a supporting PSD
reference preserves its von Neumann entropy. -/
theorem vonNeumann_psdSupportCompressedState_eq
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    (_root_.QIT.psdSupportCompressedState ρ hσ hSupport).vonNeumann = ρ.vonNeumann := by
  classical
  let ρc : State (psdSupportIndex σ hσ) :=
    _root_.QIT.psdSupportCompressedState ρ hσ hSupport
  let V : Matrix a (psdSupportIndex σ hσ) ℂ := psdSupportIsometry σ hσ
  have hV : Matrix.conjTranspose V * V = (1 : CMatrix (psdSupportIndex σ hσ)) := by
    simpa [V] using psdSupportIsometry_isometry σ hσ
  have hrec : V * ρc.matrix * Matrix.conjTranspose V = ρ.matrix := by
    simpa [V, ρc] using
      psdSupportCompress_reconstruct_of_supports
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
  rw [State.vonNeumann_eq_neg_sum_eigenvalueMultiset,
    State.vonNeumann_eq_neg_sum_eigenvalueMultiset]
  have hpoly := Matrix.charpoly_isometry_conj (V := V) ρc.matrix hV
  rw [hrec] at hpoly
  have hP : ρ.matrix.charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hQ : ρc.matrix.charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hroot :=
    Matrix.roots_re_xlog2_sum_eq_of_X_pow_mul_eq
      (P := ρ.matrix.charpoly) (Q := ρc.matrix.charpoly) hP hQ hpoly
  have hrootsρ := ρ.pos.isHermitian.roots_charpoly_eq_eigenvalues
  have hrootsρc := ρc.pos.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hrootsρ, hrootsρc] at hroot
  have hsum :
      ((eigenvalueMultiset ρc.pos.isHermitian).map xlog2).sum =
        ((eigenvalueMultiset ρ.pos.isHermitian).map xlog2).sum := by
    simpa [eigenvalueMultiset, Multiset.map_map, Function.comp_def] using hroot.symm
  rw [hsum]

/-- Embedding the logarithm of the compressed positive support reference gives
the finite-spectrum `log 0 = 0` functional calculus of the original PSD
reference. -/
theorem psdSupportLog_embedding_eq_cfc_logZero
    (σ : CMatrix a) (hσ : σ.PosSemidef) :
    let V : Matrix a (psdSupportIndex σ hσ) ℂ := psdSupportIsometry σ hσ
    V * State.psdLog (psdSupportCompress σ hσ σ) (psdSupportCompress_self_posDef σ hσ) *
        Matrix.conjTranspose V =
      cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) σ := by
  classical
  let V : Matrix a (psdSupportIndex σ hσ) ℂ := psdSupportIsometry σ hσ
  let U : Matrix.unitaryGroup a ℂ := hσ.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hσ.isHermitian.eigenvalues
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.log x
  have hσspec :
      σ = (U : CMatrix a) * (Matrix.diagonal fun i => ((d i : ℝ) : ℂ)) *
        star (U : CMatrix a) := by
    simpa [U, d, Matrix.IsHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply, Function.comp_def]
      using hσ.isHermitian.spectral_theorem
  have hlogσ :
      cfc f σ =
        (U : CMatrix a) * (Matrix.diagonal fun i => ((f (d i) : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    rw [hσspec]
    exact cfc_unitary_conj_diagonal_ofReal U d f
  have hσc :
      psdSupportCompress σ hσ σ =
        (Matrix.diagonal fun i : psdSupportIndex σ hσ => ((d i.1 : ℝ) : ℂ)) := by
    simpa [d] using psdSupportCompress_self_eq_diagonal σ hσ
  have hlogc :
      State.psdLog (psdSupportCompress σ hσ σ) (psdSupportCompress_self_posDef σ hσ) =
        (Matrix.diagonal fun i : psdSupportIndex σ hσ => ((Real.log (d i.1) : ℝ) : ℂ)) := by
    rw [State.psdLog, hσc]
    exact cfc_diagonal_ofReal (fun i : psdSupportIndex σ hσ => d i.1) Real.log
  rw [hlogσ, hlogc]
  ext r s
  simp [psdSupportIsometry, U, f, Matrix.mul_apply, Matrix.diagonal,
    Matrix.conjTranspose_apply]
  let g : a → ℂ := fun x =>
    (hσ.isHermitian.eigenvectorUnitary : CMatrix a) r x * ↑(Real.log (d x)) *
      star ((hσ.isHermitian.eigenvectorUnitary : CMatrix a) s x)
  change (∑ x : psdSupportIndex σ hσ, g x.1) =
    ∑ x : a,
      (hσ.isHermitian.eigenvectorUnitary : CMatrix a) r x *
        ↑(if d x = 0 then 0 else Real.log (d x)) *
        star ((hσ.isHermitian.eigenvectorUnitary : CMatrix a) s x)
  have hleft :
      (∑ x : psdSupportIndex σ hσ, g x.1) =
        ∑ x ∈ (Finset.univ : Finset a) with 0 < d x, g x := by
    simpa [g, d] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset a))
        (p := fun x => 0 < d x) (f := g))
  rw [hleft]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases hxpos : 0 < d x
  · have hxne : d x ≠ 0 := ne_of_gt hxpos
    simp [g, hxpos, hxne]
  · have hzero : d x = 0 := by
      exact le_antisymm (not_lt.mp hxpos) (hσ.eigenvalues_nonneg x)
    simp [g, hzero]

/-- The support-compressed trace-log pairing is the same as pairing the
original state with the finite-dimensional `log 0 = 0` calculus of the PSD
reference. -/
theorem trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
    (ρ : State a) {σ : CMatrix a} (hσ : σ.PosSemidef)
    (hSupport : Matrix.Supports ρ.matrix σ) :
    ((psdSupportCompress σ hσ ρ.matrix *
      State.psdLog (psdSupportCompress σ hσ σ) (psdSupportCompress_self_posDef σ hσ)).trace).re =
      ((ρ.matrix * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) σ).trace).re := by
  classical
  let V : Matrix a (psdSupportIndex σ hσ) ℂ := psdSupportIsometry σ hσ
  let ρc : CMatrix (psdSupportIndex σ hσ) := psdSupportCompress σ hσ ρ.matrix
  let L : CMatrix (psdSupportIndex σ hσ) :=
    State.psdLog (psdSupportCompress σ hσ σ) (psdSupportCompress_self_posDef σ hσ)
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.log x
  have htrace : ((ρc * L).trace).re =
      ((V * (ρc * L) * Matrix.conjTranspose V).trace).re := by
    simpa [V] using
      (congrArg Complex.re (psdSupportIsometry_conj_trace σ hσ (ρc * L))).symm
  have hrec : V * ρc * Matrix.conjTranspose V = ρ.matrix := by
    simpa [V, ρc] using
      psdSupportCompress_reconstruct_of_supports
        (M := ρ.matrix) (N := σ) ρ.pos hσ hSupport
  have hlog : V * L * Matrix.conjTranspose V = cfc f σ := by
    simpa [V, L, f] using psdSupportLog_embedding_eq_cfc_logZero σ hσ
  have hmul : V * (ρc * L) * Matrix.conjTranspose V =
      (V * ρc * Matrix.conjTranspose V) * (V * L * Matrix.conjTranspose V) := by
    symm
    calc
      (V * ρc * Matrix.conjTranspose V) * (V * L * Matrix.conjTranspose V) =
          V * ρc * (Matrix.conjTranspose V * V) * L * Matrix.conjTranspose V := by
            simp [Matrix.mul_assoc]
      _ = V * ρc * L * Matrix.conjTranspose V := by
            rw [psdSupportIsometry_isometry σ hσ]
            simp [Matrix.mul_assoc]
      _ = V * (ρc * L) * Matrix.conjTranspose V := by
            simp [Matrix.mul_assoc]
  calc
    ((psdSupportCompress σ hσ ρ.matrix *
      State.psdLog (psdSupportCompress σ hσ σ) (psdSupportCompress_self_posDef σ hσ)).trace).re =
        ((ρc * L).trace).re := by rfl
    _ = ((V * (ρc * L) * Matrix.conjTranspose V).trace).re := htrace
    _ = (((V * ρc * Matrix.conjTranspose V) *
            (V * L * Matrix.conjTranspose V)).trace).re := by rw [hmul]
    _ = ((ρ.matrix * cfc f σ).trace).re := by rw [hrec, hlog]

/-- Product marginal references contribute exactly the negative marginal
entropy sum to the trace-log term. -/
theorem trace_mul_cfc_logZero_prod_marginals_eq_neg_marginal_vonNeumann_sum
    (ρ : State (Prod a b)) :
    ((ρ.matrix * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x)
        (ρ.marginalA.prod ρ.marginalB).matrix).trace).re / Real.log 2 =
      -(ρ.marginalA.vonNeumann + ρ.marginalB.vonNeumann) := by
  classical
  let τ : State (Prod a b) := ρ.marginalA.prod ρ.marginalB
  let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
    BinaryHypothesisTest.productMarginalEigenvectorUnitary ρ
  let coeff : Prod a b → ℝ := fun y =>
    ((star (Uprod : CMatrix (Prod a b)) * ρ.matrix *
      (Uprod : CMatrix (Prod a b))) y y).re
  let mu : Prod a b → ℝ := fun y =>
    ((BinaryHypothesisTest.productMarginalSpectralWeight ρ y : NNReal) : ℝ)
  let muA : a → ℝ := fun i =>
    ((BinaryHypothesisTest.stateSpectralWeight ρ.marginalA i : NNReal) : ℝ)
  let muB : b → ℝ := fun j =>
    ((BinaryHypothesisTest.stateSpectralWeight ρ.marginalB j : NNReal) : ℝ)
  let w : Prod a b → ℝ := fun y =>
    ∑ x : Prod a b,
      ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
        ((BinaryHypothesisTest.productMarginalNussbaumSzkolaOverlap ρ x y : NNReal) : ℝ)
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.log x
  have hτspec :
      τ.matrix = (Uprod : CMatrix (Prod a b)) *
        (Matrix.diagonal fun y : Prod a b => ((mu y : ℝ) : ℂ)) *
        star (Uprod : CMatrix (Prod a b)) := by
    simpa [τ, Uprod, mu] using
      BinaryHypothesisTest.productMarginal_matrix_eq_productEigenbasis_diagonal ρ
  have hlogτ :
      cfc f τ.matrix = (Uprod : CMatrix (Prod a b)) *
        (Matrix.diagonal fun y : Prod a b => ((f (mu y) : ℝ) : ℂ)) *
        star (Uprod : CMatrix (Prod a b)) := by
    rw [hτspec]
    exact cfc_unitary_conj_diagonal_ofReal Uprod mu f
  have hf_log : ∀ y : Prod a b, f (mu y) = Real.log (mu y) := by
    intro y
    by_cases hy : mu y = 0
    · simp [f, hy]
    · simp [f, hy]
  have hcoeff : ∀ y : Prod a b, coeff y = w y := by
    intro y
    simpa [coeff, w, Uprod] using
      (BinaryHypothesisTest.productMarginalNussbaumSzkolaOverlap_weighted_col_sum_eq_productBasis_diag
        ρ y).symm
  have hfst : ∀ i : a, ∑ j : b, w (i, j) = muA i := by
    intro i
    rw [Finset.sum_comm]
    simpa [w, muA] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaOverlap_weighted_fst_sum ρ i
  have hsnd : ∀ j : b, ∑ i : a, w (i, j) = muB j := by
    intro j
    rw [Finset.sum_comm]
    simpa [w, muB] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaOverlap_weighted_snd_sum ρ j
  have hsum :
      ∑ y : Prod a b, coeff y * f (mu y) =
        (∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j)) := by
    calc
      ∑ y : Prod a b, coeff y * f (mu y) =
          ∑ y : Prod a b, w y * Real.log (mu y) := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            rw [hcoeff y, hf_log y]
      _ = ∑ y : Prod a b, w y *
            (Real.log (muA y.1) + Real.log (muB y.2)) := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            simpa [w, mu, muA, muB] using
              BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_weighted_log_product ρ y
      _ = (∑ i : a, ∑ j : b, w (i, j) * Real.log (muA i)) +
          (∑ i : a, ∑ j : b, w (i, j) * Real.log (muB j)) := by
            rw [Fintype.sum_prod_type]
            simp [mul_add, Finset.sum_add_distrib]
      _ = (∑ i : a, (∑ j : b, w (i, j)) * Real.log (muA i)) +
          (∑ j : b, (∑ i : a, w (i, j)) * Real.log (muB j)) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro i _hi
              simp [Finset.sum_mul]
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro j _hj
              simp [Finset.sum_mul]
      _ = (∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j)) := by
            simp [hfst, hsnd]
  have htrace :
      ((ρ.matrix * cfc f τ.matrix).trace).re =
        ∑ y : Prod a b, coeff y * f (mu y) := by
    rw [hlogτ]
    simpa [coeff] using
      Matrix.trace_mul_unitary_conj_diagonal_right_re Uprod ρ.matrix
        (fun y : Prod a b => f (mu y))
  have hA : (∑ i : a, muA i * Real.log (muA i)) / Real.log 2 =
      -ρ.marginalA.vonNeumann := by
    simpa [muA] using
      State.spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann ρ.marginalA
  have hB : (∑ j : b, muB j * Real.log (muB j)) / Real.log 2 =
      -ρ.marginalB.vonNeumann := by
    simpa [muB] using
      State.spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann ρ.marginalB
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  calc
    ((ρ.matrix * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x)
        (ρ.marginalA.prod ρ.marginalB).matrix).trace).re / Real.log 2 =
        ((ρ.matrix * cfc f τ.matrix).trace).re / Real.log 2 := by rfl
    _ = ((∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j))) / Real.log 2 := by
          rw [htrace, hsum]
    _ = -(ρ.marginalA.vonNeumann + ρ.marginalB.vonNeumann) := by
          rw [show ((∑ i : a, muA i * Real.log (muA i)) +
                (∑ j : b, muB j * Real.log (muB j))) / Real.log 2 =
              (∑ i : a, muA i * Real.log (muA i)) / Real.log 2 +
                (∑ j : b, muB j * Real.log (muB j)) / Real.log 2 by
            field_simp [hlog_ne]]
          rw [hA, hB]
          ring

/-- The single trace-log term that remains after unfolding
`D(ρ_AB ‖ ρ_A ⊗ ρ_B)` on the positive support of the product reference. -/
noncomputable def prodMarginalsSupportTraceLogTerm
    (ρ : State (Prod a b)) : ℝ := by
  classical
  let τ : State (Prod a b) := ρ.marginalA.prod ρ.marginalB
  let hSupport : Matrix.Supports ρ.matrix τ.matrix :=
    ρ.matrix_supports_prod_marginals
  let ρc : State (psdSupportIndex τ.matrix τ.pos) :=
    _root_.QIT.psdSupportCompressedState ρ τ.pos hSupport
  let σc : CMatrix (psdSupportIndex τ.matrix τ.pos) :=
    psdSupportCompress τ.matrix τ.pos τ.matrix
  have hσc : σc.PosDef := by
    simpa [σc] using psdSupportCompressedState_reference_posDef τ.pos
  exact ((ρc.matrix * psdLog σc hσc).trace.re / Real.log 2)

/-- The mutual-information trace-log bridge reduces to the product-reference
trace term.  The remaining mathematical input is
`prodMarginalsSupportTraceLogTerm ρ = -(S(ρ_A) + S(ρ_B))`. -/
theorem relativeEntropyPSDReferenceTraceLogE_prod_marginals_eq_mutualInformation_of_trace_term
    (ρ : State (Prod a b))
    (hTrace :
      ρ.prodMarginalsSupportTraceLogTerm =
        -(ρ.marginalA.vonNeumann + ρ.marginalB.vonNeumann)) :
    relativeEntropyPSDReferenceTraceLogE ρ
        (ρ.marginalA.prod ρ.marginalB).matrix
        (ρ.marginalA.prod ρ.marginalB).pos =
      (mutualInformation ρ : EReal) := by
  classical
  let τ : State (Prod a b) := ρ.marginalA.prod ρ.marginalB
  let hSupport : Matrix.Supports ρ.matrix τ.matrix :=
    ρ.matrix_supports_prod_marginals
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports ρ τ.pos hSupport]
  congr 1
  have hEntropy :
      (_root_.QIT.psdSupportCompressedState ρ τ.pos hSupport).vonNeumann =
        ρ.vonNeumann :=
    State.vonNeumann_psdSupportCompressedState_eq ρ τ.pos hSupport
  have hTrace' :
      ((psdSupportCompress τ.matrix τ.pos ρ.matrix *
            psdLog (psdSupportCompress τ.matrix τ.pos τ.matrix)
              (by
                simpa using psdSupportCompressedState_reference_posDef τ.pos)).trace.re *
          (Real.log 2)⁻¹) =
        -(ρ.marginalA.vonNeumann + ρ.marginalB.vonNeumann) := by
    simpa [prodMarginalsSupportTraceLogTerm, τ, div_eq_mul_inv] using hTrace
  simp [relativeEntropyPSDReferenceTraceLogFinite, τ, hTrace',
    mutualInformation, div_eq_mul_inv]
  rw [hEntropy]
  ring_nf

/-- State-state trace-log relative entropy against the product of the marginals
is mutual information, assuming the product-reference trace term identity. -/
theorem relativeEntropy_prod_marginals_eq_mutualInformation_of_trace_term
    (ρ : State (Prod a b))
    (hTrace :
      ρ.prodMarginalsSupportTraceLogTerm =
        -(ρ.marginalA.vonNeumann + ρ.marginalB.vonNeumann)) :
    ρ.relativeEntropy (ρ.marginalA.prod ρ.marginalB) =
      (mutualInformation ρ : EReal) := by
  simpa [relativeEntropy] using
    relativeEntropyPSDReferenceTraceLogE_prod_marginals_eq_mutualInformation_of_trace_term
      ρ hTrace

/-- The product-reference trace-log term is the negative sum of the two
marginal entropies. -/
theorem prodMarginalsSupportTraceLogTerm_eq_neg_marginal_vonNeumann_sum
    (ρ : State (Prod a b)) :
    ρ.prodMarginalsSupportTraceLogTerm =
      -(ρ.marginalA.vonNeumann + ρ.marginalB.vonNeumann) := by
  classical
  let τ : State (Prod a b) := ρ.marginalA.prod ρ.marginalB
  let hSupport : Matrix.Supports ρ.matrix τ.matrix :=
    ρ.matrix_supports_prod_marginals
  have hTrace :
      ((psdSupportCompress τ.matrix τ.pos ρ.matrix *
        State.psdLog (psdSupportCompress τ.matrix τ.pos τ.matrix)
          (psdSupportCompress_self_posDef τ.matrix τ.pos)).trace).re =
        ((ρ.matrix * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) τ.matrix).trace).re :=
    trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero ρ τ.pos hSupport
  have hProd :=
    trace_mul_cfc_logZero_prod_marginals_eq_neg_marginal_vonNeumann_sum ρ
  calc
    ρ.prodMarginalsSupportTraceLogTerm =
        ((ρ.matrix * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x)
          τ.matrix).trace).re / Real.log 2 := by
          simpa [prodMarginalsSupportTraceLogTerm, τ, hSupport] using
            congrArg (fun x : ℝ => x / Real.log 2) hTrace
    _ = -(ρ.marginalA.vonNeumann + ρ.marginalB.vonNeumann) := by
          simpa [τ] using hProd

/-- Trace-log relative entropy against the product of the marginals is mutual
information. -/
theorem relativeEntropyPSDReferenceTraceLogE_prod_marginals_eq_mutualInformation
    (ρ : State (Prod a b)) :
    relativeEntropyPSDReferenceTraceLogE ρ
        (ρ.marginalA.prod ρ.marginalB).matrix
        (ρ.marginalA.prod ρ.marginalB).pos =
      (mutualInformation ρ : EReal) :=
  relativeEntropyPSDReferenceTraceLogE_prod_marginals_eq_mutualInformation_of_trace_term
    ρ (prodMarginalsSupportTraceLogTerm_eq_neg_marginal_vonNeumann_sum ρ)

/-- State-state relative entropy against the product of the marginals is mutual
information. -/
theorem relativeEntropy_prod_marginals_eq_mutualInformation
    (ρ : State (Prod a b)) :
    ρ.relativeEntropy (ρ.marginalA.prod ρ.marginalB) =
      (mutualInformation ρ : EReal) :=
  relativeEntropy_prod_marginals_eq_mutualInformation_of_trace_term
    ρ (prodMarginalsSupportTraceLogTerm_eq_neg_marginal_vonNeumann_sum ρ)

/-- A two-sided product channel maps the left marginal by the left channel. -/
theorem marginalA_applyState_prod
    (ρ : State (Prod a b)) (Φ : Channel a c) (Ψ : Channel b d) :
    ((Φ.prod Ψ).applyState ρ).marginalA = Φ.applyState ρ.marginalA := by
  let ρ' : State (Prod c b) := (Φ.prod (Channel.idChannel b)).applyState ρ
  have hseq :
      ((Φ.prod Ψ).applyState ρ) =
        (((Channel.idChannel c).prod Ψ).applyState ρ') := by
    apply State.ext
    change MatrixMap.kron Φ.map Ψ.map ρ.matrix =
      MatrixMap.kron (Channel.idChannel c).map Ψ.map
        (MatrixMap.kron Φ.map (Channel.idChannel b).map ρ.matrix)
    have hleft : (Channel.idChannel c).map.comp Φ.map = Φ.map := by
      rw [Channel.idChannel_map_eq_linearMap_id]
      ext X i j
      rfl
    have hright : Ψ.map.comp (Channel.idChannel b).map = Ψ.map := by
      rw [Channel.idChannel_map_eq_linearMap_id]
      ext X i j
      rfl
    simpa [hleft, hright] using
      (MatrixMap.kron_comp_apply_general
        (Channel.idChannel c).map Ψ.map Φ.map (Channel.idChannel b).map ρ.matrix).symm
  rw [hseq]
  calc
    ((((Channel.idChannel c).prod Ψ).applyState ρ').marginalA) = ρ'.marginalA := by
      exact State.marginalA_applyState_id_prod ρ' Ψ
    _ = Φ.applyState ρ.marginalA := by
      simpa [ρ'] using State.marginalA_applyState_prod_id ρ Φ

/-- A two-sided product channel maps the right marginal by the right channel. -/
theorem marginalB_applyState_prod
    (ρ : State (Prod a b)) (Φ : Channel a c) (Ψ : Channel b d) :
    ((Φ.prod Ψ).applyState ρ).marginalB = Ψ.applyState ρ.marginalB := by
  let ρ' : State (Prod a d) := ((Channel.idChannel a).prod Ψ).applyState ρ
  have hseq :
      ((Φ.prod Ψ).applyState ρ) =
        ((Φ.prod (Channel.idChannel d)).applyState ρ') := by
    apply State.ext
    change MatrixMap.kron Φ.map Ψ.map ρ.matrix =
      MatrixMap.kron Φ.map (Channel.idChannel d).map
        (MatrixMap.kron (Channel.idChannel a).map Ψ.map ρ.matrix)
    have hleft : Φ.map.comp (Channel.idChannel a).map = Φ.map := by
      rw [Channel.idChannel_map_eq_linearMap_id]
      ext X i j
      rfl
    have hright : (Channel.idChannel d).map.comp Ψ.map = Ψ.map := by
      rw [Channel.idChannel_map_eq_linearMap_id]
      ext X i j
      rfl
    simpa [hleft, hright] using
      (MatrixMap.kron_comp_apply_general
        Φ.map (Channel.idChannel d).map (Channel.idChannel a).map Ψ.map ρ.matrix).symm
  rw [hseq]
  calc
    (((Φ.prod (Channel.idChannel d)).applyState ρ').marginalB) = ρ'.marginalB := by
      exact State.marginalB_applyState_prod_id ρ' Φ
    _ = Ψ.applyState ρ.marginalB := by
      -- Right-local postprocessing is handled symmetrically by tracing out the
      -- left subsystem.
      apply State.ext
      change partialTraceA (a := a) (b := d)
          (MatrixMap.kron (Channel.idChannel a).map Ψ.map ρ.matrix) =
        Ψ.map (partialTraceA (a := a) (b := b) ρ.matrix)
      ext j j'
      simp only [partialTraceA]
      let S : a → CMatrix b := fun i => fun y y' => ρ.matrix (i, y) (i, y')
      have hsum :
          (fun y y' => ∑ i : a, ρ.matrix (i, y) (i, y')) =
            ∑ i : a, S i := by
        ext y y'
        change (∑ i : a, ρ.matrix (i, y) (i, y')) =
          (∑ i : a, S i) y y'
        simp only [Matrix.sum_apply]
        rfl
      change (∑ i : a,
          MatrixMap.kron (Channel.idChannel a).map Ψ.map ρ.matrix (i, j) (i, j')) =
        Ψ.map (fun y y' => ∑ i : a, ρ.matrix (i, y) (i, y')) j j'
      rw [hsum, map_sum]
      simp only [Matrix.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simpa [S] using
        (MatrixMap.kron_idChannel_left_apply_slice (a := a)
          (Φ := Ψ.map) (X := ρ.matrix) (ad := (i, j)) (ad' := (i, j')))

/-- Product channels send the product of input marginals to the product of
output marginals. -/
theorem applyState_prod_marginals
    (ρ : State (Prod a b)) (Φ : Channel a c) (Ψ : Channel b d) :
    (Φ.prod Ψ).applyState (ρ.marginalA.prod ρ.marginalB) =
      (((Φ.prod Ψ).applyState ρ).marginalA).prod
        (((Φ.prod Ψ).applyState ρ).marginalB) := by
  rw [Channel.applyState_prod]
  rw [marginalA_applyState_prod, marginalB_applyState_prod]

end State

/-- Once the source-facing trace-log bridge
`D(ρ_AB ‖ ρ_A ⊗ ρ_B) = I(A;B)_ρ` is available for the input and output
states, mutual-information DPI under local channels is a direct instance of
relative-entropy DPI. -/
theorem mutualInformation_dataProcessing_local_channels_ge_of_traceLog_bridge
    {a : Type u} {b : Type v} {c : Type w} {d : Type x}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (ρ : State (Prod a b)) (Φ : Channel a c) (Ψ : Channel b d)
    (hIn :
      ρ.relativeEntropy (ρ.marginalA.prod ρ.marginalB) =
        (mutualInformation ρ : EReal))
    (hOut :
      ((Φ.prod Ψ).applyState ρ).relativeEntropy
          ((((Φ.prod Ψ).applyState ρ).marginalA).prod
            (((Φ.prod Ψ).applyState ρ).marginalB)) =
        (mutualInformation ((Φ.prod Ψ).applyState ρ) : EReal)) :
    mutualInformation ρ ≥ mutualInformation ((Φ.prod Ψ).applyState ρ) := by
  classical
  let τ : State (Prod a b) := ρ.marginalA.prod ρ.marginalB
  let ω : State (Prod c d) := (Φ.prod Ψ).applyState ρ
  have hτstate :
      (Φ.prod Ψ).applyState τ = ω.marginalA.prod ω.marginalB := by
    simpa [τ, ω] using
      State.applyState_prod_marginals ρ Φ Ψ
  have hOut' :
      ω.relativeEntropy ((Φ.prod Ψ).applyState τ) =
        (mutualInformation ω : EReal) := by
    simpa [τ, ω, hτstate] using hOut
  have hDPI :
      ω.relativeEntropy ((Φ.prod Ψ).applyState τ) ≤
        ρ.relativeEntropy τ := by
    exact State.relativeEntropy_dataProcessing_channel_ge ρ τ (Φ.prod Ψ)
  have hE :
      (mutualInformation ω : EReal) ≤ (mutualInformation ρ : EReal) := by
    simpa [τ, hIn, hOut'] using hDPI
  exact EReal.coe_le_coe_iff.mp hE

/-- Quantum mutual information is monotone under local channels:
`I(A;B)_ρ ≥ I(A';B')_(Φ ⊗ Ψ)(ρ)`. -/
theorem mutualInformation_dataProcessing_local_channels_ge
    {a : Type u} {b : Type v} {c : Type w} {d : Type x}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (ρ : State (Prod a b)) (Φ : Channel a c) (Ψ : Channel b d) :
    mutualInformation ρ ≥ mutualInformation ((Φ.prod Ψ).applyState ρ) := by
  exact
    mutualInformation_dataProcessing_local_channels_ge_of_traceLog_bridge ρ Φ Ψ
      (State.relativeEntropy_prod_marginals_eq_mutualInformation ρ)
      (State.relativeEntropy_prod_marginals_eq_mutualInformation
        ((Φ.prod Ψ).applyState ρ))

end

end QIT
