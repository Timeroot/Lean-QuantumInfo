/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.RelativeEntropyDPI
public import QuantumLib.QIT.Information.Entropy.Entropy
public import QuantumLib.QIT.Information.Entropy.EntropyTensorPower
public import QuantumLib.QIT.Information.BinaryHypothesisTest

/-!
# Mutual information data processing

This module develops the local-channel rewrite layer needed for the
Khatri--Wilde quantum mutual information data-processing statement
[KhatriWilde2024Principles, Chapters/entropies.tex:1081-1130].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

noncomputable section
universe u v w x y z

namespace MState

open QIT

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Embedding the logarithm of the compressed positive support reference gives
the finite-spectrum `log 0 = 0` functional calculus of the original PSD
reference. -/
theorem psdSupportLog_embedding_eq_cfc_logZero
    (σ : CMatrix a) (hσ : σ.PosSemidef) :
    let V : Matrix a (psdSupportIndex σ hσ) ℂ := psdSupportIsometry σ hσ
    V * MState.psdLog (psdSupportCompress σ hσ σ) (psdSupportCompress_self_posDef σ hσ) *
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
      MState.psdLog (psdSupportCompress σ hσ σ) (psdSupportCompress_self_posDef σ hσ) =
        (Matrix.diagonal fun i : psdSupportIndex σ hσ => ((Real.log (d i.1) : ℝ) : ℂ)) := by
    rw [MState.psdLog, hσc]
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
    refine (Finset.sum_subtype _ ?_ g).symm
    intro x
    simp [d]
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

/-- Product marginal references contribute exactly the negative marginal
entropy sum to the trace-log term. -/
theorem trace_mul_cfc_logZero_prod_marginals_eq_neg_marginal_vonNeumann_sum
    (ρ : MState (a × b)) :
    ((ρ.m * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x)
        (ρ.traceRight.prod ρ.traceLeft).m).trace).re / Real.log 2 =
      -(ρ.traceRight.vonNeumann + ρ.traceLeft.vonNeumann) := by
  classical
  let τ : MState (a × b) := ρ.traceRight.prod ρ.traceLeft
  let Uprod : Matrix.unitaryGroup (a × b) ℂ :=
    BinaryHypothesisTest.productMarginalEigenvectorUnitary ρ
  let coeff : a × b → ℝ := fun y =>
    ((star (Uprod : CMatrix (a × b)) * ρ.m *
      (Uprod : CMatrix (a × b))) y y).re
  let mu : a × b → ℝ := fun y =>
    ((BinaryHypothesisTest.productMarginalSpectralWeight ρ y : NNReal) : ℝ)
  let muA : a → ℝ := fun i =>
    ((BinaryHypothesisTest.stateSpectralWeight ρ.traceRight i : NNReal) : ℝ)
  let muB : b → ℝ := fun j =>
    ((BinaryHypothesisTest.stateSpectralWeight ρ.traceLeft j : NNReal) : ℝ)
  let w : a × b → ℝ := fun y =>
    ∑ x : a × b,
      ((BinaryHypothesisTest.stateSpectralWeight ρ x : NNReal) : ℝ) *
        ((BinaryHypothesisTest.productMarginalNussbaumSzkolaOverlap ρ x y : NNReal) : ℝ)
  let f : ℝ → ℝ := fun x => if x = 0 then 0 else Real.log x
  have hτspec :
      τ.m = (Uprod : CMatrix (a × b)) *
        (Matrix.diagonal fun y : a × b => ((mu y : ℝ) : ℂ)) *
        star (Uprod : CMatrix (a × b)) := by
    simpa [τ, Uprod, mu] using
      BinaryHypothesisTest.productMarginal_matrix_eq_productEigenbasis_diagonal ρ
  have hlogτ :
      cfc f τ.m = (Uprod : CMatrix (a × b)) *
        (Matrix.diagonal fun y : a × b => ((f (mu y) : ℝ) : ℂ)) *
        star (Uprod : CMatrix (a × b)) := by
    rw [hτspec]
    exact cfc_unitary_conj_diagonal_ofReal Uprod mu f
  have hf_log : ∀ y : a × b, f (mu y) = Real.log (mu y) := by
    intro y
    by_cases hy : mu y = 0
    · simp [f, hy]
    · simp [f, hy]
  have hcoeff : ∀ y : a × b, coeff y = w y := by
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
      ∑ y : a × b, coeff y * f (mu y) =
        (∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j)) := by
    calc
      ∑ y : a × b, coeff y * f (mu y) =
          ∑ y : a × b, w y * Real.log (mu y) := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            rw [hcoeff y, hf_log y]
      _ = ∑ y : a × b, w y *
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
      ((ρ.m * cfc f τ.m).trace).re =
        ∑ y : a × b, coeff y * f (mu y) := by
    rw [hlogτ]
    simpa [coeff] using
      Matrix.trace_mul_unitary_conj_diagonal_right_re Uprod ρ.m
        (fun y : a × b => f (mu y))
  have hA : (∑ i : a, muA i * Real.log (muA i)) / Real.log 2 =
      -ρ.traceRight.vonNeumann := by
    simpa [muA] using
      MState.spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann ρ.traceRight
  have hB : (∑ j : b, muB j * Real.log (muB j)) / Real.log 2 =
      -ρ.traceLeft.vonNeumann := by
    simpa [muB] using
      MState.spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann ρ.traceLeft
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  calc
    ((ρ.m * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x)
        (ρ.traceRight.prod ρ.traceLeft).m).trace).re / Real.log 2 =
        ((ρ.m * cfc f τ.m).trace).re / Real.log 2 := by rfl
    _ = ((∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j))) / Real.log 2 := by
          rw [htrace, hsum]
    _ = -(ρ.traceRight.vonNeumann + ρ.traceLeft.vonNeumann) := by
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
    (ρ : MState (a × b)) : ℝ := by
  classical
  let τ : MState (a × b) := ρ.traceRight.prod ρ.traceLeft
  let hSupport : Matrix.Supports ρ.m τ.m :=
    ρ.matrix_supports_prod_marginals
  let ρc : MState (psdSupportIndex τ.m τ.psd) :=
    _root_.QIT.psdSupportCompressedState ρ τ.psd hSupport
  let σc : CMatrix (psdSupportIndex τ.m τ.psd) :=
    psdSupportCompress τ.m τ.psd τ.m
  have hσc : σc.PosDef := by
    simpa [σc] using psdSupportCompress_self_posDef _ τ.psd
  exact ((ρc.m * psdLog σc hσc).trace.re / Real.log 2)

/-- The mutual-information trace-log bridge reduces to the product-reference
trace term.  The remaining mathematical input is
`prodMarginalsSupportTraceLogTerm ρ = -(S(ρ_A) + S(ρ_B))`. -/
theorem relativeEntropyPSDReferenceTraceLogE_prod_marginals_eq_mutualInformation_of_trace_term
    (ρ : MState (a × b))
    (hTrace :
      ρ.prodMarginalsSupportTraceLogTerm =
        -(ρ.traceRight.vonNeumann + ρ.traceLeft.vonNeumann)) :
    relativeEntropyPSDReferenceTraceLogE ρ
        (ρ.traceRight.prod ρ.traceLeft).m
        (ρ.traceRight.prod ρ.traceLeft).psd =
      (mutualInformation ρ : EReal) := by
  classical
  let τ : MState (a × b) := ρ.traceRight.prod ρ.traceLeft
  let hSupport : Matrix.Supports ρ.m τ.m :=
    ρ.matrix_supports_prod_marginals
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports ρ τ.psd hSupport]
  congr 1
  have hEntropy :
      (_root_.QIT.psdSupportCompressedState ρ τ.psd hSupport).vonNeumann =
        ρ.vonNeumann :=
    MState.vonNeumann_psdSupportCompressedState_eq ρ τ.psd hSupport
  have hTrace' :
      ((psdSupportCompress τ.m τ.psd ρ.m *
            psdLog (psdSupportCompress τ.m τ.psd τ.m)
              (by
                simpa using psdSupportCompress_self_posDef _ τ.psd)).trace.re *
          (Real.log 2)⁻¹) =
        -(ρ.traceRight.vonNeumann + ρ.traceLeft.vonNeumann) := by
    simpa [prodMarginalsSupportTraceLogTerm, τ, div_eq_mul_inv] using hTrace
  simp [relativeEntropyPSDReferenceTraceLogFinite, τ, hTrace',
    mutualInformation, div_eq_mul_inv]
  rw [hEntropy]
  ring_nf

/-- State-to-state trace-log relative entropy against the product of the marginals
is mutual information, assuming the product-reference trace term identity. -/
theorem relativeEntropy_prod_marginals_eq_mutualInformation_of_trace_term
    (ρ : MState (a × b))
    (hTrace :
      ρ.prodMarginalsSupportTraceLogTerm =
        -(ρ.traceRight.vonNeumann + ρ.traceLeft.vonNeumann)) :
    ρ.relativeEntropy (ρ.traceRight.prod ρ.traceLeft) =
      (mutualInformation ρ : EReal) := by
  simpa [relativeEntropy] using
    relativeEntropyPSDReferenceTraceLogE_prod_marginals_eq_mutualInformation_of_trace_term
      ρ hTrace

/-- The product-reference trace-log term is the negative sum of the two
marginal entropies. -/
theorem prodMarginalsSupportTraceLogTerm_eq_neg_marginal_vonNeumann_sum
    (ρ : MState (a × b)) :
    ρ.prodMarginalsSupportTraceLogTerm =
      -(ρ.traceRight.vonNeumann + ρ.traceLeft.vonNeumann) := by
  classical
  let τ : MState (a × b) := ρ.traceRight.prod ρ.traceLeft
  let hSupport : Matrix.Supports ρ.m τ.m :=
    ρ.matrix_supports_prod_marginals
  have hTrace :
      ((psdSupportCompress τ.m τ.psd ρ.m *
        MState.psdLog (psdSupportCompress τ.m τ.psd τ.m)
          (psdSupportCompress_self_posDef τ.m τ.psd)).trace).re =
        ((ρ.m * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x) τ.m).trace).re :=
    trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero ρ τ.psd hSupport
  have hProd :=
    trace_mul_cfc_logZero_prod_marginals_eq_neg_marginal_vonNeumann_sum ρ
  calc
    ρ.prodMarginalsSupportTraceLogTerm =
        ((ρ.m * cfc (fun x : ℝ => if x = 0 then 0 else Real.log x)
          τ.m).trace).re / Real.log 2 := by
          simpa [prodMarginalsSupportTraceLogTerm, τ, hSupport] using
            congrArg (fun x : ℝ => x / Real.log 2) hTrace
    _ = -(ρ.traceRight.vonNeumann + ρ.traceLeft.vonNeumann) := by
          simpa [τ] using hProd

/-- Trace-log relative entropy against the product of the marginals is mutual
information. -/
theorem relativeEntropyPSDReferenceTraceLogE_prod_marginals_eq_mutualInformation
    (ρ : MState (a × b)) :
    relativeEntropyPSDReferenceTraceLogE ρ
        (ρ.traceRight.prod ρ.traceLeft).m
        (ρ.traceRight.prod ρ.traceLeft).psd =
      (mutualInformation ρ : EReal) :=
  relativeEntropyPSDReferenceTraceLogE_prod_marginals_eq_mutualInformation_of_trace_term
    ρ (prodMarginalsSupportTraceLogTerm_eq_neg_marginal_vonNeumann_sum ρ)

/-- State-to-state relative entropy against the product of the marginals is mutual
information. -/
theorem relativeEntropy_prod_marginals_eq_mutualInformation
    (ρ : MState (a × b)) :
    ρ.relativeEntropy (ρ.traceRight.prod ρ.traceLeft) =
      (mutualInformation ρ : EReal) :=
  relativeEntropy_prod_marginals_eq_mutualInformation_of_trace_term
    ρ (prodMarginalsSupportTraceLogTerm_eq_neg_marginal_vonNeumann_sum ρ)

/-- A two-sided product channel maps the left marginal by the left channel. -/
theorem traceRight_applyState_prod
    (ρ : MState (a × b)) (Φ : CPTPMap a c) (Ψ : CPTPMap b d) :
    MState.traceRight ((Φ.prod Ψ) ρ) = Φ ρ.traceRight := by
  let ρ' : MState (c × b) := (Φ.prod (CPTPOp.id (dIn := b))) ρ
  have hseq :
      ((Φ.prod Ψ) ρ) =
        (((CPTPOp.id (dIn := c)).prod Ψ) ρ') := by
    apply MState.ext
    simp only [CPTPOp.mat_coe_eq_apply_mat, ρ', CPTPOp.prod_map]
    have hleft : (CPTPOp.id (dIn := c)).map.comp Φ.map = Φ.map := by
      rw [CPTPOp.id_map]
      ext X i j
      rfl
    have hright : Ψ.map.comp (CPTPOp.id (dIn := b)).map = Ψ.map := by
      rw [CPTPOp.id_map]
      ext X i j
      rfl
    simpa [hleft, hright] using
      (MatrixMap.kron_comp_apply_general
        (CPTPOp.id (dIn := c)).map Ψ.map Φ.map (CPTPOp.id (dIn := b)).map ρ.m).symm
  rw [hseq]
  calc
    MState.traceRight (((CPTPOp.id (dIn := c)).prod Ψ) ρ') = ρ'.traceRight := by
      exact MState.traceRight_applyState_id_prod ρ' Ψ
    _ = Φ ρ.traceRight := by
      simpa [ρ'] using MState.traceRight_applyState_prod_id ρ Φ

/-- A two-sided product channel maps the right marginal by the right channel. -/
theorem traceLeft_applyState_prod
    (ρ : MState (a × b)) (Φ : CPTPMap a c) (Ψ : CPTPMap b d) :
    MState.traceLeft ((Φ.prod Ψ) ρ) = Ψ ρ.traceLeft := by
  let ρ' : MState (a × d) := ((CPTPOp.id (dIn := a)).prod Ψ) ρ
  have hseq :
      ((Φ.prod Ψ) ρ) =
        ((Φ.prod (CPTPOp.id (dIn := d))) ρ') := by
    apply MState.ext
    simp only [CPTPOp.mat_coe_eq_apply_mat, ρ', CPTPOp.prod_map]
    have hleft : Φ.map.comp (CPTPOp.id (dIn := a)).map = Φ.map := by
      rw [CPTPOp.id_map]
      ext X i j
      rfl
    have hright : (CPTPOp.id (dIn := d)).map.comp Ψ.map = Ψ.map := by
      rw [CPTPOp.id_map]
      ext X i j
      rfl
    simpa [hleft, hright] using
      (MatrixMap.kron_comp_apply_general
        Φ.map (CPTPOp.id (dIn := d)).map (CPTPOp.id (dIn := a)).map Ψ.map ρ.m).symm
  rw [hseq]
  calc
    MState.traceLeft ((Φ.prod (CPTPOp.id (dIn := d))) ρ') = ρ'.traceLeft := by
      exact MState.traceLeft_applyState_prod_id ρ' Φ
    _ = Ψ ρ.traceLeft := by
      -- Right-local postprocessing is handled symmetrically by tracing out the
      -- left subsystem.
      apply MState.ext
      simp only [CPTPOp.mat_coe_eq_apply_mat, MState.traceLeft_m, ρ',
        CPTPOp.prod_map]
      ext j j'
      simp only [Matrix.traceLeft, Matrix.of_apply]
      let S : a → CMatrix b := fun i => Matrix.of fun y y' => ρ.m (i, y) (i, y')
      have hsum :
          (fun y y' => ∑ i : a, ρ.m (i, y) (i, y')) =
            ∑ i : a, S i := by
        ext y y'
        simp only [Matrix.sum_apply]
        rfl
      change (∑ i : a,
          MatrixMap.kron (CPTPOp.id (dIn := a)).map Ψ.map ρ.m (i, j) (i, j')) =
        Ψ.map (fun y y' => ∑ i : a, ρ.m (i, y) (i, y')) j j'
      rw [hsum, map_sum]
      simp only [Matrix.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact MatrixMap.kron_idChannel_left_apply_slice (a := a)
        (Φ := Ψ.map) (X := ρ.m) (ad := (i, j)) (ad' := (i, j'))

/-- Product channels send the product of input marginals to the product of
output marginals. -/
theorem applyState_prod_marginals
    (ρ : MState (a × b)) (Φ : CPTPMap a c) (Ψ : CPTPMap b d) :
    (Φ.prod Ψ) (ρ.traceRight.prod ρ.traceLeft) =
      MState.prod (MState.traceRight ((Φ.prod Ψ) ρ))
        (MState.traceLeft ((Φ.prod Ψ) ρ)) := by
  rw [CPTPOp.prod_apply_prod]
  rw [traceRight_applyState_prod, traceLeft_applyState_prod]

end MState

namespace QIT

/-- Once the source-facing trace-log bridge
`D(ρ_AB ‖ ρ_A ⊗ ρ_B) = I(A;B)_ρ` is available for the input and output
states, mutual-information DPI under local channels is a direct instance of
relative-entropy DPI. -/
theorem mutualInformation_dataProcessing_local_channels_ge_of_traceLog_bridge
    {a : Type u} {b : Type v} {c : Type w} {d : Type x}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (ρ : MState (a × b)) (Φ : CPTPMap a c) (Ψ : CPTPMap b d)
    (hIn :
      ρ.relativeEntropy (ρ.traceRight.prod ρ.traceLeft) =
        (mutualInformation ρ : EReal))
    (hOut :
      MState.relativeEntropy ((Φ.prod Ψ) ρ)
          (MState.prod (MState.traceRight ((Φ.prod Ψ) ρ))
            (MState.traceLeft ((Φ.prod Ψ) ρ))) =
        (mutualInformation ((Φ.prod Ψ) ρ) : EReal)) :
    mutualInformation ρ ≥ mutualInformation ((Φ.prod Ψ) ρ) := by
  classical
  let τ : MState (a × b) := ρ.traceRight.prod ρ.traceLeft
  let ω : MState (c × d) := (Φ.prod Ψ) ρ
  have hτstate :
      (Φ.prod Ψ) τ = ω.traceRight.prod ω.traceLeft := by
    simpa [τ, ω] using
      MState.applyState_prod_marginals ρ Φ Ψ
  have hOut' :
      ω.relativeEntropy ((Φ.prod Ψ) τ) =
        (mutualInformation ω : EReal) := by
    simpa [τ, ω, hτstate] using hOut
  have hDPI :
      ω.relativeEntropy ((Φ.prod Ψ) τ) ≤
        ρ.relativeEntropy τ := by
    exact MState.relativeEntropy_dataProcessing_channel_ge ρ τ (Φ.prod Ψ)
  have hE :
      (mutualInformation ω : EReal) ≤ (mutualInformation ρ : EReal) := by
    rw [hOut'] at hDPI
    simp only [τ, hIn] at hDPI
    exact hDPI
  exact EReal.coe_le_coe_iff.mp hE

/-- Quantum mutual information is monotone under local channels:
`I(A;B)_ρ ≥ I(A';B')_(Φ ⊗ Ψ)(ρ)`. -/
theorem mutualInformation_dataProcessing_local_channels_ge
    {a : Type u} {b : Type v} {c : Type w} {d : Type x}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (ρ : MState (a × b)) (Φ : CPTPMap a c) (Ψ : CPTPMap b d) :
    mutualInformation ρ ≥ mutualInformation ((Φ.prod Ψ) ρ) := by
  exact
    mutualInformation_dataProcessing_local_channels_ge_of_traceLog_bridge ρ Φ Ψ
      (MState.relativeEntropy_prod_marginals_eq_mutualInformation ρ)
      (MState.relativeEntropy_prod_marginals_eq_mutualInformation
        ((Φ.prod Ψ) ρ))

end QIT

namespace MState

open QIT

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Quantum mutual information is nonnegative.  Measuring both sides down to a
trivial system leaves no correlation, and data processing bounds `I(A;B)` below
by that zero. -/
theorem mutualInformation_nonneg (ρ : MState (a × b)) :
    0 ≤ QIT.mutualInformation ρ := by
  have hDPI :=
    QIT.mutualInformation_dataProcessing_local_channels_ge ρ
      (terminalMeasureChannel a) (terminalMeasureChannel b)
  have hzero :
      QIT.mutualInformation
          (((terminalMeasureChannel a).prod (terminalMeasureChannel b)) ρ) = 0 :=
    mutualInformation_punit_punit_eq_zero _
  linarith

end MState
