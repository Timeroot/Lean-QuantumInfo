/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Renyi.AlphaEntropyContinuity
public import QuantumLib.QIT.Information.Renyi.FrankLieb.DPI
public import QuantumLib.QIT.Util.BlockMatrix

/-!
# Direct-sum mean property for sandwiched Renyi divergence

This file proves the unequal-dimensional direct-sum identities used in
Tomamichel (2015), Property (VI).  In particular, the zero block in the first
argument stays zero; the second reference block is not averaged into the
result.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

noncomputable section
universe u v w

open QIT

namespace QIT

/-- Real continuous functional calculus preserves unequal-dimensional
positive-semidefinite diagonal blocks.  The proof explicitly joins the two
spectral decompositions into a block unitary. -/
theorem cMatrix_cfc_fromBlocks_diagonal
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    {A : CMatrix p} {D : CMatrix q} (hA : A.PosSemidef) (hD : D.PosSemidef)
    (f : ℝ → ℝ) :
    cfc f (Matrix.fromBlocks A 0 0 D : CMatrix (p ⊕ q)) =
      Matrix.fromBlocks (cfc f A) 0 0 (cfc f D) := by
  let UA : Matrix.unitaryGroup p ℂ := hA.isHermitian.eigenvectorUnitary
  let UD : Matrix.unitaryGroup q ℂ := hD.isHermitian.eigenvectorUnitary
  let da : p → ℝ := hA.isHermitian.eigenvalues
  let dd : q → ℝ := hD.isHermitian.eigenvalues
  have hspecA :
      A = (UA : CMatrix p) * Matrix.diagonal (fun i => (da i : ℂ)) *
        star (UA : CMatrix p) := by
    simpa [UA, da, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
      Function.comp_def] using hA.isHermitian.spectral_theorem
  have hspecD :
      D = (UD : CMatrix q) * Matrix.diagonal (fun i => (dd i : ℂ)) *
        star (UD : CMatrix q) := by
    simpa [UD, dd, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc,
      Function.comp_def] using hD.isHermitian.spectral_theorem
  let U : Matrix.unitaryGroup (p ⊕ q) ℂ :=
    ⟨Matrix.fromBlocks (UA : CMatrix p) 0 0 (UD : CMatrix q), by
      rw [Matrix.mem_unitaryGroup_iff]
      simp only [Matrix.star_eq_conjTranspose]
      rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      have hUA : (UA : CMatrix p) * (UA : CMatrix p).conjTranspose = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp UA.2
      have hUD : (UD : CMatrix q) * (UD : CMatrix q).conjTranspose = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp UD.2
      simp only [Matrix.conjTranspose_zero]
      rw [hUA, hUD]
      ext i j
      cases i <;> cases j <;> simp [Matrix.one_apply]⟩
  let d : p ⊕ q → ℝ := Sum.elim da dd
  have hdiag :
      (Matrix.fromBlocks
          (Matrix.diagonal (fun i => (da i : ℂ))) 0 0
          (Matrix.diagonal (fun i => (dd i : ℂ))) : CMatrix (p ⊕ q)) =
        Matrix.diagonal (fun i => (d i : ℂ)) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.diagonal, d]
  have hspec :
      (Matrix.fromBlocks A 0 0 D : CMatrix (p ⊕ q)) =
        (U : CMatrix (p ⊕ q)) * Matrix.diagonal (fun i => (d i : ℂ)) *
          star (U : CMatrix (p ⊕ q)) := by
    rw [hspecA, hspecD, ← hdiag]
    change Matrix.fromBlocks
        ((UA : CMatrix p) * Matrix.diagonal (fun i => (da i : ℂ)) *
          star (UA : CMatrix p)) 0 0
        ((UD : CMatrix q) * Matrix.diagonal (fun i => (dd i : ℂ)) *
          star (UD : CMatrix q)) =
      Matrix.fromBlocks (UA : CMatrix p) 0 0 (UD : CMatrix q) *
        Matrix.fromBlocks (Matrix.diagonal (fun i => (da i : ℂ))) 0 0
          (Matrix.diagonal (fun i => (dd i : ℂ))) *
        star (Matrix.fromBlocks (UA : CMatrix p) 0 0 (UD : CMatrix q))
    simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hcfcA :
      cfc f A =
        (UA : CMatrix p) * Matrix.diagonal (fun i => ((f (da i) : ℝ) : ℂ)) *
          star (UA : CMatrix p) := by
    rw [hspecA]
    exact cfc_unitary_conj_diagonal_ofReal UA da f
  have hcfcD :
      cfc f D =
        (UD : CMatrix q) * Matrix.diagonal (fun i => ((f (dd i) : ℝ) : ℂ)) *
          star (UD : CMatrix q) := by
    rw [hspecD]
    exact cfc_unitary_conj_diagonal_ofReal UD dd f
  have hdiagCfc :
      (Matrix.fromBlocks
          (Matrix.diagonal (fun i => ((f (da i) : ℝ) : ℂ))) 0 0
          (Matrix.diagonal (fun i => ((f (dd i) : ℝ) : ℂ))) :
            CMatrix (p ⊕ q)) =
        Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.diagonal, d]
  have hcfcSpec :
      (Matrix.fromBlocks (cfc f A) 0 0 (cfc f D) : CMatrix (p ⊕ q)) =
        (U : CMatrix (p ⊕ q)) *
          Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) *
          star (U : CMatrix (p ⊕ q)) := by
    rw [hcfcA, hcfcD, ← hdiagCfc]
    change Matrix.fromBlocks
        ((UA : CMatrix p) * Matrix.diagonal (fun i => ((f (da i) : ℝ) : ℂ)) *
          star (UA : CMatrix p)) 0 0
        ((UD : CMatrix q) * Matrix.diagonal (fun i => ((f (dd i) : ℝ) : ℂ)) *
          star (UD : CMatrix q)) =
      Matrix.fromBlocks (UA : CMatrix p) 0 0 (UD : CMatrix q) *
        Matrix.fromBlocks
          (Matrix.diagonal (fun i => ((f (da i) : ℝ) : ℂ))) 0 0
          (Matrix.diagonal (fun i => ((f (dd i) : ℝ) : ℂ))) *
        star (Matrix.fromBlocks (UA : CMatrix p) 0 0 (UD : CMatrix q))
    simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  rw [hspec]
  exact (cfc_unitary_conj_diagonal_ofReal U d f).trans hcfcSpec.symm

/-- Real powers preserve unequal-dimensional positive-semidefinite diagonal
blocks, including for negative exponents under the repository's support
convention at zero. -/
theorem cMatrix_rpow_fromBlocks_diagonal
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    {A : CMatrix p} {D : CMatrix q} (hA : A.PosSemidef) (hD : D.PosSemidef)
    (s : ℝ) :
    CFC.rpow (Matrix.fromBlocks A 0 0 D : CMatrix (p ⊕ q)) s =
      Matrix.fromBlocks (CFC.rpow A s) 0 0 (CFC.rpow D s) := by
  change ((Matrix.fromBlocks A 0 0 D : CMatrix (p ⊕ q)) ^ s) =
    Matrix.fromBlocks (A ^ s) 0 0 (D ^ s)
  rw [CFC.rpow_eq_cfc_real (a := (Matrix.fromBlocks A 0 0 D : CMatrix (p ⊕ q)))
      (y := s) (Matrix.nonneg_iff_posSemidef.mpr
        (Matrix.fromBlocks_diagonal_posSemidef hA hD)),
    CFC.rpow_eq_cfc_real (a := A) (y := s) (Matrix.nonneg_iff_posSemidef.mpr hA),
    CFC.rpow_eq_cfc_real (a := D) (y := s) (Matrix.nonneg_iff_posSemidef.mpr hD)]
  exact cMatrix_cfc_fromBlocks_diagonal hA hD (fun x => x ^ s)

end QIT

namespace MState

/-- Extend a normalized state by a zero lower-right block. -/
def directSumZero
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : MState p) (q : Type v) [Fintype q] [DecidableEq q] : MState (p ⊕ q) := .ofMatrix
  (matrix := Matrix.fromBlocks rho.m 0 0 0)
  (pos := Matrix.fromBlocks_diagonal_posSemidef rho.psd Matrix.PosSemidef.zero)
  (trace_eq_one := by
    rw [Matrix.trace_fromBlocks_diagonal, rho.tr']
    simp)

@[simp]
theorem directSumZero_matrix
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : MState p) (q : Type v) [Fintype q] [DecidableEq q] :
    (rho.directSumZero q).m = Matrix.fromBlocks rho.m 0 0 0 :=
  MState.matrix_ofMatrix _ _ _

/-- The zero extension is positive semidefinite. -/
theorem directSumZero_posSemidef
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : MState p) (q : Type v) [Fintype q] [DecidableEq q] :
    (rho.directSumZero q).m.PosSemidef :=
  (rho.directSumZero q).psd

/-- The zero extension remains normalized. -/
theorem directSumZero_trace
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : MState p) (q : Type v) [Fintype q] [DecidableEq q] :
    (rho.directSumZero q).m.trace = 1 :=
  (rho.directSumZero q).tr'

private def directSumInclusion
    (p : Type u) (q : Type v) [DecidableEq p] [DecidableEq q] :
    Matrix (p ⊕ q) p ℂ :=
  fun i j => if i = Sum.inl j then 1 else 0

private theorem directSumInclusion_isometry
    (p : Type u) (q : Type v) [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] :
    Matrix.conjTranspose (directSumInclusion p q) * directSumInclusion p q =
      (1 : CMatrix p) := by
  ext i j
  simp [directSumInclusion, Matrix.mul_apply, Matrix.conjTranspose, Matrix.one_apply,
    eq_comm]

private theorem directSumInclusion_conj
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (M : CMatrix p) :
    directSumInclusion p q * M * Matrix.conjTranspose (directSumInclusion p q) =
      (Matrix.fromBlocks M 0 0 0 : CMatrix (p ⊕ q)) := by
  ext i j
  cases i <;> cases j <;>
    simp [directSumInclusion, Matrix.mul_apply, Matrix.conjTranspose]

/-- Zero extension adds only zero eigenvalues and therefore preserves von
Neumann entropy. -/
@[simp]
theorem directSumZero_vonNeumann
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : MState p) (q : Type v) [Fintype q] [DecidableEq q] :
    (rho.directSumZero q).vonNeumann = rho.vonNeumann := by
  refine vonNeumann_eq_of_matrix_eq_isometry_conj
    rho (rho.directSumZero q) (directSumInclusion p q)
    (directSumInclusion_isometry p q) ?_
  rw [directSumZero_matrix]
  exact (directSumInclusion_conj (q := q) rho.m).symm

/-- The positive-definite matrix logarithm preserves unequal-dimensional
diagonal blocks. -/
theorem psdLog_fromBlocks_diagonal
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    {A : CMatrix p} {D : CMatrix q} (hA : A.PosDef) (hD : D.PosDef) :
    psdLog (Matrix.fromBlocks A 0 0 D)
        (Matrix.fromBlocks_diagonal_posDef hA hD) =
      Matrix.fromBlocks (psdLog A hA) 0 0 (psdLog D hD) := by
  unfold psdLog
  exact cMatrix_cfc_fromBlocks_diagonal hA.posSemidef hD.posSemidef Real.log

/-- Positive-definite matrix logarithms commute with finite basis relabeling. -/
theorem psdLog_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {sigma : CMatrix a} (hSigma : sigma.PosDef) (e : a ≃ b) :
    psdLog (Matrix.reindex e e sigma) (hSigma.submatrix e.symm.injective) =
      Matrix.reindex e e (psdLog sigma hSigma) := by
  unfold psdLog
  exact cMatrix_cfc_reindex_posSemidef
    e hSigma.posSemidef Real.log

/-- The sandwiched `Q` functional is invariant under a simultaneous finite
basis relabeling, including the negative sandwich exponent used above order
one. -/
theorem sandwichedRenyiQ_reindex_posSemidef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {rho sigma : CMatrix a} (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef)
    (e : a ≃ b) (alpha : ℝ) :
    sandwichedRenyiQ (Matrix.reindex e e rho) (Matrix.reindex e e sigma)
        (hRho.submatrix e.symm) (hSigma.submatrix e.symm) alpha =
      sandwichedRenyiQ rho sigma hRho hSigma alpha := by
  let t : ℝ := (1 - alpha) / (2 * alpha)
  let C : CMatrix a := CFC.rpow sigma t
  let inner : CMatrix a := C * rho * C
  have hC : C.PosSemidef := by
    exact cMatrix_rpow_posSemidef hSigma
  have hInner : inner.PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hRho C
    rw [hC.isHermitian.eq] at h
    exact h
  have hPowSigma :
      CFC.rpow (Matrix.reindex e e sigma) t = Matrix.reindex e e C := by
    exact cMatrix_rpow_reindex_posSemidef e hSigma t
  have hSandwich :
      CFC.rpow (Matrix.reindex e e sigma) t * Matrix.reindex e e rho *
          CFC.rpow (Matrix.reindex e e sigma) t =
        Matrix.reindex e e inner := by
    rw [hPowSigma]
    change
      (Matrix.reindexAlgEquiv ℂ ℂ e) C *
          (Matrix.reindexAlgEquiv ℂ ℂ e) rho *
        (Matrix.reindexAlgEquiv ℂ ℂ e) C =
      (Matrix.reindexAlgEquiv ℂ ℂ e) inner
    rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) C rho]
    rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
      (C * rho) C]
  have hPowInner :
      CFC.rpow (Matrix.reindex e e inner) alpha =
        Matrix.reindex e e (CFC.rpow inner alpha) :=
    cMatrix_rpow_reindex_posSemidef e hInner alpha
  unfold sandwichedRenyiQ
  change
    (CFC.rpow
      (CFC.rpow (Matrix.reindex e e sigma) t * Matrix.reindex e e rho *
        CFC.rpow (Matrix.reindex e e sigma) t) alpha).trace.re =
      (CFC.rpow inner alpha).trace.re
  rw [hSandwich, hPowInner]
  exact congrArg Complex.re
    (Matrix.trace_submatrix (CFC.rpow inner alpha) e.symm)

/-- The support-aware trace-log branch at order one ignores a zero state
extension against an arbitrary positive-definite complementary reference. -/
theorem relativeEntropyPSDReferenceTraceLogE_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : MState p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef) :
    relativeEntropyPSDReferenceTraceLogE (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma.posSemidef := by
  let hBlock : (Matrix.fromBlocks sigma 0 0 tau : CMatrix (p ⊕ q)).PosDef :=
    Matrix.fromBlocks_diagonal_posDef hSigma hTau
  let hSupportBlock : Matrix.Supports (rho.directSumZero q).m
      (Matrix.fromBlocks sigma 0 0 tau) :=
    Matrix.Supports.of_right_posDef _ _ hBlock
  let hSupport : Matrix.Supports rho.m sigma :=
    Matrix.Supports.of_right_posDef _ _ hSigma
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
      (rho.directSumZero q) hBlock.posSemidef hSupportBlock,
    relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
      rho hSigma.posSemidef hSupport]
  congr 1
  rw [relativeEntropyPSDReferenceTraceLogFinite_eq_of_posDef
      (rho.directSumZero q) hBlock hSupportBlock,
    relativeEntropyPSDReferenceTraceLogFinite_eq_of_posDef rho hSigma hSupport,
    directSumZero_vonNeumann]
  congr 2
  rw [directSumZero_matrix, psdLog_fromBlocks_diagonal hSigma hTau,
    Matrix.fromBlocks_multiply]
  simp [Matrix.trace_fromBlocks_diagonal]

private theorem trace_mul_psdLog_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rho : CMatrix a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) :
    ((Matrix.reindex e e rho *
      psdLog (Matrix.reindex e e sigma) (hSigma.submatrix e.symm.injective)).trace).re =
      ((rho * psdLog sigma hSigma).trace).re := by
  rw [psdLog_reindex_posDef hSigma e]
  change
    (((Matrix.reindexAlgEquiv ℂ ℂ e) rho *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (psdLog sigma hSigma)).trace).re = _
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
    rho (psdLog sigma hSigma)]
  exact congrArg Complex.re
    (Matrix.trace_submatrix (rho * psdLog sigma hSigma) e.symm)

/-- The support-aware trace-log branch is invariant under a finite basis
relabeling when the reference is positive definite.  The input state need not
be positive definite. -/
theorem relativeEntropyPSDReferenceTraceLogE_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rho : MState a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) :
    relativeEntropyPSDReferenceTraceLogE (rho.reindex e)
        (Matrix.reindex e e sigma)
        (hSigma.submatrix e.symm.injective).posSemidef =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma.posSemidef := by
  let hSigmaRe : (Matrix.reindex e e sigma).PosDef :=
    hSigma.submatrix e.symm.injective
  let hSupportRe : Matrix.Supports (rho.reindex e).m
      (Matrix.reindex e e sigma) :=
    Matrix.Supports.of_right_posDef _ _ hSigmaRe
  let hSupport : Matrix.Supports rho.m sigma :=
    Matrix.Supports.of_right_posDef _ _ hSigma
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
      (rho.reindex e) hSigmaRe.posSemidef hSupportRe,
    relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
      rho hSigma.posSemidef hSupport]
  congr 1
  rw [relativeEntropyPSDReferenceTraceLogFinite_eq_of_posDef
      (rho.reindex e) hSigmaRe hSupportRe,
    relativeEntropyPSDReferenceTraceLogFinite_eq_of_posDef rho hSigma hSupport,
    vonNeumann_reindex]
  congr 2
  rw [MState.reindex_matrix]
  exact trace_mul_psdLog_reindex_posDef rho.m hSigma e

/-- The sandwiched `Q` functional splits over unequal-dimensional diagonal
blocks. -/
theorem sandwichedRenyiQ_fromBlocks_diagonal
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    {rhoP sigmaP : CMatrix p} {rhoQ sigmaQ : CMatrix q}
    (hRhoP : rhoP.PosSemidef) (hRhoQ : rhoQ.PosSemidef)
    (hSigmaP : sigmaP.PosSemidef) (hSigmaQ : sigmaQ.PosSemidef)
    (alpha : ℝ) :
    sandwichedRenyiQ
        (Matrix.fromBlocks rhoP 0 0 rhoQ)
        (Matrix.fromBlocks sigmaP 0 0 sigmaQ)
        (Matrix.fromBlocks_diagonal_posSemidef hRhoP hRhoQ)
        (Matrix.fromBlocks_diagonal_posSemidef hSigmaP hSigmaQ) alpha =
      sandwichedRenyiQ rhoP sigmaP hRhoP hSigmaP alpha +
        sandwichedRenyiQ rhoQ sigmaQ hRhoQ hSigmaQ alpha := by
  let t : ℝ := (1 - alpha) / (2 * alpha)
  let CP : CMatrix p := CFC.rpow sigmaP t
  let CQ : CMatrix q := CFC.rpow sigmaQ t
  have hCP : CP.PosSemidef := by
    exact cMatrix_rpow_posSemidef hSigmaP
  have hCQ : CQ.PosSemidef := by
    exact cMatrix_rpow_posSemidef hSigmaQ
  have hInnerP : (CP * rhoP * CP).PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hRhoP CP
    rw [hCP.isHermitian.eq] at h
    exact h
  have hInnerQ : (CQ * rhoQ * CQ).PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hRhoQ CQ
    rw [hCQ.isHermitian.eq] at h
    exact h
  have hSandwich :
      CFC.rpow (Matrix.fromBlocks sigmaP 0 0 sigmaQ : CMatrix (p ⊕ q)) t *
          Matrix.fromBlocks rhoP 0 0 rhoQ *
        CFC.rpow (Matrix.fromBlocks sigmaP 0 0 sigmaQ : CMatrix (p ⊕ q)) t =
      Matrix.fromBlocks (CP * rhoP * CP) 0 0 (CQ * rhoQ * CQ) := by
    rw [cMatrix_rpow_fromBlocks_diagonal hSigmaP hSigmaQ t]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [CP, CQ]
  unfold sandwichedRenyiQ
  change
    (CFC.rpow
      (CFC.rpow (Matrix.fromBlocks sigmaP 0 0 sigmaQ : CMatrix (p ⊕ q)) t *
          Matrix.fromBlocks rhoP 0 0 rhoQ *
        CFC.rpow (Matrix.fromBlocks sigmaP 0 0 sigmaQ : CMatrix (p ⊕ q)) t)
      alpha).trace.re =
      (CFC.rpow (CP * rhoP * CP) alpha).trace.re +
        (CFC.rpow (CQ * rhoQ * CQ) alpha).trace.re
  rw [hSandwich, cMatrix_rpow_fromBlocks_diagonal hInnerP hInnerQ alpha,
    Matrix.trace_fromBlocks_diagonal]
  exact Complex.add_re _ _

/-- Adding a zero state block and an arbitrary PSD reference block leaves the
`Q` functional unchanged for positive orders. -/
theorem sandwichedRenyiQ_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : MState p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosSemidef) (hTau : tau.PosSemidef)
    {alpha : ℝ} (hAlpha : 0 < alpha) :
    sandwichedRenyiQ (rho.directSumZero q).m
        (Matrix.fromBlocks sigma 0 0 tau)
        (rho.directSumZero q).psd
        (Matrix.fromBlocks_diagonal_posSemidef hSigma hTau) alpha =
      sandwichedRenyiQ rho.m sigma rho.psd hSigma alpha := by
  rw [sandwichedRenyiQ_congr (rho.directSumZero q).psd
      (Matrix.fromBlocks_diagonal_posSemidef hSigma hTau)
      (Matrix.fromBlocks_diagonal_posSemidef rho.psd Matrix.PosSemidef.zero)
      (Matrix.fromBlocks_diagonal_posSemidef hSigma hTau)
      (directSumZero_matrix rho q) rfl alpha]
  rw [sandwichedRenyiQ_fromBlocks_diagonal rho.psd Matrix.PosSemidef.zero
    hSigma hTau alpha]
  rw [sandwichedRenyiQ_zero_left tau hTau hAlpha, add_zero]

/-- The extended-real low-order branch ignores a zero state extension against
a positive-definite complementary reference. -/
theorem sandwichedRenyiPSDReferenceLowAlphaE_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : MState p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    {alpha : ℝ} (hAlpha : 0 < alpha) :
    sandwichedRenyiPSDReferenceLowAlphaE (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha =
      sandwichedRenyiPSDReferenceLowAlphaE rho sigma hSigma.posSemidef alpha := by
  unfold sandwichedRenyiPSDReferenceLowAlphaE sandwichedRenyiPSDReferenceLowAlpha
  rw [sandwichedRenyiQ_directSumZero rho hSigma.posSemidef hTau.posSemidef hAlpha]

/-- The finite high-order branch ignores a zero state extension against a
positive-definite complementary reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : MState p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    {alpha : ℝ} (hAlpha : 0 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma.posSemidef alpha := by
  unfold sandwichedRenyiPSDReferenceHighAlphaFinite
  rw [← sandwichedRenyiQ_eq_psdTracePower_referenceInner
      (rho.directSumZero q)
      (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha,
    ← sandwichedRenyiQ_eq_psdTracePower_referenceInner rho hSigma.posSemidef alpha,
    sandwichedRenyiQ_directSumZero rho hSigma.posSemidef hTau.posSemidef hAlpha]

/-- The support-aware high-order branch ignores a zero state extension against
a positive-definite complementary reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : MState p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    {alpha : ℝ} (hAlpha : 0 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaE (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha =
      sandwichedRenyiPSDReferenceHighAlphaE rho sigma hSigma.posSemidef alpha := by
  let hBlock : (Matrix.fromBlocks sigma 0 0 tau : CMatrix (p ⊕ q)).PosDef :=
    Matrix.fromBlocks_diagonal_posDef hSigma hTau
  let hSupportBlock : Matrix.Supports (rho.directSumZero q).m
      (Matrix.fromBlocks sigma 0 0 tau) :=
    Matrix.Supports.of_right_posDef _ _ hBlock
  let hSupport : Matrix.Supports rho.m sigma :=
    Matrix.Supports.of_right_posDef _ _ hSigma
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (rho.directSumZero q) hBlock.posSemidef alpha hSupportBlock,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho hSigma.posSemidef alpha hSupport]
  congr 1
  exact sandwichedRenyiPSDReferenceHighAlphaFinite_directSumZero
    rho hSigma hTau hAlpha

/-- Tomamichel's direct-sum mean property for a normalized zero extension.

For every finite order `alpha ≥ 1 / 2`, including the support-aware
trace-log branch at `alpha = 1`, the nonzero complementary reference block is
ignored because the corresponding state block is zero.  No positive-
definiteness assumption is made on `rho`. -/
theorem sandwichedRenyiPSDReferenceE_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : MState p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    {alpha : ℝ} (hAlpha : 1 / 2 ≤ alpha) :
    sandwichedRenyiPSDReferenceE (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha =
      sandwichedRenyiPSDReferenceE rho sigma hSigma.posSemidef alpha := by
  have hAlphaPos : 0 < alpha := by
    have : (0 : ℝ) < 1 / 2 := by norm_num
    exact this.trans_le hAlpha
  rcases lt_trichotomy alpha 1 with hlt | heq | hgt
  · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
        (rho.directSumZero q)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef hlt,
      sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
        rho hSigma.posSemidef hlt]
    exact sandwichedRenyiPSDReferenceLowAlphaE_directSumZero
      rho hSigma hTau hAlphaPos
  · rw [sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one
        (rho.directSumZero q)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef heq,
      sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one
        rho hSigma.posSemidef heq]
    exact relativeEntropyPSDReferenceTraceLogE_directSumZero rho hSigma hTau
  · rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
        (rho.directSumZero q)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef hgt,
      sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
        rho hSigma.posSemidef hgt]
    exact sandwichedRenyiPSDReferenceHighAlphaE_directSumZero
      rho hSigma hTau hAlphaPos

/-- The extended-real low-order branch is invariant under finite basis
relabeling for a positive-definite reference. -/
theorem sandwichedRenyiPSDReferenceLowAlphaE_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rho : MState a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) (alpha : ℝ) :
    sandwichedRenyiPSDReferenceLowAlphaE (rho.reindex e)
        (Matrix.reindex e e sigma)
        (hSigma.submatrix e.symm.injective).posSemidef alpha =
      sandwichedRenyiPSDReferenceLowAlphaE rho sigma hSigma.posSemidef alpha := by
  have hQ := sandwichedRenyiQ_reindex_posSemidef
    rho.psd hSigma.posSemidef e alpha
  simp only [Matrix.reindex_apply] at hQ
  unfold sandwichedRenyiPSDReferenceLowAlphaE sandwichedRenyiPSDReferenceLowAlpha
  simp only [MState.reindex_matrix, Matrix.reindex_apply]
  simp only [hQ]

/-- The finite high-order branch is invariant under finite basis relabeling
for a positive-definite reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rho : MState a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) (alpha : ℝ) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (rho.reindex e)
        (Matrix.reindex e e sigma)
        (hSigma.submatrix e.symm.injective).posSemidef alpha =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma.posSemidef alpha := by
  have hQ := sandwichedRenyiQ_reindex_posSemidef
    rho.psd hSigma.posSemidef e alpha
  simp only [Matrix.reindex_apply] at hQ
  unfold sandwichedRenyiPSDReferenceHighAlphaFinite
  simp only [Matrix.reindex_apply]
  rw [← sandwichedRenyiQ_eq_psdTracePower_referenceInner
      (rho.reindex e) (hSigma.submatrix e.symm.injective).posSemidef alpha,
    ← sandwichedRenyiQ_eq_psdTracePower_referenceInner rho hSigma.posSemidef alpha]
  simp only [MState.reindex_matrix]
  rw [hQ]

/-- The support-aware high-order branch is invariant under finite basis
relabeling for a positive-definite reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rho : MState a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) (alpha : ℝ) :
    sandwichedRenyiPSDReferenceHighAlphaE (rho.reindex e)
        (Matrix.reindex e e sigma)
        (hSigma.submatrix e.symm.injective).posSemidef alpha =
      sandwichedRenyiPSDReferenceHighAlphaE rho sigma hSigma.posSemidef alpha := by
  let hSigmaRe : (Matrix.reindex e e sigma).PosDef :=
    hSigma.submatrix e.symm.injective
  let hSupportRe : Matrix.Supports (rho.reindex e).m
      (Matrix.reindex e e sigma) :=
    Matrix.Supports.of_right_posDef _ _ hSigmaRe
  let hSupport : Matrix.Supports rho.m sigma :=
    Matrix.Supports.of_right_posDef _ _ hSigma
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (rho.reindex e) hSigmaRe.posSemidef alpha hSupportRe,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho hSigma.posSemidef alpha hSupport]
  congr 1
  exact sandwichedRenyiPSDReferenceHighAlphaFinite_reindex_posDef
    rho hSigma e alpha

/-- The source-facing PSD-reference sandwiched Renyi divergence is invariant
under finite basis relabeling for every real order when the reference is
positive definite. -/
theorem sandwichedRenyiPSDReferenceE_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rho : MState a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) (alpha : ℝ) :
    sandwichedRenyiPSDReferenceE (rho.reindex e)
        (Matrix.reindex e e sigma)
        (hSigma.submatrix e.symm.injective).posSemidef alpha =
      sandwichedRenyiPSDReferenceE rho sigma hSigma.posSemidef alpha := by
  simp only [Matrix.reindex_apply]
  rcases lt_trichotomy alpha 1 with hlt | heq | hgt
  · rw [sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
        (rho.reindex e) (hSigma.submatrix e.symm.injective).posSemidef hlt,
      sandwichedRenyiPSDReferenceE_eq_lowAlphaE_of_lt_one
        rho hSigma.posSemidef hlt]
    simpa only [Matrix.reindex_apply] using
      sandwichedRenyiPSDReferenceLowAlphaE_reindex_posDef rho hSigma e alpha
  · rw [sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one
        (rho.reindex e) (hSigma.submatrix e.symm.injective).posSemidef heq,
      sandwichedRenyiPSDReferenceE_eq_traceLogE_of_eq_one
        rho hSigma.posSemidef heq]
    simpa only [Matrix.reindex_apply] using
      relativeEntropyPSDReferenceTraceLogE_reindex_posDef rho hSigma e
  · rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
        (rho.reindex e) (hSigma.submatrix e.symm.injective).posSemidef hgt,
      sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt
        rho hSigma.posSemidef hgt]
    simpa only [Matrix.reindex_apply] using
      sandwichedRenyiPSDReferenceHighAlphaE_reindex_posDef rho hSigma e alpha

/-- Reindexed form of the direct-sum mean property for coherent
image/complement decompositions whose ambient basis is merely equivalent to
the canonical sum basis. -/
theorem sandwichedRenyiPSDReferenceE_directSumZero_reindex
    {p : Type u} {q : Type v} {r : Type w}
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    [Fintype r] [DecidableEq r]
    (rho : MState p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    (e : (p ⊕ q) ≃ r) {alpha : ℝ} (hAlpha : 1 / 2 ≤ alpha) :
    sandwichedRenyiPSDReferenceE ((rho.directSumZero q).reindex e)
        (Matrix.reindex e e (Matrix.fromBlocks sigma 0 0 tau))
        ((Matrix.fromBlocks_diagonal_posDef hSigma hTau).submatrix
          e.symm.injective).posSemidef alpha =
      sandwichedRenyiPSDReferenceE rho sigma hSigma.posSemidef alpha := by
  calc
    sandwichedRenyiPSDReferenceE ((rho.directSumZero q).reindex e)
        (Matrix.reindex e e (Matrix.fromBlocks sigma 0 0 tau))
        ((Matrix.fromBlocks_diagonal_posDef hSigma hTau).submatrix
          e.symm.injective).posSemidef alpha =
      sandwichedRenyiPSDReferenceE (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha :=
          sandwichedRenyiPSDReferenceE_reindex_posDef
            (rho.directSumZero q) (Matrix.fromBlocks_diagonal_posDef hSigma hTau)
            e alpha
    _ = sandwichedRenyiPSDReferenceE rho sigma hSigma.posSemidef alpha :=
      sandwichedRenyiPSDReferenceE_directSumZero rho hSigma hTau hAlpha

end MState
