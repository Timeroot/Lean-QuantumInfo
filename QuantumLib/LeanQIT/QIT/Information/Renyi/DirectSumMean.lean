/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.AlphaEntropyContinuity
public import QIT.Information.Renyi.FrankLieb.DPI
public import QIT.Util.BlockMatrix

/-!
# Direct-sum mean property for sandwiched Renyi divergence

This file proves the unequal-dimensional direct-sum identities used in
Tomamichel (2015), Property (VI).  In particular, the zero block in the first
argument stays zero; the second reference block is not averaged into the
result.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

/-- Real continuous functional calculus preserves unequal-dimensional
positive-semidefinite diagonal blocks.  The proof explicitly joins the two
spectral decompositions into a block unitary. -/
theorem cMatrix_cfc_fromBlocks_diagonal
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    {A : CMatrix p} {D : CMatrix q} (hA : A.PosSemidef) (hD : D.PosSemidef)
    (f : Real -> Real) :
    cfc f (Matrix.fromBlocks A 0 0 D : CMatrix (Sum p q)) =
      Matrix.fromBlocks (cfc f A) 0 0 (cfc f D) := by
  let UA : Matrix.unitaryGroup p Complex := hA.isHermitian.eigenvectorUnitary
  let UD : Matrix.unitaryGroup q Complex := hD.isHermitian.eigenvectorUnitary
  let da : p -> Real := hA.isHermitian.eigenvalues
  let dd : q -> Real := hD.isHermitian.eigenvalues
  have hspecA :
      A = (UA : CMatrix p) * Matrix.diagonal (fun i => (da i : Complex)) *
        star (UA : CMatrix p) := by
    simpa [UA, da, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      hA.isHermitian.spectral_theorem
  have hspecD :
      D = (UD : CMatrix q) * Matrix.diagonal (fun i => (dd i : Complex)) *
        star (UD : CMatrix q) := by
    simpa [UD, dd, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      hD.isHermitian.spectral_theorem
  let U : Matrix.unitaryGroup (Sum p q) Complex :=
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
  let d : Sum p q -> Real := Sum.elim da dd
  have hdiag :
      (Matrix.fromBlocks
          (Matrix.diagonal (fun i => (da i : Complex))) 0 0
          (Matrix.diagonal (fun i => (dd i : Complex))) : CMatrix (Sum p q)) =
        Matrix.diagonal (fun i => (d i : Complex)) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.diagonal, d]
  have hspec :
      (Matrix.fromBlocks A 0 0 D : CMatrix (Sum p q)) =
        (U : CMatrix (Sum p q)) * Matrix.diagonal (fun i => (d i : Complex)) *
          star (U : CMatrix (Sum p q)) := by
    rw [hspecA, hspecD, <- hdiag]
    change Matrix.fromBlocks
        ((UA : CMatrix p) * Matrix.diagonal (fun i => (da i : Complex)) *
          star (UA : CMatrix p)) 0 0
        ((UD : CMatrix q) * Matrix.diagonal (fun i => (dd i : Complex)) *
          star (UD : CMatrix q)) =
      Matrix.fromBlocks (UA : CMatrix p) 0 0 (UD : CMatrix q) *
        Matrix.fromBlocks (Matrix.diagonal (fun i => (da i : Complex))) 0 0
          (Matrix.diagonal (fun i => (dd i : Complex))) *
        star (Matrix.fromBlocks (UA : CMatrix p) 0 0 (UD : CMatrix q))
    simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hcfcA :
      cfc f A =
        (UA : CMatrix p) * Matrix.diagonal (fun i => ((f (da i) : Real) : Complex)) *
          star (UA : CMatrix p) := by
    rw [hspecA]
    exact cfc_unitary_conj_diagonal_ofReal UA da f
  have hcfcD :
      cfc f D =
        (UD : CMatrix q) * Matrix.diagonal (fun i => ((f (dd i) : Real) : Complex)) *
          star (UD : CMatrix q) := by
    rw [hspecD]
    exact cfc_unitary_conj_diagonal_ofReal UD dd f
  have hdiagCfc :
      (Matrix.fromBlocks
          (Matrix.diagonal (fun i => ((f (da i) : Real) : Complex))) 0 0
          (Matrix.diagonal (fun i => ((f (dd i) : Real) : Complex))) :
            CMatrix (Sum p q)) =
        Matrix.diagonal (fun i => ((f (d i) : Real) : Complex)) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.diagonal, d]
  have hcfcSpec :
      (Matrix.fromBlocks (cfc f A) 0 0 (cfc f D) : CMatrix (Sum p q)) =
        (U : CMatrix (Sum p q)) *
          Matrix.diagonal (fun i => ((f (d i) : Real) : Complex)) *
          star (U : CMatrix (Sum p q)) := by
    rw [hcfcA, hcfcD, <- hdiagCfc]
    change Matrix.fromBlocks
        ((UA : CMatrix p) * Matrix.diagonal (fun i => ((f (da i) : Real) : Complex)) *
          star (UA : CMatrix p)) 0 0
        ((UD : CMatrix q) * Matrix.diagonal (fun i => ((f (dd i) : Real) : Complex)) *
          star (UD : CMatrix q)) =
      Matrix.fromBlocks (UA : CMatrix p) 0 0 (UD : CMatrix q) *
        Matrix.fromBlocks
          (Matrix.diagonal (fun i => ((f (da i) : Real) : Complex))) 0 0
          (Matrix.diagonal (fun i => ((f (dd i) : Real) : Complex))) *
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
    (s : Real) :
    CFC.rpow (Matrix.fromBlocks A 0 0 D : CMatrix (Sum p q)) s =
      Matrix.fromBlocks (CFC.rpow A s) 0 0 (CFC.rpow D s) := by
  change ((Matrix.fromBlocks A 0 0 D : CMatrix (Sum p q)) ^ s) =
    Matrix.fromBlocks (A ^ s) 0 0 (D ^ s)
  rw [CFC.rpow_eq_cfc_real (a := (Matrix.fromBlocks A 0 0 D : CMatrix (Sum p q)))
      (y := s) (Matrix.nonneg_iff_posSemidef.mpr
        (Matrix.fromBlocks_diagonal_posSemidef hA hD)),
    CFC.rpow_eq_cfc_real (a := A) (y := s) (Matrix.nonneg_iff_posSemidef.mpr hA),
    CFC.rpow_eq_cfc_real (a := D) (y := s) (Matrix.nonneg_iff_posSemidef.mpr hD)]
  exact cMatrix_cfc_fromBlocks_diagonal hA hD (fun x => x ^ s)

private theorem cMatrix_reindex_mem_unitary_directSumMean
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (e : a ≃ b) (U : Matrix.unitaryGroup a Complex) :
    Matrix.reindex e e (U : CMatrix a) ∈ Matrix.unitaryGroup b Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have hU := Matrix.mem_unitaryGroup_iff.mp U.2
  have happ := congrFun (congrFun hU (e.symm i)) (e.symm j)
  simp [Matrix.mul_apply, Matrix.star_apply] at happ ⊢
  have hsum :
      (∑ x : b, (U : CMatrix a) (e.symm i) (e.symm x) *
          starRingEnd Complex ((U : CMatrix a) (e.symm j) (e.symm x))) =
        ∑ y : a, (U : CMatrix a) (e.symm i) y *
          starRingEnd Complex ((U : CMatrix a) (e.symm j) y) := by
    exact Fintype.sum_equiv e.symm
      (fun x : b => (U : CMatrix a) (e.symm i) (e.symm x) *
        starRingEnd Complex ((U : CMatrix a) (e.symm j) (e.symm x)))
      (fun y : a => (U : CMatrix a) (e.symm i) y *
        starRingEnd Complex ((U : CMatrix a) (e.symm j) y))
      (by intro x; rfl)
  rw [hsum]
  simpa [Matrix.one_apply] using happ

private theorem cMatrix_cfc_reindex_posSemidef_directSumMean
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (e : a ≃ b) {A : CMatrix a} (hA : A.PosSemidef) (f : Real -> Real) :
    cfc f (Matrix.reindex e e A) = Matrix.reindex e e (cfc f A) := by
  let U : Matrix.unitaryGroup a Complex := hA.isHermitian.eigenvectorUnitary
  let Ue : Matrix.unitaryGroup b Complex :=
    ⟨Matrix.reindex e e (U : CMatrix a), cMatrix_reindex_mem_unitary_directSumMean e U⟩
  let d : a -> Real := hA.isHermitian.eigenvalues
  let de : b -> Real := fun i => d (e.symm i)
  have hA_spec :
      A = Unitary.conjStarAlgAut Complex _ U
        (Matrix.diagonal (fun i => (d i : Complex))) := by
    simpa [U, d, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hdiag :
      Matrix.reindex e e (Matrix.diagonal (fun i => (d i : Complex)) : CMatrix a) =
        Matrix.diagonal (fun i => (de i : Complex)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [de]
    · simp [Matrix.diagonal, hij]
  have hstarU :
      Matrix.reindex e e (star (U : CMatrix a)) =
        star (Matrix.reindex e e (U : CMatrix a)) := by
    ext i j
    simp [Matrix.star_apply]
  have hdiagAlg :
      (Matrix.reindexAlgEquiv Complex Complex e)
          (Matrix.diagonal (fun i => (d i : Complex)) : CMatrix a) =
        Matrix.diagonal (fun i => (de i : Complex)) := by
    simpa [Matrix.reindexAlgEquiv_apply] using hdiag
  have hstarUAlg :
      (Matrix.reindexAlgEquiv Complex Complex e) (star (U : CMatrix a)) =
        star ((Matrix.reindexAlgEquiv Complex Complex e) (U : CMatrix a)) := by
    simpa [Matrix.reindexAlgEquiv_apply] using hstarU
  have hre_spec :
      Matrix.reindex e e A =
        Unitary.conjStarAlgAut Complex _ Ue
          (Matrix.diagonal (fun i => (de i : Complex))) := by
    rw [hA_spec]
    change (Matrix.reindexAlgEquiv Complex Complex e)
        (((U : CMatrix a) * Matrix.diagonal (fun i => (d i : Complex))) *
          star (U : CMatrix a)) =
      ((Ue : CMatrix b) * Matrix.diagonal (fun i => (de i : Complex))) *
        star (Ue : CMatrix b)
    rw [Matrix.reindexAlgEquiv_mul, Matrix.reindexAlgEquiv_mul]
    rw [hdiagAlg, hstarUAlg]
    rfl
  have hA_cfc :
      cfc f A =
        Unitary.conjStarAlgAut Complex _ U
          (Matrix.diagonal (fun i => ((f (d i) : Real) : Complex))) := by
    rw [hA_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cfc_unitary_conj_diagonal_ofReal U d f
  have hre_cfc :
      cfc f (Matrix.reindex e e A) =
        Unitary.conjStarAlgAut Complex _ Ue
          (Matrix.diagonal (fun i => ((f (de i) : Real) : Complex))) := by
    rw [hre_spec]
    simpa [Unitary.conjStarAlgAut_apply] using
      cfc_unitary_conj_diagonal_ofReal Ue de f
  rw [hre_cfc, hA_cfc]
  have hdiag_f :
      Matrix.reindex e e
          (Matrix.diagonal (fun i => ((f (d i) : Real) : Complex)) : CMatrix a) =
        Matrix.diagonal (fun i => ((f (de i) : Real) : Complex)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [de]
    · simp [Matrix.diagonal, hij]
  change ((Ue : CMatrix b) *
        Matrix.diagonal (fun i => ((f (de i) : Real) : Complex))) *
        star (Ue : CMatrix b) =
      (Matrix.reindexAlgEquiv Complex Complex e)
        (((U : CMatrix a) *
          Matrix.diagonal (fun i => ((f (d i) : Real) : Complex))) *
          star (U : CMatrix a))
  rw [Matrix.reindexAlgEquiv_mul, Matrix.reindexAlgEquiv_mul]
  have hdiagFAlg :
      (Matrix.reindexAlgEquiv Complex Complex e)
          (Matrix.diagonal (fun i => ((f (d i) : Real) : Complex)) : CMatrix a) =
        Matrix.diagonal (fun i => ((f (de i) : Real) : Complex)) := by
    simpa [Matrix.reindexAlgEquiv_apply] using hdiag_f
  rw [hdiagFAlg, hstarUAlg]
  rfl

private theorem cMatrix_rpow_reindex_posSemidef_directSumMean
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (e : a ≃ b) {A : CMatrix a} (hA : A.PosSemidef) (s : Real) :
    CFC.rpow (Matrix.reindex e e A) s = Matrix.reindex e e (CFC.rpow A s) := by
  change (Matrix.reindex e e A) ^ s = Matrix.reindex e e (A ^ s)
  rw [CFC.rpow_eq_cfc_real (a := Matrix.reindex e e A) (y := s)
      (Matrix.nonneg_iff_posSemidef.mpr (hA.submatrix e.symm)),
    CFC.rpow_eq_cfc_real (a := A) (y := s) (Matrix.nonneg_iff_posSemidef.mpr hA)]
  exact cMatrix_cfc_reindex_posSemidef_directSumMean e hA (fun x => x ^ s)

namespace State

/-- Extend a normalized state by a zero lower-right block. -/
def directSumZero
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : State p) (q : Type v) [Fintype q] [DecidableEq q] : State (Sum p q) where
  matrix := Matrix.fromBlocks rho.matrix 0 0 0
  pos := Matrix.fromBlocks_diagonal_posSemidef rho.pos Matrix.PosSemidef.zero
  trace_eq_one := by
    rw [Matrix.trace_fromBlocks_diagonal, rho.trace_eq_one]
    simp

@[simp]
theorem directSumZero_matrix
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : State p) (q : Type v) [Fintype q] [DecidableEq q] :
    (rho.directSumZero q).matrix = Matrix.fromBlocks rho.matrix 0 0 0 :=
  rfl

/-- The zero extension is positive semidefinite. -/
theorem directSumZero_posSemidef
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : State p) (q : Type v) [Fintype q] [DecidableEq q] :
    (rho.directSumZero q).matrix.PosSemidef :=
  (rho.directSumZero q).pos

/-- The zero extension remains normalized. -/
@[simp]
theorem directSumZero_trace
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : State p) (q : Type v) [Fintype q] [DecidableEq q] :
    (rho.directSumZero q).matrix.trace = 1 :=
  (rho.directSumZero q).trace_eq_one

private def directSumInclusion
    (p : Type u) (q : Type v) [DecidableEq p] [DecidableEq q] :
    Matrix (Sum p q) p Complex :=
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
      (Matrix.fromBlocks M 0 0 0 : CMatrix (Sum p q)) := by
  ext i j
  cases i <;> cases j <;>
    simp [directSumInclusion, Matrix.mul_apply, Matrix.conjTranspose]

/-- Zero extension adds only zero eigenvalues and therefore preserves von
Neumann entropy. -/
@[simp]
theorem directSumZero_vonNeumann
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : State p) (q : Type v) [Fintype q] [DecidableEq q] :
    (rho.directSumZero q).vonNeumann = rho.vonNeumann := by
  exact vonNeumann_eq_of_matrix_eq_isometry_conj
    rho (rho.directSumZero q) (directSumInclusion p q)
    (directSumInclusion_isometry p q) (directSumInclusion_conj (q := q) rho.matrix).symm

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
  exact cMatrix_cfc_reindex_posSemidef_directSumMean
    e hSigma.posSemidef Real.log

/-- The sandwiched `Q` functional is invariant under a simultaneous finite
basis relabeling, including the negative sandwich exponent used above order
one. -/
theorem sandwichedRenyiQ_reindex_posSemidef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    {rho sigma : CMatrix a} (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef)
    (e : a ≃ b) (alpha : Real) :
    sandwichedRenyiQ (Matrix.reindex e e rho) (Matrix.reindex e e sigma)
        (hRho.submatrix e.symm) (hSigma.submatrix e.symm) alpha =
      sandwichedRenyiQ rho sigma hRho hSigma alpha := by
  let t : Real := (1 - alpha) / (2 * alpha)
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
    exact cMatrix_rpow_reindex_posSemidef_directSumMean e hSigma t
  have hSandwich :
      CFC.rpow (Matrix.reindex e e sigma) t * Matrix.reindex e e rho *
          CFC.rpow (Matrix.reindex e e sigma) t =
        Matrix.reindex e e inner := by
    rw [hPowSigma]
    change
      (Matrix.reindexAlgEquiv Complex Complex e) C *
          (Matrix.reindexAlgEquiv Complex Complex e) rho *
        (Matrix.reindexAlgEquiv Complex Complex e) C =
      (Matrix.reindexAlgEquiv Complex Complex e) inner
    rw [<- Matrix.reindexAlgEquiv_mul (R := Complex) (A := Complex) e C rho]
    rw [<- Matrix.reindexAlgEquiv_mul (R := Complex) (A := Complex) e
      (C * rho) C]
  have hPowInner :
      CFC.rpow (Matrix.reindex e e inner) alpha =
        Matrix.reindex e e (CFC.rpow inner alpha) :=
    cMatrix_rpow_reindex_posSemidef_directSumMean e hInner alpha
  unfold sandwichedRenyiQ
  change
    (CFC.rpow
      (CFC.rpow (Matrix.reindex e e sigma) t * Matrix.reindex e e rho *
        CFC.rpow (Matrix.reindex e e sigma) t) alpha).trace.re =
      (CFC.rpow inner alpha).trace.re
  rw [hSandwich, hPowInner]
  exact congrArg Complex.re
    (trace_submatrix_equiv e.symm (CFC.rpow inner alpha))

/-- On a positive-definite reference, the support-compressed trace-log branch
has its ambient-space formula without requiring the input state to be positive
definite. -/
theorem relativeEntropyPSDReferenceTraceLogFinite_eq_of_posDef
    {p : Type u} [Fintype p] [DecidableEq p]
    (rho : State p) {sigma : CMatrix p} (hSigma : sigma.PosDef)
    (hSupport : Matrix.Supports rho.matrix sigma) :
    relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma.posSemidef hSupport =
      -rho.vonNeumann -
        ((rho.matrix * psdLog sigma hSigma).trace.re / Real.log 2) := by
  have hEntropy :
      (_root_.QIT.psdSupportCompressedState rho hSigma.posSemidef hSupport).vonNeumann =
        rho.vonNeumann :=
    relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq
      rho hSigma.posSemidef hSupport
  have hTrace :
      ((psdSupportCompress sigma hSigma.posSemidef rho.matrix *
        psdLog (psdSupportCompress sigma hSigma.posSemidef sigma)
          (psdSupportCompress_self_posDef sigma hSigma.posSemidef)).trace).re =
        ((rho.matrix *
          cfc (fun x : Real => if x = 0 then 0 else Real.log x) sigma).trace).re :=
    relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
      rho hSigma.posSemidef hSupport
  have hLogZero :
      cfc (fun x : Real => if x = 0 then 0 else Real.log x) sigma =
        psdLog sigma hSigma :=
    relativeEntropyTraceLog_cfc_logZero_eq_psdLog_of_posDef sigma hSigma
  calc
    relativeEntropyPSDReferenceTraceLogFinite rho sigma hSigma.posSemidef hSupport =
        -(_root_.QIT.psdSupportCompressedState rho hSigma.posSemidef
          hSupport).vonNeumann -
          ((psdSupportCompress sigma hSigma.posSemidef rho.matrix *
            psdLog (psdSupportCompress sigma hSigma.posSemidef sigma)
              (psdSupportCompress_self_posDef sigma hSigma.posSemidef)).trace).re /
            Real.log 2 := by
          rfl
    _ = -rho.vonNeumann -
          ((rho.matrix *
            cfc (fun x : Real => if x = 0 then 0 else Real.log x) sigma).trace).re /
            Real.log 2 := by
          rw [hEntropy, hTrace]
    _ = -rho.vonNeumann -
          ((rho.matrix * psdLog sigma hSigma).trace).re / Real.log 2 := by
          rw [hLogZero]

/-- The support-aware trace-log branch at order one ignores a zero state
extension against an arbitrary positive-definite complementary reference. -/
theorem relativeEntropyPSDReferenceTraceLogE_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : State p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef) :
    relativeEntropyPSDReferenceTraceLogE (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma.posSemidef := by
  let hBlock : (Matrix.fromBlocks sigma 0 0 tau : CMatrix (Sum p q)).PosDef :=
    Matrix.fromBlocks_diagonal_posDef hSigma hTau
  let hSupportBlock : Matrix.Supports (rho.directSumZero q).matrix
      (Matrix.fromBlocks sigma 0 0 tau) :=
    Matrix.Supports.of_right_posDef _ _ hBlock
  let hSupport : Matrix.Supports rho.matrix sigma :=
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
    (((Matrix.reindexAlgEquiv Complex Complex e) rho *
      (Matrix.reindexAlgEquiv Complex Complex e) (psdLog sigma hSigma)).trace).re = _
  rw [<- Matrix.reindexAlgEquiv_mul (R := Complex) (A := Complex) e
    rho (psdLog sigma hSigma)]
  exact congrArg Complex.re
    (trace_submatrix_equiv e.symm (rho * psdLog sigma hSigma))

/-- The support-aware trace-log branch is invariant under a finite basis
relabeling when the reference is positive definite.  The input state need not
be positive definite. -/
theorem relativeEntropyPSDReferenceTraceLogE_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) :
    relativeEntropyPSDReferenceTraceLogE (rho.reindex e)
        (Matrix.reindex e e sigma)
        (hSigma.submatrix e.symm.injective).posSemidef =
      relativeEntropyPSDReferenceTraceLogE rho sigma hSigma.posSemidef := by
  let hSigmaRe : (Matrix.reindex e e sigma).PosDef :=
    hSigma.submatrix e.symm.injective
  let hSupportRe : Matrix.Supports (rho.reindex e).matrix
      (Matrix.reindex e e sigma) :=
    Matrix.Supports.of_right_posDef _ _ hSigmaRe
  let hSupport : Matrix.Supports rho.matrix sigma :=
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
  exact trace_mul_psdLog_reindex_posDef rho.matrix hSigma e

/-- The sandwiched `Q` functional splits over unequal-dimensional diagonal
blocks. -/
theorem sandwichedRenyiQ_fromBlocks_diagonal
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    {rhoP sigmaP : CMatrix p} {rhoQ sigmaQ : CMatrix q}
    (hRhoP : rhoP.PosSemidef) (hRhoQ : rhoQ.PosSemidef)
    (hSigmaP : sigmaP.PosSemidef) (hSigmaQ : sigmaQ.PosSemidef)
    (alpha : Real) :
    sandwichedRenyiQ
        (Matrix.fromBlocks rhoP 0 0 rhoQ)
        (Matrix.fromBlocks sigmaP 0 0 sigmaQ)
        (Matrix.fromBlocks_diagonal_posSemidef hRhoP hRhoQ)
        (Matrix.fromBlocks_diagonal_posSemidef hSigmaP hSigmaQ) alpha =
      sandwichedRenyiQ rhoP sigmaP hRhoP hSigmaP alpha +
        sandwichedRenyiQ rhoQ sigmaQ hRhoQ hSigmaQ alpha := by
  let t : Real := (1 - alpha) / (2 * alpha)
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
      CFC.rpow (Matrix.fromBlocks sigmaP 0 0 sigmaQ : CMatrix (Sum p q)) t *
          Matrix.fromBlocks rhoP 0 0 rhoQ *
        CFC.rpow (Matrix.fromBlocks sigmaP 0 0 sigmaQ : CMatrix (Sum p q)) t =
      Matrix.fromBlocks (CP * rhoP * CP) 0 0 (CQ * rhoQ * CQ) := by
    rw [cMatrix_rpow_fromBlocks_diagonal hSigmaP hSigmaQ t]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [CP, CQ]
  unfold sandwichedRenyiQ
  change
    (CFC.rpow
      (CFC.rpow (Matrix.fromBlocks sigmaP 0 0 sigmaQ : CMatrix (Sum p q)) t *
          Matrix.fromBlocks rhoP 0 0 rhoQ *
        CFC.rpow (Matrix.fromBlocks sigmaP 0 0 sigmaQ : CMatrix (Sum p q)) t)
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
    (rho : State p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosSemidef) (hTau : tau.PosSemidef)
    {alpha : Real} (hAlpha : 0 < alpha) :
    sandwichedRenyiQ (rho.directSumZero q).matrix
        (Matrix.fromBlocks sigma 0 0 tau)
        (rho.directSumZero q).pos
        (Matrix.fromBlocks_diagonal_posSemidef hSigma hTau) alpha =
      sandwichedRenyiQ rho.matrix sigma rho.pos hSigma alpha := by
  change
    sandwichedRenyiQ (Matrix.fromBlocks rho.matrix 0 0 (0 : CMatrix q))
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posSemidef rho.pos Matrix.PosSemidef.zero)
        (Matrix.fromBlocks_diagonal_posSemidef hSigma hTau) alpha = _
  rw [sandwichedRenyiQ_fromBlocks_diagonal rho.pos Matrix.PosSemidef.zero
    hSigma hTau alpha]
  rw [sandwichedRenyiQ_zero_left tau hTau hAlpha, add_zero]

/-- The extended-real low-order branch ignores a zero state extension against
a positive-definite complementary reference. -/
theorem sandwichedRenyiPSDReferenceLowAlphaE_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : State p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    {alpha : Real} (hAlpha : 0 < alpha) :
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
    (rho : State p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    {alpha : Real} (hAlpha : 0 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma.posSemidef alpha := by
  unfold sandwichedRenyiPSDReferenceHighAlphaFinite
  rw [<- sandwichedRenyiQ_eq_psdTracePower_referenceInner
      (rho.directSumZero q)
      (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha,
    <- sandwichedRenyiQ_eq_psdTracePower_referenceInner rho hSigma.posSemidef alpha,
    sandwichedRenyiQ_directSumZero rho hSigma.posSemidef hTau.posSemidef hAlpha]

/-- The support-aware high-order branch ignores a zero state extension against
a positive-definite complementary reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : State p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    {alpha : Real} (hAlpha : 0 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaE (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha =
      sandwichedRenyiPSDReferenceHighAlphaE rho sigma hSigma.posSemidef alpha := by
  let hBlock : (Matrix.fromBlocks sigma 0 0 tau : CMatrix (Sum p q)).PosDef :=
    Matrix.fromBlocks_diagonal_posDef hSigma hTau
  let hSupportBlock : Matrix.Supports (rho.directSumZero q).matrix
      (Matrix.fromBlocks sigma 0 0 tau) :=
    Matrix.Supports.of_right_posDef _ _ hBlock
  let hSupport : Matrix.Supports rho.matrix sigma :=
    Matrix.Supports.of_right_posDef _ _ hSigma
  rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (rho.directSumZero q) hBlock.posSemidef alpha hSupportBlock,
    sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho hSigma.posSemidef alpha hSupport]
  congr 1
  exact sandwichedRenyiPSDReferenceHighAlphaFinite_directSumZero
    rho hSigma hTau hAlpha

/-- Tomamichel's direct-sum mean property for a normalized zero extension.

For every finite order `alpha >= 1 / 2`, including the support-aware
trace-log branch at `alpha = 1`, the nonzero complementary reference block is
ignored because the corresponding state block is zero.  No positive-
definiteness assumption is made on `rho`. -/
theorem sandwichedRenyiPSDReferenceE_directSumZero
    {p : Type u} {q : Type v} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q]
    (rho : State p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    {alpha : Real} (hAlpha : 1 / 2 <= alpha) :
    sandwichedRenyiPSDReferenceE (rho.directSumZero q)
        (Matrix.fromBlocks sigma 0 0 tau)
        (Matrix.fromBlocks_diagonal_posDef hSigma hTau).posSemidef alpha =
      sandwichedRenyiPSDReferenceE rho sigma hSigma.posSemidef alpha := by
  have hAlphaPos : 0 < alpha := by
    have : (0 : Real) < 1 / 2 := by norm_num
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
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) (alpha : Real) :
    sandwichedRenyiPSDReferenceLowAlphaE (rho.reindex e)
        (Matrix.reindex e e sigma)
        (hSigma.submatrix e.symm.injective).posSemidef alpha =
      sandwichedRenyiPSDReferenceLowAlphaE rho sigma hSigma.posSemidef alpha := by
  have hQ := sandwichedRenyiQ_reindex_posSemidef
    rho.pos hSigma.posSemidef e alpha
  simp only [Matrix.reindex_apply] at hQ
  unfold sandwichedRenyiPSDReferenceLowAlphaE sandwichedRenyiPSDReferenceLowAlpha
  simp only [State.reindex_matrix, Matrix.reindex_apply]
  rw [hQ]

/-- The finite high-order branch is invariant under finite basis relabeling
for a positive-definite reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) (alpha : Real) :
    sandwichedRenyiPSDReferenceHighAlphaFinite (rho.reindex e)
        (Matrix.reindex e e sigma)
        (hSigma.submatrix e.symm.injective).posSemidef alpha =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hSigma.posSemidef alpha := by
  have hQ := sandwichedRenyiQ_reindex_posSemidef
    rho.pos hSigma.posSemidef e alpha
  simp only [Matrix.reindex_apply] at hQ
  unfold sandwichedRenyiPSDReferenceHighAlphaFinite
  simp only [Matrix.reindex_apply]
  rw [<- sandwichedRenyiQ_eq_psdTracePower_referenceInner
      (rho.reindex e) (hSigma.submatrix e.symm.injective).posSemidef alpha,
    <- sandwichedRenyiQ_eq_psdTracePower_referenceInner rho hSigma.posSemidef alpha]
  simp only [State.reindex_matrix]
  rw [hQ]

/-- The support-aware high-order branch is invariant under finite basis
relabeling for a positive-definite reference. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_reindex_posDef
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) (alpha : Real) :
    sandwichedRenyiPSDReferenceHighAlphaE (rho.reindex e)
        (Matrix.reindex e e sigma)
        (hSigma.submatrix e.symm.injective).posSemidef alpha =
      sandwichedRenyiPSDReferenceHighAlphaE rho sigma hSigma.posSemidef alpha := by
  let hSigmaRe : (Matrix.reindex e e sigma).PosDef :=
    hSigma.submatrix e.symm.injective
  let hSupportRe : Matrix.Supports (rho.reindex e).matrix
      (Matrix.reindex e e sigma) :=
    Matrix.Supports.of_right_posDef _ _ hSigmaRe
  let hSupport : Matrix.Supports rho.matrix sigma :=
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
    (rho : State a) {sigma : CMatrix a} (hSigma : sigma.PosDef)
    (e : a ≃ b) (alpha : Real) :
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
    (rho : State p) {sigma : CMatrix p} {tau : CMatrix q}
    (hSigma : sigma.PosDef) (hTau : tau.PosDef)
    (e : Sum p q ≃ r) {alpha : Real} (hAlpha : 1 / 2 <= alpha) :
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

end State

end


end QIT
