/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothEndpoint.Normalized
public import QIT.Protocols.LOCC.InstrumentEntanglement

/-!
# Conditional min-entropy under refined finite instruments

This module supplies the matrix-order core of the local-instrument monotonicity
argument in [Berta2009SingleShotStateMerging,
diploma_thesis_berta_08_v1.tex:729-798].
The classical record used below contains both the instrument outcome and the
chosen Kraus index.  Retaining that refined record is essential: the proof sums
the complete family of Kraus Gram matrices before returning to the input.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x

noncomputable section

namespace Matrix

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Rectangular Gram matrices have the same unit Loewner bound on their two
sides.  This is the Schur-complement form of the equal-nonzero-spectrum step
used for the two marginals of a pure vector in Berta's proof. -/
theorem conjTranspose_mul_self_le_one_iff_self_mul_conjTranspose_le_one
    (A : Matrix m n Complex) :
    Matrix.conjTranspose A * A <= (1 : CMatrix n) <->
      A * Matrix.conjTranspose A <= (1 : CMatrix m) := by
  constructor
  · intro h
    have hblock :
        (Matrix.fromBlocks (1 : CMatrix m) A
          (Matrix.conjTranspose A) (1 : CMatrix n) :
            CMatrix (Sum m n)).PosSemidef := by
      letI : Invertible (1 : CMatrix m) := invertibleOne
      apply (Matrix.PosDef.fromBlocks₁₁
        A (1 : CMatrix n) Matrix.PosDef.one).2
      simpa [Matrix.le_iff] using h
    letI : Invertible (1 : CMatrix n) := invertibleOne
    have hschur := (Matrix.PosDef.fromBlocks₂₂
      (1 : CMatrix m) A Matrix.PosDef.one).1 hblock
    simpa [Matrix.le_iff] using hschur
  · intro h
    have hblock :
        (Matrix.fromBlocks (1 : CMatrix m) A
          (Matrix.conjTranspose A) (1 : CMatrix n) :
            CMatrix (Sum m n)).PosSemidef := by
      letI : Invertible (1 : CMatrix n) := invertibleOne
      apply (Matrix.PosDef.fromBlocks₂₂
        (1 : CMatrix m) A Matrix.PosDef.one).2
      simpa [Matrix.le_iff] using h
    letI : Invertible (1 : CMatrix m) := invertibleOne
    have hschur := (Matrix.PosDef.fromBlocks₁₁
      A (1 : CMatrix n) Matrix.PosDef.one).1 hblock
    simpa [Matrix.le_iff] using hschur

/-- Positive scalar version of
`conjTranspose_mul_self_le_one_iff_self_mul_conjTranspose_le_one`.

For a rectangular amplitude matrix, a Loewner bound by `c I` can therefore be
transported between the two complementary Gram matrices. -/
theorem conjTranspose_mul_self_le_smul_one_iff_self_mul_conjTranspose_le_smul_one
    (A : Matrix m n Complex) {c : Real} (hc : 0 < c) :
    Matrix.conjTranspose A * A <= (c : Complex) • (1 : CMatrix n) <->
      A * Matrix.conjTranspose A <= (c : Complex) • (1 : CMatrix m) := by
  let Cn : CMatrix n := (c : Complex) • (1 : CMatrix n)
  let Cm : CMatrix m := (c : Complex) • (1 : CMatrix m)
  have hcComplex : (0 : Complex) < (c : Complex) := by
    exact_mod_cast hc
  have hCn : Cn.PosDef := by
    simpa [Cn] using Matrix.PosDef.smul (Matrix.PosDef.one :
      (1 : CMatrix n).PosDef) hcComplex
  have hCm : Cm.PosDef := by
    simpa [Cm] using Matrix.PosDef.smul (Matrix.PosDef.one :
      (1 : CMatrix m).PosDef) hcComplex
  have hcne : (c : Complex) ≠ 0 := ne_of_gt hcComplex
  letI : Invertible (c : Complex) := invertibleOfNonzero hcne
  have hCnInv : Cn⁻¹ = ((c : Complex)⁻¹) • (1 : CMatrix n) := by
    have hdet : IsUnit (1 : CMatrix n).det := by simp
    simpa [Cn, invOf_eq_inv] using
      (Matrix.inv_smul (1 : CMatrix n) (c : Complex) hdet)
  have hCmInv : Cm⁻¹ = ((c : Complex)⁻¹) • (1 : CMatrix m) := by
    have hdet : IsUnit (1 : CMatrix m).det := by simp
    simpa [Cm, invOf_eq_inv] using
      (Matrix.inv_smul (1 : CMatrix m) (c : Complex) hdet)
  constructor
  · intro h
    have hblock :
        (Matrix.fromBlocks (1 : CMatrix m) A (Matrix.conjTranspose A) Cn :
          CMatrix (Sum m n)).PosSemidef := by
      letI : Invertible (1 : CMatrix m) := invertibleOne
      apply (Matrix.PosDef.fromBlocks₁₁ A Cn Matrix.PosDef.one).2
      simpa [Cn, Matrix.le_iff] using h
    letI : Invertible Cn := hCn.isUnit.invertible
    have hschur :=
      (Matrix.PosDef.fromBlocks₂₂ (1 : CMatrix m) A hCn).1 hblock
    have hscaled := hschur.smul (le_of_lt hcComplex)
    rw [hCnInv] at hscaled
    rw [Matrix.le_iff]
    simpa [Matrix.mul_smul, Matrix.smul_mul, smul_sub,
      smul_smul, hcne] using hscaled
  · intro h
    have hblock :
        (Matrix.fromBlocks Cm A (Matrix.conjTranspose A) (1 : CMatrix n) :
          CMatrix (Sum m n)).PosSemidef := by
      letI : Invertible (1 : CMatrix n) := invertibleOne
      apply (Matrix.PosDef.fromBlocks₂₂ Cm A Matrix.PosDef.one).2
      simpa [Cm, Matrix.le_iff] using h
    letI : Invertible Cm := hCm.isUnit.invertible
    have hschur :=
      (Matrix.PosDef.fromBlocks₁₁ A (1 : CMatrix n) hCm).1 hblock
    have hscaled := hschur.smul (le_of_lt hcComplex)
    rw [hCmInv] at hscaled
    rw [Matrix.le_iff]
    simpa [Matrix.mul_smul, Matrix.smul_mul, smul_sub,
      smul_smul, hcne] using hscaled

/-- Schur transport through a positive-definite left reference.

This is the fixed-reference form of Berta's equal-nonzero-spectrum step: the
bound on the target Gram matrix is equivalent to the corresponding bound on
the complementary Gram matrix after inserting the inverse reference. -/
theorem conjTranspose_mul_inv_mul_self_le_smul_one_iff_self_mul_conjTranspose_le_smul
    (A : Matrix m n Complex) (Q : CMatrix m) (hQ : Q.PosDef)
    {c : Real} (hc : 0 < c) :
    Matrix.conjTranspose A * Q⁻¹ * A <=
        (c : Complex) • (1 : CMatrix n) <->
      A * Matrix.conjTranspose A <= (c : Complex) • Q := by
  let Cn : CMatrix n := (c : Complex) • (1 : CMatrix n)
  have hcComplex : (0 : Complex) < (c : Complex) := by
    exact_mod_cast hc
  have hCn : Cn.PosDef := by
    simpa [Cn] using Matrix.PosDef.smul (Matrix.PosDef.one :
      (1 : CMatrix n).PosDef) hcComplex
  have hcne : (c : Complex) ≠ 0 := ne_of_gt hcComplex
  letI : Invertible (c : Complex) := invertibleOfNonzero hcne
  have hCnInv : Cn⁻¹ = ((c : Complex)⁻¹ • (1 : CMatrix n)) := by
    have hdet : IsUnit (1 : CMatrix n).det := by simp
    simpa [Cn, invOf_eq_inv] using
      (Matrix.inv_smul (1 : CMatrix n) (c : Complex) hdet)
  constructor
  · intro h
    have hblock :
        (Matrix.fromBlocks Q A (Matrix.conjTranspose A) Cn :
          CMatrix (Sum m n)).PosSemidef := by
      letI : Invertible Q := hQ.isUnit.invertible
      apply (Matrix.PosDef.fromBlocks₁₁ A Cn hQ).2
      simpa [Cn, Matrix.le_iff] using h
    letI : Invertible Cn := hCn.isUnit.invertible
    have hschur := (Matrix.PosDef.fromBlocks₂₂ Q A hCn).1 hblock
    have hscaled := hschur.smul (le_of_lt hcComplex)
    rw [hCnInv] at hscaled
    rw [Matrix.le_iff]
    simpa [Matrix.mul_smul, Matrix.smul_mul, smul_sub,
      smul_smul, hcne] using hscaled
  · intro h
    have hdiff :
        ((c : Complex) • Q - A * Matrix.conjTranspose A).PosSemidef := by
      simpa [Matrix.le_iff] using h
    have hcInv : (0 : Complex) <= (c : Complex)⁻¹ :=
      le_of_lt (inv_pos.mpr hcComplex)
    have hschur :
        (Q - A * Cn⁻¹ * Matrix.conjTranspose A).PosSemidef := by
      have hscaled := hdiff.smul hcInv
      have hcancel :
          (c : Complex)⁻¹ • ((c : Complex) • Q) = Q := by
        rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
      rw [smul_sub, hcancel] at hscaled
      rw [hCnInv]
      simpa [Matrix.mul_smul, Matrix.smul_mul] using hscaled
    have hblock :
        (Matrix.fromBlocks Q A (Matrix.conjTranspose A) Cn :
          CMatrix (Sum m n)).PosSemidef := by
      letI : Invertible Cn := hCn.isUnit.invertible
      exact (Matrix.PosDef.fromBlocks₂₂ Q A hCn).2 hschur
    letI : Invertible Q := hQ.isUnit.invertible
    have htop := (Matrix.PosDef.fromBlocks₁₁ A Cn hQ).1 hblock
    simpa [Cn, Matrix.le_iff] using htop

/-- The positive-semidefinite cone is closed under removal of an arbitrarily
small positive scalar regularization. -/
theorem posSemidef_of_add_pos_smul_one_posSemidef
    (A : CMatrix m) (hA : A.IsHermitian)
    (hreg : ∀ epsilon : Real, 0 < epsilon ->
      (A + (epsilon : Complex) • (1 : CMatrix m)).PosSemidef) :
    A.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA ?_
  intro z
  let q : Complex := star z ⬝ᵥ Matrix.mulVec A z
  let r : Complex := star z ⬝ᵥ z
  have hr : 0 <= r := by
    dsimp [r]
    exact dotProduct_star_self_nonneg z
  have hquad (epsilon : Real) (hepsilon : 0 < epsilon) :
      0 <= q + (epsilon : Complex) * r := by
    have h := (hreg epsilon hepsilon).dotProduct_mulVec_nonneg z
    simpa [q, r, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_add, dotProduct_smul] using h
  rw [Complex.nonneg_iff]
  constructor
  · by_contra hqnonneg
    have hqneg : q.re < 0 := lt_of_not_ge hqnonneg
    have hrre : 0 <= r.re := (Complex.nonneg_iff.mp hr).1
    let delta : Real := (-q.re) / (2 * (r.re + 1))
    have hdenpos : 0 < 2 * (r.re + 1) := by nlinarith
    have hdeltapos : 0 < delta := by
      exact div_pos (neg_pos.mpr hqneg) hdenpos
    have hdeltaEq : delta * (2 * (r.re + 1)) = -q.re := by
      dsimp [delta]
      field_simp
    have hdeltar_lt : delta * r.re < -q.re := by
      nlinarith
    have hdelta := (Complex.nonneg_iff.mp (hquad delta hdeltapos)).1
    have hdeltaRe : 0 <= q.re + delta * r.re := by
      simpa [Complex.add_re, Complex.mul_re] using hdelta
    linarith
  · have hOne := (Complex.nonneg_iff.mp (hquad 1 zero_lt_one)).2
    have hrim := (Complex.nonneg_iff.mp hr).2
    simp only [Complex.add_im, Complex.mul_im] at hOne
    norm_num at hOne
    linarith
end Matrix

/-- Regroup `A (R E)` as `(A R) E`, so that tracing out `E` leaves the
source and untouched reference registers used by the Berta bound. -/
def sourceReferenceRegroupEquiv
    (A : Type u) (R : Type v) (E : Type w) :
    Prod A (Prod R E) ≃ Prod (Prod A R) E where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun x := (x.1.1, (x.1.2, x.2))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

namespace FiniteInstrument

variable {A : Type u} {A' : Type v} {R : Type w} {E : Type x} {X : Type*}
variable [Fintype A] [DecidableEq A]
variable [Fintype A'] [DecidableEq A']
variable [Fintype R] [DecidableEq R]
variable [Fintype E] [DecidableEq E]
variable [Fintype X]

/-- The `AR` state before Alice's instrument, obtained from a chosen pure
extension `psi : A (R E)`. -/
def sourceReferenceState (psi : PureVector (Prod A (Prod R E))) :
    State (Prod A R) :=
  (psi.state.reindex (sourceReferenceRegroupEquiv A R E)).marginalA

/-- The normalized `A'R` state on a positive refined Alice branch.  The
purifying register `E` is discarded, while the complete Alice outcome/Kraus
index remains available as the branch index. -/
def positiveBranchSourceReferenceState
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (i : M.positiveSupport psi) : State (Prod A' R) :=
  ((M.normalizedBranch psi i).state.reindex
    (sourceReferenceRegroupEquiv A' R E)).marginalA

/-- Target-by-purifier amplitude matrix for the pre-instrument `AR` state. -/
def sourceReferenceAmplitude (psi : PureVector (Prod A (Prod R E))) :
    Matrix (Prod A R) E Complex :=
  fun ar e => psi.amp (ar.1, (ar.2, e))

/-- Target-by-purifier amplitude matrix of one unnormalized refined Alice
branch. -/
def branchSourceReferenceAmplitude
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (i : M.refinedBranchIndex) : Matrix (Prod A' R) E Complex :=
  fun ar e => M.postAmplitude psi i (ar.1, (ar.2, e))

@[simp]
theorem sourceReferenceState_matrix
    (psi : PureVector (Prod A (Prod R E))) :
    (sourceReferenceState psi).matrix =
      sourceReferenceAmplitude psi *
        Matrix.conjTranspose (sourceReferenceAmplitude psi) := by
  classical
  ext x y
  simp [sourceReferenceState, sourceReferenceAmplitude,
    sourceReferenceRegroupEquiv, State.marginalA, State.reindex,
    partialTraceB, PureVector.state, rankOneMatrix_apply, Matrix.mul_apply]

theorem branchWeight_smul_positiveBranchSourceReferenceState_matrix
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (i : M.positiveSupport psi) :
    M.branchWeight psi i.1 •
        (M.positiveBranchSourceReferenceState psi i).matrix =
      M.branchSourceReferenceAmplitude psi i.1 *
        Matrix.conjTranspose (M.branchSourceReferenceAmplitude psi i.1) := by
  classical
  have hfull := M.branchWeight_smul_normalizedBranch_state_matrix psi i
  ext x y
  simp only [positiveBranchSourceReferenceState, State.marginalA,
    State.reindex, sourceReferenceRegroupEquiv, partialTraceB,
    Matrix.submatrix_apply, Matrix.smul_apply]
  rw [Finset.smul_sum]
  simp only [Matrix.mul_apply, branchSourceReferenceAmplitude,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro e _
  have hentry := congrFun (congrFun hfull (x.1, (x.2, e)))
    (y.1, (y.2, e))
  simpa only [Matrix.smul_apply, rankOneMatrix_apply] using hentry

/-- A refined branch acts only on Alice's register; the reference and
purifying registers are untouched. -/
theorem branchSourceReferenceAmplitude_eq_kronecker_mul
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (i : M.refinedBranchIndex) :
    M.branchSourceReferenceAmplitude psi i =
      Matrix.kronecker (M.refinedKraus i) (1 : CMatrix R) *
        sourceReferenceAmplitude psi := by
  classical
  ext ar e
  simp [branchSourceReferenceAmplitude, sourceReferenceAmplitude,
    FiniteInstrument.postAmplitude, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  simp [Matrix.one_apply, eq_comm]

/-- The complete refined Alice Kraus family satisfies the usual isometry
normalization. -/
theorem sum_conjTranspose_refinedKraus_mul_refinedKraus
    (M : FiniteInstrument A A' X) :
    (∑ i : M.refinedBranchIndex,
        Matrix.conjTranspose (M.refinedKraus i) * M.refinedKraus i) =
      (1 : CMatrix A) := by
  classical
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus M.refinedKraus) := by
    rw [M.ofKraus_refinedKraus_eq_total]
    exact M.total.tracePreserving
  simpa [MatrixMap.krausAdjoint] using
    (MatrixMap.krausAdjoint_one_of_tracePreserving M.refinedKraus hTP)

/-- The complete refined Alice Kraus family also gives a feasible endpoint
conditional-min dual effect.  This packages the same Kraus-stack contraction
used by the Gram proof through the repository's existing SDP API. -/
theorem refinedKraus_conditionalMinEntropyDualEffectFeasible
    (M : FiniteInstrument A A' X) :
    State.ConditionalMinEntropyDualEffectFeasible (a := A')
      (State.conditionalMinEntropyDualEffectOfKraus
        (a := A') (b := A) M.refinedKraus) := by
  apply State.conditionalMinEntropyDualEffectOfKraus_feasible
  rw [MatrixMap.smoothEndpointKrausStack_conjTranspose_mul]
  have hcomplete := M.sum_conjTranspose_refinedKraus_mul_refinedKraus
  simpa [MatrixMap.krausAdjoint, Matrix.mul_one] using hcomplete.le

/-- Summing complementary Gram matrices after the complete refined Alice
instrument recovers the input complementary Gram matrix.  The matrix `S`
acts only on the untouched reference register. -/
theorem sum_branchSourceReferenceAmplitude_referenceSandwich
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (S : CMatrix R) :
    (∑ i : M.refinedBranchIndex,
        Matrix.conjTranspose (M.branchSourceReferenceAmplitude psi i) *
          Matrix.kronecker (1 : CMatrix A') S *
          M.branchSourceReferenceAmplitude psi i) =
      Matrix.conjTranspose (sourceReferenceAmplitude psi) *
        Matrix.kronecker (1 : CMatrix A) S *
        sourceReferenceAmplitude psi := by
  classical
  have hbranch (i : M.refinedBranchIndex) :
      Matrix.conjTranspose (M.branchSourceReferenceAmplitude psi i) *
          Matrix.kronecker (1 : CMatrix A') S *
          M.branchSourceReferenceAmplitude psi i =
        Matrix.conjTranspose (sourceReferenceAmplitude psi) *
          Matrix.kronecker
            (Matrix.conjTranspose (M.refinedKraus i) * M.refinedKraus i) S *
          sourceReferenceAmplitude psi := by
    have hct :
        Matrix.conjTranspose
            (Matrix.kronecker (M.refinedKraus i) (1 : CMatrix R)) =
          Matrix.kronecker (Matrix.conjTranspose (M.refinedKraus i))
            (1 : CMatrix R) := by
      simpa [Matrix.kronecker] using
        (Matrix.conjTranspose_kronecker
          (M.refinedKraus i) (1 : CMatrix R))
    have hleft :
        Matrix.kronecker (Matrix.conjTranspose (M.refinedKraus i))
            (1 : CMatrix R) * Matrix.kronecker (1 : CMatrix A') S =
          Matrix.kronecker (Matrix.conjTranspose (M.refinedKraus i)) S := by
      simpa [Matrix.kronecker] using
        (Matrix.mul_kronecker_mul (Matrix.conjTranspose (M.refinedKraus i))
          (1 : CMatrix A') (1 : CMatrix R) S).symm
    have hright :
        Matrix.kronecker (Matrix.conjTranspose (M.refinedKraus i)) S *
            Matrix.kronecker (M.refinedKraus i) (1 : CMatrix R) =
          Matrix.kronecker
            (Matrix.conjTranspose (M.refinedKraus i) * M.refinedKraus i) S := by
      simpa [Matrix.kronecker] using
        (Matrix.mul_kronecker_mul (Matrix.conjTranspose (M.refinedKraus i))
          (M.refinedKraus i) S (1 : CMatrix R)).symm
    rw [M.branchSourceReferenceAmplitude_eq_kronecker_mul psi i,
      Matrix.conjTranspose_mul, hct]
    calc
      Matrix.conjTranspose (sourceReferenceAmplitude psi) *
            Matrix.kronecker (Matrix.conjTranspose (M.refinedKraus i))
              (1 : CMatrix R) * Matrix.kronecker (1 : CMatrix A') S *
            (Matrix.kronecker (M.refinedKraus i) (1 : CMatrix R) *
              sourceReferenceAmplitude psi) =
          Matrix.conjTranspose (sourceReferenceAmplitude psi) *
            ((Matrix.kronecker (Matrix.conjTranspose (M.refinedKraus i))
                (1 : CMatrix R) * Matrix.kronecker (1 : CMatrix A') S) *
              Matrix.kronecker (M.refinedKraus i) (1 : CMatrix R)) *
            sourceReferenceAmplitude psi := by simp only [Matrix.mul_assoc]
      _ = Matrix.conjTranspose (sourceReferenceAmplitude psi) *
          Matrix.kronecker
            (Matrix.conjTranspose (M.refinedKraus i) * M.refinedKraus i) S *
          sourceReferenceAmplitude psi := by rw [hleft, hright]
  calc
    (∑ i : M.refinedBranchIndex,
        Matrix.conjTranspose (M.branchSourceReferenceAmplitude psi i) *
          Matrix.kronecker (1 : CMatrix A') S *
          M.branchSourceReferenceAmplitude psi i) =
        ∑ i : M.refinedBranchIndex,
          Matrix.conjTranspose (sourceReferenceAmplitude psi) *
            Matrix.kronecker
              (Matrix.conjTranspose (M.refinedKraus i) * M.refinedKraus i) S *
            sourceReferenceAmplitude psi := by
      apply Finset.sum_congr rfl
      intro i _
      exact hbranch i
    _ = Matrix.conjTranspose (sourceReferenceAmplitude psi) *
        (∑ i : M.refinedBranchIndex,
          Matrix.kronecker
            (Matrix.conjTranspose (M.refinedKraus i) * M.refinedKraus i) S) *
        sourceReferenceAmplitude psi := by
      symm
      ext e e'
      simp only [Matrix.mul_apply, Matrix.sum_apply]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      conv_lhs =>
        enter [2, j]
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = Matrix.conjTranspose (sourceReferenceAmplitude psi) *
        Matrix.kronecker
          (∑ i : M.refinedBranchIndex,
            Matrix.conjTranspose (M.refinedKraus i) * M.refinedKraus i) S *
        sourceReferenceAmplitude psi := by
      congr 2
      ext ar ar'
      simp only [Matrix.sum_apply, Matrix.kronecker,
        Matrix.kroneckerMap_apply]
      rw [Finset.sum_mul]
    _ = Matrix.conjTranspose (sourceReferenceAmplitude psi) *
        Matrix.kronecker (1 : CMatrix A) S *
        sourceReferenceAmplitude psi := by
      rw [M.sum_conjTranspose_refinedKraus_mul_refinedKraus]

/-- A zero-probability refined branch has zero `A'R`-by-`E` amplitude. -/
theorem branchSourceReferenceAmplitude_eq_zero_of_branchWeight_eq_zero
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (i : M.refinedBranchIndex) (hi : M.branchWeight psi i = 0) :
    M.branchSourceReferenceAmplitude psi i = 0 := by
  classical
  have hrank := M.rankOne_postAmplitude_eq_zero_of_branchWeight_eq_zero psi i hi
  ext ar e
  have hdiag := congrFun (congrFun hrank (ar.1, (ar.2, e))) (ar.1, (ar.2, e))
  exact (CStarRing.mul_star_self_eq_zero_iff _).mp (by
    simpa [rankOneMatrix_apply, branchSourceReferenceAmplitude] using hdiag)

/-- Berta's refined-instrument inequality in unnormalized scale form, first
for a positive-definite side operator.  If the same `R` side operator is
feasible for every positive Alice outcome/Kraus branch, it is feasible for
the pre-instrument `AR` state. -/
theorem conditionalMinEntropyScaleFeasible_of_positiveBranches_posDef
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (T : CMatrix R) (hT : T.PosDef)
    (hbranch : ∀ i : M.positiveSupport psi,
      State.ConditionalMinEntropyScaleFeasible (a := A')
        (M.positiveBranchSourceReferenceState psi i) T) :
    State.ConditionalMinEntropyScaleFeasible (a := A)
      (sourceReferenceState psi) T := by
  classical
  let QA : CMatrix (Prod A R) := Matrix.kronecker (1 : CMatrix A) T
  let QA' : CMatrix (Prod A' R) := Matrix.kronecker (1 : CMatrix A') T
  have hQA : QA.PosDef := by
    simpa [QA] using (Matrix.PosDef.one.kronecker hT)
  have hQA' : QA'.PosDef := by
    simpa [QA'] using (Matrix.PosDef.one.kronecker hT)
  have hQAinv : QA⁻¹ = Matrix.kronecker (1 : CMatrix A) T⁻¹ := by
    simpa [QA] using (Matrix.inv_kronecker (1 : CMatrix A) T)
  have hQA'inv : QA'⁻¹ = Matrix.kronecker (1 : CMatrix A') T⁻¹ := by
    simpa [QA'] using (Matrix.inv_kronecker (1 : CMatrix A') T)
  have hcomponent : ∀ i : M.refinedBranchIndex,
      Matrix.conjTranspose (M.branchSourceReferenceAmplitude psi i) * QA'⁻¹ *
          M.branchSourceReferenceAmplitude psi i <=
        ((M.branchWeight psi i : Real) : Complex) • (1 : CMatrix E) := by
    intro i
    by_cases hi : 0 < M.branchWeight psi i
    · let ipos : M.positiveSupport psi := ⟨i, hi⟩
      have hpReal : 0 < (M.branchWeight psi i : Real) := by
        exact_mod_cast hi
      have hpComplex : (0 : Complex) <= ((M.branchWeight psi i : Real) : Complex) := by
        exact_mod_cast hpReal.le
      have hscale := (hbranch ipos).2
      have hscaled := (Matrix.le_iff.mp hscale).smul hpComplex
      have hgram :
          M.branchSourceReferenceAmplitude psi i *
              Matrix.conjTranspose (M.branchSourceReferenceAmplitude psi i) <=
            ((M.branchWeight psi i : Real) : Complex) • QA' := by
        rw [Matrix.le_iff, ← M.branchWeight_smul_positiveBranchSourceReferenceState_matrix
          psi ipos]
        simpa [QA', smul_sub] using hscaled
      exact
        (Matrix.conjTranspose_mul_inv_mul_self_le_smul_one_iff_self_mul_conjTranspose_le_smul
          (M.branchSourceReferenceAmplitude psi i) QA' hQA' hpReal).2 hgram
    · have hzero : M.branchWeight psi i = 0 :=
        le_antisymm (not_lt.mp hi) bot_le
      have hamp := M.branchSourceReferenceAmplitude_eq_zero_of_branchWeight_eq_zero
        psi i hzero
      simp [hamp, hzero]
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ :
      Finset M.refinedBranchIndex)) => hcomponent i
  have hweightComplex :
      (∑ i : M.refinedBranchIndex,
          ((M.branchWeight psi i : Real) : Complex)) = 1 := by
    exact_mod_cast M.sum_branchWeight_eq_one psi
  have hsumWeights :
      (∑ i : M.refinedBranchIndex,
          ((M.branchWeight psi i : Real) : Complex) • (1 : CMatrix E)) =
        (1 : CMatrix E) := by
    rw [← Finset.sum_smul, hweightComplex, one_smul]
  have hcomplement :
      Matrix.conjTranspose (sourceReferenceAmplitude psi) * QA⁻¹ *
          sourceReferenceAmplitude psi <= (1 : CMatrix E) := by
    rw [hQAinv]
    rw [← M.sum_branchSourceReferenceAmplitude_referenceSandwich psi T⁻¹]
    rw [hQA'inv] at hsum
    rw [hsumWeights] at hsum
    exact hsum
  refine ⟨hT.posSemidef, ?_⟩
  rw [sourceReferenceState_matrix]
  change sourceReferenceAmplitude psi *
      Matrix.conjTranspose (sourceReferenceAmplitude psi) <= QA
  have hcomplement' :
      Matrix.conjTranspose (sourceReferenceAmplitude psi) * QA⁻¹ *
          sourceReferenceAmplitude psi <=
        (((1 : Real) : Complex) • (1 : CMatrix E)) := by
    norm_num
    exact hcomplement
  have hresult :=
    (Matrix.conjTranspose_mul_inv_mul_self_le_smul_one_iff_self_mul_conjTranspose_le_smul
      (sourceReferenceAmplitude psi) QA hQA (c := 1) zero_lt_one).1 hcomplement'
  norm_num at hresult
  exact hresult

/-- Berta's refined-instrument inequality in canonical scale-feasibility
form.  No full-support assumption is needed: an arbitrarily small identity
regularization is removed using closedness of the PSD cone. -/
theorem conditionalMinEntropyScaleFeasible_of_positiveBranches
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (T : CMatrix R) (hT : T.PosSemidef)
    (hbranch : ∀ i : M.positiveSupport psi,
      State.ConditionalMinEntropyScaleFeasible (a := A')
        (M.positiveBranchSourceReferenceState psi i) T) :
    State.ConditionalMinEntropyScaleFeasible (a := A)
      (sourceReferenceState psi) T := by
  classical
  let D : CMatrix (Prod A R) :=
    Matrix.kronecker (1 : CMatrix A) T - (sourceReferenceState psi).matrix
  have hDherm : D.IsHermitian := by
    exact ((Matrix.PosSemidef.one.kronecker hT).isHermitian).sub
      (sourceReferenceState psi).pos.isHermitian
  have hreg : ∀ epsilon : Real, 0 < epsilon ->
      (D + (epsilon : Complex) • (1 : CMatrix (Prod A R))).PosSemidef := by
    intro epsilon hepsilon
    let Tepsilon : CMatrix R := T + (epsilon : Complex) • (1 : CMatrix R)
    have hTepsilon : Tepsilon.PosDef := by
      simpa [Tepsilon] using
        (State.cMatrix_posSemidef_add_pos_smul_one_posDef hT hepsilon)
    have hperturbR :
        ((epsilon : Complex) • (1 : CMatrix R)).PosSemidef := by
      exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (by
        exact_mod_cast hepsilon.le)
    have hTle : T <= Tepsilon := by
      rw [Matrix.le_iff]
      simpa [Tepsilon, sub_eq_add_neg, add_assoc] using hperturbR
    have hQle :
        Matrix.kronecker (1 : CMatrix A') T <=
          Matrix.kronecker (1 : CMatrix A') Tepsilon := by
      rw [Matrix.le_iff]
      have hkron :=
        (Matrix.PosSemidef.one : (1 : CMatrix A').PosSemidef).kronecker
          (Matrix.le_iff.mp hTle)
      simpa [Tepsilon, Matrix.kronecker_add, Matrix.kronecker_smul,
        sub_eq_add_neg, add_assoc] using hkron
    have hbranchEpsilon : ∀ i : M.positiveSupport psi,
        State.ConditionalMinEntropyScaleFeasible (a := A')
          (M.positiveBranchSourceReferenceState psi i) Tepsilon := by
      intro i
      exact ⟨hTepsilon.posSemidef, (hbranch i).2.trans hQle⟩
    have hinput := M.conditionalMinEntropyScaleFeasible_of_positiveBranches_posDef
      psi Tepsilon hTepsilon hbranchEpsilon
    have horder := Matrix.le_iff.mp hinput.2
    simpa [D, Tepsilon, Matrix.kronecker_add, Matrix.kronecker_smul,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using horder
  refine ⟨hT, ?_⟩
  rw [Matrix.le_iff]
  exact Matrix.posSemidef_of_add_pos_smul_one_posSemidef D hDherm hreg

/-- Fixed-reference form of Berta's local-operation proposition
[Berta2009SingleShotStateMerging,
diploma_thesis_berta_08_v1.tex:729-798].

The retained classical record is precisely `M.positiveSupport psi`: Alice's
instrument outcome together with Alice's chosen Kraus refinement.  No Bob
operation or Bob Kraus record occurs in the statement. -/
theorem conditionalMinEntropyFeasible_of_positiveBranches
    (M : FiniteInstrument A A' X) (psi : PureVector (Prod A (Prod R E)))
    (sigma : State R) (lam : Real)
    (hbranch : ∀ i : M.positiveSupport psi,
      State.ConditionalMinEntropyFeasible (a := A')
        (M.positiveBranchSourceReferenceState psi i) sigma lam) :
    State.ConditionalMinEntropyFeasible (a := A)
      (sourceReferenceState psi) sigma lam := by
  classical
  let T : CMatrix R := (Real.rpow 2 (-lam) : Complex) • sigma.matrix
  have hcpos : 0 < Real.rpow 2 (-lam) := Real.rpow_pos_of_pos (by norm_num) _
  have hT : T.PosSemidef := by
    exact Matrix.PosSemidef.smul sigma.pos (by exact_mod_cast hcpos.le)
  have hbranchScale : ∀ i : M.positiveSupport psi,
      State.ConditionalMinEntropyScaleFeasible (a := A')
        (M.positiveBranchSourceReferenceState psi i) T := by
    intro i
    simpa [T] using
      (State.conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
        (hbranch i))
  have hinputScale := M.conditionalMinEntropyScaleFeasible_of_positiveBranches
    psi T hT hbranchScale
  simpa [State.ConditionalMinEntropyFeasible, State.identityTensorStateMatrix,
    T, Matrix.kronecker_smul] using hinputScale.2

end FiniteInstrument

end

end QIT
