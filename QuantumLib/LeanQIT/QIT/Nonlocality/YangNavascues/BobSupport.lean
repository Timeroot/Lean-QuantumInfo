/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.YangNavascues.RankOneSupport

/-!
# Bob reduced support projections for Yang-Navascues data

This module packages the rank-one reduced-support bridge from
`QIT.Nonlocality.YangNavascues.RankOneSupport` as a Bob-local `Projection HB`.  The
API is intentionally small: it gives later Bob-local orthogonalization work a
stable projection-valued support object and the preservation theorem needed to
compare it with Bob's original source projection.

It does not prove pairwise orthogonality of these reduced supports and does not
construct the final replacement projection family.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u v w

noncomputable section

namespace YangNavascues

namespace Matrix

variable {HA : Type v} {HB : Type w}
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

/-- Applying a matrix to a pure state gives the rank-one matrix of the
transformed amplitude vector. -/
theorem mul_rankOneMatrix_mul_conjTranspose
    {a : Type*} [Fintype a] [DecidableEq a] (M : CMatrix a) (φ : a → ℂ) :
    M * rankOneMatrix φ * Matrix.conjTranspose M = rankOneMatrix (M.mulVec φ) := by
  rw [rankOneMatrix, rankOneMatrix]
  rw [Matrix.mul_vecMulVec]
  rw [Matrix.vecMulVec_mul]
  congr
  ext i
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose, mul_comm]

/-- A zero rank-one matrix has a zero generating vector. -/
theorem mulVec_eq_zero_of_rankOneMatrix_eq_zero
    {a : Type*} [Fintype a] [DecidableEq a] {φ : a → ℂ}
    (h : rankOneMatrix φ = 0) :
    φ = 0 := by
  funext i
  have hdiag := congrFun (congrFun h i) i
  have hzero : φ i * star (φ i) = 0 := by
    simpa [rankOneMatrix_apply] using hdiag
  rcases mul_eq_zero.mp hzero with hi | hi
  · exact hi
  · simpa using congrArg star hi

/--
If two Bob-by-Alice amplitude matrices have orthogonal ranges on Bob's side,
then their Bob reduced-support projections are orthogonal.
-/
theorem rangeProjection_amplitudeGram_mul_rangeProjection_eq_zero
    (A B : Matrix HB HA ℂ)
    (hAB : Matrix.conjTranspose A * B = 0) :
    Matrix.rangeProjection (A * Matrix.conjTranspose A) *
        Matrix.rangeProjection (B * Matrix.conjTranspose B) = 0 := by
  have hRangeOrth :
      LinearMap.range A.toEuclideanLin ⟂ LinearMap.range B.toEuclideanLin := by
    intro x hx y hy
    rcases hx with ⟨x0, rfl⟩
    rcases hy with ⟨y0, rfl⟩
    have hlin : A.toEuclideanLin.adjoint.comp B.toEuclideanLin = 0 := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      rw [← Matrix.toLpLin_mul]
      simpa using congrArg Matrix.toEuclideanLin hAB
    calc
      inner ℂ (B.toEuclideanLin y0) (A.toEuclideanLin x0)
          = inner ℂ ((A.toEuclideanLin.adjoint.comp B.toEuclideanLin) y0) x0 := by
              simp [LinearMap.adjoint_inner_left]
      _ = 0 := by simp [hlin]
  have hRangeA :
      LinearMap.range (A * Matrix.conjTranspose A).toEuclideanLin =
        LinearMap.range A.toEuclideanLin := by
    rw [Matrix.toLpLin_mul]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact LinearMap.range_self_comp_adjoint A.toEuclideanLin
  have hRangeB :
      LinearMap.range (B * Matrix.conjTranspose B).toEuclideanLin =
        LinearMap.range B.toEuclideanLin := by
    rw [Matrix.toLpLin_mul]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact LinearMap.range_self_comp_adjoint B.toEuclideanLin
  have hRangeOrthGram :
      LinearMap.range (A * Matrix.conjTranspose A).toEuclideanLin ⟂
        LinearMap.range (B * Matrix.conjTranspose B).toEuclideanLin := by
    exact hRangeOrth.mono (by rw [hRangeA]) (by rw [hRangeB])
  have hstar := Submodule.starProjection_comp_starProjection_eq_zero_iff.mpr hRangeOrthGram
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul, Matrix.rangeProjection_toEuclideanLin,
    Matrix.rangeProjection_toEuclideanLin]
  simpa using congrArg ContinuousLinearMap.toLinearMap hstar

omit [DecidableEq HB] in
/--
If a product of two Bob-local operators kills a bipartite vector, then the
corresponding Bob-side amplitude ranges are orthogonal.
-/
theorem bobAmplitudeMatrix_projection_conjTranspose_mul_eq_zero
    (P Q : CMatrix HB) (hPherm : P.IsHermitian) (φ : HA × HB → ℂ)
    (hPQ : (Matrix.kronecker (1 : CMatrix HA) (P * Q)).mulVec φ = 0) :
    Matrix.conjTranspose
        (Matrix.bobAmplitudeMatrix ((Matrix.kronecker (1 : CMatrix HA) P).mulVec φ)) *
      Matrix.bobAmplitudeMatrix ((Matrix.kronecker (1 : CMatrix HA) Q).mulVec φ) = 0 := by
  let A := Matrix.bobAmplitudeMatrix φ
  have hPQA : (P * Q) * A = 0 := by
    rw [← Matrix.bobAmplitudeMatrix_kronecker_mulVec]
    rw [hPQ]
    ext b a
    simp [Matrix.bobAmplitudeMatrix]
  rw [Matrix.bobAmplitudeMatrix_kronecker_mulVec,
    Matrix.bobAmplitudeMatrix_kronecker_mulVec]
  calc
    Matrix.conjTranspose (P * A) * (Q * A)
        = (Matrix.conjTranspose A * P) * (Q * A) := by
            rw [Matrix.conjTranspose_mul, hPherm]
    _ = (Matrix.conjTranspose A * P) * Q * A := by
            simp only [Matrix.mul_assoc]
    _ = Matrix.conjTranspose A * ((P * Q) * A) := by
            simp only [Matrix.mul_assoc]
    _ = 0 := by
            rw [hPQA]
            simp

end Matrix

namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/-- Pure-state post-selection unfolds to the rank-one matrix of the transformed
amplitude vector. -/
theorem postMatrix_pure_eq_rankOneMatrix_mulVec
    (ψ : PureVector (HA × HB)) (op : CMatrix (HA × HB)) :
    data.postMatrix ψ.state op = rankOneMatrix (op.mulVec ψ.amp) := by
  simp [postMatrix, PureVector.state_matrix, Matrix.mul_rankOneMatrix_mul_conjTranspose]

/-- Bob's lifted source projection is Hermitian. -/
theorem bobProjectionOp_isHermitian (k : ι) :
    (data.bobProjectionOp k).IsHermitian := by
  rw [bobProjectionOp_eq]
  change Matrix.conjTranspose ((1 : CMatrix HA) ⊗ₖ ((data.bobProjection k).matrix)) =
    (1 : CMatrix HA) ⊗ₖ ((data.bobProjection k).matrix)
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  simp [(data.bobProjection k).matrix_conjTranspose]

/-- Bob's lifted source projection is idempotent. -/
theorem bobProjectionOp_idempotent (k : ι) :
    data.bobProjectionOp k * data.bobProjectionOp k = data.bobProjectionOp k := by
  rw [bobProjectionOp_eq]
  change ((1 : CMatrix HA) ⊗ₖ ((data.bobProjection k).matrix)) *
      ((1 : CMatrix HA) ⊗ₖ ((data.bobProjection k).matrix)) =
    (1 : CMatrix HA) ⊗ₖ ((data.bobProjection k).matrix)
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, (data.bobProjection k).idempotent]

/-- Alice-lifted and Bob-lifted local projections commute. -/
theorem aliceProjectionOp_mul_bobProjectionOp_comm (i j : ι) :
    data.aliceProjectionOp i * data.bobProjectionOp j =
      data.bobProjectionOp j * data.aliceProjectionOp i := by
  rw [aliceProjectionOp_eq, bobProjectionOp_eq]
  change (((data.aliceProjection).effects i) ⊗ₖ (1 : CMatrix HB)) *
      ((1 : CMatrix HA) ⊗ₖ ((data.bobProjection j).matrix)) =
    ((1 : CMatrix HA) ⊗ₖ ((data.bobProjection j).matrix)) *
      (((data.aliceProjection).effects i) ⊗ₖ (1 : CMatrix HB))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/--
Under the YN projection-agreement hypothesis, distinct Bob source projections
are orthogonal when acting on the pure realization vector.
-/
theorem bobProjectionOp_mul_bobProjectionOp_mulVec_eq_zero
    (ψ : PureVector (HA × HB)) (h : YNConditions data ψ.state)
    (i j : ι) (hij : i ≠ j) :
    (data.bobProjectionOp i * data.bobProjectionOp j).mulVec ψ.amp = 0 := by
  apply Matrix.mulVec_eq_zero_of_rankOneMatrix_eq_zero
  have hpost :
      data.postMatrix ψ.state (data.bobProjectionOp i * data.bobProjectionOp j) = 0 := by
    have hBi : Matrix.conjTranspose (data.bobProjectionOp i) = data.bobProjectionOp i :=
      data.bobProjectionOp_isHermitian i
    have hBj : Matrix.conjTranspose (data.bobProjectionOp j) = data.bobProjectionOp j :=
      data.bobProjectionOp_isHermitian j
    have hcomm_i_j : data.aliceProjectionOp j * data.bobProjectionOp i =
        data.bobProjectionOp i * data.aliceProjectionOp j :=
      data.aliceProjectionOp_mul_bobProjectionOp_comm j i
    have hcomm_i_j' : data.bobProjectionOp i * data.aliceProjectionOp j =
        data.aliceProjectionOp j * data.bobProjectionOp i :=
      hcomm_i_j.symm
    calc
      data.postMatrix ψ.state (data.bobProjectionOp i * data.bobProjectionOp j)
          =
            data.bobProjectionOp i *
              data.bobProjectionAgreementMatrix ψ.state j *
              data.bobProjectionOp i := by
              simp [postMatrix, bobProjectionAgreementMatrix, Matrix.conjTranspose_mul,
                Matrix.conjTranspose_kronecker, Matrix.mul_assoc,
                (data.bobProjection i).matrix_conjTranspose,
                (data.bobProjection j).matrix_conjTranspose]
      _ =
            data.bobProjectionOp i *
              data.projectionAgreementMatrix ψ.state j *
              data.bobProjectionOp i := by
              rw [h.projectionAgreement j]
      _ =
            data.aliceProjectionOp j *
              data.bobProjectionAgreementMatrix ψ.state i *
              data.aliceProjectionOp j := by
              unfold projectionAgreementMatrix bobProjectionAgreementMatrix postMatrix
              rw [hBi, data.aliceProjectionOp_isHermitian j]
              calc
                data.bobProjectionOp i *
                    (data.aliceProjectionOp j * ψ.state.matrix * data.aliceProjectionOp j) *
                    data.bobProjectionOp i
                    =
                  (data.bobProjectionOp i * data.aliceProjectionOp j) *
                    ψ.state.matrix * (data.aliceProjectionOp j * data.bobProjectionOp i) := by
                    noncomm_ring
                _ =
                  (data.aliceProjectionOp j * data.bobProjectionOp i) *
                    ψ.state.matrix * (data.bobProjectionOp i * data.aliceProjectionOp j) := by
                    rw [hcomm_i_j', hcomm_i_j]
                _ =
                  data.aliceProjectionOp j *
                      (data.bobProjectionOp i * ψ.state.matrix * data.bobProjectionOp i) *
                    data.aliceProjectionOp j := by
                    noncomm_ring
      _ =
              data.aliceProjectionOp j *
              data.projectionAgreementMatrix ψ.state i *
              data.aliceProjectionOp j := by
              rw [h.projectionAgreement i]
      _ = 0 := by
              unfold projectionAgreementMatrix postMatrix
              rw [data.aliceProjectionOp_isHermitian i]
              have horth : data.aliceProjectionOp j * data.aliceProjectionOp i = 0 :=
                data.aliceProjectionOp_orthogonal j i (Ne.symm hij)
              calc
                data.aliceProjectionOp j *
                    (data.aliceProjectionOp i * ψ.state.matrix * data.aliceProjectionOp i) *
                    data.aliceProjectionOp j
                    =
                  (data.aliceProjectionOp j * data.aliceProjectionOp i) *
                    ψ.state.matrix * (data.aliceProjectionOp i * data.aliceProjectionOp j) := by
                    noncomm_ring
                _ = 0 := by
                    rw [horth]
                    simp
  have hpure := data.postMatrix_pure_eq_rankOneMatrix_mulVec ψ
      (data.bobProjectionOp i * data.bobProjectionOp j)
  rw [hpure] at hpost
  exact hpost

/--
Bob-local projection onto the reduced support of
`(1_A ⊗ P_B^(k)) ψ`.

The underlying matrix is `data.bobProjectedReducedSupport ψ k`; this wrapper
records the Hermitian/idempotent projection facts needed by later Bob-local
replacement constructions.
-/
def bobProjectedReducedSupportProjection
    (ψ : PureVector (HA × HB)) (k : ι) : Projection HB where
  matrix := data.bobProjectedReducedSupport ψ k
  isHermitian := by
    simp [bobProjectedReducedSupport_eq, Matrix.rangeProjection_isHermitian]
  idempotent := by
    simp [bobProjectedReducedSupport_eq, Matrix.rangeProjection_idempotent]

@[simp]
theorem bobProjectedReducedSupportProjection_matrix
    (ψ : PureVector (HA × HB)) (k : ι) :
    (data.bobProjectedReducedSupportProjection ψ k).matrix =
      data.bobProjectedReducedSupport ψ k :=
  rfl

theorem bobProjectedReducedSupportProjection_isHermitian
    (ψ : PureVector (HA × HB)) (k : ι) :
    ((data.bobProjectedReducedSupportProjection ψ k).matrix).IsHermitian :=
  (data.bobProjectedReducedSupportProjection ψ k).isHermitian

theorem bobProjectedReducedSupportProjection_idempotent
    (ψ : PureVector (HA × HB)) (k : ι) :
    (data.bobProjectedReducedSupportProjection ψ k).matrix *
        (data.bobProjectedReducedSupportProjection ψ k).matrix =
      (data.bobProjectedReducedSupportProjection ψ k).matrix :=
  (data.bobProjectedReducedSupportProjection ψ k).idempotent

/--
The reduced support projection has the same Bob-local post-selected density
action on the rank-one state `ψ.state` as Bob's original projection.
-/
theorem bobProjectedReducedSupportProjection_preserves_postMatrix
    (ψ : PureVector (HA × HB)) (k : ι) :
    data.BobLocalSamePostMatrix ψ.state
      (data.bobProjectedReducedSupportProjection ψ k).matrix
      ((data.bobProjection k).matrix) := by
  simpa using data.bobProjectedReducedSupport_bobLocalSamePostMatrix ψ k

/--
The Bob reduced-support projections obtained from distinct YN outcomes are
orthogonal, on the pure/rank-one YN route.

This theorem does not assume Bob's original source projections are globally
orthogonal.  Orthogonality is proved only for the reduced-support replacement
projections assembled into a Bob-local witness.
-/
theorem bobProjectedReducedSupportProjection_orthogonal
    (ψ : PureVector (HA × HB)) (h : YNConditions data ψ.state)
    (i j : ι) (hij : i ≠ j) :
    (data.bobProjectedReducedSupportProjection ψ i).matrix *
        (data.bobProjectedReducedSupportProjection ψ j).matrix = 0 := by
  have hvec :=
    data.bobProjectionOp_mul_bobProjectionOp_mulVec_eq_zero ψ h i j hij
  have hvecLocal :
      (Matrix.kronecker (1 : CMatrix HA)
        ((data.bobProjection i).matrix * (data.bobProjection j).matrix)).mulVec ψ.amp = 0 := by
    simpa [bobProjectionOp_eq, ← Matrix.mul_kronecker_mul, Matrix.one_mul] using hvec
  have hAmp :
      Matrix.conjTranspose (Matrix.bobAmplitudeMatrix (data.bobProjectedVector ψ i)) *
        Matrix.bobAmplitudeMatrix (data.bobProjectedVector ψ j) = 0 := by
    rw [bobProjectedVector_eq, bobProjectedVector_eq]
    exact Matrix.bobAmplitudeMatrix_projection_conjTranspose_mul_eq_zero
      ((data.bobProjection i).matrix)
      ((data.bobProjection j).matrix)
      (data.bobProjection i).isHermitian
      ψ.amp hvecLocal
  change
    Matrix.rangeProjection (data.bobProjectedReducedMatrix ψ i) *
        Matrix.rangeProjection (data.bobProjectedReducedMatrix ψ j) = 0
  rw [bobProjectedReducedMatrix_eq, bobProjectedReducedMatrix_eq]
  rw [Matrix.partialTraceA_rankOneMatrix_eq_bobAmplitudeMatrix_mul_conjTranspose,
    Matrix.partialTraceA_rankOneMatrix_eq_bobAmplitudeMatrix_mul_conjTranspose]
  exact Matrix.rangeProjection_amplitudeGram_mul_rangeProjection_eq_zero
    (Matrix.bobAmplitudeMatrix (data.bobProjectedVector ψ i))
    (Matrix.bobAmplitudeMatrix (data.bobProjectedVector ψ j))
    hAmp

end YNData
end YangNavascues

end

end QIT
