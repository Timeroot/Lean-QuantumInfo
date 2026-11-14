/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Measurements.Projective
public import QIT.Measurements.Support
public import QIT.Core.Pure
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Yang-Navascues self-testing target scaffold

This module starts the Yang-Navascues sufficient-criterion route by recording
the finite Schmidt-target convention from
[ColadangeloGohScarani2016SelfTesting, all_pure_v2.tex:161-188].  The target
pure state is represented as `sum_i c_i |ii>`, with positive finite Schmidt
coefficients whose squared sum is one.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT
namespace YangNavascues

universe u

noncomputable section

/--
Finite Schmidt data for the target state in the Yang-Navascues sufficient
criterion.  The distinguished `base` coefficient corresponds to the source's
`c_0`; later YN conditions use it in coefficient-ratio hypotheses.
-/
structure SchmidtTarget (ι : Type u) [Fintype ι] [DecidableEq ι] where
  /-- Schmidt coefficients `c_i` of the target state. -/
  coeff : ι → ℝ
  /-- Distinguished index used as the source's `0` coefficient. -/
  base : ι
  /-- Source hypothesis `0 < c_i`. -/
  coeff_pos : ∀ i, 0 < coeff i
  /-- Source hypothesis `c_i < 1`. -/
  coeff_lt_one : ∀ i, coeff i < 1
  /-- Source normalization `sum_i c_i^2 = 1`. -/
  coeff_sq_sum : ∑ i, coeff i ^ 2 = 1

namespace SchmidtTarget

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Amplitudes of the diagonal target vector `sum_i c_i |ii>`. -/
def amp (target : SchmidtTarget ι) : ι × ι → ℂ
  | (i, j) => if i = j then (target.coeff i : ℂ) else 0

@[simp]
theorem amp_diag (target : SchmidtTarget ι) (i : ι) :
    target.amp (i, i) = (target.coeff i : ℂ) := by
  simp [amp]

@[simp]
theorem amp_offDiag (target : SchmidtTarget ι) {i j : ι} (hij : i ≠ j) :
    target.amp (i, j) = 0 := by
  simp [amp, hij]

/-- The diagonal target vector is trace-normalized. -/
theorem trace_rankOne_eq_one (target : SchmidtTarget ι) :
    (rankOneMatrix target.amp).trace = 1 := by
  rw [rankOneMatrix_trace]
  change (∑ x : ι × ι, target.amp x * star (target.amp x)) = 1
  rw [← Finset.univ_product_univ, Finset.sum_product]
  calc
    (∑ i : ι, ∑ j : ι, target.amp (i, j) * star (target.amp (i, j)))
        = ∑ i : ι, (target.coeff i : ℂ) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_eq_single i]
          · simp [amp, pow_two]
          · intro j _ hji
            simp [amp, hji.symm]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim
    _ = ((∑ i : ι, target.coeff i ^ 2 : ℝ) : ℂ) := by
          simp [Complex.ofReal_sum]
    _ = 1 := by
          simp [target.coeff_sq_sum]

/-- The Yang-Navascues diagonal target as a normalized pure vector. -/
def pureVector (target : SchmidtTarget ι) : PureVector (ι × ι) where
  amp := target.amp
  trace_rankOne_eq_one := target.trace_rankOne_eq_one

/-- The Yang-Navascues diagonal target as a density state. -/
def state (target : SchmidtTarget ι) : State (ι × ι) :=
  target.pureVector.state

@[simp]
theorem pureVector_amp (target : SchmidtTarget ι) :
    target.pureVector.amp = target.amp :=
  rfl

@[simp]
theorem state_matrix (target : SchmidtTarget ι) :
    target.state.matrix = rankOneMatrix target.amp :=
  rfl

end SchmidtTarget

/--
A finite projection used for the Bob-side YN hypotheses.

Unlike `ProjectiveMeasurement`, this records one projection at a time and does
not require the whole Bob family to be complete or mutually orthogonal.
-/
structure Projection (a : Type u) [Fintype a] [DecidableEq a] where
  /-- The projection matrix. -/
  matrix : CMatrix a
  /-- The projection is Hermitian. -/
  isHermitian : matrix.IsHermitian
  /-- The projection is idempotent. -/
  idempotent : matrix * matrix = matrix

namespace Projection

variable {a : Type u} [Fintype a] [DecidableEq a]

@[simp]
theorem matrix_conjTranspose (P : Projection a) :
    Matrix.conjTranspose P.matrix = P.matrix := by
  simpa [Matrix.IsHermitian] using P.isHermitian

end Projection

universe v w

/--
Operator data for the Yang-Navascues sufficient criterion.

`aliceProjection` is a complete projective family.  `bobProjection` is only a
family of individual projections, following the source statement that Bob's
projections need not form a complete orthogonal family.
-/
structure YNData (ι : Type u) (HA : Type v) (HB : Type w)
    [Fintype ι] [DecidableEq ι]
    [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB] where
  /-- Target Schmidt data `sum_i c_i |ii>`. -/
  target : SchmidtTarget ι
  /-- Alice's complete orthogonal projection family. -/
  aliceProjection : ProjectiveMeasurement ι HA
  /-- Bob's projection family, not required to be complete or orthogonal. -/
  bobProjection : ι → Projection HB
  /-- Alice's local unitary family `X_A^(k)`. -/
  aliceUnitary : ι → Matrix.unitaryGroup HA ℂ
  /-- Bob's local unitary family `X_B^(k)`. -/
  bobUnitary : ι → Matrix.unitaryGroup HB ℂ

namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/-- Alice's projection lifted to the bipartite system. -/
def aliceProjectionOp (k : ι) : CMatrix (HA × HB) :=
  Matrix.kronecker ((data.aliceProjection).effects k) (1 : CMatrix HB)

/-- Bob's projection lifted to the bipartite system. -/
def bobProjectionOp (k : ι) : CMatrix (HA × HB) :=
  Matrix.kronecker (1 : CMatrix HA) ((data.bobProjection k).matrix)

/-- Lift a Bob-local operator to the bipartite system. -/
def bobLocalOp (_data : YNData ι HA HB) (Q : CMatrix HB) : CMatrix (HA × HB) :=
  Matrix.kronecker (1 : CMatrix HA) Q

/-- The local unitary `X_A^(k) tensor X_B^(k)` lifted to the bipartite system. -/
def unitaryOp (k : ι) : CMatrix (HA × HB) :=
  Matrix.kronecker (data.aliceUnitary k : CMatrix HA) (data.bobUnitary k : CMatrix HB)

/-- The source-side product `X_A^(k) X_B^(k) P_B^(k)` as a bipartite operator. -/
def transformedBobProjectionOp (k : ι) : CMatrix (HA × HB) :=
  data.unitaryOp k * data.bobProjectionOp k

/-- Density matrix after applying an unnormalized linear operator. -/
def postMatrix (_data : YNData ι HA HB) (rho : State (HA × HB)) (op : CMatrix (HA × HB)) :
    CMatrix (HA × HB) :=
  op * rho.matrix * Matrix.conjTranspose op

/-- Density version of `P_A^(k)|psi>`. -/
def projectionAgreementMatrix (rho : State (HA × HB)) (k : ι) : CMatrix (HA × HB) :=
  data.postMatrix rho (data.aliceProjectionOp k)

/-- Density version of `P_B^(k)|psi>`. -/
def bobProjectionAgreementMatrix (rho : State (HA × HB)) (k : ι) : CMatrix (HA × HB) :=
  data.postMatrix rho (data.bobProjectionOp k)

/-- The support projection of Bob's post-selected density matrix for outcome `k`. -/
def bobProjectedSupport (rho : State (HA × HB)) (k : ι) : CMatrix (HA × HB) :=
  Matrix.rangeProjection (data.bobProjectionAgreementMatrix rho k)

/-- Density matrix after applying a Bob-local operator. -/
def bobLocalPostMatrix (rho : State (HA × HB)) (Q : CMatrix HB) : CMatrix (HA × HB) :=
  data.postMatrix rho (data.bobLocalOp Q)

/--
Two Bob-local operators have the same state-supported action on `rho` when
their lifted post-selected density matrices agree.
-/
def BobLocalSamePostMatrix (rho : State (HA × HB)) (Q R : CMatrix HB) : Prop :=
  data.bobLocalPostMatrix rho Q = data.bobLocalPostMatrix rho R

/-- Density version of `X_A^(k) X_B^(k) P_B^(k)|psi>`. -/
def unitaryCoefficientMatrix (rho : State (HA × HB)) (k : ι) : CMatrix (HA × HB) :=
  data.postMatrix rho (data.transformedBobProjectionOp k)

/-- Density version of `P_A^(0)|psi>`, using the target's distinguished base. -/
def baseProjectionMatrix (rho : State (HA × HB)) : CMatrix (HA × HB) :=
  data.postMatrix rho (data.aliceProjectionOp data.target.base)

@[simp]
theorem aliceProjectionOp_eq (k : ι) :
    data.aliceProjectionOp k =
      Matrix.kronecker ((data.aliceProjection).effects k) (1 : CMatrix HB) :=
  rfl

@[simp]
theorem bobProjectionOp_eq (k : ι) :
    data.bobProjectionOp k =
      Matrix.kronecker (1 : CMatrix HA) ((data.bobProjection k).matrix) :=
  rfl

@[simp]
theorem bobLocalOp_eq (Q : CMatrix HB) :
    data.bobLocalOp Q = Matrix.kronecker (1 : CMatrix HA) Q :=
  rfl

@[simp]
theorem bobProjectionOp_eq_bobLocalOp (k : ι) :
    data.bobProjectionOp k = data.bobLocalOp ((data.bobProjection k).matrix) :=
  rfl

@[simp]
theorem transformedBobProjectionOp_eq (k : ι) :
    data.transformedBobProjectionOp k = data.unitaryOp k * data.bobProjectionOp k :=
  rfl

/-- The lifted local unitary `X_A^(k) tensor X_B^(k)` is an isometry. -/
theorem unitaryOp_isometry (k : ι) :
    Matrix.conjTranspose (data.unitaryOp k) * data.unitaryOp k = 1 := by
  unfold unitaryOp
  change Matrix.conjTranspose
      ((data.aliceUnitary k : CMatrix HA) ⊗ₖ (data.bobUnitary k : CMatrix HB)) *
      ((data.aliceUnitary k : CMatrix HA) ⊗ₖ (data.bobUnitary k : CMatrix HB)) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  have hA :
      Matrix.conjTranspose (data.aliceUnitary k : CMatrix HA) *
          (data.aliceUnitary k : CMatrix HA) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.UnitaryGroup.star_mul_self (data.aliceUnitary k)
  have hB :
      Matrix.conjTranspose (data.bobUnitary k : CMatrix HB) *
          (data.bobUnitary k : CMatrix HB) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.UnitaryGroup.star_mul_self (data.bobUnitary k)
  rw [hA, hB, Matrix.one_kronecker_one]

@[simp]
theorem bobLocalPostMatrix_eq (rho : State (HA × HB)) (Q : CMatrix HB) :
    data.bobLocalPostMatrix rho Q = data.postMatrix rho (data.bobLocalOp Q) :=
  rfl

@[simp]
theorem bobProjectionAgreementMatrix_eq_bobLocalPostMatrix
    (rho : State (HA × HB)) (k : ι) :
    data.bobProjectionAgreementMatrix rho k =
      data.bobLocalPostMatrix rho ((data.bobProjection k).matrix) :=
  rfl

@[simp]
theorem bobProjectedSupport_eq (rho : State (HA × HB)) (k : ι) :
    data.bobProjectedSupport rho k =
      Matrix.rangeProjection (data.bobProjectionAgreementMatrix rho k) :=
  rfl

theorem bobLocalSamePostMatrix_refl (rho : State (HA × HB)) (Q : CMatrix HB) :
    data.BobLocalSamePostMatrix rho Q Q :=
  rfl

theorem bobLocalSamePostMatrix_symm {rho : State (HA × HB)} {Q R : CMatrix HB}
    (h : data.BobLocalSamePostMatrix rho Q R) :
    data.BobLocalSamePostMatrix rho R Q :=
  h.symm

theorem bobLocalSamePostMatrix_trans {rho : State (HA × HB)} {Q R S : CMatrix HB}
    (hQR : data.BobLocalSamePostMatrix rho Q R)
    (hRS : data.BobLocalSamePostMatrix rho R S) :
    data.BobLocalSamePostMatrix rho Q S :=
  hQR.trans hRS

/-- If two Bob-local lifted operators agree on the bipartite state support,
then they produce the same Bob-local post-selected density matrix. -/
theorem bobLocalSamePostMatrix_of_sameOnStateSupport
    (rho : State (HA × HB)) (Q R : CMatrix HB)
    (h : Matrix.sameOnStateSupport rho.matrix (data.bobLocalOp Q) (data.bobLocalOp R)) :
    data.BobLocalSamePostMatrix rho Q R := by
  exact Matrix.postMatrix_eq_of_sameOnStateSupport rho.pos.isHermitian h

/-- Alice's lifted projective effect is Hermitian. -/
theorem aliceProjectionOp_isHermitian (k : ι) :
    (data.aliceProjectionOp k).IsHermitian := by
  rw [aliceProjectionOp_eq]
  change Matrix.conjTranspose
      (((data.aliceProjection).effects k) ⊗ₖ (1 : CMatrix HB)) =
    ((data.aliceProjection).effects k) ⊗ₖ (1 : CMatrix HB)
  rw [Matrix.conjTranspose_kronecker, data.aliceProjection.isHermitian k]
  simp

/-- Alice's lifted projective effect is idempotent. -/
theorem aliceProjectionOp_idempotent (k : ι) :
    data.aliceProjectionOp k * data.aliceProjectionOp k = data.aliceProjectionOp k := by
  rw [aliceProjectionOp_eq]
  change (((data.aliceProjection).effects k) ⊗ₖ (1 : CMatrix HB)) *
      (((data.aliceProjection).effects k) ⊗ₖ (1 : CMatrix HB)) =
    ((data.aliceProjection).effects k) ⊗ₖ (1 : CMatrix HB)
  rw [← Matrix.mul_kronecker_mul, data.aliceProjection.idempotent k, Matrix.one_mul]

/-- Alice's lifted projective effects are mutually orthogonal. -/
theorem aliceProjectionOp_orthogonal (i j : ι) (hij : i ≠ j) :
    data.aliceProjectionOp i * data.aliceProjectionOp j = 0 := by
  rw [aliceProjectionOp_eq, aliceProjectionOp_eq]
  change (((data.aliceProjection).effects i) ⊗ₖ (1 : CMatrix HB)) *
      (((data.aliceProjection).effects j) ⊗ₖ (1 : CMatrix HB)) = 0
  rw [← Matrix.mul_kronecker_mul, data.aliceProjection.orthogonal i j hij,
    Matrix.zero_kronecker]

/-- Alice's lifted projective effects sum to the bipartite identity. -/
theorem aliceProjectionOp_sum_eq_one :
    ∑ k : ι, data.aliceProjectionOp k = (1 : CMatrix (HA × HB)) := by
  ext x y
  rcases x with ⟨ha, hb⟩
  rcases y with ⟨ha', hb'⟩
  by_cases hhb : hb = hb'
  · subst hb'
    have hAlice := congrArg (fun M : CMatrix HA => M ha ha')
      data.aliceProjection.sum_effects
    simpa [aliceProjectionOp, Matrix.sum_apply, Matrix.kronecker,
      Matrix.one_apply] using hAlice
  · simp [aliceProjectionOp, Matrix.sum_apply, Matrix.kronecker, hhb]

/-- Alice's lifted projection fixes its own post-selected density matrix. -/
theorem projectionAgreementMatrix_fixed_by_aliceProjectionOp
    (rho : State (HA × HB)) (k : ι) :
    data.aliceProjectionOp k * data.projectionAgreementMatrix rho k =
      data.projectionAgreementMatrix rho k := by
  unfold projectionAgreementMatrix postMatrix
  let A := data.aliceProjectionOp k
  change A * (A * rho.matrix * Matrix.conjTranspose A) =
    A * rho.matrix * Matrix.conjTranspose A
  calc
    A * (A * rho.matrix * Matrix.conjTranspose A)
        = (A * A) * rho.matrix * Matrix.conjTranspose A := by
            rw [← Matrix.mul_assoc A (A * rho.matrix) (Matrix.conjTranspose A)]
            rw [← Matrix.mul_assoc A A rho.matrix]
    _ = A * rho.matrix * Matrix.conjTranspose A := by
            rw [data.aliceProjectionOp_idempotent k]

/-- The lifted Alice projective post-selections have total trace one. -/
theorem projectionAgreementMatrix_trace_sum_eq_one (ψ : PureVector (HA × HB)) :
    ∑ k : ι, (data.projectionAgreementMatrix ψ.state k).trace = 1 := by
  have hterm :
      ∀ k : ι,
        (data.projectionAgreementMatrix ψ.state k).trace =
          (ψ.state.matrix * data.aliceProjectionOp k).trace := by
    intro k
    unfold projectionAgreementMatrix postMatrix
    let P := data.aliceProjectionOp k
    have hHerm : Matrix.conjTranspose P = P := data.aliceProjectionOp_isHermitian k
    have hIdem : P * P = P := data.aliceProjectionOp_idempotent k
    calc
      (P * ψ.state.matrix * Matrix.conjTranspose P).trace =
          (P * ψ.state.matrix * P).trace := by rw [hHerm]
      _ = ((P * ψ.state.matrix) * P).trace := by rw [Matrix.mul_assoc]
      _ = (P * (P * ψ.state.matrix)).trace := by rw [Matrix.trace_mul_comm]
      _ = ((P * P) * ψ.state.matrix).trace := by rw [Matrix.mul_assoc]
      _ = (P * ψ.state.matrix).trace := by rw [hIdem]
      _ = (ψ.state.matrix * P).trace := by rw [Matrix.trace_mul_comm]
  calc
    ∑ k : ι, (data.projectionAgreementMatrix ψ.state k).trace =
        ∑ k : ι, (ψ.state.matrix * data.aliceProjectionOp k).trace := by
          exact Finset.sum_congr rfl (fun k _ => hterm k)
    _ = (∑ k : ι, ψ.state.matrix * data.aliceProjectionOp k).trace := by
          rw [Matrix.trace_sum]
    _ = (ψ.state.matrix * ∑ k : ι, data.aliceProjectionOp k).trace := by
          congr 1
          exact (Matrix.mul_sum Finset.univ data.aliceProjectionOp ψ.state.matrix).symm
    _ = (ψ.state.matrix * 1).trace := by rw [data.aliceProjectionOp_sum_eq_one]
    _ = 1 := by simpa [PureVector.state_matrix] using ψ.trace_rankOne_eq_one

/-- The local unitary in the YN coefficient condition preserves post-selected trace. -/
theorem unitaryCoefficientMatrix_trace_eq_bobProjectionAgreementMatrix_trace
    (rho : State (HA × HB)) (k : ι) :
    (data.unitaryCoefficientMatrix rho k).trace =
      (data.bobProjectionAgreementMatrix rho k).trace := by
  unfold unitaryCoefficientMatrix bobProjectionAgreementMatrix transformedBobProjectionOp postMatrix
  let U := data.unitaryOp k
  let P := data.bobProjectionOp k
  let A := P * rho.matrix * Matrix.conjTranspose P
  have hU : Matrix.conjTranspose U * U = 1 := data.unitaryOp_isometry k
  calc
    (U * P * rho.matrix * Matrix.conjTranspose (U * P)).trace =
        (U * A * Matrix.conjTranspose U).trace := by
          rw [Matrix.conjTranspose_mul]
          congr 1
          simp [A]
          noncomm_ring
    _ = (Matrix.conjTranspose U * U * A).trace := by
          rw [Matrix.trace_mul_cycle]
    _ = A.trace := by
          rw [hU]
          simp

/-- The squared coefficient ratios sum to the inverse square of the base coefficient. -/
theorem target_ratio_sq_sum_eq_inv_base_sq :
    (∑ k : ι,
      ((((data.target.coeff k / data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ))) =
      ((((data.target.coeff data.target.base) ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hbase_ne : data.target.coeff data.target.base ≠ 0 :=
    ne_of_gt (data.target.coeff_pos data.target.base)
  have hreal :
      (∑ k : ι,
        (data.target.coeff k / data.target.coeff data.target.base) ^ 2) =
        (((data.target.coeff data.target.base) ^ 2)⁻¹ : ℝ) := by
    calc
      (∑ k : ι,
        (data.target.coeff k / data.target.coeff data.target.base) ^ 2) =
          (∑ k : ι, data.target.coeff k ^ 2) /
            (data.target.coeff data.target.base ^ 2) := by
            simp [div_pow]
            rw [Finset.sum_div]
      _ = ((data.target.coeff data.target.base) ^ 2)⁻¹ := by
            rw [data.target.coeff_sq_sum]
            field_simp [hbase_ne]
  exact_mod_cast hreal

end YNData

/--
An exact state-supported orthogonalization witness for Bob-side YN projections.

The witness is intentionally phrased through post-selected density matrices:
it does not assert that Bob's original projections are globally complete or
mutually orthogonal, only that there is an orthogonal projection family with
the same action on the state for the purposes of the YN construction.
-/
structure StateSupportedBobOrthogonalization {ι : Type u} {HA : Type v} {HB : Type w}
    [Fintype ι] [DecidableEq ι]
    [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
    (data : YNData ι HA HB) (rho : State (HA × HB)) where
  /-- Orthogonalized projection effects on the bipartite support space. -/
  effects : ι → CMatrix (HA × HB)
  /-- Each witness effect is Hermitian. -/
  isHermitian : ∀ k, (effects k).IsHermitian
  /-- Each witness effect is idempotent. -/
  idempotent : ∀ k, effects k * effects k = effects k
  /-- Distinct witness effects are orthogonal. -/
  orthogonal : ∀ i j, i ≠ j → effects i * effects j = 0
  /-- The witness preserves Bob's post-selected density matrices on `rho`. -/
  preserves_postMatrix :
    ∀ k, data.postMatrix rho (effects k) = data.bobProjectionAgreementMatrix rho k

/--
Density-matrix form of the Yang-Navascues sufficient-criterion hypotheses.

The first field mirrors `P_A^(k)|psi> = P_B^(k)|psi>`.  The second mirrors
`X_A^(k) X_B^(k) P_B^(k)|psi> = (c_k/c_0) P_A^(0)|psi>`; because the
condition is stated on density matrices, the real coefficient ratio is
squared.
-/
def YNConditions {ι : Type u} {HA : Type v} {HB : Type w}
    [Fintype ι] [DecidableEq ι]
    [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
    (data : YNData ι HA HB) (rho : State (HA × HB)) : Prop :=
  (∀ k : ι,
    data.projectionAgreementMatrix rho k =
      data.bobProjectionAgreementMatrix rho k) ∧
  (∀ k : ι,
    data.unitaryCoefficientMatrix rho k =
      (((data.target.coeff k / data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ) •
        data.baseProjectionMatrix rho)

namespace YNConditions

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable {data : YNData ι HA HB} {rho : State (HA × HB)}

/-- Extract the projection-agreement part of the YN conditions. -/
theorem projectionAgreement (h : YNConditions data rho) (k : ι) :
    data.projectionAgreementMatrix rho k =
      data.bobProjectionAgreementMatrix rho k :=
  h.1 k

/-- The YN projection-agreement condition lets Alice's lifted projection fix
Bob's corresponding post-selected density matrix. -/
theorem bobProjectionAgreementMatrix_fixed_by_aliceProjectionOp
    (h : YNConditions data rho) (k : ι) :
    data.aliceProjectionOp k * data.bobProjectionAgreementMatrix rho k =
      data.bobProjectionAgreementMatrix rho k := by
  rw [← h.projectionAgreement k]
  exact data.projectionAgreementMatrix_fixed_by_aliceProjectionOp rho k

/-- Extract the coefficient/unitary part of the YN conditions. -/
theorem unitaryCoefficient (h : YNConditions data rho) (k : ι) :
    data.unitaryCoefficientMatrix rho k =
      (((data.target.coeff k / data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ) •
        data.baseProjectionMatrix rho :=
  h.2 k

/-- Trace form of the YN coefficient condition for each branch. -/
theorem projectionAgreementMatrix_trace_eq_coeff_mul_base
    (h : YNConditions data rho) (k : ι) :
    (data.projectionAgreementMatrix rho k).trace =
      ((((data.target.coeff k / data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ)) *
        (data.baseProjectionMatrix rho).trace := by
  calc
    (data.projectionAgreementMatrix rho k).trace =
        (data.bobProjectionAgreementMatrix rho k).trace := by
          rw [h.projectionAgreement k]
    _ = (data.unitaryCoefficientMatrix rho k).trace := by
          rw [data.unitaryCoefficientMatrix_trace_eq_bobProjectionAgreementMatrix_trace]
    _ = ((((data.target.coeff k / data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ) •
        data.baseProjectionMatrix rho).trace := by
          rw [h.unitaryCoefficient k]
    _ = ((((data.target.coeff k / data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ)) *
        (data.baseProjectionMatrix rho).trace := by
          simp

/-- For a pure YN witness, the base projection has trace `c_0^2`. -/
theorem baseProjectionMatrix_trace_eq_coeff_base_sq
    {ψ : PureVector (HA × HB)} (h : YNConditions data ψ.state) :
    (data.baseProjectionMatrix ψ.state).trace =
      (((data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ) := by
  let T : ℂ := (data.baseProjectionMatrix ψ.state).trace
  let c : ℂ := (((data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ)
  let ratio : ι → ℂ := fun k =>
    ((((data.target.coeff k / data.target.coeff data.target.base) ^ 2 : ℝ) : ℂ))
  have hsumTrace : (∑ k : ι, ratio k) * T = 1 := by
    calc
      (∑ k : ι, ratio k) * T =
          ∑ k : ι, ratio k * T := by rw [Finset.sum_mul]
      _ = ∑ k : ι, (data.projectionAgreementMatrix ψ.state k).trace := by
          refine Finset.sum_congr rfl ?_
          intro k _
          symm
          simpa [ratio, T] using h.projectionAgreementMatrix_trace_eq_coeff_mul_base k
      _ = 1 := data.projectionAgreementMatrix_trace_sum_eq_one ψ
  have hratio : (∑ k : ι, ratio k) = c⁻¹ := by
    simpa [ratio, c] using data.target_ratio_sq_sum_eq_inv_base_sq
  have hbase_ne : data.target.coeff data.target.base ≠ 0 :=
    ne_of_gt (data.target.coeff_pos data.target.base)
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (pow_ne_zero 2 hbase_ne)
  have hinvT : c⁻¹ * T = 1 := by
    simpa [hratio] using hsumTrace
  have hmul := congrArg (fun z : ℂ => c * z) hinvT
  have hT : T = c := by
    simpa [hc_ne, mul_assoc] using hmul
  simpa [T, c] using hT

/--
The YN projection-agreement condition supplies an exact state-supported
orthogonalization witness for Bob's projection family.

The constructed witness uses Alice's complete orthogonal lifted projective
family, together with the density equality `P_A^(k) rho P_A^(k) =
P_B^(k) rho P_B^(k)`.  Thus Bob's projections remain source-general: they are
not assumed to be a PVM.
-/
def stateSupportedBobOrthogonalization (h : YNConditions data rho) :
    StateSupportedBobOrthogonalization data rho where
  effects := data.aliceProjectionOp
  isHermitian := data.aliceProjectionOp_isHermitian
  idempotent := data.aliceProjectionOp_idempotent
  orthogonal := data.aliceProjectionOp_orthogonal
  preserves_postMatrix := by
    intro k
    exact h.projectionAgreement k

/-- Bob projected supports are mutually orthogonal on the state support. -/
theorem bobProjectedSupport_orthogonal
    (h : YNConditions data rho) (i j : ι) (hij : i ≠ j) :
    data.bobProjectedSupport rho i * data.bobProjectedSupport rho j = 0 := by
  exact Matrix.rangeProjection_mul_rangeProjection_eq_zero_of_fixed_orthogonal
    (data.aliceProjectionOp_isHermitian i)
    (data.aliceProjectionOp_orthogonal i j hij)
    (h.bobProjectionAgreementMatrix_fixed_by_aliceProjectionOp i)
    (h.bobProjectionAgreementMatrix_fixed_by_aliceProjectionOp j)

end YNConditions

end

end YangNavascues
end QIT
