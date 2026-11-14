/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.PositionBasedCoding
public import QIT.Symmetry.DeFinetti
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import Mathlib.Data.Complex.BigOperators

/-!
# Sequential decoding

This module records the finite projector-sequence interface for the
position-based sequential decoder used in the one-shot entanglement-assisted
classical communication lower bound
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:530-665].

The source proof uses the OMW quantum union bound for a sequence of projectors:
for projectors `P₁, ..., P_N`, a state `ρ`, and `c > 0`,
`1 - Tr[P_N ... P₁ ρ P₁ ... P_N]` is bounded by a final missed-detection term
plus a weighted sum of earlier failed-event terms.  We keep the ordered
`Fin (n+1)` interface explicit so the lower-bound proof can instantiate it
with the sequential decoder's reject-earlier / accept-current projector list.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- A single finite-dimensional orthogonal projection, represented as a
Hermitian idempotent matrix. -/
structure ProjectionMatrix (a : Type u) [Fintype a] [DecidableEq a] where
  matrix : CMatrix a
  isHermitian : matrix.IsHermitian
  idempotent : matrix * matrix = matrix

namespace ProjectionMatrix

variable (P : ProjectionMatrix a)

/-- The complement projection `1 - P`. -/
def compl : ProjectionMatrix a where
  matrix := 1 - P.matrix
  isHermitian := Matrix.isHermitian_one.sub P.isHermitian
  idempotent := by
    calc
      (1 - P.matrix) * (1 - P.matrix)
          = 1 - P.matrix - P.matrix + P.matrix * P.matrix := by noncomm_ring
      _ = 1 - P.matrix := by
        rw [P.idempotent]
        abel

@[simp]
theorem compl_matrix :
    P.compl.matrix = 1 - P.matrix :=
  rfl

/-- Projection matrices are positive semidefinite. -/
theorem posSemidef : P.matrix.PosSemidef := by
  have hpsd : (Matrix.conjTranspose P.matrix * P.matrix).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self P.matrix
  rw [P.isHermitian, P.idempotent] at hpsd
  exact hpsd

@[simp]
theorem mulVec_idempotent (v : a → ℂ) :
    P.matrix.mulVec (P.matrix.mulVec v) = P.matrix.mulVec v := by
  calc
    P.matrix.mulVec (P.matrix.mulVec v) = (P.matrix * P.matrix).mulVec v :=
      Matrix.mulVec_mulVec v P.matrix P.matrix
    _ = P.matrix.mulVec v := by
      rw [P.idempotent]

@[simp]
theorem mul_compl :
    P.matrix * P.compl.matrix = 0 := by
  calc
    P.matrix * P.compl.matrix = P.matrix * (1 - P.matrix) := by
      simp [compl]
    _ = P.matrix - P.matrix * P.matrix := by
      noncomm_ring
    _ = 0 := by
      rw [P.idempotent]
      noncomm_ring

@[simp]
theorem compl_mul :
    P.compl.matrix * P.matrix = 0 := by
  calc
    P.compl.matrix * P.matrix = (1 - P.matrix) * P.matrix := by
      simp [compl]
    _ = P.matrix - P.matrix * P.matrix := by
      noncomm_ring
    _ = 0 := by
      rw [P.idempotent]
      noncomm_ring

@[simp]
theorem compl_posSemidef : P.compl.matrix.PosSemidef :=
  P.compl.posSemidef

end ProjectionMatrix

/-- An ordered finite sequence of projectors indexed by `Fin n`.  The order is
the source order: index `0` is `P₁`, and the last index is `P_N`. -/
abbrev ProjectionSequence (a : Type u) [Fintype a] [DecidableEq a] (n : ℕ) :=
  Fin n → ProjectionMatrix a

namespace ProjectionSequence

variable {n : ℕ} (P : ProjectionSequence a n)

/-- Matrix list in source order `P₁, ..., P_N`. -/
def matrixList : List (CMatrix a) :=
  List.ofFn fun i : Fin n => (P i).matrix

/-- Ordered product `P_N ... P₁`, with the empty product equal to `1`. -/
def reverseProduct : CMatrix a :=
  P.matrixList.reverse.prod

/-- Ordered prefix product `P_k ... P₁`, with `k = 0` giving the empty product.
The input `k : Fin (n+1)` records a prefix length bounded by the sequence length. -/
def prefixReverseProduct (k : Fin (n + 1)) : CMatrix a :=
  ((List.ofFn fun i : Fin k.val =>
    (P ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩).matrix).reverse.prod)

@[simp]
theorem matrixList_length :
    P.matrixList.length = n := by
  simp [matrixList]

@[simp]
theorem reverseProduct_zero (P : ProjectionSequence a 0) :
    P.reverseProduct = 1 := by
  simp [reverseProduct, matrixList]

@[simp]
theorem reverseProduct_one (P : ProjectionSequence a 1) :
    P.reverseProduct = (P 0).matrix := by
  simp [reverseProduct, matrixList]

@[simp]
theorem prefixReverseProduct_zero :
    P.prefixReverseProduct 0 = 1 := by
  simp [prefixReverseProduct]

theorem prefixReverseProduct_one [NeZero n] :
    P.prefixReverseProduct
        ⟨1, by exact Nat.succ_le_succ (Nat.pos_of_ne_zero (NeZero.ne n))⟩ =
      (P ⟨0, by exact Nat.pos_of_ne_zero (NeZero.ne n)⟩).matrix := by
  simp [prefixReverseProduct]

@[simp]
theorem prefixReverseProduct_last :
    P.prefixReverseProduct (Fin.last n) = P.reverseProduct := by
  simp [prefixReverseProduct, reverseProduct, matrixList]

end ProjectionSequence

namespace SequentialDecoding

variable {n : ℕ}

/-- Squared Euclidean norm of a finite complex amplitude vector, kept in
coordinate form so it can be compared directly with matrix quadratic forms. -/
def vecNormSq (v : a → ℂ) : ℝ :=
  (dotProduct (star v) v).re

omit [DecidableEq a] in
theorem vecNormSq_eq_sum_norm (v : a → ℂ) :
    vecNormSq v = ∑ i, ‖v i‖ ^ 2 := by
  unfold vecNormSq
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.conj_re, Complex.conj_im]

omit [DecidableEq a] in
theorem vecNormSq_eq_norm_sq (v : a → ℂ) :
    vecNormSq v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ a)‖ ^ 2 := by
  rw [vecNormSq_eq_sum_norm]
  exact (PiLp.norm_sq_eq_of_L2 (fun _ : a => ℂ) (WithLp.toLp 2 v)).symm

omit [DecidableEq a] in
theorem vecNormSq_nonneg (v : a → ℂ) :
    0 ≤ vecNormSq v := by
  rw [vecNormSq_eq_norm_sq]
  positivity

omit [DecidableEq a] in
theorem vecNormSq_triangle (v w : a → ℂ) :
    Real.sqrt (vecNormSq (v + w)) ≤
      Real.sqrt (vecNormSq v) + Real.sqrt (vecNormSq w) := by
  rw [vecNormSq_eq_norm_sq (v + w), vecNormSq_eq_norm_sq v, vecNormSq_eq_norm_sq w]
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  simpa [WithLp.toLp_add, abs_of_nonneg (norm_nonneg _)] using
    norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℂ a) (WithLp.toLp 2 w : EuclideanSpace ℂ a)

omit [DecidableEq a] in
theorem vecNormSq_sub_le_weighted (v w : a → ℂ) {c : ℝ} (hc : 0 < c) :
    vecNormSq (v - w) ≤ (1 + c) * vecNormSq v + (1 + c⁻¹) * vecNormSq w := by
  rw [vecNormSq_eq_norm_sq (v - w), vecNormSq_eq_norm_sq v, vecNormSq_eq_norm_sq w]
  let V : EuclideanSpace ℂ a := WithLp.toLp 2 v
  let W : EuclideanSpace ℂ a := WithLp.toLp 2 w
  have hsub : (WithLp.toLp 2 (v - w) : EuclideanSpace ℂ a) = V - W := by
    simp [V, W]
  rw [hsub]
  have hnorm : ‖V - W‖ ≤ ‖V‖ + ‖W‖ := norm_sub_le V W
  have hnorm_nonneg : 0 ≤ ‖V‖ + ‖W‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsquare : ‖V - W‖ ^ 2 ≤ (‖V‖ + ‖W‖) ^ 2 :=
    sq_le_sq' (by nlinarith [norm_nonneg (V - W), hnorm_nonneg]) hnorm
  have hcross : 2 * ‖V‖ * ‖W‖ ≤ c * ‖V‖ ^ 2 + c⁻¹ * ‖W‖ ^ 2 := by
    have hcne : c ≠ 0 := ne_of_gt hc
    let x : ℝ := ‖V‖
    let y : ℝ := ‖W‖
    have hsq : 0 ≤ c⁻¹ * (c * x - y) ^ 2 :=
      mul_nonneg (inv_nonneg.mpr (le_of_lt hc)) (sq_nonneg _)
    have hquad : 0 ≤ c * x ^ 2 - 2 * x * y + c⁻¹ * y ^ 2 := by
      convert hsq using 1
      field_simp [hcne]
      ring
    nlinarith
  calc
    ‖V - W‖ ^ 2 ≤ (‖V‖ + ‖W‖) ^ 2 := hsquare
    _ = ‖V‖ ^ 2 + 2 * ‖V‖ * ‖W‖ + ‖W‖ ^ 2 := by ring
    _ ≤ ‖V‖ ^ 2 + (c * ‖V‖ ^ 2 + c⁻¹ * ‖W‖ ^ 2) + ‖W‖ ^ 2 := by
      nlinarith
    _ = (1 + c) * ‖V‖ ^ 2 + (1 + c⁻¹) * ‖W‖ ^ 2 := by ring

omit [DecidableEq a] in
def vecInnerRe (v w : a → ℂ) : ℝ :=
  RCLike.re (inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ a)
    (WithLp.toLp 2 w : EuclideanSpace ℂ a))

omit [DecidableEq a] in
theorem vecInnerRe_eq_dotProduct (v w : a → ℂ) :
    vecInnerRe v w = (dotProduct (star v) w).re := by
  simp [vecInnerRe, inner, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

omit [DecidableEq a] in
theorem vecNormSq_sub_eq (v w : a → ℂ) :
    vecNormSq (v - w) = vecNormSq v - 2 * vecInnerRe v w + vecNormSq w := by
  rw [vecNormSq_eq_norm_sq (v - w), vecNormSq_eq_norm_sq v, vecNormSq_eq_norm_sq w]
  let V : EuclideanSpace ℂ a := WithLp.toLp 2 v
  let W : EuclideanSpace ℂ a := WithLp.toLp 2 w
  have hsub : (WithLp.toLp 2 (v - w) : EuclideanSpace ℂ a) = V - W := by
    simp [V, W]
  rw [hsub]
  simpa [vecInnerRe, V, W] using norm_sub_sq (𝕜 := ℂ) V W

omit [DecidableEq a] in
theorem vecInnerRe_self (v : a → ℂ) :
    vecInnerRe v v = vecNormSq v := by
  rw [vecInnerRe_eq_dotProduct]
  rfl

omit [DecidableEq a] in
theorem vecInnerRe_add_right (u v w : a → ℂ) :
    vecInnerRe u (v + w) = vecInnerRe u v + vecInnerRe u w := by
  unfold vecInnerRe
  rw [WithLp.toLp_add, inner_add_right]
  simp

omit [DecidableEq a] in
theorem vecInnerRe_sub_right (u v w : a → ℂ) :
    vecInnerRe u (v - w) = vecInnerRe u v - vecInnerRe u w := by
  unfold vecInnerRe
  rw [show (WithLp.toLp 2 (v - w) : EuclideanSpace ℂ a) =
      WithLp.toLp 2 v - WithLp.toLp 2 w by simp]
  rw [inner_sub_right]
  simp

omit [DecidableEq a] in
theorem vecInnerRe_sum_right {ι : Type*} [Fintype ι]
    (u : a → ℂ) (v : ι → a → ℂ) :
    vecInnerRe u (∑ i, v i) = ∑ i, vecInnerRe u (v i) := by
  unfold vecInnerRe
  rw [show (WithLp.toLp 2 (∑ i, v i) : EuclideanSpace ℂ a) =
      ∑ i, (WithLp.toLp 2 (v i) : EuclideanSpace ℂ a) by simp]
  rw [inner_sum]
  simp

omit [DecidableEq a] in
theorem two_vecInnerRe_sub_norm_le_norm (u v : a → ℂ) :
    2 * vecInnerRe u v - vecNormSq v ≤ vecNormSq u := by
  have hnonneg : 0 ≤ vecNormSq (u - v) := vecNormSq_nonneg (u - v)
  rw [vecNormSq_sub_eq] at hnonneg
  nlinarith

theorem vecInnerRe_mulVec_projection_left
    (P : ProjectionMatrix a) (v w : a → ℂ) :
    vecInnerRe (P.matrix.mulVec v) w = vecInnerRe v (P.matrix.mulVec w) := by
  rw [vecInnerRe_eq_dotProduct, vecInnerRe_eq_dotProduct]
  congr 1
  simp [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hentry : (starRingEnd ℂ) (P.matrix j i) = P.matrix i j := by
    have h := congrFun (congrFun P.isHermitian i) j
    simpa [Matrix.conjTranspose_apply] using h
  rw [hentry]
  ring_nf

theorem vecInnerRe_projection_mulVec
    (P : ProjectionMatrix a) (v w : a → ℂ) :
  vecInnerRe (P.matrix.mulVec v) (P.matrix.mulVec w) =
      vecInnerRe v (P.matrix.mulVec w) := by
  rw [vecInnerRe_mulVec_projection_left]
  rw [P.mulVec_idempotent]

theorem projection_compl_mulVec_add_mulVec
    (P : ProjectionMatrix a) (ψ : a → ℂ) :
    P.compl.matrix.mulVec ψ + P.matrix.mulVec ψ = ψ := by
  calc
    P.compl.matrix.mulVec ψ + P.matrix.mulVec ψ =
        (P.compl.matrix + P.matrix).mulVec ψ := by
          rw [Matrix.add_mulVec]
    _ = (1 : CMatrix a).mulVec ψ := by
          have hmat : P.compl.matrix + P.matrix = (1 : CMatrix a) := by
            rw [ProjectionMatrix.compl_matrix]
            abel
          rw [hmat]
    _ = ψ := by
          simp

omit [DecidableEq a] in
theorem vecNormSq_mulVec_eq_trace (M : CMatrix a) (ψ : a → ℂ) :
    vecNormSq (M.mulVec ψ) = ((M * rankOneMatrix ψ * Matrix.conjTranspose M).trace).re := by
  unfold vecNormSq
  have htrace : (M * rankOneMatrix ψ * Matrix.conjTranspose M).trace =
      dotProduct (star (M.mulVec ψ)) (M.mulVec ψ) := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, rankOneMatrix_apply,
      Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
  rw [htrace]

theorem vecNormSq_projection_mulVec_eq_rankOne_trace
    (P : ProjectionMatrix a) (ψ : a → ℂ) :
    vecNormSq (P.matrix.mulVec ψ) = ((rankOneMatrix ψ * P.matrix).trace).re := by
  rw [vecNormSq_mulVec_eq_trace]
  have htrace : (P.matrix * rankOneMatrix ψ * Matrix.conjTranspose P.matrix).trace =
      (rankOneMatrix ψ * P.matrix).trace := by
    rw [P.isHermitian]
    calc
      (P.matrix * rankOneMatrix ψ * P.matrix).trace =
          ((P.matrix * rankOneMatrix ψ) * P.matrix).trace := by rfl
      _ = (P.matrix * (P.matrix * rankOneMatrix ψ)).trace := by
        rw [Matrix.trace_mul_comm]
      _ = ((P.matrix * P.matrix) * rankOneMatrix ψ).trace := by
        rw [Matrix.mul_assoc]
      _ = (P.matrix * rankOneMatrix ψ).trace := by
        rw [P.idempotent]
      _ = (rankOneMatrix ψ * P.matrix).trace := by
        rw [Matrix.trace_mul_comm]
  rw [htrace]

theorem vecNormSq_projection_add_compl (P : ProjectionMatrix a) (ψ : a → ℂ) :
    vecNormSq (P.matrix.mulVec ψ) + vecNormSq (P.compl.matrix.mulVec ψ) =
      vecNormSq ψ := by
  rw [vecNormSq_projection_mulVec_eq_rankOne_trace P ψ,
    vecNormSq_projection_mulVec_eq_rankOne_trace P.compl ψ]
  unfold vecNormSq
  calc
    ((rankOneMatrix ψ * P.matrix).trace).re +
        ((rankOneMatrix ψ * P.compl.matrix).trace).re =
        (((rankOneMatrix ψ * P.matrix).trace) +
          ((rankOneMatrix ψ * P.compl.matrix).trace)).re := by simp
    _ = ((rankOneMatrix ψ * P.matrix + rankOneMatrix ψ * P.compl.matrix).trace).re := by
        rw [Matrix.trace_add]
    _ = ((rankOneMatrix ψ).trace).re := by
        have hmat :
            rankOneMatrix ψ * P.matrix + rankOneMatrix ψ * P.compl.matrix =
              rankOneMatrix ψ := by
          rw [ProjectionMatrix.compl_matrix]
          noncomm_ring
        rw [hmat]
    _ = (dotProduct ψ (star ψ)).re := by
        rw [rankOneMatrix_trace]
        rfl
    _ = (dotProduct (star ψ) ψ).re := by
        rw [dotProduct_comm]

theorem PureVector.vecNormSq_amp (ψ : PureVector a) :
    vecNormSq ψ.amp = 1 := by
  unfold vecNormSq
  have h := ψ.trace_rankOne_eq_one
  rw [rankOneMatrix_trace] at h
  rw [dotProduct_comm]
  exact congrArg Complex.re h

/-- The real trace of an effect against a state.  This is the convention used
by the hypothesis-testing API, repeated here for local source readability. -/
def effectTrace (ρ : State a) (E : CMatrix a) : ℝ :=
  effectAcceptProbability ρ E

theorem vecNormSq_projection_mulVec_eq_effectTrace_pure
    (P : ProjectionMatrix a) (ψ : PureVector a) :
    vecNormSq (P.matrix.mulVec ψ.amp) = effectTrace ψ.state P.matrix := by
  rw [vecNormSq_mulVec_eq_trace]
  unfold effectTrace effectAcceptProbability
  rw [PureVector.state_matrix]
  have htrace : (P.matrix * rankOneMatrix ψ.amp * Matrix.conjTranspose P.matrix).trace =
      (rankOneMatrix ψ.amp * P.matrix).trace := by
    rw [P.isHermitian]
    calc
      (P.matrix * rankOneMatrix ψ.amp * P.matrix).trace =
          ((P.matrix * rankOneMatrix ψ.amp) * P.matrix).trace := by rfl
      _ = (P.matrix * (P.matrix * rankOneMatrix ψ.amp)).trace := by
        rw [Matrix.trace_mul_comm]
      _ = ((P.matrix * P.matrix) * rankOneMatrix ψ.amp).trace := by
        rw [Matrix.mul_assoc]
      _ = (P.matrix * rankOneMatrix ψ.amp).trace := by
        rw [P.idempotent]
      _ = (rankOneMatrix ψ.amp * P.matrix).trace := by
        rw [Matrix.trace_mul_comm]
  rw [htrace]

theorem vecNormSq_projection_compl_mulVec_eq_effectTrace_pure
    (P : ProjectionMatrix a) (ψ : PureVector a) :
    vecNormSq (P.compl.matrix.mulVec ψ.amp) = effectTrace ψ.state P.compl.matrix :=
  vecNormSq_projection_mulVec_eq_effectTrace_pure P.compl ψ

theorem effectTrace_nonneg_of_posSemidef
    (ρ : State a) {E : CMatrix a} (hE : E.PosSemidef) :
    0 ≤ effectTrace ρ E := by
  unfold effectTrace effectAcceptProbability
  exact cMatrix_trace_mul_posSemidef_re_nonneg ρ.pos hE

theorem effectTrace_add (ρ : State a) (E F : CMatrix a) :
    effectTrace ρ (E + F) = effectTrace ρ E + effectTrace ρ F := by
  unfold effectTrace effectAcceptProbability
  rw [Matrix.mul_add, Matrix.trace_add]
  simp

@[simp]
theorem effectTrace_zero (ρ : State a) :
    effectTrace ρ (0 : CMatrix a) = 0 := by
  unfold effectTrace effectAcceptProbability
  simp

theorem effectTrace_projection_nonneg (ρ : State a) (P : ProjectionMatrix a) :
    0 ≤ effectTrace ρ P.matrix :=
  effectTrace_nonneg_of_posSemidef ρ P.posSemidef

theorem effectTrace_projection_compl_nonneg (ρ : State a) (P : ProjectionMatrix a) :
    0 ≤ effectTrace ρ P.compl.matrix :=
  effectTrace_nonneg_of_posSemidef ρ P.compl_posSemidef

theorem effectTrace_spectral (ρ : State a) (E : CMatrix a) :
    effectTrace ρ E =
      ∑ i : a, ρ.pos.isHermitian.eigenvalues i *
        effectTrace (ρ.spectralPureVector i).state E := by
  unfold effectTrace effectAcceptProbability
  have hmatrix := ρ.matrix_eq_sum_spectralPureVector
  conv_lhs =>
    rw [hmatrix]
  simp [Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul]

theorem projection_trace_conj_eq_effect (P : ProjectionMatrix a) (ρ : State a) :
    ((P.matrix * ρ.matrix * Matrix.conjTranspose P.matrix).trace).re =
      effectTrace ρ P.matrix := by
  unfold effectTrace effectAcceptProbability
  have htrace : (P.matrix * ρ.matrix * Matrix.conjTranspose P.matrix).trace =
      (ρ.matrix * P.matrix).trace := by
    rw [P.isHermitian]
    calc
      (P.matrix * ρ.matrix * P.matrix).trace =
          ((P.matrix * ρ.matrix) * P.matrix).trace := by rfl
      _ = (P.matrix * (P.matrix * ρ.matrix)).trace := by
        rw [Matrix.trace_mul_comm]
      _ = ((P.matrix * P.matrix) * ρ.matrix).trace := by
        rw [Matrix.mul_assoc]
      _ = (P.matrix * ρ.matrix).trace := by
        rw [P.idempotent]
      _ = (ρ.matrix * P.matrix).trace := by
        rw [Matrix.trace_mul_comm]
  rw [htrace]

theorem effectTrace_add_compl (ρ : State a) (P : ProjectionMatrix a) :
    effectTrace ρ P.matrix + effectTrace ρ P.compl.matrix = 1 := by
  unfold effectTrace effectAcceptProbability
  rw [ProjectionMatrix.compl_matrix]
  calc
    ((ρ.matrix * P.matrix).trace).re +
        ((ρ.matrix * (1 - P.matrix)).trace).re =
          (((ρ.matrix * P.matrix).trace) +
            ((ρ.matrix * (1 - P.matrix)).trace)).re := by
            simp
    _ = ((ρ.matrix * P.matrix + ρ.matrix * (1 - P.matrix)).trace).re := by
        rw [Matrix.trace_add]
    _ = ρ.matrix.trace.re := by
        have hmat : ρ.matrix * P.matrix + ρ.matrix * (1 - P.matrix) = ρ.matrix := by
          noncomm_ring
        rw [hmat]
    _ = 1 := by
        rw [ρ.trace_eq_one]
        norm_num

/-- Acceptance probability after applying the ordered projector sequence
`P_N ... P₁`. -/
def sequenceAcceptTrace (P : ProjectionSequence a n) (ρ : State a) : ℝ :=
  ((P.reverseProduct * ρ.matrix * Matrix.conjTranspose P.reverseProduct).trace).re

theorem sequenceAcceptTrace_pure_eq_vecNormSq
    (P : ProjectionSequence a n) (ψ : PureVector a) :
    sequenceAcceptTrace P ψ.state = vecNormSq (P.reverseProduct.mulVec ψ.amp) := by
  unfold sequenceAcceptTrace
  rw [vecNormSq_mulVec_eq_trace]
  rw [PureVector.state_matrix]

theorem sequenceAcceptTrace_spectral (P : ProjectionSequence a n) (ρ : State a) :
    sequenceAcceptTrace P ρ =
      ∑ i : a, ρ.pos.isHermitian.eigenvalues i *
        sequenceAcceptTrace P (ρ.spectralPureVector i).state := by
  unfold sequenceAcceptTrace
  have hmatrix := ρ.matrix_eq_sum_spectralPureVector
  conv_lhs =>
    rw [hmatrix]
  simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul]

/-- Source-shaped message error for an ordered projector sequence. -/
def sequenceError (P : ProjectionSequence a n) (ρ : State a) : ℝ :=
  1 - sequenceAcceptTrace P ρ

/-- Right-hand side of the OMW/Khatri--Wilde quantum union bound for a nonempty
projector sequence.  The sequence has length `n+1`; the final term uses the
last projector, and the sum ranges over the earlier projectors. -/
def quantumUnionBoundRHS (P : ProjectionSequence a (n + 1)) (ρ : State a) (c : ℝ) : ℝ :=
  (1 + c) * effectTrace ρ (P (Fin.last n)).compl.matrix
    + (2 + c + c⁻¹) *
      ∑ i : Fin n, effectTrace ρ (P (Fin.castSucc i)).compl.matrix

/-- Prefix before the `i`th source projector: for source index `i`, this is
`P_{i-1} ... P₁`; at `i=0` it is the empty product. -/
def prefixBefore (P : ProjectionSequence a (n + 1)) (i : Fin (n + 1)) : CMatrix a :=
  P.prefixReverseProduct ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

@[simp]
theorem prefixBefore_zero (P : ProjectionSequence a (n + 1)) :
    prefixBefore P 0 = 1 := by
  simp [prefixBefore]

theorem prefixBefore_succ
    (P : ProjectionSequence a (n + 2)) (i : Fin (n + 1)) :
    prefixBefore P i.succ =
      prefixBefore (fun j : Fin (n + 1) => P j.succ) i * (P 0).matrix := by
  simp [prefixBefore, ProjectionSequence.prefixReverseProduct, List.ofFn_succ,
    List.prod_append]

/-- Squared norm of the source missed-event vector `(1-P_i)|ψ⟩`. -/
def missedNormSq (P : ProjectionSequence a (n + 1)) (i : Fin (n + 1)) (ψ : a → ℂ) : ℝ :=
  vecNormSq ((P i).compl.matrix.mulVec ψ)

/-- Squared norm of the source auxiliary vector
`(1-P_i)(1-P_{i-1}...P_1)|ψ⟩`, used in Lemma L3. -/
def missedPrefixGapNormSq
    (P : ProjectionSequence a (n + 1)) (i : Fin (n + 1)) (ψ : a → ℂ) : ℝ :=
  vecNormSq ((P i).compl.matrix.mulVec
    ((1 - prefixBefore P i).mulVec ψ))

/-- Squared norm of the sequential missed-event vector
`(1-P_i)P_{i-1}...P_1|ψ⟩`. -/
def prefixMissedNormSq
    (P : ProjectionSequence a (n + 1)) (i : Fin (n + 1)) (ψ : a → ℂ) : ℝ :=
  vecNormSq ((P i).compl.matrix.mulVec ((prefixBefore P i).mulVec ψ))

theorem prefixMissedNormSq_zero
    (P : ProjectionSequence a (n + 1)) (ψ : a → ℂ) :
    prefixMissedNormSq P 0 ψ = missedNormSq P 0 ψ := by
  simp [prefixMissedNormSq, missedNormSq]

theorem prefixMissedNormSq_tail
    (P : ProjectionSequence a (n + 2)) (i : Fin (n + 1)) (ψ : a → ℂ) :
    prefixMissedNormSq (fun j : Fin (n + 1) => P j.succ) i
        ((P 0).matrix.mulVec ψ) =
      prefixMissedNormSq P i.succ ψ := by
  unfold prefixMissedNormSq
  rw [prefixBefore_succ P i]
  simp [Matrix.mulVec_mulVec]

theorem prefixMissedNormSq_le_weighted
    (P : ProjectionSequence a (n + 1)) (i : Fin (n + 1)) (ψ : a → ℂ)
    {c : ℝ} (hc : 0 < c) :
    prefixMissedNormSq P i ψ ≤
      (1 + c) * missedNormSq P i ψ + (1 + c⁻¹) * missedPrefixGapNormSq P i ψ := by
  unfold prefixMissedNormSq missedNormSq missedPrefixGapNormSq
  let Q : CMatrix a := (P i).compl.matrix
  let R : CMatrix a := prefixBefore P i
  have hvec :
      Q.mulVec (R.mulVec ψ) = Q.mulVec ψ - Q.mulVec ((1 - R).mulVec ψ) := by
    calc
      Q.mulVec (R.mulVec ψ) = (Q * R).mulVec ψ := Matrix.mulVec_mulVec ψ Q R
      _ = (Q - Q * (1 - R)).mulVec ψ := by
        have hmat : Q * R = Q - Q * (1 - R) := by
          noncomm_ring
        rw [hmat]
      _ = Q.mulVec ψ - (Q * (1 - R)).mulVec ψ := by
        rw [Matrix.sub_mulVec]
      _ = Q.mulVec ψ - Q.mulVec ((1 - R).mulVec ψ) := by
        rw [Matrix.mulVec_mulVec]
  rw [hvec]
  exact vecNormSq_sub_le_weighted (Q.mulVec ψ) (Q.mulVec ((1 - R).mulVec ψ)) hc

theorem prefixMissed_sum_le_weighted
    (P : ProjectionSequence a (n + 1)) (ψ : a → ℂ)
    {c : ℝ} (hc : 0 < c) :
    (∑ i : Fin (n + 1), prefixMissedNormSq P i ψ) ≤
      (1 + c) * (∑ i : Fin (n + 1), missedNormSq P i ψ)
        + (1 + c⁻¹) * (∑ i : Fin (n + 1), missedPrefixGapNormSq P i ψ) := by
  calc
    (∑ i : Fin (n + 1), prefixMissedNormSq P i ψ)
        ≤ ∑ i : Fin (n + 1),
            ((1 + c) * missedNormSq P i ψ
              + (1 + c⁻¹) * missedPrefixGapNormSq P i ψ) := by
          exact Finset.sum_le_sum fun i _ => prefixMissedNormSq_le_weighted P i ψ hc
    _ = (1 + c) * (∑ i : Fin (n + 1), missedNormSq P i ψ)
        + (1 + c⁻¹) * (∑ i : Fin (n + 1), missedPrefixGapNormSq P i ψ) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem missedPrefixGapNormSq_expand
    (P : ProjectionSequence a (n + 1)) (i : Fin (n + 1)) (ψ : a → ℂ) :
    missedPrefixGapNormSq P i ψ =
      missedNormSq P i ψ
        - 2 * vecInnerRe ψ
            ((P i).compl.matrix.mulVec ((prefixBefore P i).mulVec ψ))
        + prefixMissedNormSq P i ψ := by
  unfold missedPrefixGapNormSq missedNormSq prefixMissedNormSq
  let Q : ProjectionMatrix a := (P i).compl
  let R : CMatrix a := prefixBefore P i
  have hvec :
      Q.matrix.mulVec ((1 - R).mulVec ψ) =
        Q.matrix.mulVec ψ - Q.matrix.mulVec (R.mulVec ψ) := by
    calc
      Q.matrix.mulVec ((1 - R).mulVec ψ) = (Q.matrix * (1 - R)).mulVec ψ := by
        rw [Matrix.mulVec_mulVec]
      _ = (Q.matrix - Q.matrix * R).mulVec ψ := by
        have hmat : Q.matrix * (1 - R) = Q.matrix - Q.matrix * R := by
          noncomm_ring
        rw [hmat]
      _ = Q.matrix.mulVec ψ - (Q.matrix * R).mulVec ψ := by
        rw [Matrix.sub_mulVec]
      _ = Q.matrix.mulVec ψ - Q.matrix.mulVec (R.mulVec ψ) := by
        rw [Matrix.mulVec_mulVec]
  rw [hvec, vecNormSq_sub_eq]
  rw [vecInnerRe_projection_mulVec Q ψ (R.mulVec ψ)]

/-- Apply a source-ordered list of projectors to a vector.  For
`[P₁, ..., P_N]`, this is `P_N ... P₁ ψ`.  The list formulation is used for
inductive telescoping identities before bridging back to the `Fin`-indexed
public interface. -/
def applyProjectionList : List (ProjectionMatrix a) → (a → ℂ) → (a → ℂ)
  | [], ψ => ψ
  | P :: Ps, ψ => applyProjectionList Ps (P.matrix.mulVec ψ)

/-- Sum of the stepwise lost squared norms along a source-ordered projector
list. -/
def projectionListLossSum : List (ProjectionMatrix a) → (a → ℂ) → ℝ
  | [], _ => 0
  | P :: Ps, ψ =>
      vecNormSq (P.compl.matrix.mulVec ψ) + projectionListLossSum Ps (P.matrix.mulVec ψ)

/-- Sum of the stepwise missed vectors along a source-ordered projector list. -/
def projectionListMissedVectorSum : List (ProjectionMatrix a) → (a → ℂ) → (a → ℂ)
  | [], _ => 0
  | P :: Ps, ψ =>
      P.compl.matrix.mulVec ψ + projectionListMissedVectorSum Ps (P.matrix.mulVec ψ)

theorem projectionList_loss_telescope (Ps : List (ProjectionMatrix a)) (ψ : a → ℂ) :
    vecNormSq ψ - vecNormSq (applyProjectionList Ps ψ) =
      projectionListLossSum Ps ψ := by
  induction Ps generalizing ψ with
  | nil =>
      simp [applyProjectionList, projectionListLossSum]
  | cons P Ps ih =>
      have hdecomp :
          vecNormSq (P.matrix.mulVec ψ) + vecNormSq (P.compl.matrix.mulVec ψ) =
            vecNormSq ψ :=
        vecNormSq_projection_add_compl P ψ
      calc
        vecNormSq ψ - vecNormSq (applyProjectionList (P :: Ps) ψ)
            = vecNormSq ψ - vecNormSq (applyProjectionList Ps (P.matrix.mulVec ψ)) := by
                rfl
        _ = vecNormSq ψ - vecNormSq (P.matrix.mulVec ψ) +
              (vecNormSq (P.matrix.mulVec ψ) -
                vecNormSq (applyProjectionList Ps (P.matrix.mulVec ψ))) := by
                ring
        _ = vecNormSq (P.compl.matrix.mulVec ψ) +
              projectionListLossSum Ps (P.matrix.mulVec ψ) := by
                rw [ih]
                nlinarith
        _ = projectionListLossSum (P :: Ps) ψ := by
                rfl

theorem projectionListLossSum_nonneg (Ps : List (ProjectionMatrix a)) (ψ : a → ℂ) :
    0 ≤ projectionListLossSum Ps ψ := by
  induction Ps generalizing ψ with
  | nil =>
      simp [projectionListLossSum]
  | cons P Ps ih =>
      exact add_nonneg (vecNormSq_nonneg _) (ih _)

theorem projectionList_missedVector_telescope
    (Ps : List (ProjectionMatrix a)) (ψ : a → ℂ) :
    projectionListMissedVectorSum Ps ψ = ψ - applyProjectionList Ps ψ := by
  induction Ps generalizing ψ with
  | nil =>
      simp [projectionListMissedVectorSum, applyProjectionList]
  | cons P Ps ih =>
      calc
        projectionListMissedVectorSum (P :: Ps) ψ =
            P.compl.matrix.mulVec ψ + projectionListMissedVectorSum Ps (P.matrix.mulVec ψ) := by
              rfl
        _ = P.compl.matrix.mulVec ψ +
            (P.matrix.mulVec ψ - applyProjectionList Ps (P.matrix.mulVec ψ)) := by
              rw [ih]
        _ = ψ - applyProjectionList (P :: Ps) ψ := by
              rw [← add_sub_assoc]
              rw [projection_compl_mulVec_add_mulVec P ψ]
              rfl

theorem projectionList_cross_telescope
    (Ps : List (ProjectionMatrix a)) (ψ : a → ℂ) :
    vecInnerRe ψ (projectionListMissedVectorSum Ps ψ) =
      vecInnerRe ψ ψ - vecInnerRe ψ (applyProjectionList Ps ψ) := by
  rw [projectionList_missedVector_telescope]
  rw [vecInnerRe_sub_right]

theorem applyProjectionList_eq_reverse_prod
    (Ps : List (ProjectionMatrix a)) (ψ : a → ℂ) :
    applyProjectionList Ps ψ = ((Ps.map ProjectionMatrix.matrix).reverse.prod).mulVec ψ := by
  induction Ps generalizing ψ with
  | nil =>
      simp [applyProjectionList]
  | cons P Ps ih =>
      calc
        applyProjectionList (P :: Ps) ψ = applyProjectionList Ps (P.matrix.mulVec ψ) := by
          rfl
        _ = ((Ps.map ProjectionMatrix.matrix).reverse.prod).mulVec (P.matrix.mulVec ψ) := by
          rw [ih]
        _ = (((Ps.map ProjectionMatrix.matrix).reverse.prod) * P.matrix).mulVec ψ := by
          rw [Matrix.mulVec_mulVec]
        _ = (((P :: Ps).map ProjectionMatrix.matrix).reverse.prod).mulVec ψ := by
          simp [List.prod_append]

theorem applyProjectionList_matrixList
    (P : ProjectionSequence a n) (ψ : a → ℂ) :
    applyProjectionList (List.ofFn fun i : Fin n => P i) ψ =
      P.reverseProduct.mulVec ψ := by
  rw [applyProjectionList_eq_reverse_prod]
  rw [List.map_ofFn]
  simp [Function.comp_def, ProjectionSequence.reverseProduct, ProjectionSequence.matrixList]

theorem reverseProduct_loss_telescope
    (P : ProjectionSequence a n) (ψ : a → ℂ) :
    vecNormSq ψ - vecNormSq (P.reverseProduct.mulVec ψ) =
      projectionListLossSum (List.ofFn fun i : Fin n => P i) ψ := by
  rw [← applyProjectionList_matrixList P ψ]
  exact projectionList_loss_telescope (List.ofFn fun i : Fin n => P i) ψ

theorem reverseProduct_vecNormSq_le
    (P : ProjectionSequence a n) (ψ : a → ℂ) :
    vecNormSq (P.reverseProduct.mulVec ψ) ≤ vecNormSq ψ := by
  have htelescope := reverseProduct_loss_telescope P ψ
  have hnonneg :
      0 ≤ projectionListLossSum (List.ofFn fun i : Fin n => P i) ψ :=
    projectionListLossSum_nonneg _ _
  linarith

theorem projectionList_reverseProduct_effect_compl_posSemidef
    (Ps : List (ProjectionMatrix a)) :
    ((1 : CMatrix a) -
        Matrix.conjTranspose ((Ps.map ProjectionMatrix.matrix).reverse.prod) *
          (Ps.map ProjectionMatrix.matrix).reverse.prod).PosSemidef := by
  induction Ps with
  | nil =>
      simpa using (Matrix.PosSemidef.zero : Matrix.PosSemidef (0 : CMatrix a))
  | cons P Ps ih =>
      let R : CMatrix a := (Ps.map ProjectionMatrix.matrix).reverse.prod
      have hR :
          ((P :: Ps).map ProjectionMatrix.matrix).reverse.prod = R * P.matrix := by
        simp [R, List.prod_append]
      have hconjR :
          Matrix.conjTranspose (((P :: Ps).map ProjectionMatrix.matrix).reverse.prod) *
              ((P :: Ps).map ProjectionMatrix.matrix).reverse.prod =
            P.matrix * (Matrix.conjTranspose R * R) * P.matrix := by
        rw [hR, Matrix.conjTranspose_mul, P.isHermitian]
        noncomm_ring
      have hdecomp :
          (1 : CMatrix a) -
              Matrix.conjTranspose (((P :: Ps).map ProjectionMatrix.matrix).reverse.prod) *
                ((P :: Ps).map ProjectionMatrix.matrix).reverse.prod =
            P.compl.matrix + P.matrix * ((1 : CMatrix a) - Matrix.conjTranspose R * R) *
              P.matrix := by
        rw [hconjR, ProjectionMatrix.compl_matrix]
        calc
          (1 : CMatrix a) - P.matrix * (Matrix.conjTranspose R * R) * P.matrix =
              1 - P.matrix + P.matrix * P.matrix -
                P.matrix * (Matrix.conjTranspose R * R) * P.matrix := by
                rw [P.idempotent]
                abel
          _ = 1 - P.matrix + P.matrix * (1 - Matrix.conjTranspose R * R) *
                P.matrix := by
                noncomm_ring
      rw [hdecomp]
      refine Matrix.PosSemidef.add P.compl_posSemidef ?_
      have hmul := ih.mul_mul_conjTranspose_same P.matrix
      rw [P.isHermitian] at hmul
      simpa [R] using hmul

theorem reverseProduct_effect_le_one
    (P : ProjectionSequence a n) :
    Matrix.conjTranspose P.reverseProduct * P.reverseProduct ≤ (1 : CMatrix a) := by
  rw [Matrix.le_iff]
  simpa [ProjectionSequence.reverseProduct, ProjectionSequence.matrixList] using
    projectionList_reverseProduct_effect_compl_posSemidef
      (List.ofFn fun i : Fin n => P i)

/-- Heisenberg effect for accepting an ordered sequential projector test. -/
def sequentialAcceptEffect (P : ProjectionSequence a n) : CMatrix a :=
  Matrix.conjTranspose P.reverseProduct * P.reverseProduct

theorem sequentialAcceptEffect_posSemidef (P : ProjectionSequence a n) :
    (sequentialAcceptEffect P).PosSemidef := by
  unfold sequentialAcceptEffect
  exact Matrix.posSemidef_conjTranspose_mul_self P.reverseProduct

theorem sequentialAcceptEffect_le_one (P : ProjectionSequence a n) :
    sequentialAcceptEffect P ≤ (1 : CMatrix a) := by
  unfold sequentialAcceptEffect
  exact reverseProduct_effect_le_one P

theorem sequentialAcceptEffect_compl_posSemidef (P : ProjectionSequence a n) :
    ((1 : CMatrix a) - sequentialAcceptEffect P).PosSemidef := by
  simpa [Matrix.le_iff] using sequentialAcceptEffect_le_one P

/-- Binary POVM that accepts an ordered sequential projector test.  The `true`
outcome is the coherent sequential accept effect `RᴴR`; the `false` outcome is
its complement. -/
def sequentialAcceptPOVM (P : ProjectionSequence a n) : POVM Bool a where
  effects accept := if accept then sequentialAcceptEffect P else 1 - sequentialAcceptEffect P
  pos accept := by
    by_cases h : accept
    · simp [h, sequentialAcceptEffect_posSemidef P]
    · simp [h, sequentialAcceptEffect_compl_posSemidef P]
  sum_eq_one := by
    rw [Fintype.sum_bool]
    simp [sequentialAcceptEffect]

@[simp]
theorem sequentialAcceptPOVM_true_effect (P : ProjectionSequence a n) :
    (sequentialAcceptPOVM P).effects true = sequentialAcceptEffect P := by
  simp [sequentialAcceptPOVM]

@[simp]
theorem sequentialAcceptPOVM_false_effect (P : ProjectionSequence a n) :
    (sequentialAcceptPOVM P).effects false = 1 - sequentialAcceptEffect P := by
  simp [sequentialAcceptPOVM]

theorem sequenceAcceptTrace_eq_effectTrace_accept (P : ProjectionSequence a n)
    (ρ : State a) :
    sequenceAcceptTrace P ρ =
      effectTrace ρ (sequentialAcceptEffect P) := by
  unfold sequenceAcceptTrace effectTrace effectAcceptProbability sequentialAcceptEffect
  calc
    ((P.reverseProduct * ρ.matrix * Matrix.conjTranspose P.reverseProduct).trace).re =
        ((ρ.matrix * Matrix.conjTranspose P.reverseProduct * P.reverseProduct).trace).re := by
          have h₁ :
              (P.reverseProduct * ρ.matrix * Matrix.conjTranspose P.reverseProduct).trace =
                (Matrix.conjTranspose P.reverseProduct * P.reverseProduct *
                  ρ.matrix).trace :=
            Matrix.trace_mul_cycle P.reverseProduct ρ.matrix
              (Matrix.conjTranspose P.reverseProduct)
          have h₂ :
              (Matrix.conjTranspose P.reverseProduct * P.reverseProduct *
                  ρ.matrix).trace =
                (ρ.matrix * (Matrix.conjTranspose P.reverseProduct) *
                  P.reverseProduct).trace :=
            Matrix.trace_mul_cycle (Matrix.conjTranspose P.reverseProduct)
              P.reverseProduct ρ.matrix
          exact congrArg Complex.re (h₁.trans h₂)
    _ = ((ρ.matrix * (Matrix.conjTranspose P.reverseProduct * P.reverseProduct)).trace).re := by
          rw [Matrix.mul_assoc]

theorem sequentialAcceptPOVM_true_prob_eq_sequenceAcceptTrace
    (P : ProjectionSequence a n) (ρ : State a) :
    ((sequentialAcceptPOVM P).prob ρ true : ℝ) =
      sequenceAcceptTrace P ρ := by
  rw [POVM.prob_eq_trace_re]
  exact (sequenceAcceptTrace_eq_effectTrace_accept P ρ).symm

theorem sequentialAcceptPOVM_error_eq_sequenceError
    (P : ProjectionSequence a n) (ρ : State a) :
    1 - ((sequentialAcceptPOVM P).prob ρ true : ℝ) =
      sequenceError P ρ := by
  rw [sequentialAcceptPOVM_true_prob_eq_sequenceAcceptTrace]
  rfl

theorem sequentialAcceptPOVM_error_le_sequenceError
    (P : ProjectionSequence a n) (ρ : State a) :
    1 - ((sequentialAcceptPOVM P).prob ρ true : ℝ) ≤
      sequenceError P ρ := by
  rw [sequentialAcceptPOVM_error_eq_sequenceError]

/-! ## Message-indexed sequential decoder POVM -/

/-- Base effects of a sequential decoder over an ordered list of accept
projectors.  The head effect accepts the first projector immediately; later
effects are conjugated by the earlier rejection projector. -/
def sequentialDecoderEffectsList : List (ProjectionMatrix a) → List (CMatrix a)
  | [] => []
  | P :: Ps =>
      P.matrix ::
        (sequentialDecoderEffectsList Ps).map
          (fun E => P.compl.matrix * E * P.compl.matrix)

/-- Failure effect of rejecting every projector in the ordered sequential
decoder. -/
def sequentialDecoderFailureEffect : List (ProjectionMatrix a) → CMatrix a
  | [] => 1
  | P :: Ps =>
      P.compl.matrix * sequentialDecoderFailureEffect Ps * P.compl.matrix

@[simp]
theorem sequentialDecoderEffectsList_length (Ps : List (ProjectionMatrix a)) :
    (sequentialDecoderEffectsList Ps).length = Ps.length := by
  induction Ps with
  | nil => simp [sequentialDecoderEffectsList]
  | cons P Ps ih => simp [sequentialDecoderEffectsList, ih]

theorem sequentialDecoderFailureEffect_posSemidef
    (Ps : List (ProjectionMatrix a)) :
    (sequentialDecoderFailureEffect Ps).PosSemidef := by
  induction Ps with
  | nil =>
      simpa [sequentialDecoderFailureEffect] using
        (Matrix.PosSemidef.one : Matrix.PosSemidef (1 : CMatrix a))
  | cons P Ps ih =>
      have hmul := ih.mul_mul_conjTranspose_same P.compl.matrix
      rw [P.compl.isHermitian] at hmul
      simpa [sequentialDecoderFailureEffect] using hmul

theorem sequentialDecoderEffectsList_get_posSemidef
    (Ps : List (ProjectionMatrix a))
    (i : Fin (sequentialDecoderEffectsList Ps).length) :
    ((sequentialDecoderEffectsList Ps).get i).PosSemidef := by
  induction Ps with
  | nil =>
      exact Fin.elim0 (Fin.cast (by simp [sequentialDecoderEffectsList]) i)
  | cons P Ps ih =>
      cases i using Fin.cases with
      | zero =>
          simpa [sequentialDecoderEffectsList] using P.posSemidef
      | succ i =>
          let i' : Fin (sequentialDecoderEffectsList Ps).length :=
            ⟨i.val, by simpa using i.isLt⟩
          have htail :
              ((sequentialDecoderEffectsList Ps).get i').PosSemidef := ih i'
          have hmul := htail.mul_mul_conjTranspose_same P.compl.matrix
          rw [P.compl.isHermitian] at hmul
          simpa [sequentialDecoderEffectsList, i'] using hmul

theorem sequentialDecoderEffectsList_get_succ
    (P : ProjectionMatrix a) (Ps : List (ProjectionMatrix a))
    (i : ℕ) (hi : i < (sequentialDecoderEffectsList Ps).length) :
    (sequentialDecoderEffectsList (P :: Ps)).get
        ⟨i + 1, by
          have hiPs : i < Ps.length := by
            simpa [sequentialDecoderEffectsList_length] using hi
          simp [sequentialDecoderEffectsList, hiPs]⟩ =
      P.compl.matrix *
        (sequentialDecoderEffectsList Ps).get ⟨i, hi⟩ *
          P.compl.matrix := by
  simp [sequentialDecoderEffectsList]

theorem sequentialDecoderEffectsList_conj_sum
    (C : CMatrix a) (Es : List (CMatrix a)) :
    (Es.map fun E => C * E * C).sum = C * Es.sum * C := by
  induction Es with
  | nil =>
      simp
  | cons E Es ih =>
      simp [ih]
      noncomm_ring

theorem sequentialDecoderEffectsList_sum_add_failure
    (Ps : List (ProjectionMatrix a)) :
    (sequentialDecoderEffectsList Ps).sum + sequentialDecoderFailureEffect Ps =
      (1 : CMatrix a) := by
  induction Ps with
  | nil =>
      simp [sequentialDecoderEffectsList, sequentialDecoderFailureEffect]
  | cons P Ps ih =>
      simp [sequentialDecoderEffectsList, sequentialDecoderFailureEffect,
        sequentialDecoderEffectsList_conj_sum]
      calc
        P.matrix +
            P.compl.matrix * (sequentialDecoderEffectsList Ps).sum * P.compl.matrix +
              P.compl.matrix * sequentialDecoderFailureEffect Ps * P.compl.matrix =
          P.matrix +
            P.compl.matrix *
              ((sequentialDecoderEffectsList Ps).sum + sequentialDecoderFailureEffect Ps) *
                P.compl.matrix := by
              noncomm_ring
        _ = P.matrix + P.compl.matrix * (1 : CMatrix a) * P.compl.matrix := by
              rw [ih]
        _ = P.matrix + P.compl.matrix := by
              rw [Matrix.mul_one, P.compl.idempotent]
        _ = 1 := by
              rw [ProjectionMatrix.compl_matrix]
              abel

def sequentialDecoderProjectorList (A : ProjectionSequence a (n + 1)) :
    List (ProjectionMatrix a) :=
  List.ofFn fun i : Fin (n + 1) => A i

def sequentialDecoderBaseEffect (A : ProjectionSequence a (n + 1))
    (j : Fin (n + 1)) : CMatrix a :=
  (sequentialDecoderEffectsList (sequentialDecoderProjectorList A)).get
    ⟨j.val, by
      simpa [sequentialDecoderProjectorList] using j.isLt⟩

def sequentialDecoderFailure (A : ProjectionSequence a (n + 1)) : CMatrix a :=
  sequentialDecoderFailureEffect (sequentialDecoderProjectorList A)

def sequentialDecoderEffect (A : ProjectionSequence a (n + 1))
    (j : Fin (n + 1)) : CMatrix a :=
  sequentialDecoderBaseEffect A j +
    if j = 0 then sequentialDecoderFailure A else 0

theorem sequentialDecoderBaseEffect_posSemidef
    (A : ProjectionSequence a (n + 1)) (j : Fin (n + 1)) :
    (sequentialDecoderBaseEffect A j).PosSemidef := by
  unfold sequentialDecoderBaseEffect
  exact sequentialDecoderEffectsList_get_posSemidef
    (sequentialDecoderProjectorList A)
    ⟨j.val, by simpa [sequentialDecoderProjectorList] using j.isLt⟩

theorem sequentialDecoderFailure_posSemidef
    (A : ProjectionSequence a (n + 1)) :
    (sequentialDecoderFailure A).PosSemidef := by
  unfold sequentialDecoderFailure
  exact sequentialDecoderFailureEffect_posSemidef _

theorem sequentialDecoderEffect_posSemidef
    (A : ProjectionSequence a (n + 1)) (j : Fin (n + 1)) :
    (sequentialDecoderEffect A j).PosSemidef := by
  unfold sequentialDecoderEffect
  refine Matrix.PosSemidef.add (sequentialDecoderBaseEffect_posSemidef A j) ?_
  by_cases h : j = 0
  · simp [h, sequentialDecoderFailure_posSemidef A]
  · simp [h, Matrix.PosSemidef.zero]

theorem sequentialDecoderBaseEffect_sum
    (A : ProjectionSequence a (n + 1)) :
    (∑ j : Fin (n + 1), sequentialDecoderBaseEffect A j) =
      (sequentialDecoderEffectsList (sequentialDecoderProjectorList A)).sum := by
  let Es := sequentialDecoderEffectsList (sequentialDecoderProjectorList A)
  have hlen : n + 1 = Es.length := by
    simp [Es, sequentialDecoderProjectorList]
  let e : Fin (n + 1) ≃ Fin Es.length := finCongr hlen
  have hsum_equiv :
      (∑ j : Fin (n + 1), Es[j.val]) =
        ∑ j : Fin Es.length, Es[j.val] := by
    simpa [e] using
      (Finset.sum_equiv e (s := Finset.univ) (t := Finset.univ)
        (f := fun j : Fin (n + 1) => Es[j.val])
        (g := fun j : Fin Es.length => Es[j.val])
        (fun _ => by simp)
        (fun j _ => by simp [e]))
  calc
    (∑ j : Fin (n + 1), sequentialDecoderBaseEffect A j) =
        ∑ j : Fin (n + 1), Es[j.val] := by
          simp [sequentialDecoderBaseEffect, Es]
    _ = ∑ j : Fin Es.length, Es[j.val] := hsum_equiv
    _ = Es.sum := Fin.sum_univ_getElem Es

theorem sequentialDecoderEffect_sum
    (A : ProjectionSequence a (n + 1)) :
    (∑ j : Fin (n + 1), sequentialDecoderEffect A j) = (1 : CMatrix a) := by
  unfold sequentialDecoderEffect
  rw [Finset.sum_add_distrib, sequentialDecoderBaseEffect_sum]
  have hfailure :
      (∑ j : Fin (n + 1), (if j = 0 then sequentialDecoderFailure A else 0)) =
        sequentialDecoderFailure A := by
    simp
  rw [hfailure]
  simpa [sequentialDecoderFailure] using
    sequentialDecoderEffectsList_sum_add_failure (sequentialDecoderProjectorList A)

/-- Message-indexed POVM obtained by a sequential ordered decoder.  The
leftover reject-all effect is assigned to message `0`, which can only increase
that message's success probability and keeps the decoder a genuine POVM over
the message register. -/
def sequentialDecoderPOVM (A : ProjectionSequence a (n + 1)) :
    POVM (Fin (n + 1)) a where
  effects := sequentialDecoderEffect A
  pos := sequentialDecoderEffect_posSemidef A
  sum_eq_one := sequentialDecoderEffect_sum A

@[simp]
theorem sequentialDecoderPOVM_effects
    (A : ProjectionSequence a (n + 1)) (j : Fin (n + 1)) :
    (sequentialDecoderPOVM A).effects j = sequentialDecoderEffect A j :=
  rfl

theorem projectionListLossSum_ofFn
    (P : ProjectionSequence a (n + 1)) (ψ : a → ℂ) :
    projectionListLossSum (List.ofFn fun i : Fin (n + 1) => P i) ψ =
      ∑ i : Fin (n + 1), prefixMissedNormSq P i ψ := by
  induction n generalizing ψ with
  | zero =>
      simp [projectionListLossSum, prefixMissedNormSq]
  | succ n ih =>
      rw [List.ofFn_succ, projectionListLossSum, Fin.sum_univ_succ]
      rw [prefixMissedNormSq_zero P ψ]
      rw [ih (fun j : Fin (n + 1) => P j.succ) ((P 0).matrix.mulVec ψ)]
      simp [prefixMissedNormSq_tail, missedNormSq]

theorem projectionListMissedVectorSum_ofFn
    (P : ProjectionSequence a (n + 1)) (ψ : a → ℂ) :
    projectionListMissedVectorSum (List.ofFn fun i : Fin (n + 1) => P i) ψ =
      ∑ i : Fin (n + 1),
        (P i).compl.matrix.mulVec ((prefixBefore P i).mulVec ψ) := by
  induction n generalizing ψ with
  | zero =>
      simp [projectionListMissedVectorSum, prefixBefore]
  | succ n ih =>
      rw [List.ofFn_succ, projectionListMissedVectorSum, Fin.sum_univ_succ]
      rw [ih (fun j : Fin (n + 1) => P j.succ) ((P 0).matrix.mulVec ψ)]
      simp [prefixBefore_succ, Matrix.mulVec_mulVec]

theorem prefixMissedVector_cross_telescope
    (P : ProjectionSequence a (n + 1)) (ψ : a → ℂ) :
    (∑ i : Fin (n + 1),
        vecInnerRe ψ ((P i).compl.matrix.mulVec ((prefixBefore P i).mulVec ψ))) =
      vecInnerRe ψ ψ - vecInnerRe ψ (P.reverseProduct.mulVec ψ) := by
  have hsum := projectionListMissedVectorSum_ofFn P ψ
  have hcross := projectionList_cross_telescope
    (List.ofFn fun i : Fin (n + 1) => P i) ψ
  rw [hsum] at hcross
  rw [vecInnerRe_sum_right] at hcross
  rw [applyProjectionList_matrixList P ψ] at hcross
  exact hcross

theorem missedPrefixGap_sum_expand
    (P : ProjectionSequence a (n + 1)) (ψ : a → ℂ) :
    (∑ i : Fin (n + 1), missedPrefixGapNormSq P i ψ) =
      (∑ i : Fin (n + 1), missedNormSq P i ψ)
        - 2 *
          (∑ i : Fin (n + 1),
            vecInnerRe ψ ((P i).compl.matrix.mulVec ((prefixBefore P i).mulVec ψ)))
        + (∑ i : Fin (n + 1), prefixMissedNormSq P i ψ) := by
  calc
    (∑ i : Fin (n + 1), missedPrefixGapNormSq P i ψ)
        = ∑ i : Fin (n + 1),
            (missedNormSq P i ψ
              - 2 * vecInnerRe ψ
                  ((P i).compl.matrix.mulVec ((prefixBefore P i).mulVec ψ))
              + prefixMissedNormSq P i ψ) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [missedPrefixGapNormSq_expand]
    _ = (∑ i : Fin (n + 1), missedNormSq P i ψ)
        - 2 *
          (∑ i : Fin (n + 1),
            vecInnerRe ψ ((P i).compl.matrix.mulVec ((prefixBefore P i).mulVec ψ)))
        + (∑ i : Fin (n + 1), prefixMissedNormSq P i ψ) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem reverseProduct_fixed_by_last
    (P : ProjectionSequence a (n + 1)) (ψ : a → ℂ) :
    (P (Fin.last n)).matrix.mulVec (P.reverseProduct.mulVec ψ) =
      P.reverseProduct.mulVec ψ := by
  rw [ProjectionSequence.reverseProduct, ProjectionSequence.matrixList, List.ofFn_succ']
  simp [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, (P (Fin.last n)).idempotent]

theorem pureVector_loss_eq_prefixMissed_sum
    (P : ProjectionSequence a (n + 1)) (ψ : PureVector a) :
    1 - vecNormSq (P.reverseProduct.mulVec ψ.amp) =
      ∑ i : Fin (n + 1), prefixMissedNormSq P i ψ.amp := by
  rw [← PureVector.vecNormSq_amp ψ]
  rw [reverseProduct_loss_telescope P ψ.amp]
  exact projectionListLossSum_ofFn P ψ.amp

theorem missedPrefixGap_sum_le_early
    (P : ProjectionSequence a (n + 1)) (ψ : PureVector a) :
    (∑ i : Fin (n + 1), missedPrefixGapNormSq P i ψ.amp) ≤
      ∑ i : Fin n, missedNormSq P (Fin.castSucc i) ψ.amp := by
  rw [missedPrefixGap_sum_expand]
  rw [prefixMissedVector_cross_telescope]
  rw [← pureVector_loss_eq_prefixMissed_sum]
  rw [vecInnerRe_self, PureVector.vecNormSq_amp]
  rw [Fin.sum_univ_castSucc]
  have hlast_decomp :
      missedNormSq P (Fin.last n) ψ.amp =
        1 - vecNormSq ((P (Fin.last n)).matrix.mulVec ψ.amp) := by
    unfold missedNormSq
    have hdecomp := vecNormSq_projection_add_compl (P (Fin.last n)) ψ.amp
    rw [PureVector.vecNormSq_amp] at hdecomp
    nlinarith
  rw [hlast_decomp]
  have hfixed :
      (P (Fin.last n)).matrix.mulVec (P.reverseProduct.mulVec ψ.amp) =
        P.reverseProduct.mulVec ψ.amp :=
    reverseProduct_fixed_by_last P ψ.amp
  have hinner :
      vecInnerRe ψ.amp (P.reverseProduct.mulVec ψ.amp) =
        vecInnerRe ((P (Fin.last n)).matrix.mulVec ψ.amp)
          (P.reverseProduct.mulVec ψ.amp) := by
    rw [vecInnerRe_mulVec_projection_left]
    rw [hfixed]
  have hquad := two_vecInnerRe_sub_norm_le_norm
    ((P (Fin.last n)).matrix.mulVec ψ.amp) (P.reverseProduct.mulVec ψ.amp)
  rw [← hinner] at hquad
  nlinarith

/-- Vector-form right-hand side of the quantum union bound.  This is the
larger RHS used in Theorem `thm-q_union_bd` after the sharper pure-vector T1
estimate has been averaged over a spectral decomposition. -/
def quantumUnionBoundVectorRHS
    (P : ProjectionSequence a (n + 1)) (ψ : a → ℂ) (c : ℝ) : ℝ :=
  (1 + c) * missedNormSq P (Fin.last n) ψ
    + (2 + c + c⁻¹) *
      ∑ i : Fin n, missedNormSq P (Fin.castSucc i) ψ

/-- Vector-form source theorem for the OMW/Khatri--Wilde quantum union bound. -/
def VectorQuantumUnionBound (P : ProjectionSequence a (n + 1)) : Prop :=
  ∀ ψ : PureVector a, ∀ c : ℝ, 0 < c →
    1 - vecNormSq (P.reverseProduct.mulVec ψ.amp) ≤
      quantumUnionBoundVectorRHS P ψ.amp c

/-- OMW/Khatri--Wilde quantum union bound in pure-vector form.  This is the
finite-dimensional vector proof route behind `thm-q_union_bd`: the sequential
loss telescope is bounded by the source weighted missed/gap inequality, and
the auxiliary gap sum is controlled by the earlier missed-detection terms. -/
theorem vectorQuantumUnionBound (P : ProjectionSequence a (n + 1)) :
    VectorQuantumUnionBound P := by
  intro ψ c hc
  rw [pureVector_loss_eq_prefixMissed_sum]
  have hweighted := prefixMissed_sum_le_weighted P ψ.amp hc
  have hgap := missedPrefixGap_sum_le_early P ψ
  have hcoef : 0 ≤ 1 + c⁻¹ := by
    have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
    linarith
  calc
    (∑ i : Fin (n + 1), prefixMissedNormSq P i ψ.amp)
        ≤ (1 + c) * (∑ i : Fin (n + 1), missedNormSq P i ψ.amp)
          + (1 + c⁻¹) *
            (∑ i : Fin (n + 1), missedPrefixGapNormSq P i ψ.amp) := hweighted
    _ ≤ (1 + c) * (∑ i : Fin (n + 1), missedNormSq P i ψ.amp)
          + (1 + c⁻¹) *
            (∑ i : Fin n, missedNormSq P (Fin.castSucc i) ψ.amp) := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hgap hcoef)
    _ = quantumUnionBoundVectorRHS P ψ.amp c := by
          unfold quantumUnionBoundVectorRHS
          rw [Fin.sum_univ_castSucc]
          ring

theorem quantumUnionBoundRHS_pure_eq_vector
    (P : ProjectionSequence a (n + 1)) (ψ : PureVector a) (c : ℝ) :
    quantumUnionBoundRHS P ψ.state c =
      quantumUnionBoundVectorRHS P ψ.amp c := by
  unfold quantumUnionBoundRHS quantumUnionBoundVectorRHS missedNormSq
  rw [← vecNormSq_projection_compl_mulVec_eq_effectTrace_pure (P (Fin.last n)) ψ]
  have hsum :
      (∑ i : Fin n, effectTrace ψ.state (P (Fin.castSucc i)).compl.matrix) =
        ∑ i : Fin n, vecNormSq ((P (Fin.castSucc i)).compl.matrix.mulVec ψ.amp) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact (vecNormSq_projection_compl_mulVec_eq_effectTrace_pure (P (Fin.castSucc i)) ψ).symm
  rw [hsum]

/-- The source-shaped finite matrix quantum union bound as a reusable
predicate.  Proving this predicate from the projector hypotheses is the
mathematical core of the OMW Appendix route. -/
def QuantumUnionBound (P : ProjectionSequence a (n + 1)) : Prop :=
  ∀ ρ : State a, ∀ c : ℝ, 0 < c →
    sequenceError P ρ ≤ quantumUnionBoundRHS P ρ c

/-- Pure-state version of the source-shaped quantum union bound.  The OMW
appendix first proves a vector theorem and then averages over a spectral
decomposition of `ρ`; this predicate isolates the vector theorem. -/
def PureQuantumUnionBound (P : ProjectionSequence a (n + 1)) : Prop :=
  ∀ ψ : PureVector a, ∀ c : ℝ, 0 < c →
    sequenceError P ψ.state ≤ quantumUnionBoundRHS P ψ.state c

theorem PureQuantumUnionBound.of_vector
    (P : ProjectionSequence a (n + 1)) (hP : VectorQuantumUnionBound P) :
    PureQuantumUnionBound P := by
  intro ψ c hc
  unfold sequenceError
  rw [sequenceAcceptTrace_pure_eq_vecNormSq,
    quantumUnionBoundRHS_pure_eq_vector P ψ c]
  exact hP ψ c hc

theorem sequenceError_spectral (P : ProjectionSequence a n) (ρ : State a) :
    sequenceError P ρ =
      ∑ i : a, ρ.pos.isHermitian.eigenvalues i *
        sequenceError P (ρ.spectralPureVector i).state := by
  unfold sequenceError
  rw [sequenceAcceptTrace_spectral]
  conv_lhs =>
    rw [← ρ.sum_eigenvalues_eq_one]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

theorem quantumUnionBoundRHS_spectral
    (P : ProjectionSequence a (n + 1)) (ρ : State a) (c : ℝ) :
    quantumUnionBoundRHS P ρ c =
      ∑ i : a, ρ.pos.isHermitian.eigenvalues i *
        quantumUnionBoundRHS P (ρ.spectralPureVector i).state c := by
  let lam : a → ℝ := fun i => ρ.pos.isHermitian.eigenvalues i
  let last : a → ℝ := fun i =>
    effectTrace (ρ.spectralPureVector i).state (P (Fin.last n)).compl.matrix
  let early : a → Fin n → ℝ := fun i j =>
    effectTrace (ρ.spectralPureVector i).state (P (Fin.castSucc j)).compl.matrix
  have hlast :
      effectTrace ρ (P (Fin.last n)).compl.matrix =
        ∑ i : a, lam i * last i := by
    simpa [lam, last] using effectTrace_spectral ρ (P (Fin.last n)).compl.matrix
  have hearly :
      (∑ j : Fin n, effectTrace ρ (P (Fin.castSucc j)).compl.matrix) =
        ∑ i : a, lam i * ∑ j : Fin n, early i j := by
    calc
      (∑ j : Fin n, effectTrace ρ (P (Fin.castSucc j)).compl.matrix)
          = ∑ j : Fin n, ∑ i : a, lam i * early i j := by
            refine Finset.sum_congr rfl ?_
            intro j _
            simpa [lam, early] using effectTrace_spectral ρ (P (Fin.castSucc j)).compl.matrix
      _ = ∑ i : a, lam i * ∑ j : Fin n, early i j := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
  unfold quantumUnionBoundRHS
  rw [hlast, hearly]
  change (1 + c) * (∑ i : a, lam i * last i) +
      (2 + c + c⁻¹) * (∑ i : a, lam i * ∑ j : Fin n, early i j) =
    ∑ i : a, lam i *
      ((1 + c) * last i + (2 + c + c⁻¹) * ∑ j : Fin n, early i j)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- Spectral-decomposition lift from the pure-vector OMW theorem to the
source-shaped state theorem.  This formalizes the reduction in
Khatri--Wilde 2024, `EA_capacity.tex:1706-1728`; it turns a pure-vector
union bound into the state theorem by averaging over a spectral decomposition. -/
theorem quantumUnionBound_of_pure
    (P : ProjectionSequence a (n + 1)) (hP : PureQuantumUnionBound P) :
    QuantumUnionBound P := by
  intro ρ c hc
  rw [sequenceError_spectral P ρ, quantumUnionBoundRHS_spectral P ρ c]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hP (ρ.spectralPureVector i) c hc)
      (ρ.pos.eigenvalues_nonneg i)

/-- End-to-end reduction from the vector OMW theorem to the state theorem used
by the sequential decoder. -/
theorem quantumUnionBound_of_vector
    (P : ProjectionSequence a (n + 1)) (hP : VectorQuantumUnionBound P) :
    QuantumUnionBound P :=
  quantumUnionBound_of_pure P (PureQuantumUnionBound.of_vector P hP)

/-- Source-shaped OMW/Khatri--Wilde quantum union bound for finite projector
sequences and arbitrary finite-dimensional normalized states. -/
theorem quantumUnionBound (P : ProjectionSequence a (n + 1)) :
    QuantumUnionBound P :=
  quantumUnionBound_of_vector P (vectorQuantumUnionBound P)

theorem missedNormSq_eq_effectTrace_pure
    (P : ProjectionSequence a (n + 1)) (i : Fin (n + 1)) (ψ : PureVector a) :
    missedNormSq P i ψ.amp = effectTrace ψ.state (P i).compl.matrix :=
  vecNormSq_projection_compl_mulVec_eq_effectTrace_pure (P i) ψ

theorem vectorQuantumUnionBound_one (P : ProjectionSequence a 1) :
    VectorQuantumUnionBound P := by
  intro ψ c hc
  have haccept :
      vecNormSq (P.reverseProduct.mulVec ψ.amp) =
        effectTrace ψ.state (P 0).matrix := by
    rw [ProjectionSequence.reverseProduct_one]
    exact vecNormSq_projection_mulVec_eq_effectTrace_pure (P 0) ψ
  have hmiss :
      missedNormSq P 0 ψ.amp = effectTrace ψ.state (P 0).compl.matrix :=
    missedNormSq_eq_effectTrace_pure P 0 ψ
  have hdecomp : effectTrace ψ.state (P 0).matrix +
      effectTrace ψ.state (P 0).compl.matrix = 1 :=
    effectTrace_add_compl ψ.state (P 0)
  have hmiss_nonneg : 0 ≤ missedNormSq P 0 ψ.amp := by
    rw [hmiss]
    exact effectTrace_projection_compl_nonneg ψ.state (P 0)
  have hrhs : quantumUnionBoundVectorRHS P ψ.amp c =
      (1 + c) * missedNormSq P 0 ψ.amp := by
    simp [quantumUnionBoundVectorRHS]
  rw [haccept, hrhs]
  have hmiss' : 1 - effectTrace ψ.state (P 0).matrix = missedNormSq P 0 ψ.amp := by
    rw [hmiss]
    nlinarith
  rw [hmiss']
  have hmul : 0 ≤ c * missedNormSq P 0 ψ.amp :=
    mul_nonneg (le_of_lt hc) hmiss_nonneg
  nlinarith

theorem quantumUnionBound_one (P : ProjectionSequence a 1) :
    QuantumUnionBound P := by
  intro ρ c hc
  have haccept : sequenceAcceptTrace P ρ = effectTrace ρ (P 0).matrix := by
    unfold sequenceAcceptTrace
    rw [ProjectionSequence.reverseProduct_one]
    exact projection_trace_conj_eq_effect (P 0) ρ
  have hdecomp : effectTrace ρ (P 0).matrix + effectTrace ρ (P 0).compl.matrix = 1 :=
    effectTrace_add_compl ρ (P 0)
  have hmiss_nonneg : 0 ≤ effectTrace ρ (P 0).compl.matrix :=
    effectTrace_projection_compl_nonneg ρ (P 0)
  have hrhs : quantumUnionBoundRHS P ρ c =
      (1 + c) * effectTrace ρ (P 0).compl.matrix := by
    simp [quantumUnionBoundRHS]
  unfold sequenceError
  rw [haccept]
  have hmiss : 1 - effectTrace ρ (P 0).matrix = effectTrace ρ (P 0).compl.matrix := by
    nlinarith
  rw [hmiss, hrhs]
  have hmul : 0 ≤ c * effectTrace ρ (P 0).compl.matrix :=
    mul_nonneg (le_of_lt hc) hmiss_nonneg
  nlinarith

/-- Given accept projectors for messages `0, ..., n`, the sequential decoder
tests the complements of earlier acceptors and then the final acceptor. -/
def decoderTestSequence (A : ProjectionSequence a (n + 1)) :
    ProjectionSequence a (n + 1) :=
  fun i =>
    if h : i = Fin.last n then
      A (Fin.last n)
    else
      (A (Fin.castSucc ⟨i.val, by
        have hi : i.val < n + 1 := i.isLt
        have hne : i.val ≠ n := by
          intro hv
          apply h
          exact Fin.ext hv
        omega⟩)).compl

/-- Source-shaped sequential-decoding error RHS:
miss the transmitted projector, plus false-alarm traces for earlier messages. -/
def decoderErrorRHS (A : ProjectionSequence a (n + 1)) (ρ : State a) (c : ℝ) : ℝ :=
  (1 + c) * effectTrace ρ (A (Fin.last n)).compl.matrix
    + (2 + c + c⁻¹) *
      ∑ i : Fin n, effectTrace ρ (A (Fin.castSucc i)).matrix

@[simp]
theorem decoderTestSequence_last (A : ProjectionSequence a (n + 1)) :
    decoderTestSequence A (Fin.last n) = A (Fin.last n) := by
  simp [decoderTestSequence]

@[simp]
theorem decoderTestSequence_castSucc (A : ProjectionSequence a (n + 1)) (i : Fin n) :
    decoderTestSequence A (Fin.castSucc i) = (A (Fin.castSucc i)).compl := by
  simp [decoderTestSequence]

theorem sequentialDecoderBaseEffect_last_tail
    (A : ProjectionSequence a (n + 2)) :
    sequentialDecoderBaseEffect A (Fin.last (n + 1)) =
      (A 0).compl.matrix *
        sequentialDecoderBaseEffect (fun i : Fin (n + 1) => A i.succ) (Fin.last n) *
          (A 0).compl.matrix := by
  simpa [sequentialDecoderBaseEffect, sequentialDecoderProjectorList, List.ofFn_succ] using
    sequentialDecoderEffectsList_get_succ (A 0)
      (List.ofFn fun i : Fin (n + 1) => A i.succ) n
      (by simp [sequentialDecoderEffectsList])

theorem sequentialAcceptEffect_decoderTestSequence_tail
    (A : ProjectionSequence a (n + 2)) :
    sequentialAcceptEffect (decoderTestSequence A) =
      (A 0).compl.matrix *
        sequentialAcceptEffect
          (decoderTestSequence (fun i : Fin (n + 1) => A i.succ)) *
          (A 0).compl.matrix := by
  unfold sequentialAcceptEffect
  simp [ProjectionSequence.reverseProduct, ProjectionSequence.matrixList,
    decoderTestSequence]
  rw [(A 0).isHermitian]
  noncomm_ring

theorem sequentialDecoderBaseEffect_last_eq_sequentialAcceptEffect
    (A : ProjectionSequence a (n + 1)) :
    sequentialDecoderBaseEffect A (Fin.last n) =
      sequentialAcceptEffect (decoderTestSequence A) := by
  induction n with
  | zero =>
      simp [sequentialDecoderBaseEffect, sequentialDecoderProjectorList,
        sequentialDecoderEffectsList, sequentialAcceptEffect, decoderTestSequence,
        ProjectionSequence.reverseProduct, ProjectionSequence.matrixList]
      rw [(A 0).isHermitian, (A 0).idempotent]
  | succ n ih =>
      rw [sequentialDecoderBaseEffect_last_tail A]
      rw [ih (fun i : Fin (n + 1) => A i.succ)]
      rw [sequentialAcceptEffect_decoderTestSequence_tail A]

/-- Prefix of an ordered projector sequence ending at `j`.

This is the finite-dimensional bookkeeping used to read the fixed sequential
decoder's `j`th outcome as the final outcome of the prefix
`0, ..., j`. -/
def prefixProjectionSequence (A : ProjectionSequence a (n + 1))
    (j : Fin (n + 1)) : ProjectionSequence a (j.val + 1) :=
  fun i => A ⟨i.val, by omega⟩

@[simp]
theorem prefixProjectionSequence_apply
    (A : ProjectionSequence a (n + 1)) (j : Fin (n + 1))
    (i : Fin (j.val + 1)) :
    prefixProjectionSequence A j i = A ⟨i.val, by omega⟩ :=
  rfl

/-- The fixed ordered decoder's base effect for outcome `j` agrees with the
coherent sequential-accept effect of the prefix `0, ..., j`. -/
theorem sequentialDecoderBaseEffect_eq_prefixSequentialAcceptEffect
    (A : ProjectionSequence a (n + 1)) (j : Fin (n + 1)) :
    sequentialDecoderBaseEffect A j =
      sequentialAcceptEffect (decoderTestSequence (prefixProjectionSequence A j)) := by
  induction n with
  | zero =>
      have hj : j = 0 := by ext; omega
      subst hj
      simp [prefixProjectionSequence, sequentialDecoderBaseEffect,
        sequentialDecoderProjectorList, sequentialDecoderEffectsList,
        sequentialAcceptEffect, decoderTestSequence,
        ProjectionSequence.reverseProduct, ProjectionSequence.matrixList]
      rw [(A 0).isHermitian, (A 0).idempotent]
  | succ n ih =>
      cases j using Fin.cases with
      | zero =>
          simp [prefixProjectionSequence, sequentialDecoderBaseEffect,
            sequentialDecoderProjectorList, sequentialDecoderEffectsList,
            sequentialAcceptEffect, decoderTestSequence,
            ProjectionSequence.reverseProduct, ProjectionSequence.matrixList]
          rw [(A 0).isHermitian, (A 0).idempotent]
      | succ j =>
          rw [sequentialDecoderBaseEffect]
          have hget :
              (sequentialDecoderEffectsList (sequentialDecoderProjectorList A)).get
                  ⟨j.val + 1, by
                    simpa [sequentialDecoderProjectorList] using (Fin.succ j).isLt⟩ =
                (A 0).compl.matrix *
                  (sequentialDecoderEffectsList
                      (sequentialDecoderProjectorList
                        (fun i : Fin (n + 1) => A i.succ))).get
                    ⟨j.val, by
                      simpa [sequentialDecoderProjectorList] using j.isLt⟩ *
                    (A 0).compl.matrix := by
            simpa [sequentialDecoderProjectorList, List.ofFn_succ] using
              sequentialDecoderEffectsList_get_succ (A 0)
                (List.ofFn fun i : Fin (n + 1) => A i.succ) j.val
                (by simpa [sequentialDecoderProjectorList] using j.isLt)
          change (sequentialDecoderEffectsList (sequentialDecoderProjectorList A)).get
                  ⟨j.val + 1, by
                    simpa [sequentialDecoderProjectorList] using (Fin.succ j).isLt⟩ =
                sequentialAcceptEffect
                  (decoderTestSequence (prefixProjectionSequence A (Fin.succ j)))
          rw [hget]
          have ih' :=
            ih (fun i : Fin (n + 1) => A i.succ) j
          rw [sequentialDecoderBaseEffect] at ih'
          rw [ih']
          have hprefix :
              prefixProjectionSequence A (Fin.succ j) =
                fun i : Fin (j.val + 2) =>
                  match i with
                  | ⟨0, _⟩ => A 0
                  | ⟨Nat.succ k, hk⟩ =>
                      prefixProjectionSequence
                        (fun i : Fin (n + 1) => A i.succ) j
                        ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := by
            funext i
            cases i with
            | mk k hk =>
                cases k with
                | zero => rfl
                | succ k => rfl
          rw [hprefix]
          let B : ProjectionSequence a (j.val + 2) :=
            fun i : Fin (j.val + 2) =>
              match i with
              | ⟨0, _⟩ => A 0
              | ⟨Nat.succ k, hk⟩ =>
                  prefixProjectionSequence
                    (fun i : Fin (n + 1) => A i.succ) j
                    ⟨k, Nat.lt_of_succ_lt_succ hk⟩
          change (B 0).compl.matrix *
                sequentialAcceptEffect
                  (decoderTestSequence (fun i : Fin (j.val + 1) => B i.succ)) *
                  (B 0).compl.matrix =
              sequentialAcceptEffect (decoderTestSequence B)
          exact (sequentialAcceptEffect_decoderTestSequence_tail B).symm

theorem sequenceError_eq_one_sub_effectTrace_accept
    (P : ProjectionSequence a n) (ρ : State a) :
    sequenceError P ρ = 1 - effectTrace ρ (sequentialAcceptEffect P) := by
  unfold sequenceError
  rw [sequenceAcceptTrace_eq_effectTrace_accept P ρ]

theorem sequentialDecoderPOVM_last_prob_ge_sequenceAcceptTrace
    (A : ProjectionSequence a (n + 1)) (ρ : State a) :
    sequenceAcceptTrace (decoderTestSequence A) ρ ≤
      ((sequentialDecoderPOVM A).prob ρ (Fin.last n) : ℝ) := by
  rw [sequenceAcceptTrace_eq_effectTrace_accept]
  rw [POVM.prob_eq_trace_re]
  rw [sequentialDecoderPOVM_effects]
  unfold sequentialDecoderEffect
  rw [sequentialDecoderBaseEffect_last_eq_sequentialAcceptEffect A]
  have hextra_nonneg :
      0 ≤ effectTrace ρ
        (if Fin.last n = 0 then sequentialDecoderFailure A else 0) := by
    by_cases h : Fin.last n = 0
    · simp [h, effectTrace_nonneg_of_posSemidef ρ (sequentialDecoderFailure_posSemidef A)]
    · simp [h]
  unfold effectTrace effectAcceptProbability at hextra_nonneg ⊢
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  linarith

/-- Born-rule bridge for the ordered sequential decoder: the genuine
message-indexed POVM succeeds on the final message at least as often as the
binary coherent sequential test accepts.  The reject-all leftover outcome is
assigned to message `0`, so no external sequentiality hypothesis is needed. -/
theorem sequentialDecoderPOVM_last_error_le_sequenceError
    (A : ProjectionSequence a (n + 1)) (ρ : State a) :
    1 - ((sequentialDecoderPOVM A).prob ρ (Fin.last n) : ℝ) ≤
      sequenceError (decoderTestSequence A) ρ := by
  have hprob := sequentialDecoderPOVM_last_prob_ge_sequenceAcceptTrace A ρ
  unfold sequenceError
  linarith

theorem sequentialDecoderPOVM_prob_ge_prefixSequenceAcceptTrace
    (A : ProjectionSequence a (n + 1)) (ρ : State a) (j : Fin (n + 1)) :
    sequenceAcceptTrace (decoderTestSequence (prefixProjectionSequence A j)) ρ ≤
      ((sequentialDecoderPOVM A).prob ρ j : ℝ) := by
  rw [sequenceAcceptTrace_eq_effectTrace_accept]
  rw [POVM.prob_eq_trace_re]
  rw [sequentialDecoderPOVM_effects]
  unfold sequentialDecoderEffect
  rw [sequentialDecoderBaseEffect_eq_prefixSequentialAcceptEffect A j]
  have hextra_nonneg :
      0 ≤ effectTrace ρ
        (if j = 0 then sequentialDecoderFailure A else 0) := by
    by_cases h : j = 0
    · simp [h, effectTrace_nonneg_of_posSemidef ρ (sequentialDecoderFailure_posSemidef A)]
    · simp [h]
  unfold effectTrace effectAcceptProbability at hextra_nonneg ⊢
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  linarith

/-- Born-rule bridge for every outcome of the fixed ordered sequential
decoder.  Outcome `j` succeeds at least as often as the coherent sequential
test over the prefix `0, ..., j`, with `j` treated as the final acceptor. -/
theorem sequentialDecoderPOVM_error_le_prefixSequenceError
    (A : ProjectionSequence a (n + 1)) (ρ : State a) (j : Fin (n + 1)) :
    1 - ((sequentialDecoderPOVM A).prob ρ j : ℝ) ≤
      sequenceError (decoderTestSequence (prefixProjectionSequence A j)) ρ := by
  have hprob := sequentialDecoderPOVM_prob_ge_prefixSequenceAcceptTrace A ρ j
  unfold sequenceError
  linarith

/-- The quantum-union-bound RHS for the instantiated sequential test sequence
is the source sequential-decoding RHS. -/
theorem quantumUnionBoundRHS_decoderTestSequence
    (A : ProjectionSequence a (n + 1)) (ρ : State a) (c : ℝ) :
    quantumUnionBoundRHS (decoderTestSequence A) ρ c =
      decoderErrorRHS A ρ c := by
  simp [quantumUnionBoundRHS, decoderErrorRHS]

/-- Sequential-decoding message-error bound obtained by instantiating the
finite quantum union bound with the reject-earlier / accept-current test list.

This theorem is deliberately conditional on `QuantumUnionBound`; the unconditional
OMW/Khatri--Wilde quantum-union-bound theorem below supplies the source-shaped
instantiation used by the sequential decoder. -/
theorem decoderError_le_of_quantumUnionBound
    (A : ProjectionSequence a (n + 1)) (ρ : State a) {c : ℝ} (hc : 0 < c)
    (hqub : QuantumUnionBound (decoderTestSequence A)) :
    sequenceError (decoderTestSequence A) ρ ≤ decoderErrorRHS A ρ c := by
  rw [← quantumUnionBoundRHS_decoderTestSequence A ρ c]
  exact hqub ρ c hc

/-- Unconditional sequential-decoding message-error bound obtained by applying
the finite quantum union bound to the reject-earlier / accept-current test
sequence. -/
theorem decoderError_le
    (A : ProjectionSequence a (n + 1)) (ρ : State a) {c : ℝ} (hc : 0 < c) :
    sequenceError (decoderTestSequence A) ρ ≤ decoderErrorRHS A ρ c :=
  decoderError_le_of_quantumUnionBound A ρ hc (quantumUnionBound (decoderTestSequence A))

end SequentialDecoding

end

end QIT
