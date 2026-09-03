/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothSupportRestriction
public import QIT.States.Purification.ReferenceIsometry

set_option maxHeartbeats 3000000

/-!
# Smooth conditional entropy and reference isometries

This file records the source-level invariance statement for smooth endpoint
entropies.  The compression maps used below are the adjoints of the reference
isometries; they are trace-nonincreasing completely positive maps, so they
also transport purified-distance balls in the reverse direction.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal Pointwise
open Matrix
open Set

namespace QIT

universe u v w x

noncomputable section

namespace ReferenceIsometry

variable {r₁ : Type u} {r₂ : Type v} {a : Type w}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
  [Fintype a] [DecidableEq a]

omit [Fintype a] [DecidableEq a] in
private theorem applyMatrixRight_conjTranspose
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod a r₁)) :
    Matrix.conjTranspose (V.applyMatrixRight X) =
      V.applyMatrixRight (Matrix.conjTranspose X) := by
  ext i j
  simp [applyMatrixRight, rightBlock, Matrix.conjTranspose, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, mul_comm]
  rw [Finset.sum_comm]
  simp [ mul_comm, mul_left_comm]

omit [DecidableEq a] in
private theorem trace_applyMatrixRight
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod a r₁)) :
    (V.applyMatrixRight X).trace = X.trace := by
  have h := V.partialTraceB_applyMatrixRight X
  have ht := congrArg Matrix.trace h
  simpa [partialTraceB_trace] using ht

private theorem traceNorm_applyMatrixRight
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod a r₁)) :
    traceNorm (V.applyMatrixRight X) = traceNorm X := by
  rw [traceNorm_eq_trace_psdSqrt_mul_conjTranspose,
    traceNorm_eq_trace_psdSqrt_mul_conjTranspose]
  have hmul :
      V.applyMatrixRight X * Matrix.conjTranspose (V.applyMatrixRight X) =
      V.applyMatrixRight (X * Matrix.conjTranspose X) := by
    rw [applyMatrixRight_conjTranspose, ← applyMatrixRight_mul]
  rw [hmul, V.psdSqrt_applyMatrixRight
    (Matrix.posSemidef_self_mul_conjTranspose X)]
  exact congrArg Complex.re (trace_applyMatrixRight V
    (psdSqrt (X * Matrix.conjTranspose X)))

theorem applyMatrixRight_eq_kron_conj
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod a r₁)) :
    V.applyMatrixRight X =
      Matrix.kronecker (1 : CMatrix a) V.matrix * X *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) := by
  ext i j
  simp [ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
    Matrix.kronecker, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_assoc, mul_comm
    ]

theorem conditioningK_isometry
    (V : ReferenceIsometry r₁ r₂) :
    Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) *
        Matrix.kronecker (1 : CMatrix a) V.matrix =
      (1 : CMatrix (Prod a r₁)) := by
  have hconj : Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) =
      Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose V.matrix) := by
    simpa [Matrix.kronecker] using
      (Matrix.conjTranspose_kronecker (1 : CMatrix a) V.matrix)
  rw [hconj]
  simpa [V.isometry] using
    (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
      (Matrix.conjTranspose V.matrix) V.matrix).symm

private theorem conditioning_projector_left_fixes
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod a r₁)) :
    (Matrix.kronecker (1 : CMatrix a) V.matrix *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix)) *
        V.applyMatrixRight X = V.applyMatrixRight X := by
  rw [applyMatrixRight_eq_kron_conj V X]
  let K : Matrix (Prod a r₂) (Prod a r₁) ℂ :=
    Matrix.kronecker (1 : CMatrix a) V.matrix
  have hK : Matrix.conjTranspose K * K = (1 : CMatrix (Prod a r₁)) := by
    simpa [K] using ReferenceIsometry.conditioningK_isometry (a := a) V
  change K * Matrix.conjTranspose K * (K * X * Matrix.conjTranspose K) =
    K * X * Matrix.conjTranspose K
  calc
    K * Matrix.conjTranspose K * (K * X * Matrix.conjTranspose K) =
        K * ((Matrix.conjTranspose K * K) * X * Matrix.conjTranspose K) := by
      simp [Matrix.mul_assoc]
    _ = K * X * Matrix.conjTranspose K := by rw [hK]; simp [Matrix.mul_assoc]

private theorem applyMatrix_eq_kron_conj
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod r₁ a)) :
    V.applyMatrix X =
      Matrix.kronecker V.matrix (1 : CMatrix a) * X *
        Matrix.conjTranspose (Matrix.kronecker V.matrix (1 : CMatrix a)) := by
  ext i j
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    Matrix.kronecker, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type,
    mul_assoc, mul_comm]

private theorem applyMatrix_conjTranspose
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod r₁ a)) :
    Matrix.conjTranspose (V.applyMatrix X) =
      V.applyMatrix (Matrix.conjTranspose X) := by
  rw [applyMatrix_eq_kron_conj V X, applyMatrix_eq_kron_conj V
    (Matrix.conjTranspose X)]
  simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

private theorem applyMatrix_mul
    (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (Prod r₁ a)) :
    V.applyMatrix X * V.applyMatrix Y = V.applyMatrix (X * Y) := by
  let K : Matrix (Prod r₂ a) (Prod r₁ a) ℂ :=
    Matrix.kronecker V.matrix (1 : CMatrix a)
  have hK : Matrix.conjTranspose K * K = (1 : CMatrix (Prod r₁ a)) := by
    have hconj : Matrix.conjTranspose K =
        Matrix.kronecker (Matrix.conjTranspose V.matrix) (1 : CMatrix a) := by
      dsimp [K]
      simpa [Matrix.kronecker] using
        (Matrix.conjTranspose_kronecker V.matrix (1 : CMatrix a))
    rw [hconj]
    simpa [V.isometry] using
      (Matrix.mul_kronecker_mul (Matrix.conjTranspose V.matrix) V.matrix
        (1 : CMatrix a) (1 : CMatrix a)).symm
  rw [applyMatrix_eq_kron_conj V X, applyMatrix_eq_kron_conj V Y,
    applyMatrix_eq_kron_conj V (X * Y)]
  exact ((Matrix.isometryConjNonUnitalStarAlgHom K hK).map_mul X Y).symm

private theorem applyMatrix_posSemidef
    (V : ReferenceIsometry r₁ r₂) {X : CMatrix (Prod r₁ a)}
    (hX : X.PosSemidef) :
    (V.applyMatrix X).PosSemidef := by
  let K : Matrix (Prod r₂ a) (Prod r₁ a) ℂ :=
    Matrix.kronecker V.matrix (1 : CMatrix a)
  have h := hX.conjTranspose_mul_mul_same (Matrix.conjTranspose K)
  rw [applyMatrix_eq_kron_conj V X]
  simpa [K, Matrix.conjTranspose_conjTranspose] using h

private theorem psdSqrt_applyMatrix
    (V : ReferenceIsometry r₁ r₂) {X : CMatrix (Prod r₁ a)}
    (hX : X.PosSemidef) :
    psdSqrt (V.applyMatrix X) = V.applyMatrix (psdSqrt X) := by
  let S : CMatrix (Prod r₂ a) := V.applyMatrix (psdSqrt X)
  have hSpos : S.PosSemidef := by
    simpa [S] using applyMatrix_posSemidef V (psdSqrt_pos X)
  have hSsq : S * S = V.applyMatrix X := by
    dsimp [S]
    rw [applyMatrix_mul, psdSqrt_mul_self_of_posSemidef hX]
  simpa [psdSqrt, S] using
    (CFC.sqrt_unique (a := V.applyMatrix X) (b := S) hSsq hSpos.nonneg)

omit [DecidableEq a] in
private theorem partialTraceB_applyMatrix
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod r₁ a)) :
    partialTraceB (a := r₂) (b := a) (V.applyMatrix X) =
      V.matrix * partialTraceB (a := r₁) (b := a) X *
        Matrix.conjTranspose V.matrix := by
  ext x y
  simp [partialTraceB, applyMatrix, targetBlock, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

private theorem traceNorm_applyMatrix
    (V : ReferenceIsometry r₁ r₂) (X : CMatrix (Prod r₁ a)) :
    traceNorm (V.applyMatrix X) = traceNorm X := by
  rw [traceNorm_eq_trace_psdSqrt_mul_conjTranspose,
    traceNorm_eq_trace_psdSqrt_mul_conjTranspose]
  have hconj : Matrix.conjTranspose (V.applyMatrix X) =
      V.applyMatrix (Matrix.conjTranspose X) := by
    exact applyMatrix_conjTranspose V X
  have hmul :
      V.applyMatrix X * Matrix.conjTranspose (V.applyMatrix X) =
        V.applyMatrix (X * Matrix.conjTranspose X) := by
    rw [hconj, applyMatrix_mul]
  rw [hmul]
  let S : CMatrix (Prod r₂ a) :=
    V.applyMatrix (psdSqrt (X * Matrix.conjTranspose X))
  have hsqrt : psdSqrt (V.applyMatrix (X * Matrix.conjTranspose X)) = S := by
    have hSpos : S.PosSemidef := by
      change (V.applyMatrix (psdSqrt (X * Matrix.conjTranspose X))).PosSemidef
      have hp : (psdSqrt (X * Matrix.conjTranspose X)).PosSemidef :=
        psdSqrt_pos (X * Matrix.conjTranspose X)
      exact applyMatrix_posSemidef V hp
    have hSsq : S * S = V.applyMatrix (X * Matrix.conjTranspose X) := by
      dsimp [S]
      calc
        V.applyMatrix (psdSqrt (X * Matrix.conjTranspose X)) *
            V.applyMatrix (psdSqrt (X * Matrix.conjTranspose X)) =
            V.applyMatrix (psdSqrt (X * Matrix.conjTranspose X) *
              psdSqrt (X * Matrix.conjTranspose X)) := applyMatrix_mul V _ _
        _ = V.applyMatrix (X * Matrix.conjTranspose X) := by
          rw [psdSqrt_mul_self_of_posSemidef
            (Matrix.posSemidef_self_mul_conjTranspose X)]
    exact CFC.sqrt_unique (a := V.applyMatrix (X * Matrix.conjTranspose X))
      (b := S) hSsq hSpos.nonneg
  rw [hsqrt]
  exact congrArg Complex.re (trace_applyMatrix V
    (psdSqrt (X * Matrix.conjTranspose X)))

end ReferenceIsometry

namespace SubnormalizedState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private def referenceIsometryCompressed
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (σPlus : SubnormalizedState bPlus) (V : ReferenceIsometry b bPlus) :
    SubnormalizedState b :=
  σPlus.applyTraceNonincreasingCP
    (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
    (referenceIsometry_conjTranspose_traceNonincreasingCP V)

@[simp] private theorem referenceIsometryCompressed_matrix
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (σPlus : SubnormalizedState bPlus) (V : ReferenceIsometry b bPlus) :
    (referenceIsometryCompressed σPlus V).matrix =
      Matrix.conjTranspose V.matrix * σPlus.matrix * V.matrix := by
  simp [referenceIsometryCompressed, applyTraceNonincreasingCP_matrix,
    MatrixMap.ofKraus]

private theorem smoothIsometry_psdSqrt_projector_factor
    {c : Type*} [Fintype c] [DecidableEq c]
    (E A : CMatrix c) (hA : A.PosSemidef)
    (hEherm : E.IsHermitian) :
    ∃ U : Matrix.unitaryGroup c ℂ,
      psdSqrt (E * A * E) = E * psdSqrt A * (U : CMatrix c) := by
  have hEA : (E * A * E).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same E
    rw [hEherm.eq] at h
    simpa [Matrix.mul_assoc] using h
  let X : CMatrix c := E * psdSqrt A
  let S : CMatrix c := psdSqrt (E * A * E)
  have hSsq : S * Matrix.conjTranspose S = E * A * E := by
    dsimp [S]
    rw [psdSqrt_isHermitian (E * A * E), psdSqrt_mul_self_of_posSemidef hEA]
  have hXgram : X * Matrix.conjTranspose X = E * A * E := by
    dsimp [X]
    rw [Matrix.conjTranspose_mul, hEherm.eq, psdSqrt_isHermitian A]
    calc
      E * psdSqrt A * (psdSqrt A * E) =
          E * (psdSqrt A * psdSqrt A) * E := by simp [Matrix.mul_assoc]
      _ = E * A * E := by rw [psdSqrt_mul_self_of_posSemidef hA]
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := X) (B := S) (by rw [hXgram, hSsq]) (Nat.le_refl _)
  let U : Matrix.unitaryGroup c ℂ :=
    ⟨Matrix.transpose V.matrix, by
      classical
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      have h := congrFun (congrFun V.isometry j) i
      simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose,
        Matrix.one_apply, Finset.mul_sum, mul_comm, eq_comm] using h⟩
  refine ⟨U, ?_⟩
  simpa [X, S, U] using hV

private theorem smoothIsometry_traceNorm_sqrt_mul_sqrt_eq_trace_sandwich
    {c : Type*} [Fintype c] [DecidableEq c]
    (A B : CMatrix c) (hA : A.PosSemidef) :
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

private theorem smoothIsometry_candidate_side_compression_eq
    {c : Type*} [Fintype c] [DecidableEq c]
    (A R E : CMatrix c) (hR : R.PosSemidef)
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
      rw [Matrix.conjTranspose_mul, psdSqrt_isHermitian A,
        psdSqrt_isHermitian R]
    _ = (psdSqrt (psdSqrt A * R * psdSqrt A)).trace.re :=
      smoothIsometry_traceNorm_sqrt_mul_sqrt_eq_trace_sandwich R A hR
    _ = (psdSqrt (psdSqrt A * (E * R * E) * psdSqrt A)).trace.re := by
      rw [hsand]
    _ = traceNorm (psdSqrt (E * R * E) * psdSqrt A) :=
      (smoothIsometry_traceNorm_sqrt_mul_sqrt_eq_trace_sandwich
        (E * R * E) A hER).symm
    _ = traceNorm (psdSqrt A * psdSqrt (E * R * E)) := by
      rw [← traceNorm_conjTranspose]
      rw [Matrix.conjTranspose_mul, psdSqrt_isHermitian A,
        psdSqrt_isHermitian (E * R * E)]

private theorem conditionalMaxEntropyTraceNorm_conditioningIsometryApply_eq
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (σPlus : SubnormalizedState bPlus)
    (V : ReferenceIsometry b bPlus) :
    traceNorm (psdSqrt (ρ.conditioningIsometryApply V).matrix *
        psdSqrt (identityTensorStateMatrix (a := a) σPlus)) =
      traceNorm (psdSqrt ρ.matrix *
        psdSqrt (identityTensorStateMatrix (a := a)
          (referenceIsometryCompressed σPlus V))) := by
  let K : Matrix (Prod a bPlus) (Prod a b) ℂ :=
    Matrix.kronecker (1 : CMatrix a) V.matrix
  let E : CMatrix (Prod a bPlus) := K * Matrix.conjTranspose K
  let ρPlus : SubnormalizedState (Prod a bPlus) :=
    ρ.conditioningIsometryApply V
  let σ : SubnormalizedState b := referenceIsometryCompressed σPlus V
  let RPlus : CMatrix (Prod a bPlus) :=
    identityTensorStateMatrix (a := a) σPlus
  let R : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  have hK : Matrix.conjTranspose K * K = (1 : CMatrix (Prod a b)) := by
    simpa [K] using ReferenceIsometry.conditioningK_isometry (a := a) V
  have hEpos : E.PosSemidef := by
    dsimp [E]
    exact Matrix.posSemidef_self_mul_conjTranspose K
  have hEherm : E.IsHermitian := hEpos.isHermitian
  have hEid : E * E = E := by
    dsimp [E]
    calc
      K * Matrix.conjTranspose K * (K * Matrix.conjTranspose K) =
          K * ((Matrix.conjTranspose K * K) * Matrix.conjTranspose K) := by
            simp [Matrix.mul_assoc]
      _ = E := by rw [hK]; simp [E]
  have hA : ρPlus.matrix = K * ρ.matrix * Matrix.conjTranspose K := by
    dsimp [ρPlus, K]
    rw [conditioningIsometryApply_matrix,
      ReferenceIsometry.applyMatrixRight_eq_kron_conj]
    simp [Matrix.kronecker]
  have hAfix : E * ρPlus.matrix * E = ρPlus.matrix := by
    calc
      E * ρPlus.matrix * E = E * (K * ρ.matrix * Matrix.conjTranspose K) * E := by
        rw [hA]
      _ =
      K * ((Matrix.conjTranspose K * K) * ρ.matrix *
            (Matrix.conjTranspose K * K)) * Matrix.conjTranspose K := by
              simp [E, Matrix.mul_assoc]
      _ = ρPlus.matrix := by rw [hK]; simp only [one_mul, mul_one]; exact hA.symm
  obtain ⟨U, hU⟩ := smoothIsometry_psdSqrt_projector_factor E
    ρPlus.matrix ρPlus.pos hEherm
  have hU' : psdSqrt ρPlus.matrix =
      E * psdSqrt ρPlus.matrix * (U : CMatrix (Prod a bPlus)) := by
    simpa [hAfix] using hU
  have hright : E * psdSqrt ρPlus.matrix = psdSqrt ρPlus.matrix := by
    calc
      E * psdSqrt ρPlus.matrix =
          E * (E * psdSqrt ρPlus.matrix * (U : CMatrix (Prod a bPlus))) :=
            congrArg (fun X : CMatrix (Prod a bPlus) => E * X) hU'
      _ = E * psdSqrt ρPlus.matrix * (U : CMatrix (Prod a bPlus)) := by
            calc
              E * (E * psdSqrt ρPlus.matrix * (U : CMatrix (Prod a bPlus))) =
                  (E * E) * psdSqrt ρPlus.matrix * (U : CMatrix (Prod a bPlus)) := by
                    simp [Matrix.mul_assoc]
              _ = E * psdSqrt ρPlus.matrix * (U : CMatrix (Prod a bPlus)) := by
                    rw [hEid]
      _ = psdSqrt ρPlus.matrix := hU'.symm
  have hleft : psdSqrt ρPlus.matrix * E = psdSqrt ρPlus.matrix := by
    have h := congrArg Matrix.conjTranspose hright
    rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian ρPlus.matrix).eq,
      hEherm.eq] at h
    exact h
  have hER : E * RPlus * E = V.applyMatrixRight R := by
    have hconj : Matrix.conjTranspose K =
        Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose V.matrix) := by
      dsimp [K]
      simpa [Matrix.kronecker] using
        (Matrix.conjTranspose_kronecker (1 : CMatrix a) V.matrix)
    have hcompress : Matrix.conjTranspose K * RPlus * K =
        Matrix.kronecker (1 : CMatrix a)
          (Matrix.conjTranspose V.matrix * σPlus.matrix * V.matrix) := by
      dsimp [RPlus]
      rw [hconj]
      change Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose V.matrix) *
          Matrix.kronecker (1 : CMatrix a) σPlus.matrix *
          Matrix.kronecker (1 : CMatrix a) V.matrix = _
      have h1 :
          Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose V.matrix) *
              Matrix.kronecker (1 : CMatrix a) σPlus.matrix =
            Matrix.kronecker (1 * 1 : CMatrix a)
              (Matrix.conjTranspose V.matrix * σPlus.matrix) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
            (Matrix.conjTranspose V.matrix) σPlus.matrix).symm
      have h2 :
          Matrix.kronecker (1 * 1 : CMatrix a)
              (Matrix.conjTranspose V.matrix * σPlus.matrix) *
              Matrix.kronecker (1 : CMatrix a) V.matrix =
            Matrix.kronecker (1 * 1 * 1 : CMatrix a)
              (Matrix.conjTranspose V.matrix * σPlus.matrix * V.matrix) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul (1 * 1 : CMatrix a) (1 : CMatrix a)
            (Matrix.conjTranspose V.matrix * σPlus.matrix) V.matrix).symm
      rw [h1, h2]
      simp
    calc
      E * RPlus * E = K * (Matrix.conjTranspose K * RPlus * K) *
          Matrix.conjTranspose K := by simp [E, Matrix.mul_assoc]
      _ = K * R * Matrix.conjTranspose K := by
        have hRmatrix : R =
            Matrix.kronecker (1 : CMatrix a)
              (Matrix.conjTranspose V.matrix * σPlus.matrix * V.matrix) := by
          dsimp [R, σ]
          change Matrix.kronecker (1 : CMatrix a)
              (referenceIsometryCompressed σPlus V).matrix = _
          rw [referenceIsometryCompressed_matrix]
          rfl
        rw [hcompress, hRmatrix]
      _ = V.applyMatrixRight R := by
        rw [ReferenceIsometry.applyMatrixRight_eq_kron_conj]
  have hRplus : RPlus.PosSemidef :=
    identityTensorStateMatrix_posSemidef (a := a) σPlus
  have hR : R.PosSemidef :=
    identityTensorStateMatrix_posSemidef (a := a) σ
  have hERpos : (E * RPlus * E).PosSemidef := by
    rw [hER]
    exact ReferenceIsometry.applyMatrixRight_posSemidef V hR
  have hroot : psdSqrt (E * RPlus * E) = V.applyMatrixRight (psdSqrt R) := by
    rw [hER, V.psdSqrt_applyMatrixRight hR]
  have hcandidate := smoothIsometry_candidate_side_compression_eq
    ρPlus.matrix RPlus E hRplus hERpos hleft hright
  dsimp [ρPlus, RPlus, R, σ] at *
  rw [hroot, conditioningIsometryApply_matrix,
    V.psdSqrt_applyMatrixRight ρ.pos, ReferenceIsometry.applyMatrixRight_mul,
    ReferenceIsometry.traceNorm_applyMatrixRight] at hcandidate
  rw [← V.psdSqrt_applyMatrixRight ρ.pos] at hcandidate
  simpa [conditioningIsometryApply_matrix] using hcandidate

private theorem conditionalMaxEntropyTraceNorm_sourceIsometryApply_eq
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b)
    (U : ReferenceIsometry a aPlus) :
    traceNorm (psdSqrt (ρ.sourceIsometryApply U).matrix *
        psdSqrt (identityTensorStateMatrix (a := aPlus) σ)) =
      traceNorm (psdSqrt ρ.matrix *
        psdSqrt (identityTensorStateMatrix (a := a) σ)) := by
  let K : Matrix (Prod aPlus b) (Prod a b) ℂ :=
    Matrix.kronecker U.matrix (1 : CMatrix b)
  let E : CMatrix (Prod aPlus b) := K * Matrix.conjTranspose K
  let ρPlus : SubnormalizedState (Prod aPlus b) := ρ.sourceIsometryApply U
  let RPlus : CMatrix (Prod aPlus b) :=
    identityTensorStateMatrix (a := aPlus) σ
  let R : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  have hK : Matrix.conjTranspose K * K = (1 : CMatrix (Prod a b)) := by
    have hconj : Matrix.conjTranspose K =
        Matrix.kronecker (Matrix.conjTranspose U.matrix) (1 : CMatrix b) := by
      dsimp [K]
      simpa [Matrix.kronecker] using
        (Matrix.conjTranspose_kronecker U.matrix (1 : CMatrix b))
    rw [hconj]
    simpa [U.isometry] using
      (Matrix.mul_kronecker_mul (Matrix.conjTranspose U.matrix) U.matrix
        (1 : CMatrix b) (1 : CMatrix b)).symm
  have hEpos : E.PosSemidef := by
    dsimp [E]
    exact Matrix.posSemidef_self_mul_conjTranspose K
  have hEherm : E.IsHermitian := hEpos.isHermitian
  have hEid : E * E = E := by
    dsimp [E]
    calc
      K * Matrix.conjTranspose K * (K * Matrix.conjTranspose K) =
          K * ((Matrix.conjTranspose K * K) * Matrix.conjTranspose K) := by
            simp [Matrix.mul_assoc]
      _ = E := by rw [hK]; simp [E]
  have hA : ρPlus.matrix = K * ρ.matrix * Matrix.conjTranspose K := by
    dsimp [ρPlus, K]
    rw [sourceIsometryApply_matrix,
      ReferenceIsometry.applyMatrix_eq_kron_conj]
    simp [Matrix.kronecker]
  have hAfix : E * ρPlus.matrix * E = ρPlus.matrix := by
    calc
      E * ρPlus.matrix * E = E * (K * ρ.matrix * Matrix.conjTranspose K) * E := by
        rw [hA]
      _ = K * ((Matrix.conjTranspose K * K) * ρ.matrix *
            (Matrix.conjTranspose K * K)) * Matrix.conjTranspose K := by
              simp [E, Matrix.mul_assoc]
      _ = ρPlus.matrix := by rw [hK]; simp only [one_mul, mul_one]; exact hA.symm
  obtain ⟨W, hW⟩ := smoothIsometry_psdSqrt_projector_factor E
    ρPlus.matrix ρPlus.pos hEherm
  have hW' : psdSqrt ρPlus.matrix =
      E * psdSqrt ρPlus.matrix * (W : CMatrix (Prod aPlus b)) := by
    simpa [hAfix] using hW
  have hright : E * psdSqrt ρPlus.matrix = psdSqrt ρPlus.matrix := by
    calc
      E * psdSqrt ρPlus.matrix =
          E * (E * psdSqrt ρPlus.matrix * (W : CMatrix (Prod aPlus b))) :=
            congrArg (fun X : CMatrix (Prod aPlus b) => E * X) hW'
      _ = E * psdSqrt ρPlus.matrix * (W : CMatrix (Prod aPlus b)) := by
            calc
              E * (E * psdSqrt ρPlus.matrix * (W : CMatrix (Prod aPlus b))) =
                  (E * E) * psdSqrt ρPlus.matrix * (W : CMatrix (Prod aPlus b)) := by
                    simp [Matrix.mul_assoc]
              _ = E * psdSqrt ρPlus.matrix * (W : CMatrix (Prod aPlus b)) := by
                    rw [hEid]
      _ = psdSqrt ρPlus.matrix := hW'.symm
  have hleft : psdSqrt ρPlus.matrix * E = psdSqrt ρPlus.matrix := by
    have h := congrArg Matrix.conjTranspose hright
    rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian ρPlus.matrix).eq,
      hEherm.eq] at h
    exact h
  have hER : E * RPlus * E = U.applyMatrix R := by
    have hconj : Matrix.conjTranspose K =
        Matrix.kronecker (Matrix.conjTranspose U.matrix) (1 : CMatrix b) := by
      dsimp [K]
      simpa [Matrix.kronecker] using
        (Matrix.conjTranspose_kronecker U.matrix (1 : CMatrix b))
    have hcompress : Matrix.conjTranspose K * RPlus * K = R := by
      dsimp [RPlus, R]
      rw [hconj]
      change Matrix.kronecker (Matrix.conjTranspose U.matrix) (1 : CMatrix b) *
          Matrix.kronecker (1 : CMatrix aPlus) σ.matrix *
          Matrix.kronecker U.matrix (1 : CMatrix b) = _
      have h1 :
          Matrix.kronecker (Matrix.conjTranspose U.matrix) (1 : CMatrix b) *
              Matrix.kronecker (1 : CMatrix aPlus) σ.matrix =
            Matrix.kronecker (Matrix.conjTranspose U.matrix *
              (1 : CMatrix aPlus)) ((1 : CMatrix b) * σ.matrix) := by
        simpa [Matrix.kronecker] using
          (Matrix.mul_kronecker_mul (Matrix.conjTranspose U.matrix)
            (1 : CMatrix aPlus) (1 : CMatrix b) σ.matrix).symm
      rw [h1]
      have h2 := Matrix.mul_kronecker_mul
        (Matrix.conjTranspose U.matrix * (1 : CMatrix aPlus))
        U.matrix ((1 : CMatrix b) * σ.matrix) (1 : CMatrix b)
      simpa [Matrix.kronecker, Matrix.mul_one, Matrix.one_mul, U.isometry] using h2.symm
    calc
      E * RPlus * E = K * (Matrix.conjTranspose K * RPlus * K) *
          Matrix.conjTranspose K := by simp [E, Matrix.mul_assoc]
      _ = K * R * Matrix.conjTranspose K := by rw [hcompress]
      _ = U.applyMatrix R := by
        rw [ReferenceIsometry.applyMatrix_eq_kron_conj]
  have hRplus : RPlus.PosSemidef :=
    identityTensorStateMatrix_posSemidef (a := aPlus) σ
  have hR : R.PosSemidef :=
    identityTensorStateMatrix_posSemidef (a := a) σ
  have hERpos : (E * RPlus * E).PosSemidef := by
    rw [hER]
    exact ReferenceIsometry.applyMatrix_posSemidef U hR
  have hroot : psdSqrt (E * RPlus * E) = U.applyMatrix (psdSqrt R) := by
    rw [hER, ReferenceIsometry.psdSqrt_applyMatrix U hR]
  have hcandidate := smoothIsometry_candidate_side_compression_eq
    ρPlus.matrix RPlus E hRplus hERpos hleft hright
  dsimp [ρPlus, RPlus, R] at *
  rw [hroot, sourceIsometryApply_matrix,
    ReferenceIsometry.psdSqrt_applyMatrix U ρ.pos, ReferenceIsometry.applyMatrix_mul,
    ReferenceIsometry.traceNorm_applyMatrix] at hcandidate
  rw [sourceIsometryApply_matrix,
    ReferenceIsometry.psdSqrt_applyMatrix U ρ.pos]
  exact hcandidate

private theorem conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_compressed_eq
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (σPlus : SubnormalizedState bPlus)
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalMaxEntropyExponentCandidate σPlus =
      ρ.conditionalMaxEntropyExponentCandidate
        (referenceIsometryCompressed σPlus V) := by
  unfold conditionalMaxEntropyExponentCandidate
  rw [conditionalMaxEntropyTraceNorm_conditioningIsometryApply_eq]

private theorem conditionalMaxEntropyFidelityCandidate_conditioningIsometryApply_compressed_eq
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (σPlus : SubnormalizedState bPlus)
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalMaxEntropyFidelityCandidate σPlus =
      ρ.conditionalMaxEntropyFidelityCandidate
        (referenceIsometryCompressed σPlus V) := by
  unfold conditionalMaxEntropyFidelityCandidate
  rw [conditionalMaxEntropyTraceNorm_conditioningIsometryApply_eq]

private theorem referenceIsometryCompressed_referenceIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (σ : SubnormalizedState b) (V : ReferenceIsometry b bPlus) :
    referenceIsometryCompressed (σ.referenceIsometryApply V) V = σ := by
  apply SubnormalizedState.ext
  rw [referenceIsometryCompressed_matrix, referenceIsometryApply_matrix]
  rw [MatrixMap.ofReferenceIsometry_apply]
  change Matrix.conjTranspose V.matrix *
      (V.matrix * σ.matrix * Matrix.conjTranspose V.matrix) * V.matrix = σ.matrix
  calc
    Matrix.conjTranspose V.matrix *
        (V.matrix * σ.matrix * Matrix.conjTranspose V.matrix) * V.matrix =
      (Matrix.conjTranspose V.matrix * V.matrix) * σ.matrix *
        (Matrix.conjTranspose V.matrix * V.matrix) := by
          simp only [Matrix.mul_assoc]
    _ = σ.matrix := by rw [V.isometry]; simp

private theorem conditioningIsometryCompressed_apply_matrix
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (τPlus : SubnormalizedState (Prod a bPlus)) (V : ReferenceIsometry b bPlus) :
    ((τPlus.conditioningIsometryCompressed V).conditioningIsometryApply V).matrix =
      Matrix.kronecker (1 : CMatrix a) (V.matrix * Matrix.conjTranspose V.matrix) *
          τPlus.matrix *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a)
          (V.matrix * Matrix.conjTranspose V.matrix)) := by
  rw [conditioningIsometryApply_matrix, conditioningIsometryCompressed_matrix]
  let K : Matrix (Prod a bPlus) (Prod a b) ℂ :=
    Matrix.kronecker (1 : CMatrix a) V.matrix
  have hcompress :
      MatrixMap.kron (Channel.idChannel a).map
          (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose V.matrix))
          τPlus.matrix = Matrix.conjTranspose K * τPlus.matrix * K := by
    ext i j
    rw [MatrixMap.kron_idChannel_left_apply_slice]
    change MatrixMap.ofKraus
        (fun _ : Unit => Matrix.conjTranspose V.matrix)
        (ReferenceIsometry.rightBlock τPlus.matrix i.1 j.1) i.2 j.2 =
          (Matrix.conjTranspose K * τPlus.matrix * K) i j
    simp [MatrixMap.ofKraus, K, Matrix.kronecker, Matrix.mul_apply,
      Finset.mul_sum, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, mul_comm,
      mul_left_comm, Finset.sum_ite_eq',
      ReferenceIsometry.rightBlock]
    have hsum (x : bPlus) :
        (∑ x₁ : a, ∑ x₂ : bPlus,
          τPlus.matrix (x₁, x₂) (j.1, x) *
            (V.matrix x j.2 *
              (starRingEnd ℂ) (if x₁ = i.1 then V.matrix x₂ i.2 else 0))) =
          ∑ x₂ : bPlus, τPlus.matrix (i.1, x₂) (j.1, x) *
            (V.matrix x j.2 * (starRingEnd ℂ) (V.matrix x₂ i.2)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_eq_single_of_mem i.1 (Finset.mem_univ _)]
      · simp
      · intro x _ hx
        simp [hx]
    simp_rw [hsum]
  rw [hcompress]
  rw [ReferenceIsometry.applyMatrixRight_eq_kron_conj (a := a) V]
  change K * (Matrix.conjTranspose K * τPlus.matrix * K) *
      Matrix.conjTranspose K = _
  have hE : K * Matrix.conjTranspose K =
      Matrix.kronecker (1 : CMatrix a) (V.matrix * Matrix.conjTranspose V.matrix) := by
    dsimp [K]
    have hconj : Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) =
        Matrix.kronecker (1 : CMatrix a) (Matrix.conjTranspose V.matrix) := by
      simpa [Matrix.kronecker] using
        (Matrix.conjTranspose_kronecker (1 : CMatrix a) V.matrix)
    change Matrix.kronecker (1 : CMatrix a) V.matrix *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) = _
    rw [hconj]
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
        V.matrix (Matrix.conjTranspose V.matrix)).symm
  have hEherm : Matrix.conjTranspose
      (Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix)) =
      Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix) := by
    simp [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_mul]
  calc
    K * (Matrix.conjTranspose K * τPlus.matrix * K) *
          Matrix.conjTranspose K =
      (K * Matrix.conjTranspose K) * τPlus.matrix *
        (K * Matrix.conjTranspose K) := by simp [Matrix.mul_assoc]
      _ = Matrix.kronecker (1 : CMatrix a) (V.matrix * Matrix.conjTranspose V.matrix) *
        τPlus.matrix *
        Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a)
          (V.matrix * Matrix.conjTranspose V.matrix)) := by
        rw [hE, hEherm]

private theorem sourceIsometryCompressed_apply_matrix
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (τPlus : SubnormalizedState (Prod aPlus b)) (U : ReferenceIsometry a aPlus) :
    ((τPlus.sourceIsometryCompressed U).sourceIsometryApply U).matrix =
      Matrix.kronecker (U.matrix * Matrix.conjTranspose U.matrix)
          (1 : CMatrix b) * τPlus.matrix *
        Matrix.conjTranspose (Matrix.kronecker (U.matrix *
          Matrix.conjTranspose U.matrix) (1 : CMatrix b)) := by
  rw [sourceIsometryApply_matrix, sourceIsometryCompressed_matrix]
  let K : Matrix (Prod aPlus b) (Prod a b) ℂ :=
    Matrix.kronecker U.matrix (1 : CMatrix b)
  have hcompress :
      MatrixMap.kron
          (MatrixMap.ofKraus (fun _ : Unit => Matrix.conjTranspose U.matrix))
          (Channel.idChannel b).map τPlus.matrix =
        Matrix.conjTranspose K * τPlus.matrix * K := by
    ext i j
    rw [MatrixMap.kron_idChannel_apply_slice]
    change MatrixMap.ofKraus
        (fun _ : Unit => Matrix.conjTranspose U.matrix)
        (ReferenceIsometry.targetBlock τPlus.matrix i.2 j.2) i.1 j.1 =
      (Matrix.conjTranspose K * τPlus.matrix * K) i j
    simp [MatrixMap.ofKraus, K, Matrix.kronecker, Matrix.mul_apply,
      Finset.mul_sum, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, mul_comm,
      mul_left_comm, Finset.sum_ite_eq',
      ReferenceIsometry.targetBlock]
    have hsum (x x₁ : aPlus) :
        (∑ x₂ : b,
          τPlus.matrix (x₁, x₂) (x, j.2) *
            (U.matrix x j.1 *
              (starRingEnd ℂ) (if x₂ = i.2 then U.matrix x₁ i.1 else 0))) =
          τPlus.matrix (x₁, i.2) (x, j.2) *
            (U.matrix x j.1 * (starRingEnd ℂ) (U.matrix x₁ i.1)) := by
      rw [Finset.sum_eq_single_of_mem i.2 (Finset.mem_univ _)]
      · simp
      · intro y _ hy
        simp [hy]
    simp_rw [hsum]
  rw [hcompress]
  rw [ReferenceIsometry.applyMatrix_eq_kron_conj (a := b) U]
  change K * (Matrix.conjTranspose K * τPlus.matrix * K) *
      Matrix.conjTranspose K = _
  have hE : K * Matrix.conjTranspose K =
      Matrix.kronecker (U.matrix * Matrix.conjTranspose U.matrix)
        (1 : CMatrix b) := by
    dsimp [K]
    have hconj : Matrix.conjTranspose (Matrix.kronecker U.matrix (1 : CMatrix b)) =
        Matrix.kronecker (Matrix.conjTranspose U.matrix) (1 : CMatrix b) := by
      simpa [Matrix.kronecker] using
        (Matrix.conjTranspose_kronecker U.matrix (1 : CMatrix b))
    change Matrix.kronecker U.matrix (1 : CMatrix b) *
        Matrix.conjTranspose (Matrix.kronecker U.matrix (1 : CMatrix b)) = _
    rw [hconj]
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul U.matrix (Matrix.conjTranspose U.matrix)
        (1 : CMatrix b) (1 : CMatrix b)).symm
  have hEherm : Matrix.conjTranspose
      (Matrix.kronecker (U.matrix * Matrix.conjTranspose U.matrix)
        (1 : CMatrix b)) =
      Matrix.kronecker (U.matrix * Matrix.conjTranspose U.matrix)
        (1 : CMatrix b) := by
    simp [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_mul]
  calc
    K * (Matrix.conjTranspose K * τPlus.matrix * K) *
          Matrix.conjTranspose K =
      (K * Matrix.conjTranspose K) * τPlus.matrix *
        (K * Matrix.conjTranspose K) := by simp [Matrix.mul_assoc]
    _ = Matrix.kronecker (U.matrix * Matrix.conjTranspose U.matrix)
          (1 : CMatrix b) * τPlus.matrix *
        Matrix.conjTranspose (Matrix.kronecker (U.matrix *
          Matrix.conjTranspose U.matrix) (1 : CMatrix b)) := by
        rw [hE, hEherm]

private theorem smoothIsometry_fixes_of_supports_projector
    {c : Type*} [Fintype c] [DecidableEq c]
    {M P : CMatrix c} (hM : M.PosSemidef) (hP : P.PosSemidef)
    (hPid : P * P = P) (hSupport : Matrix.Supports M P) :
    P * M = M ∧ M * P = M := by
  have hPcomp : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hPid]
    abel
  have hMcomp : M * (1 - P) = 0 := by
    ext i j
    have hv := hSupport (fun k => (1 - P) k j) (by
      ext i'
      change ∑ k, P i' k * (1 - P) k j = 0
      simpa [Matrix.mul_apply] using congrFun (congrFun hPcomp i') j)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hv i
  have hright : M * P = M := by
    calc
      M * P = M * (1 - (1 - P)) := by noncomm_ring
      _ = M := by rw [Matrix.mul_sub, hMcomp, Matrix.mul_one]; abel
  have hleft : P * M = M := by
    have hconj := congrArg Matrix.conjTranspose hright
    simpa [Matrix.conjTranspose_mul, hP.isHermitian.eq, hM.isHermitian.eq]
      using hconj
  exact ⟨hleft, hright⟩

private theorem conditioning_support_projector_supports_image
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    Matrix.Supports
      (bipartiteSupportProjector (ρ.conditioningIsometryApply V))
      (Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix)) := by
  let ρPlus := ρ.conditioningIsometryApply V
  let Q : CMatrix bPlus := V.matrix * Matrix.conjTranspose V.matrix
  let P : CMatrix (Prod a bPlus) := bipartiteSupportProjector ρPlus
  have hNB : ρPlus.marginalB.matrix * Q = ρPlus.marginalB.matrix := by
    rw [SubnormalizedState.marginalB_matrix,
      SubnormalizedState.conditioningIsometryApply_matrix]
    rw [V.partialTraceA_applyMatrixRight]
    calc
      (V.matrix * ρ.marginalB.matrix * Matrix.conjTranspose V.matrix) *
          (V.matrix * Matrix.conjTranspose V.matrix) =
        V.matrix * ρ.marginalB.matrix *
          (Matrix.conjTranspose V.matrix * V.matrix) *
            Matrix.conjTranspose V.matrix := by simp [Matrix.mul_assoc]
      _ = V.matrix * ρ.marginalB.matrix * Matrix.conjTranspose V.matrix := by
        rw [V.isometry]
        simp
  let PB : CMatrix bPlus :=
    supportProjector ρPlus.marginalB.matrix ρPlus.marginalB.pos
  have hPBQ : Matrix.Supports PB Q := by
    apply Matrix.Supports.trans
      (supportProjector_supports ρPlus.marginalB.matrix ρPlus.marginalB.pos)
    exact Matrix.Supports.of_mul_right_eq_self hNB
  have hPBfix : Q * PB = PB ∧ PB * Q = PB := by
    have hQpos : Q.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V.matrix
    have hQid : Q * Q = Q := by
      dsimp [Q]
      calc
        (V.matrix * Matrix.conjTranspose V.matrix) *
            (V.matrix * Matrix.conjTranspose V.matrix) =
          V.matrix * (Matrix.conjTranspose V.matrix * V.matrix) *
            Matrix.conjTranspose V.matrix := by simp [Matrix.mul_assoc]
        _ = Q := by rw [V.isometry]; simp [Q]
    exact smoothIsometry_fixes_of_supports_projector
      (psdInvSqrt_support_posSemidef ρPlus.marginalB.pos) hQpos hQid hPBQ
  have hPE : Matrix.Supports P (Matrix.kronecker (1 : CMatrix a) Q) := by
    apply Matrix.Supports.of_mul_right_eq_self
    dsimp [P]
    change Matrix.kronecker
        (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos) PB *
        Matrix.kronecker (1 : CMatrix a) Q =
      Matrix.kronecker
        (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos) PB
    calc
      Matrix.kronecker
          (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos) PB *
          Matrix.kronecker (1 : CMatrix a) Q =
        Matrix.kronecker
          (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos * 1)
          (PB * Q) := by
            simpa [Matrix.kronecker] using
              (Matrix.mul_kronecker_mul
                (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos)
                (1 : CMatrix a) PB Q).symm
      _ = Matrix.kronecker
          (supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos) PB := by
            rw [mul_one, hPBfix.2]
  simpa [P, Q] using hPE

private theorem source_support_projector_supports_image
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρ : SubnormalizedState (Prod a b)) (U : ReferenceIsometry a aPlus) :
    Matrix.Supports
      (bipartiteSupportProjector (ρ.sourceIsometryApply U))
      (Matrix.kronecker
        (U.matrix * Matrix.conjTranspose U.matrix) (1 : CMatrix b)) := by
  let ρPlus := ρ.sourceIsometryApply U
  let Q : CMatrix aPlus := U.matrix * Matrix.conjTranspose U.matrix
  let P : CMatrix (Prod aPlus b) := bipartiteSupportProjector ρPlus
  have hNA : ρPlus.marginalA.matrix * Q = ρPlus.marginalA.matrix := by
    rw [SubnormalizedState.marginalA_matrix,
      SubnormalizedState.sourceIsometryApply_matrix]
    rw [ReferenceIsometry.partialTraceB_applyMatrix U]
    calc
      (U.matrix * ρ.marginalA.matrix * Matrix.conjTranspose U.matrix) *
          (U.matrix * Matrix.conjTranspose U.matrix) =
        U.matrix * ρ.marginalA.matrix *
          (Matrix.conjTranspose U.matrix * U.matrix) *
            Matrix.conjTranspose U.matrix := by simp [Matrix.mul_assoc]
      _ = U.matrix * ρ.marginalA.matrix * Matrix.conjTranspose U.matrix := by
        rw [U.isometry]
        simp
  let PA : CMatrix aPlus :=
    supportProjector ρPlus.marginalA.matrix ρPlus.marginalA.pos
  have hPAQ : Matrix.Supports PA Q := by
    apply Matrix.Supports.trans
      (supportProjector_supports ρPlus.marginalA.matrix ρPlus.marginalA.pos)
    exact Matrix.Supports.of_mul_right_eq_self hNA
  have hPAfix : Q * PA = PA ∧ PA * Q = PA := by
    have hQpos : Q.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose U.matrix
    have hQid : Q * Q = Q := by
      dsimp [Q]
      calc
        (U.matrix * Matrix.conjTranspose U.matrix) *
            (U.matrix * Matrix.conjTranspose U.matrix) =
          U.matrix * (Matrix.conjTranspose U.matrix * U.matrix) *
            Matrix.conjTranspose U.matrix := by simp [Matrix.mul_assoc]
        _ = Q := by rw [U.isometry]; simp [Q]
    exact smoothIsometry_fixes_of_supports_projector
      (psdInvSqrt_support_posSemidef ρPlus.marginalA.pos) hQpos hQid hPAQ
  have hPE : Matrix.Supports P (Matrix.kronecker Q (1 : CMatrix b)) := by
    apply Matrix.Supports.of_mul_right_eq_self
    dsimp [P]
    change Matrix.kronecker PA
        (supportProjector ρPlus.marginalB.matrix ρPlus.marginalB.pos) *
        Matrix.kronecker Q (1 : CMatrix b) =
      Matrix.kronecker PA
        (supportProjector ρPlus.marginalB.matrix ρPlus.marginalB.pos)
    calc
      Matrix.kronecker PA
          (supportProjector ρPlus.marginalB.matrix ρPlus.marginalB.pos) *
          Matrix.kronecker Q (1 : CMatrix b) =
        Matrix.kronecker (PA * Q)
          (supportProjector ρPlus.marginalB.matrix ρPlus.marginalB.pos * 1) := by
            simpa [Matrix.kronecker] using
              (Matrix.mul_kronecker_mul PA Q
                (supportProjector ρPlus.marginalB.matrix ρPlus.marginalB.pos)
                (1 : CMatrix b)).symm
      _ = Matrix.kronecker PA
          (supportProjector ρPlus.marginalB.matrix ρPlus.marginalB.pos) := by
            rw [hPAfix.2, mul_one]
  simpa [P, Q] using hPE

private theorem source_support_reconstruct
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (τPlus : SubnormalizedState (Prod aPlus b)) (U : ReferenceIsometry a aPlus)
    {P : CMatrix (Prod aPlus b)}
    (hSupport : Matrix.Supports τPlus.matrix P)
    (hImage : Matrix.Supports P
      (Matrix.kronecker
        (U.matrix * Matrix.conjTranspose U.matrix) (1 : CMatrix b))) :
    (τPlus.sourceIsometryCompressed U).sourceIsometryApply U = τPlus := by
  let E : CMatrix (Prod aPlus b) := Matrix.kronecker
      (U.matrix * Matrix.conjTranspose U.matrix) (1 : CMatrix b)
  have hEpos : E.PosSemidef := by
    dsimp [E]
    exact (Matrix.posSemidef_self_mul_conjTranspose U.matrix).kronecker
      (Matrix.PosSemidef.one)
  have hEid : E * E = E := by
    dsimp [E]
    rw [← Matrix.mul_kronecker_mul]
    have hUU : (U.matrix * Matrix.conjTranspose U.matrix) *
        (U.matrix * Matrix.conjTranspose U.matrix) =
        U.matrix * Matrix.conjTranspose U.matrix := by
      calc
        (U.matrix * Matrix.conjTranspose U.matrix) *
            (U.matrix * Matrix.conjTranspose U.matrix) =
          U.matrix * (Matrix.conjTranspose U.matrix * U.matrix) *
            Matrix.conjTranspose U.matrix := by simp [Matrix.mul_assoc]
        _ = U.matrix * Matrix.conjTranspose U.matrix := by
          rw [U.isometry]
          simp
    rw [hUU, one_mul]
  have hτE : Matrix.Supports τPlus.matrix E :=
    hSupport.trans (by simpa [E] using hImage)
  have hfix := smoothIsometry_fixes_of_supports_projector τPlus.pos hEpos hEid hτE
  apply SubnormalizedState.ext
  rw [sourceIsometryCompressed_apply_matrix]
  have hrecon : E * τPlus.matrix * E = τPlus.matrix := by
    calc
      E * τPlus.matrix * E = E * (τPlus.matrix * E) := by simp [Matrix.mul_assoc]
      _ = E * τPlus.matrix := by rw [hfix.2]
      _ = τPlus.matrix := hfix.1
  simpa [E, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_mul] using hrecon

private theorem conditioning_support_reconstruct
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (τPlus : SubnormalizedState (Prod a bPlus)) (V : ReferenceIsometry b bPlus)
    {P : CMatrix (Prod a bPlus)}
    (hSupport : Matrix.Supports τPlus.matrix P)
    (hImage : Matrix.Supports P
      (Matrix.kronecker (1 : CMatrix a)
        (V.matrix * Matrix.conjTranspose V.matrix))) :
    (τPlus.conditioningIsometryCompressed V).conditioningIsometryApply V = τPlus := by
  let E : CMatrix (Prod a bPlus) := Matrix.kronecker (1 : CMatrix a)
      (V.matrix * Matrix.conjTranspose V.matrix)
  have hEpos : E.PosSemidef := by
    dsimp [E]
    exact (Matrix.PosSemidef.one).kronecker
      (Matrix.posSemidef_self_mul_conjTranspose V.matrix)
  have hEid : E * E = E := by
    dsimp [E]
    rw [← Matrix.mul_kronecker_mul]
    have hVV : (V.matrix * Matrix.conjTranspose V.matrix) *
        (V.matrix * Matrix.conjTranspose V.matrix) =
        V.matrix * Matrix.conjTranspose V.matrix := by
      calc
        (V.matrix * Matrix.conjTranspose V.matrix) *
            (V.matrix * Matrix.conjTranspose V.matrix) =
          V.matrix * (Matrix.conjTranspose V.matrix * V.matrix) *
            Matrix.conjTranspose V.matrix := by simp [Matrix.mul_assoc]
        _ = V.matrix * Matrix.conjTranspose V.matrix := by
          rw [V.isometry]
          simp
    rw [one_mul, hVV]
  have hτE : Matrix.Supports τPlus.matrix E :=
    hSupport.trans (by simpa [E] using hImage)
  have hfix := smoothIsometry_fixes_of_supports_projector τPlus.pos hEpos hEid hτE
  apply SubnormalizedState.ext
  rw [conditioningIsometryCompressed_apply_matrix]
  have hrecon : E * τPlus.matrix * E = τPlus.matrix := by
    calc
      E * τPlus.matrix * E = E * (τPlus.matrix * E) := by simp [Matrix.mul_assoc]
      _ = E * τPlus.matrix := by rw [hfix.2]
      _ = τPlus.matrix := hfix.1
  simpa [E, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_mul] using hrecon


private theorem conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_eq
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b)
    (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalMaxEntropyExponentCandidate
        (σ.referenceIsometryApply V) =
      ρ.conditionalMaxEntropyExponentCandidate σ := by
  unfold conditionalMaxEntropyExponentCandidate
  rw [conditioningIsometryApply_matrix,
    identityTensorStateMatrix_referenceIsometryApply]
  rw [V.psdSqrt_applyMatrixRight ρ.pos,
    V.psdSqrt_applyMatrixRight
      (identityTensorStateMatrix_posSemidef (a := a) σ)]
  have hmul := ReferenceIsometry.applyMatrixRight_mul V
    (psdSqrt ρ.matrix) (psdSqrt (identityTensorStateMatrix (a := a) σ))
  rw [hmul, ReferenceIsometry.traceNorm_applyMatrixRight]

theorem conditionalMaxEntropyRaw_conditioningIsometryApply_eq
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalMaxEntropyRaw =
      ρ.conditionalMaxEntropyRaw := by
  unfold conditionalMaxEntropyRaw
  apply congrArg sSup
  ext h
  constructor
  · rintro ⟨σPlus, hσ, hEq⟩
    let σ : SubnormalizedState b := referenceIsometryCompressed σPlus V
    have hexp := conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_compressed_eq
      (a := a) ρ σPlus V
    have hfid := conditionalMaxEntropyFidelityCandidate_conditioningIsometryApply_compressed_eq
      (a := a) ρ σPlus V
    refine ⟨σ, ?_, ?_⟩
    · simpa [σ] using (show 0 < ρ.conditionalMaxEntropyExponentCandidate σ from by
        rw [← hexp]
        exact hσ)
    · calc
        h = (ρ.conditioningIsometryApply V).conditionalMaxEntropyFidelityCandidate σPlus := hEq
        _ = ρ.conditionalMaxEntropyFidelityCandidate σ := by simpa [σ] using hfid
  · rintro ⟨σ, hσ, hEq⟩
    let σPlus := σ.referenceIsometryApply V
    have hcomp := referenceIsometryCompressed_referenceIsometryApply σ V
    have hexp := conditionalMaxEntropyExponentCandidate_conditioningIsometryApply_compressed_eq
      (a := a) ρ σPlus V
    have hfid := conditionalMaxEntropyFidelityCandidate_conditioningIsometryApply_compressed_eq
      (a := a) ρ σPlus V
    refine ⟨σPlus, ?_, ?_⟩
    · simpa [σPlus, hcomp] using (show 0 <
        (ρ.conditioningIsometryApply V).conditionalMaxEntropyExponentCandidate σPlus from by
          rw [hexp, hcomp]
          exact hσ)
    · calc
        h = ρ.conditionalMaxEntropyFidelityCandidate σ := hEq
        _ = (ρ.conditioningIsometryApply V).conditionalMaxEntropyFidelityCandidate σPlus := by
          rw [hfid, hcomp]

private theorem conditionalMaxEntropyExponentCandidate_sourceIsometryApply_eq
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    (ρ : SubnormalizedState (Prod a b)) (σ : SubnormalizedState b)
    (U : ReferenceIsometry a aPlus) :
    (ρ.sourceIsometryApply U).conditionalMaxEntropyExponentCandidate σ =
      ρ.conditionalMaxEntropyExponentCandidate σ := by
  unfold conditionalMaxEntropyExponentCandidate
  exact congrArg (fun x : ℝ => x ^ 2)
    (conditionalMaxEntropyTraceNorm_sourceIsometryApply_eq (a := a) ρ σ U)

private theorem conditionalMaxEntropyRaw_sourceIsometryApply_eq
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus]
    (ρ : SubnormalizedState (Prod a b)) (U : ReferenceIsometry a aPlus) :
    (ρ.sourceIsometryApply U).conditionalMaxEntropyRaw =
      ρ.conditionalMaxEntropyRaw := by
  unfold conditionalMaxEntropyRaw
  apply congrArg sSup
  ext h
  constructor
  · rintro ⟨σ, hσ, hEq⟩
    have hexp := conditionalMaxEntropyExponentCandidate_sourceIsometryApply_eq
      (a := a) ρ σ U
    refine ⟨σ, ?_, ?_⟩
    · have hσ' : 0 <
          (ρ.sourceIsometryApply U).conditionalMaxEntropyExponentCandidate σ := by
        simpa only [conditionalMaxEntropyExponentCandidate_eq] using hσ
      change 0 < ρ.conditionalMaxEntropyExponentCandidate σ
      exact hexp ▸ hσ'
    · calc
        h = (ρ.sourceIsometryApply U).conditionalMaxEntropyFidelityCandidate σ := hEq
        _ = ρ.conditionalMaxEntropyFidelityCandidate σ := by
          rw [conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
            conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
            hexp]
  · rintro ⟨σ, hσ, hEq⟩
    have hexp := conditionalMaxEntropyExponentCandidate_sourceIsometryApply_eq
      (a := a) ρ σ U
    refine ⟨σ, ?_, ?_⟩
    · have hσ' : 0 < ρ.conditionalMaxEntropyExponentCandidate σ := by
        simpa only [conditionalMaxEntropyExponentCandidate_eq] using hσ
      change 0 <
        (ρ.sourceIsometryApply U).conditionalMaxEntropyExponentCandidate σ
      exact hexp.symm ▸ hσ'
    · calc
        h = ρ.conditionalMaxEntropyFidelityCandidate σ := hEq
        _ = (ρ.sourceIsometryApply U).conditionalMaxEntropyFidelityCandidate σ := by
          rw [conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
            conditionalMaxEntropyFidelityCandidate_eq_log2_exponentCandidate,
            hexp]

/-- Smooth conditional max-entropy is invariant under an isometric embedding of
the conditioning register. -/
theorem smoothConditionalMaxEntropy_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : SubnormalizedState (Prod a b)) (V : ReferenceIsometry b bPlus) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    (ρ.conditioningIsometryApply V).smoothConditionalMaxEntropy ε hε0
        (by rwa [conditioningIsometryApply_trace_re]) =
      ρ.smoothConditionalMaxEntropy ε hε0 hε := by
  have hεPlus : ε < Real.sqrt (ρ.conditioningIsometryApply V).matrix.trace.re := by
    rwa [conditioningIsometryApply_trace_re]
  rcases ρ.smoothConditionalMaxEntropy_exists_optimizer (a := a) hε0 hε with
    ⟨τ, hτne, hτball, hτeq, hτopt⟩
  rcases (ρ.conditioningIsometryApply V).smoothConditionalMaxEntropy_exists_support_optimizer
      (a := a) hε0 hεPlus with
    ⟨τPlus, hτPlusne, hτPlusball, hτPluseq, hτPlusopt, hτPlusSupport⟩
  have hforward := purifiedBall_conditioningIsometryApply (a := a) V hτball
  have hτImage : (τ.conditioningIsometryApply V).matrix ≠ 0 := by
    intro hzero
    have htrace := conditioningIsometryApply_trace_re (ρ := τ) V
    rw [hzero] at htrace
    simp at htrace
    exact (State.posSemidef_trace_ne_zero_of_ne_zero τ.pos hτne) htrace.symm
  have hrawForward := conditionalMaxEntropyRaw_conditioningIsometryApply_eq
    (a := a) τ V
  have hrawBackward := conditionalMaxEntropyRaw_conditioningIsometryApply_eq
    (a := a) (τPlus.conditioningIsometryCompressed V) V
  have hcompressedBall :=
    purifiedBall_conditioningIsometryCompressed_of_conditioningIsometryApply
      (a := a) V hτPlusball
  have hτCompressed : (τPlus.conditioningIsometryCompressed V).matrix ≠ 0 := by
    have hpos := SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      ρ (τPlus.conditioningIsometryCompressed V) hε hcompressedBall
    intro hzero
    rw [hzero] at hpos
    simp at hpos
  have himage := conditioning_support_projector_supports_image (a := a) ρ V
  have hreconstruct := conditioning_support_reconstruct (a := a) τPlus V
    hτPlusSupport himage
  apply le_antisymm
  · calc
      (ρ.conditioningIsometryApply V).smoothConditionalMaxEntropy ε hε0 hεPlus =
          τPlus.conditionalMaxEntropyFinite hτPlusne := hτPluseq
      _ ≤ (τ.conditioningIsometryApply V).conditionalMaxEntropyFinite hτImage :=
        hτPlusopt (τ.conditioningIsometryApply V) hτImage hforward
      _ = τ.conditionalMaxEntropyFinite hτne := hrawForward
      _ = ρ.smoothConditionalMaxEntropy ε hε0 hε := hτeq.symm
  · calc
      ρ.smoothConditionalMaxEntropy ε hε0 hε =
          τ.conditionalMaxEntropyFinite hτne := hτeq
      _ ≤ (τPlus.conditioningIsometryCompressed V).conditionalMaxEntropyFinite hτCompressed :=
        hτopt _ hτCompressed hcompressedBall
      _ = τPlus.conditionalMaxEntropyFinite hτPlusne := by
        change (τPlus.conditioningIsometryCompressed V).conditionalMaxEntropyRaw =
          τPlus.conditionalMaxEntropyRaw
        rw [← hrawBackward, hreconstruct]
      _ = (ρ.conditioningIsometryApply V).smoothConditionalMaxEntropy ε hε0 hεPlus :=
        hτPluseq.symm

/-- Smooth conditional max-entropy is invariant under an isometric embedding of
the source register. -/
theorem smoothConditionalMaxEntropy_sourceIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus]
    (ρ : SubnormalizedState (Prod a b)) (U : ReferenceIsometry a aPlus) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    (ρ.sourceIsometryApply U).smoothConditionalMaxEntropy ε hε0
        (by rwa [sourceIsometryApply_trace_re]) =
      ρ.smoothConditionalMaxEntropy ε hε0 hε := by
  have hεPlus : ε < Real.sqrt (ρ.sourceIsometryApply U).matrix.trace.re := by
    rwa [sourceIsometryApply_trace_re]
  rcases ρ.smoothConditionalMaxEntropy_exists_optimizer (a := a) hε0 hε with
    ⟨τ, hτne, hτball, hτeq, hτopt⟩
  rcases (ρ.sourceIsometryApply U).smoothConditionalMaxEntropy_exists_support_optimizer
      (a := aPlus) hε0 hεPlus with
    ⟨τPlus, hτPlusne, hτPlusball, hτPluseq, hτPlusopt, hτPlusSupport⟩
  have hforward := purifiedBall_sourceIsometryApply (a := a) U hτball
  have hτImage : (τ.sourceIsometryApply U).matrix ≠ 0 := by
    intro hzero
    have htrace := sourceIsometryApply_trace_re (ρ := τ) U
    rw [hzero] at htrace
    simp at htrace
    exact (State.posSemidef_trace_ne_zero_of_ne_zero τ.pos hτne) htrace.symm
  have hrawForward := conditionalMaxEntropyRaw_sourceIsometryApply_eq
    (a := a) τ U
  have hrawBackward := conditionalMaxEntropyRaw_sourceIsometryApply_eq
    (a := a) (τPlus.sourceIsometryCompressed U) U
  have hcompressedBall :=
    purifiedBall_sourceIsometryCompressed_of_sourceIsometryApply
      (a := a) U hτPlusball
  have hτCompressed : (τPlus.sourceIsometryCompressed U).matrix ≠ 0 := by
    have hpos := SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      ρ (τPlus.sourceIsometryCompressed U) hε hcompressedBall
    intro hzero
    rw [hzero] at hpos
    simp at hpos
  have himage := source_support_projector_supports_image (a := a) ρ U
  have hreconstruct := source_support_reconstruct (a := a) τPlus U
    hτPlusSupport himage
  apply le_antisymm
  · calc
      (ρ.sourceIsometryApply U).smoothConditionalMaxEntropy ε hε0 hεPlus =
          τPlus.conditionalMaxEntropyFinite hτPlusne := hτPluseq
      _ ≤ (τ.sourceIsometryApply U).conditionalMaxEntropyFinite hτImage :=
        hτPlusopt (τ.sourceIsometryApply U) hτImage hforward
      _ = τ.conditionalMaxEntropyFinite hτne := hrawForward
      _ = ρ.smoothConditionalMaxEntropy ε hε0 hε := hτeq.symm
  · calc
      ρ.smoothConditionalMaxEntropy ε hε0 hε =
          τ.conditionalMaxEntropyFinite hτne := hτeq
      _ ≤ (τPlus.sourceIsometryCompressed U).conditionalMaxEntropyFinite hτCompressed :=
        hτopt _ hτCompressed hcompressedBall
      _ = τPlus.conditionalMaxEntropyFinite hτPlusne := by
        change (τPlus.sourceIsometryCompressed U).conditionalMaxEntropyRaw =
          τPlus.conditionalMaxEntropyRaw
        rw [← hrawBackward, hreconstruct]
      _ = (ρ.sourceIsometryApply U).smoothConditionalMaxEntropy ε hε0 hεPlus :=
        hτPluseq.symm

/-- Smooth conditional min-entropy is invariant under source and conditioning
isometric embeddings. -/
theorem smoothConditionalMinEntropy_sourceConditioningIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus] [Nonempty bPlus]
    (ρ : SubnormalizedState (Prod a b)) (U : ReferenceIsometry a aPlus)
    (V : ReferenceIsometry b bPlus) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    let τ := (ρ.sourceIsometryApply U).conditioningIsometryApply V
    τ.smoothConditionalMinEntropy ε hε0
        (by rwa [conditioningIsometryApply_trace_re, sourceIsometryApply_trace_re]) =
        ρ.smoothConditionalMinEntropy ε hε0 hε := by
  dsimp
  calc
    ((ρ.sourceIsometryApply U).conditioningIsometryApply V).smoothConditionalMinEntropy
        ε hε0 (by rwa [conditioningIsometryApply_trace_re, sourceIsometryApply_trace_re]) =
        (ρ.sourceIsometryApply U).smoothConditionalMinEntropy ε hε0
          (by rwa [sourceIsometryApply_trace_re]) :=
      smoothConditionalMinEntropy_conditioningIsometryApply
        (a := aPlus) (ρ.sourceIsometryApply U) V hε0
          (by rwa [sourceIsometryApply_trace_re])
    _ = ρ.smoothConditionalMinEntropy ε hε0 hε :=
      smoothConditionalMinEntropy_sourceIsometryApply (a := a) ρ U hε0 hε

/-- Smooth conditional max-entropy is invariant under source and conditioning
isometric embeddings. -/
theorem smoothConditionalMaxEntropy_sourceConditioningIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus] [Nonempty bPlus]
    (ρ : SubnormalizedState (Prod a b)) (U : ReferenceIsometry a aPlus)
    (V : ReferenceIsometry b bPlus) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    let τ := (ρ.sourceIsometryApply U).conditioningIsometryApply V
    τ.smoothConditionalMaxEntropy ε hε0
        (by rwa [conditioningIsometryApply_trace_re, sourceIsometryApply_trace_re]) =
        ρ.smoothConditionalMaxEntropy ε hε0 hε := by
  dsimp
  calc
    ((ρ.sourceIsometryApply U).conditioningIsometryApply V).smoothConditionalMaxEntropy
        ε hε0 (by rwa [conditioningIsometryApply_trace_re, sourceIsometryApply_trace_re]) =
        (ρ.sourceIsometryApply U).smoothConditionalMaxEntropy ε hε0
          (by rwa [sourceIsometryApply_trace_re]) :=
      smoothConditionalMaxEntropy_conditioningIsometryApply
        (a := aPlus) (ρ.sourceIsometryApply U) V hε0
          (by rwa [sourceIsometryApply_trace_re])
    _ = ρ.smoothConditionalMaxEntropy ε hε0 hε :=
      smoothConditionalMaxEntropy_sourceIsometryApply (a := a) ρ U hε0 hε

/-- Smooth conditional min- and max-entropy are simultaneously invariant under
isometric embeddings of both registers. -/
theorem smoothConditionalMinMaxEntropy_sourceConditioningIsometryApply
    {aPlus : Type*} [Fintype aPlus] [DecidableEq aPlus]
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty aPlus] [Nonempty bPlus]
    (ρ : SubnormalizedState (Prod a b)) (U : ReferenceIsometry a aPlus)
    (V : ReferenceIsometry b bPlus) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < Real.sqrt ρ.matrix.trace.re) :
    let τ := (ρ.sourceIsometryApply U).conditioningIsometryApply V
    τ.smoothConditionalMinEntropy ε hε0
        (by rwa [conditioningIsometryApply_trace_re, sourceIsometryApply_trace_re]) =
        ρ.smoothConditionalMinEntropy ε hε0 hε ∧
      τ.smoothConditionalMaxEntropy ε hε0
        (by rwa [conditioningIsometryApply_trace_re, sourceIsometryApply_trace_re]) =
        ρ.smoothConditionalMaxEntropy ε hε0 hε := by
  dsimp
  constructor
  · calc
      ((ρ.sourceIsometryApply U).conditioningIsometryApply V).smoothConditionalMinEntropy
          ε hε0 (by rwa [conditioningIsometryApply_trace_re, sourceIsometryApply_trace_re]) =
          (ρ.sourceIsometryApply U).smoothConditionalMinEntropy ε hε0
            (by rwa [sourceIsometryApply_trace_re]) :=
        smoothConditionalMinEntropy_conditioningIsometryApply
          (a := aPlus) (ρ.sourceIsometryApply U) V hε0
            (by rwa [sourceIsometryApply_trace_re])
      _ = ρ.smoothConditionalMinEntropy ε hε0 hε :=
        smoothConditionalMinEntropy_sourceIsometryApply (a := a) ρ U hε0 hε
  · calc
      ((ρ.sourceIsometryApply U).conditioningIsometryApply V).smoothConditionalMaxEntropy
          ε hε0 (by rwa [conditioningIsometryApply_trace_re, sourceIsometryApply_trace_re]) =
          (ρ.sourceIsometryApply U).smoothConditionalMaxEntropy ε hε0
            (by rwa [sourceIsometryApply_trace_re]) :=
        smoothConditionalMaxEntropy_conditioningIsometryApply
          (a := aPlus) (ρ.sourceIsometryApply U) V hε0
            (by rwa [sourceIsometryApply_trace_re])
      _ = ρ.smoothConditionalMaxEntropy ε hε0 hε :=
        smoothConditionalMaxEntropy_sourceIsometryApply (a := a) ρ U hε0 hε

end SubnormalizedState

end

end QIT
