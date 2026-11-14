/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.YangNavascues

/-!
# Rank-one reduced-support bridge for Yang-Navascues Bob projections

This module supplies the pure-state bridge needed by the safe Bob-local
orthogonalization route.  For a pure bipartite vector `ψ`, the reduced Bob
support of the projected vector `(1 ⊗ P_B^(k)) ψ` has the same left
state-support action on `ψ.state` as the original Bob projection.

The result is intentionally rank-one/pure-state only.  It does not assert an
arbitrary mixed-state bridge, nor the stronger false statement that every
Bob-local operator fixing the reduced support has the same action as the
original projection.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u v w

noncomputable section

namespace Matrix

variable {HA : Type v} {HB : Type w}
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

/-- View a bipartite vector as a Bob-by-Alice amplitude matrix. -/
def bobAmplitudeMatrix (φ : HA × HB → ℂ) : Matrix HB HA ℂ :=
  fun b a => φ (a, b)

omit [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB] in
@[simp]
theorem bobAmplitudeMatrix_apply (φ : HA × HB → ℂ) (b : HB) (a : HA) :
    bobAmplitudeMatrix φ b a = φ (a, b) :=
  rfl

omit [DecidableEq HA] [Fintype HB] [DecidableEq HB] in
/-- Tracing out Alice from a rank-one bipartite vector gives the Bob-side
amplitude Gram matrix. -/
theorem partialTraceA_rankOneMatrix_eq_bobAmplitudeMatrix_mul_conjTranspose
    (φ : HA × HB → ℂ) :
    partialTraceA (a := HA) (b := HB) (rankOneMatrix φ) =
      bobAmplitudeMatrix φ * Matrix.conjTranspose (bobAmplitudeMatrix φ) := by
  ext b b'
  simp [partialTraceA, rankOneMatrix_apply, bobAmplitudeMatrix, Matrix.mul_apply]

omit [DecidableEq HB] in
/-- Applying a Bob-local operator corresponds to left multiplication of the
Bob-by-Alice amplitude matrix. -/
theorem bobAmplitudeMatrix_kronecker_mulVec
    (P : CMatrix HB) (φ : HA × HB → ℂ) :
    bobAmplitudeMatrix ((Matrix.kronecker (1 : CMatrix HA) P).mulVec φ) =
      P * bobAmplitudeMatrix φ := by
  ext b a
  simp [bobAmplitudeMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

omit [DecidableEq HB] in
/-- Coordinate form of a Bob-local operator acting on a bipartite vector. -/
theorem kronecker_one_mulVec_apply
    (P : CMatrix HB) (φ : HA × HB → ℂ) (a : HA) (b : HB) :
    (Matrix.kronecker (1 : CMatrix HA) P).mulVec φ (a, b) =
      P.mulVec (fun b' => φ (a, b')) b := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

/-- Linear-map form of the projection fact used below.  If `P` is an
orthogonal projection, then the orthogonal projection onto `range (P ∘ T)`
sends `T x` to `P (T x)`. -/
theorem starProjection_range_comp_projection_apply
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [FiniteDimensional ℂ F]
    (T : E →ₗ[ℂ] F) (P : F →ₗ[ℂ] F)
    (hPsym : P.IsSymmetric) (hPid : P.comp P = P) (x : E) :
    (LinearMap.range (P.comp T)).starProjection (T x) = P (T x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨x, rfl⟩
  · intro w hw
    rcases hw with ⟨z, rfl⟩
    change inner ℂ (T x - P (T x)) (P (T z)) = 0
    have hsym := hPsym (T x - P (T x)) (T z)
    have hzero : P (T x - P (T x)) = 0 := by
      rw [map_sub]
      change P (T x) - (P.comp P) (T x) = 0
      rw [hPid]
      simp
    calc
      inner ℂ (T x - P (T x)) (P (T z)) =
          inner ℂ (P (T x - P (T x))) (T z) := hsym.symm
      _ = 0 := by simp [hzero]

/-- The support projection of an amplitude Gram matrix fixes every column
slice of the amplitude matrix. -/
theorem rangeProjection_amplitudeGram_mulVec
    (A : Matrix HB HA ℂ) (a : HA) :
    (Matrix.rangeProjection (A * Matrix.conjTranspose A)).mulVec
        (fun b => A b a) =
      fun b => A b a := by
  let M : CMatrix HB := A * Matrix.conjTranspose A
  let v : HB → ℂ := fun b => A b a
  have hslice : A.toEuclideanLin (WithLp.toLp 2 (Pi.single a (1 : ℂ))) =
      WithLp.toLp 2 v := by
    ext b
    simp [v, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hv : WithLp.toLp 2 v ∈ LinearMap.range M.toEuclideanLin := by
    have hrange : LinearMap.range M.toEuclideanLin = LinearMap.range A.toEuclideanLin := by
      dsimp [M]
      rw [Matrix.toLpLin_mul]
      rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      exact LinearMap.range_self_comp_adjoint A.toEuclideanLin
    rw [hrange]
    exact ⟨WithLp.toLp 2 (Pi.single a (1 : ℂ)), hslice⟩
  have hstar := (LinearMap.range M.toEuclideanLin).starProjection_eq_self_iff.mpr hv
  have hlin := congrArg
    (fun f : EuclideanSpace ℂ HB →ₗ[ℂ] EuclideanSpace ℂ HB => f (WithLp.toLp 2 v))
    (Matrix.rangeProjection_toEuclideanLin M)
  have hto : (Matrix.rangeProjection M).toEuclideanLin (WithLp.toLp 2 v) =
      WithLp.toLp 2 v :=
    hlin.trans hstar
  have hto' := congrArg WithLp.ofLp hto
  change (Matrix.rangeProjection M).mulVec v = v at hto'
  simpa [M, v] using hto'

/-- Generic rank-one bridge: the Bob-local lift of the reduced support of a
rank-one bipartite vector fixes that vector. -/
theorem kronecker_rangeProjection_partialTraceA_rankOne_mulVec
    (φ : HA × HB → ℂ) :
    (Matrix.kronecker (1 : CMatrix HA)
      (Matrix.rangeProjection (partialTraceA (a := HA) (b := HB) (rankOneMatrix φ)))).mulVec φ =
        φ := by
  let A := bobAmplitudeMatrix φ
  have hM :
      partialTraceA (a := HA) (b := HB) (rankOneMatrix φ) =
        A * Matrix.conjTranspose A := by
    rw [partialTraceA_rankOneMatrix_eq_bobAmplitudeMatrix_mul_conjTranspose]
  change
    (Matrix.kronecker (1 : CMatrix HA)
      (Matrix.rangeProjection (partialTraceA (a := HA) (b := HB) (rankOneMatrix φ)))).mulVec φ =
        φ
  rw [hM]
  funext x
  rcases x with ⟨a, b⟩
  have hslice := rangeProjection_amplitudeGram_mulVec (HA := HA) (HB := HB) A a
  have hslice_b := congrFun hslice b
  calc
    (Matrix.kronecker (1 : CMatrix HA)
        (Matrix.rangeProjection (A * Matrix.conjTranspose A))).mulVec φ (a, b)
        =
          (Matrix.rangeProjection (A * Matrix.conjTranspose A)).mulVec
            (fun b' => φ (a, b')) b := by
            rw [kronecker_one_mulVec_apply]
    _ = φ (a, b) := by
            simpa [A, bobAmplitudeMatrix] using hslice_b

/-- If `P` is a Hermitian idempotent matrix and `A` is a Bob-by-Alice
amplitude matrix, the support projection of `(P*A)*(P*A)ᴴ` acts on each
unprojected Alice slice as `P` does. -/
theorem rangeProjection_projection_amplitudeGram_mulVec
    (P : CMatrix HB) (hPherm : P.IsHermitian) (hPid : P * P = P)
    (A : Matrix HB HA ℂ) (a : HA) :
    (Matrix.rangeProjection ((P * A) * Matrix.conjTranspose (P * A))).mulVec
        (fun b => A b a) =
      P.mulVec (fun b => A b a) := by
  let T : EuclideanSpace ℂ HA →ₗ[ℂ] EuclideanSpace ℂ HB := A.toEuclideanLin
  let Plin : EuclideanSpace ℂ HB →ₗ[ℂ] EuclideanSpace ℂ HB := P.toEuclideanLin
  let B : Matrix HB HA ℂ := P * A
  let M : CMatrix HB := B * Matrix.conjTranspose B
  let v : HB → ℂ := fun b => A b a
  have hslice : T (WithLp.toLp 2 (Pi.single a (1 : ℂ))) = WithLp.toLp 2 v := by
    ext b
    simp [T, v, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hslice' : T (PiLp.single 2 a (1 : ℂ)) = WithLp.toLp 2 v := by
    simpa [PiLp.toLp_single] using hslice
  have hPids : Plin.comp Plin = Plin := by
    change P.toEuclideanLin.comp P.toEuclideanLin = P.toEuclideanLin
    rw [← Matrix.toLpLin_mul]
    simpa using
      congrArg Matrix.toEuclideanLin hPid
  have hstar :=
    starProjection_range_comp_projection_apply T Plin
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hPherm) hPids
      (WithLp.toLp 2 (Pi.single a (1 : ℂ)))
  have hstar' : (LinearMap.range (Plin.comp T)).starProjection (WithLp.toLp 2 v) =
      Plin (WithLp.toLp 2 v) := by
    simpa [hslice'] using hstar
  have hrangeM : LinearMap.range M.toEuclideanLin = LinearMap.range (Plin.comp T) := by
    dsimp [M, B, Plin, T]
    rw [Matrix.toLpLin_mul]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [Matrix.toLpLin_mul]
    exact LinearMap.range_self_comp_adjoint (P.toEuclideanLin.comp A.toEuclideanLin)
  have hstarM : (LinearMap.range M.toEuclideanLin).starProjection (WithLp.toLp 2 v) =
      P.toEuclideanLin (WithLp.toLp 2 v) := by
    simpa [hrangeM, Plin, Matrix.toLpLin_toLp] using hstar'
  have hlin := congrArg
    (fun f : EuclideanSpace ℂ HB →ₗ[ℂ] EuclideanSpace ℂ HB => f (WithLp.toLp 2 v))
    (Matrix.rangeProjection_toEuclideanLin M)
  have hto : (Matrix.rangeProjection M).toEuclideanLin (WithLp.toLp 2 v) =
      P.toEuclideanLin (WithLp.toLp 2 v) :=
    hlin.trans hstarM
  have hto' := congrArg WithLp.ofLp hto
  change (Matrix.rangeProjection M).mulVec v = P.mulVec v at hto'
  simpa [M, B, v] using hto'

/-- Rank-one support bridge: for a Bob-local projection `P`, the support of
the reduced Bob state of `(1 ⊗ P)φ` acts on the original bipartite vector
exactly as `(1 ⊗ P)` does. -/
theorem kronecker_rangeProjection_partialTraceA_rankOne_projection_mulVec
    (P : CMatrix HB) (hPherm : P.IsHermitian) (hPid : P * P = P)
    (φ : HA × HB → ℂ) :
    (Matrix.kronecker (1 : CMatrix HA)
      (Matrix.rangeProjection
        (partialTraceA (a := HA) (b := HB)
          (rankOneMatrix ((Matrix.kronecker (1 : CMatrix HA) P).mulVec φ))))).mulVec φ =
      (Matrix.kronecker (1 : CMatrix HA) P).mulVec φ := by
  let A := bobAmplitudeMatrix φ
  have hAmp :=
    bobAmplitudeMatrix_kronecker_mulVec (HA := HA) (HB := HB) P φ
  have hM :
      partialTraceA (a := HA) (b := HB)
          (rankOneMatrix ((Matrix.kronecker (1 : CMatrix HA) P).mulVec φ)) =
        (P * A) * Matrix.conjTranspose (P * A) := by
    rw [partialTraceA_rankOneMatrix_eq_bobAmplitudeMatrix_mul_conjTranspose]
    rw [hAmp]
  change
    (Matrix.kronecker (1 : CMatrix HA)
      (Matrix.rangeProjection
        (partialTraceA (a := HA) (b := HB)
          (rankOneMatrix ((Matrix.kronecker (1 : CMatrix HA) P).mulVec φ))))).mulVec φ =
      (Matrix.kronecker (1 : CMatrix HA) P).mulVec φ
  rw [hM]
  funext x
  rcases x with ⟨a, b⟩
  have hslice :=
    rangeProjection_projection_amplitudeGram_mulVec
      (HA := HA) (HB := HB) P hPherm hPid A a
  have hslice_b := congrFun hslice b
  calc
    (Matrix.kronecker (1 : CMatrix HA)
        (Matrix.rangeProjection (P * A * Matrix.conjTranspose (P * A)))).mulVec φ (a, b)
        =
          (Matrix.rangeProjection (P * A * Matrix.conjTranspose (P * A))).mulVec
            (fun b' => φ (a, b')) b := by
            rw [kronecker_one_mulVec_apply]
    _ = P.mulVec (fun b' => φ (a, b')) b := by
            simpa [A, bobAmplitudeMatrix] using hslice_b
    _ = (Matrix.kronecker (1 : CMatrix HA) P).mulVec φ (a, b) := by
            rw [kronecker_one_mulVec_apply]

/-- A vector equality gives same left action on the corresponding rank-one
state support. -/
theorem sameOnStateSupport_rankOneMatrix_of_mulVec_eq
    {a : Type*} [Fintype a] [DecidableEq a]
    {Q R : CMatrix a} {φ : a → ℂ} (h : Q.mulVec φ = R.mulVec φ) :
    Matrix.sameOnStateSupport (rankOneMatrix φ) Q R := by
  change Q * rankOneMatrix φ = R * rankOneMatrix φ
  simp only [rankOneMatrix]
  rw [Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, h]

end Matrix

namespace YangNavascues
namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/-- The pure vector obtained by applying Bob's original projection `P_B^(k)`. -/
def bobProjectedVector (ψ : PureVector (HA × HB)) (k : ι) : HA × HB → ℂ :=
  (data.bobProjectionOp k).mulVec ψ.amp

/-- Bob's reduced density matrix of the projected pure vector. -/
def bobProjectedReducedMatrix (ψ : PureVector (HA × HB)) (k : ι) : CMatrix HB :=
  partialTraceA (a := HA) (b := HB) (rankOneMatrix (data.bobProjectedVector ψ k))

/-- Support projection of Bob's reduced projected density matrix. -/
def bobProjectedReducedSupport (ψ : PureVector (HA × HB)) (k : ι) : CMatrix HB :=
  Matrix.rangeProjection (data.bobProjectedReducedMatrix ψ k)

@[simp]
theorem bobProjectedVector_eq (ψ : PureVector (HA × HB)) (k : ι) :
    data.bobProjectedVector ψ k = (data.bobProjectionOp k).mulVec ψ.amp :=
  rfl

@[simp]
theorem bobProjectedReducedMatrix_eq (ψ : PureVector (HA × HB)) (k : ι) :
    data.bobProjectedReducedMatrix ψ k =
      partialTraceA (a := HA) (b := HB) (rankOneMatrix (data.bobProjectedVector ψ k)) :=
  rfl

@[simp]
theorem bobProjectedReducedSupport_eq (ψ : PureVector (HA × HB)) (k : ι) :
    data.bobProjectedReducedSupport ψ k =
      Matrix.rangeProjection (data.bobProjectedReducedMatrix ψ k) :=
  rfl

/--
The reduced support projection of `(1 ⊗ P_B^(k))ψ` has the same left action on
the rank-one state support of `ψ` as the original Bob projection.

This is deliberately a pure/rank-one theorem.  It does not claim an arbitrary
mixed-state support bridge or an arbitrary support-fixing replacement theorem.
-/
theorem bobProjectedReducedSupport_sameOnStateSupport
    (ψ : PureVector (HA × HB)) (k : ι) :
    Matrix.sameOnStateSupport ψ.state.matrix
      (data.bobLocalOp (data.bobProjectedReducedSupport ψ k))
      (data.bobProjectionOp k) := by
  have hvec :
      (data.bobLocalOp (data.bobProjectedReducedSupport ψ k)).mulVec ψ.amp =
        (data.bobProjectionOp k).mulVec ψ.amp := by
    rw [bobLocalOp_eq, bobProjectionOp_eq]
    change
      (Matrix.kronecker (1 : CMatrix HA)
        (Matrix.rangeProjection
          (partialTraceA (a := HA) (b := HB)
            (rankOneMatrix ((Matrix.kronecker (1 : CMatrix HA)
              ((data.bobProjection k).matrix)).mulVec ψ.amp))))).mulVec ψ.amp =
        (Matrix.kronecker (1 : CMatrix HA) ((data.bobProjection k).matrix)).mulVec ψ.amp
    exact Matrix.kronecker_rangeProjection_partialTraceA_rankOne_projection_mulVec
      ((data.bobProjection k).matrix)
      (data.bobProjection k).isHermitian
      (data.bobProjection k).idempotent
      ψ.amp
  simpa [PureVector.state_matrix] using
    Matrix.sameOnStateSupport_rankOneMatrix_of_mulVec_eq hvec

/-- Wrapper form directly usable by the Bob-local post-selected matrix API. -/
theorem bobProjectedReducedSupport_bobLocalSamePostMatrix
    (ψ : PureVector (HA × HB)) (k : ι) :
    data.BobLocalSamePostMatrix ψ.state
      (data.bobProjectedReducedSupport ψ k)
      ((data.bobProjection k).matrix) := by
  exact data.bobLocalSamePostMatrix_of_sameOnStateSupport ψ.state
    (data.bobProjectedReducedSupport ψ k)
    ((data.bobProjection k).matrix)
    (data.bobProjectedReducedSupport_sameOnStateSupport ψ k)

end YNData
end YangNavascues

end

end QIT
