/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.POVMProbability
public import QIT.Measurements.Projective
public import QIT.States.PosSqrt
public import QIT.States.Purification.GramFactorization

/-!
# Single-POVM Naimark dilation

This module gives the finite constructive Naimark dilation used by the
projective-realization route.  For a finite POVM `M : POVM y a`, the dilation
space is the direct-sum-like index type `a × y`; the embedding stacks the
positive square-roots of the POVM effects, and the projective measurement reads
the outcome coordinate.  The construction preserves Born-rule probabilities.

This is the single-measurement dependency for the POVM-to-projective reduction
recorded in [ColadangeloGohScarani2016SelfTesting, all_pure_v2.tex:124-128]
and [MayersYao2003SelfTesting, mayers-yao-2003-self-testing.tex:307-325].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w

noncomputable section

namespace POVM

variable {y : Type u} {a : Type v}
variable [Fintype y] [DecidableEq y] [Fintype a] [DecidableEq a]

/-- The finite dilation space for the constructive single-POVM Naimark lift. -/
abbrev NaimarkSpace (_M : POVM y a) : Type (max u v) :=
  a × y

/--
The fixed-base Naimark space used by finite families.  It is definitionally the
same finite block space as `NaimarkSpace`, but the embedding below is the fixed
inclusion into the default outcome block rather than the POVM-dependent stacked
square-root embedding.
-/
abbrev FixedNaimarkSpace (_M : POVM y a) : Type (max u v) :=
  a × y

omit [DecidableEq a] in
private theorem sum_naimarkBlock_eq (outcome : y) (f : a → ℂ) :
    ∑ idx : a × y, (if idx.2 = outcome then f idx.1 else 0) = ∑ row : a, f row := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun row _ => ?_
  rw [Finset.sum_eq_single outcome]
  · simp
  · intro other _ hother
    simp [hother]
  · intro hnot
    simp at hnot

/-- The projective dilation effect selecting one outcome block. -/
def naimarkProjector (M : POVM y a) (outcome : y) : CMatrix M.NaimarkSpace :=
  Matrix.diagonal fun idx : M.NaimarkSpace => if idx.2 = outcome then 1 else 0

/-- The Naimark embedding stacks the square roots of the POVM effects. -/
def naimarkEmbedding (M : POVM y a) : Matrix M.NaimarkSpace a ℂ :=
  fun idx col => psdSqrt (M.effects idx.2) idx.1 col

/-- The fixed embedding into the default outcome block of the Naimark space. -/
def fixedNaimarkEmbedding [Inhabited y] (M : POVM y a) :
    Matrix M.FixedNaimarkSpace a ℂ :=
  fun idx col => if idx = (col, default) then 1 else 0

@[simp]
theorem naimarkProjector_apply (M : POVM y a) (outcome : y)
    (i j : M.NaimarkSpace) :
    M.naimarkProjector outcome i j =
      if i = j then if i.2 = outcome then 1 else 0 else 0 := by
  by_cases hij : i = j <;> simp [naimarkProjector, Matrix.diagonal, hij]

omit [DecidableEq y] in
@[simp]
theorem naimarkEmbedding_apply (M : POVM y a) (idx : M.NaimarkSpace) (col : a) :
    M.naimarkEmbedding idx col = psdSqrt (M.effects idx.2) idx.1 col :=
  rfl

@[simp]
theorem fixedNaimarkEmbedding_apply [Inhabited y] (M : POVM y a)
    (idx : M.FixedNaimarkSpace) (col : a) :
    M.fixedNaimarkEmbedding idx col = if idx = (col, default) then 1 else 0 :=
  rfl

/-- The fixed block embedding is an isometry. -/
theorem fixedNaimarkEmbedding_isometry [Inhabited y] (M : POVM y a) :
    Matrix.conjTranspose M.fixedNaimarkEmbedding * M.fixedNaimarkEmbedding = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single (i, default)]
    · simp [Matrix.conjTranspose_apply]
    · intro idx _ hidx
      simp [Matrix.conjTranspose_apply, hidx]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro idx _
      by_cases hi : idx = (i, default)
      · subst idx
        simp [Matrix.conjTranspose_apply, hij]
      · simp [Matrix.conjTranspose_apply, hi]

/-- The Naimark projectors are Hermitian. -/
theorem naimarkProjector_isHermitian (M : POVM y a) (outcome : y) :
    (M.naimarkProjector outcome).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.2 = outcome <;> simp [naimarkProjector, Matrix.diagonal, hi]
  · simp [naimarkProjector, Matrix.diagonal, hij, ne_comm.mp hij]

/-- The Naimark projectors are idempotent. -/
theorem naimarkProjector_idempotent (M : POVM y a) (outcome : y) :
    M.naimarkProjector outcome * M.naimarkProjector outcome =
      M.naimarkProjector outcome := by
  simp [naimarkProjector, Matrix.diagonal_mul_diagonal]

/-- Distinct Naimark projectors are orthogonal. -/
theorem naimarkProjector_orthogonal (M : POVM y a) (i j : y) (hij : i ≠ j) :
    M.naimarkProjector i * M.naimarkProjector j = 0 := by
  ext r c
  by_cases hrc : r = c
  · subst c
    by_cases hi : r.2 = i
    · have hj : r.2 ≠ j := by
        intro h
        exact hij (hi.symm.trans h)
      simp [naimarkProjector, hi, hij]
    · simp [naimarkProjector, hi]
  · simp [naimarkProjector, hrc]

/-- The Naimark projectors form a complete projective measurement. -/
theorem naimarkProjector_sum_eq_one (M : POVM y a) :
    ∑ outcome : y, M.naimarkProjector outcome = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.sum_apply]
    simp only [naimarkProjector, Matrix.diagonal_apply, if_true, Matrix.one_apply]
    rw [Finset.sum_eq_single i.2]
    · simp
    · intro other _ hother
      have hi : i.2 ≠ other := fun h => hother h.symm
      simp [hi]
    · intro hnot
      simp at hnot
  · rw [Matrix.sum_apply]
    simp [naimarkProjector, Matrix.diagonal, hij]

/-- The projective measurement associated to the single-POVM Naimark lift. -/
def naimarkProjectiveMeasurement (M : POVM y a) :
    ProjectiveMeasurement y M.NaimarkSpace where
  effects := M.naimarkProjector
  isHermitian := M.naimarkProjector_isHermitian
  idempotent := M.naimarkProjector_idempotent
  orthogonal := M.naimarkProjector_orthogonal
  sum_eq_one := M.naimarkProjector_sum_eq_one

omit [DecidableEq y] in
/-- The Naimark embedding is an isometry. -/
theorem naimarkEmbedding_isometry (M : POVM y a) :
    Matrix.conjTranspose M.naimarkEmbedding * M.naimarkEmbedding = 1 := by
  ext i j
  have hstar : ∀ (outcome : y) (row : a),
      star (psdSqrt (M.effects outcome) row i) =
        psdSqrt (M.effects outcome) i row := by
    intro outcome row
    have h := congrFun (congrFun (psdSqrt_isHermitian (M.effects outcome)) i) row
    simpa [Matrix.conjTranspose_apply] using h
  calc
    (Matrix.conjTranspose M.naimarkEmbedding * M.naimarkEmbedding) i j
        = ∑ outcome : y,
            ∑ row : a,
              psdSqrt (M.effects outcome) i row *
                psdSqrt (M.effects outcome) row j := by
          rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
          simp [naimarkEmbedding, Matrix.conjTranspose_apply, hstar]
    _ = ∑ outcome : y,
            (psdSqrt (M.effects outcome) * psdSqrt (M.effects outcome)) i j := by
          simp [Matrix.mul_apply]
    _ = (∑ outcome : y, M.effects outcome) i j := by
          simp [psdSqrt_mul_self_of_posSemidef (M.pos _), Matrix.sum_apply]
    _ = (1 : CMatrix a) i j := by
          rw [M.sum_eq_one]

/--
Compressing a Naimark projector by the embedding recovers the original POVM
effect.
-/
theorem naimark_compression_projector (M : POVM y a) (outcome : y) :
    Matrix.conjTranspose M.naimarkEmbedding * M.naimarkProjector outcome *
        M.naimarkEmbedding = M.effects outcome := by
  ext i j
  have hstar : ∀ row : a,
      star (psdSqrt (M.effects outcome) row i) =
        psdSqrt (M.effects outcome) i row := by
    intro row
    have h := congrFun (congrFun (psdSqrt_isHermitian (M.effects outcome)) i) row
    simpa [Matrix.conjTranspose_apply] using h
  calc
    (Matrix.conjTranspose M.naimarkEmbedding * M.naimarkProjector outcome *
        M.naimarkEmbedding) i j
        = ∑ idx : M.NaimarkSpace,
            (if idx.2 = outcome then
              star (psdSqrt (M.effects idx.2) idx.1 i) *
                psdSqrt (M.effects idx.2) idx.1 j
            else 0) := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun idx _ => ?_
          simp [naimarkEmbedding, naimarkProjector, Matrix.mul_diagonal,
            Matrix.conjTranspose_apply]
    _ = ∑ idx : M.NaimarkSpace,
          (if idx.2 = outcome then
            star (psdSqrt (M.effects outcome) idx.1 i) *
              psdSqrt (M.effects outcome) idx.1 j
          else 0) := by
          refine Finset.sum_congr rfl fun idx _ => ?_
          by_cases hidx : idx.2 = outcome <;> simp [hidx]
    _ = ∑ row : a,
          psdSqrt (M.effects outcome) i row *
            psdSqrt (M.effects outcome) row j := by
          simpa [hstar] using
            (sum_naimarkBlock_eq (outcome := outcome)
              (f := fun row : a =>
                star (psdSqrt (M.effects outcome) row i) *
                  psdSqrt (M.effects outcome) row j))
    _ = (psdSqrt (M.effects outcome) * psdSqrt (M.effects outcome)) i j := by
          simp [Matrix.mul_apply]
    _ = M.effects outcome i j := by
          rw [psdSqrt_mul_self_of_posSemidef (M.pos outcome)]

/-- The lifted state in the Naimark dilation space. -/
def naimarkLiftState (M : POVM y a) (rho : State a) : State M.NaimarkSpace where
  matrix := M.naimarkEmbedding * rho.matrix * Matrix.conjTranspose M.naimarkEmbedding
  pos := rho.pos.mul_mul_conjTranspose_same M.naimarkEmbedding
  trace_eq_one := by
    rw [Matrix.trace_mul_cycle, M.naimarkEmbedding_isometry, Matrix.one_mul, rho.trace_eq_one]

/-- Matrix formula for the lifted state. -/
@[simp]
theorem naimarkLiftState_matrix (M : POVM y a) (rho : State a) :
    (M.naimarkLiftState rho).matrix =
      M.naimarkEmbedding * rho.matrix * Matrix.conjTranspose M.naimarkEmbedding :=
  rfl

/-- The Naimark dilation preserves the complex Born-rule trace. -/
theorem naimark_trace_projector_eq (M : POVM y a) (rho : State a) (outcome : y) :
    ((M.naimarkLiftState rho).matrix * M.naimarkProjector outcome).trace =
      (rho.matrix * M.effects outcome).trace := by
  calc
    ((M.naimarkLiftState rho).matrix * M.naimarkProjector outcome).trace
        =
          (rho.matrix *
            (Matrix.conjTranspose M.naimarkEmbedding * M.naimarkProjector outcome *
              M.naimarkEmbedding)).trace := by
            rw [naimarkLiftState_matrix]
            calc
              ((M.naimarkEmbedding * rho.matrix *
                      Matrix.conjTranspose M.naimarkEmbedding) *
                    M.naimarkProjector outcome).trace
                  =
                    (M.naimarkEmbedding * rho.matrix *
                      (Matrix.conjTranspose M.naimarkEmbedding *
                        M.naimarkProjector outcome)).trace := by
                    rw [Matrix.mul_assoc, Matrix.mul_assoc]
              _ =
                    (rho.matrix *
                      ((Matrix.conjTranspose M.naimarkEmbedding *
                          M.naimarkProjector outcome) *
                        M.naimarkEmbedding)).trace := by
                    rw [Matrix.trace_mul_cycle]
                    rw [Matrix.trace_mul_comm]
              _ =
                    (rho.matrix *
                      (Matrix.conjTranspose M.naimarkEmbedding *
                        M.naimarkProjector outcome *
                        M.naimarkEmbedding)).trace := by
                    rw [Matrix.mul_assoc]
    _ = (rho.matrix * M.effects outcome).trace := by
          rw [M.naimark_compression_projector outcome]

/-- The single-POVM Naimark lift preserves Born-rule outcome probabilities. -/
theorem naimark_prob_eq (M : POVM y a) (rho : State a) (outcome : y) :
    (M.naimarkProjectiveMeasurement.toPOVM).prob (M.naimarkLiftState rho) outcome =
      M.prob rho outcome := by
  apply NNReal.eq
  rw [POVM.prob_eq_trace_re, POVM.prob_eq_trace_re]
  change Complex.re (((M.naimarkLiftState rho).matrix *
      M.naimarkProjector outcome).trace) =
    Complex.re ((rho.matrix * M.effects outcome).trace)
  rw [M.naimark_trace_projector_eq rho outcome]

private theorem starMap_conjTranspose_mul_self {n : Type _} [Fintype n] [DecidableEq n]
    (U : CMatrix n) (hU : Matrix.conjTranspose U * U = 1) :
    Matrix.conjTranspose (U.map star) * U.map star = 1 := by
  ext i j
  have h := congrFun (congrFun hU j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose, Matrix.one_apply, mul_comm,
    eq_comm] using h

private theorem starMap_mul_conjTranspose_self {n : Type _} [Fintype n] [DecidableEq n]
    (U : CMatrix n) (hU : U * Matrix.conjTranspose U = 1) :
    U.map star * Matrix.conjTranspose (U.map star) = 1 := by
  ext i j
  have h := congrFun (congrFun hU j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose, Matrix.one_apply, mul_comm,
    eq_comm] using h

theorem fixedNaimarkUnitary_exists [Inhabited y] (M : POVM y a) :
    ∃ U : CMatrix M.FixedNaimarkSpace,
      Matrix.conjTranspose U * U = 1 ∧
        U * Matrix.conjTranspose U = 1 ∧
          U * M.fixedNaimarkEmbedding = M.naimarkEmbedding := by
  classical
  let J : Matrix M.FixedNaimarkSpace a ℂ := M.fixedNaimarkEmbedding
  let W : Matrix M.NaimarkSpace a ℂ := M.naimarkEmbedding
  have hGram :
      Matrix.conjTranspose J * Matrix.conjTranspose (Matrix.conjTranspose J) =
        Matrix.conjTranspose W * Matrix.conjTranspose (Matrix.conjTranspose W) := by
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
    rw [show Matrix.conjTranspose J * J = 1 by simpa [J] using M.fixedNaimarkEmbedding_isometry]
    rw [show Matrix.conjTranspose W * W = 1 by simpa [W] using M.naimarkEmbedding_isometry]
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := Matrix.conjTranspose J) (B := Matrix.conjTranspose W) hGram (Nat.le_refl _)
  let U : CMatrix M.FixedNaimarkSpace := V.matrix.map star
  have hVco : V.matrix * Matrix.conjTranspose V.matrix = 1 := by
    exact (Matrix.mul_eq_one_comm_of_card_eq M.FixedNaimarkSpace M.FixedNaimarkSpace ℂ rfl).mp
      V.isometry
  have hUiso : Matrix.conjTranspose U * U = 1 := by
    exact starMap_conjTranspose_mul_self V.matrix V.isometry
  have hUco : U * Matrix.conjTranspose U = 1 := by
    exact starMap_mul_conjTranspose_self V.matrix hVco
  have hUJ : U * J = W := by
    have h := congrArg Matrix.conjTranspose hV
    simpa [U, J, W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.transpose_conjTranspose] using h.symm
  exact ⟨U, hUiso, hUco, by simpa [J, W] using hUJ⟩

/-- A unitary carrying the fixed block embedding to the stacked Naimark embedding. -/
def fixedNaimarkUnitary [Inhabited y] (M : POVM y a) : CMatrix M.FixedNaimarkSpace :=
  Classical.choose (fixedNaimarkUnitary_exists M)

theorem fixedNaimarkUnitary_isometry [Inhabited y] (M : POVM y a) :
    Matrix.conjTranspose M.fixedNaimarkUnitary * M.fixedNaimarkUnitary = 1 :=
  (Classical.choose_spec (fixedNaimarkUnitary_exists M)).1

theorem fixedNaimarkUnitary_coisometry [Inhabited y] (M : POVM y a) :
    M.fixedNaimarkUnitary * Matrix.conjTranspose M.fixedNaimarkUnitary = 1 :=
  (Classical.choose_spec (fixedNaimarkUnitary_exists M)).2.1

theorem fixedNaimarkUnitary_mul_embedding [Inhabited y] (M : POVM y a) :
    M.fixedNaimarkUnitary * M.fixedNaimarkEmbedding = M.naimarkEmbedding :=
  (Classical.choose_spec (fixedNaimarkUnitary_exists M)).2.2

/--
The fixed-base Naimark projector obtained by conjugating the stacked block
projector back along the unitary carrying the fixed embedding to the stacked
embedding.
-/
def fixedNaimarkProjector [Inhabited y] (M : POVM y a) (outcome : y) :
    CMatrix M.FixedNaimarkSpace :=
  Matrix.conjTranspose M.fixedNaimarkUnitary * M.naimarkProjector outcome *
    M.fixedNaimarkUnitary

theorem fixedNaimarkProjector_isHermitian [Inhabited y] (M : POVM y a) (outcome : y) :
    (M.fixedNaimarkProjector outcome).IsHermitian := by
  rw [Matrix.IsHermitian]
  unfold fixedNaimarkProjector
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, M.naimarkProjector_isHermitian outcome]
  rw [Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc]

theorem fixedNaimarkProjector_idempotent [Inhabited y] (M : POVM y a) (outcome : y) :
    M.fixedNaimarkProjector outcome * M.fixedNaimarkProjector outcome =
      M.fixedNaimarkProjector outcome := by
  unfold fixedNaimarkProjector
  calc
    (Matrix.conjTranspose M.fixedNaimarkUnitary * M.naimarkProjector outcome *
          M.fixedNaimarkUnitary) *
        (Matrix.conjTranspose M.fixedNaimarkUnitary * M.naimarkProjector outcome *
          M.fixedNaimarkUnitary)
        =
        Matrix.conjTranspose M.fixedNaimarkUnitary * M.naimarkProjector outcome *
          (M.fixedNaimarkUnitary * Matrix.conjTranspose M.fixedNaimarkUnitary) *
          M.naimarkProjector outcome * M.fixedNaimarkUnitary := by
          noncomm_ring
    _ =
        Matrix.conjTranspose M.fixedNaimarkUnitary * M.naimarkProjector outcome *
          1 * M.naimarkProjector outcome * M.fixedNaimarkUnitary := by
          rw [M.fixedNaimarkUnitary_coisometry]
    _ =
        Matrix.conjTranspose M.fixedNaimarkUnitary *
          (M.naimarkProjector outcome * M.naimarkProjector outcome) *
          M.fixedNaimarkUnitary := by
          noncomm_ring
    _ =
        Matrix.conjTranspose M.fixedNaimarkUnitary *
          M.naimarkProjector outcome * M.fixedNaimarkUnitary := by
          rw [M.naimarkProjector_idempotent outcome]

theorem fixedNaimarkProjector_orthogonal [Inhabited y] (M : POVM y a)
    (i j : y) (hij : i ≠ j) :
    M.fixedNaimarkProjector i * M.fixedNaimarkProjector j = 0 := by
  unfold fixedNaimarkProjector
  calc
    (Matrix.conjTranspose M.fixedNaimarkUnitary * M.naimarkProjector i *
          M.fixedNaimarkUnitary) *
        (Matrix.conjTranspose M.fixedNaimarkUnitary * M.naimarkProjector j *
          M.fixedNaimarkUnitary)
        =
        Matrix.conjTranspose M.fixedNaimarkUnitary * M.naimarkProjector i *
          (M.fixedNaimarkUnitary * Matrix.conjTranspose M.fixedNaimarkUnitary) *
          M.naimarkProjector j * M.fixedNaimarkUnitary := by
          noncomm_ring
    _ =
        Matrix.conjTranspose M.fixedNaimarkUnitary * M.naimarkProjector i *
          1 * M.naimarkProjector j * M.fixedNaimarkUnitary := by
          rw [M.fixedNaimarkUnitary_coisometry]
    _ =
        Matrix.conjTranspose M.fixedNaimarkUnitary *
          (M.naimarkProjector i * M.naimarkProjector j) *
          M.fixedNaimarkUnitary := by
          noncomm_ring
    _ = 0 := by
          rw [M.naimarkProjector_orthogonal i j hij]
          simp

theorem fixedNaimarkProjector_sum_eq_one [Inhabited y] (M : POVM y a) :
    ∑ outcome : y, M.fixedNaimarkProjector outcome = 1 := by
  calc
    ∑ outcome : y, M.fixedNaimarkProjector outcome =
        Matrix.conjTranspose M.fixedNaimarkUnitary *
          (∑ outcome : y, M.naimarkProjector outcome) *
            M.fixedNaimarkUnitary := by
          simp [fixedNaimarkProjector, Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
    _ = 1 := by
          rw [M.naimarkProjector_sum_eq_one]
          simp [M.fixedNaimarkUnitary_isometry]

/-- The projective measurement associated to the fixed-base Naimark lift. -/
def fixedNaimarkProjectiveMeasurement [Inhabited y] (M : POVM y a) :
    ProjectiveMeasurement y M.FixedNaimarkSpace where
  effects := M.fixedNaimarkProjector
  isHermitian := M.fixedNaimarkProjector_isHermitian
  idempotent := M.fixedNaimarkProjector_idempotent
  orthogonal := M.fixedNaimarkProjector_orthogonal
  sum_eq_one := M.fixedNaimarkProjector_sum_eq_one

theorem fixedNaimark_compression_projector [Inhabited y] (M : POVM y a) (outcome : y) :
    Matrix.conjTranspose M.fixedNaimarkEmbedding *
        M.fixedNaimarkProjector outcome *
        M.fixedNaimarkEmbedding = M.effects outcome := by
  calc
    Matrix.conjTranspose M.fixedNaimarkEmbedding *
        M.fixedNaimarkProjector outcome *
        M.fixedNaimarkEmbedding =
        Matrix.conjTranspose (M.fixedNaimarkUnitary * M.fixedNaimarkEmbedding) *
          M.naimarkProjector outcome *
          (M.fixedNaimarkUnitary * M.fixedNaimarkEmbedding) := by
          simp [fixedNaimarkProjector, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.conjTranspose M.naimarkEmbedding * M.naimarkProjector outcome *
        M.naimarkEmbedding := by
          rw [M.fixedNaimarkUnitary_mul_embedding]
    _ = M.effects outcome := M.naimark_compression_projector outcome

/-- The lifted state for the fixed-base Naimark dilation. -/
def fixedNaimarkLiftState [Inhabited y] (M : POVM y a) (rho : State a) :
    State M.FixedNaimarkSpace where
  matrix := M.fixedNaimarkEmbedding * rho.matrix * Matrix.conjTranspose M.fixedNaimarkEmbedding
  pos := rho.pos.mul_mul_conjTranspose_same M.fixedNaimarkEmbedding
  trace_eq_one := by
    rw [Matrix.trace_mul_cycle, M.fixedNaimarkEmbedding_isometry, Matrix.one_mul, rho.trace_eq_one]

@[simp]
theorem fixedNaimarkLiftState_matrix [Inhabited y] (M : POVM y a) (rho : State a) :
    (M.fixedNaimarkLiftState rho).matrix =
      M.fixedNaimarkEmbedding * rho.matrix * Matrix.conjTranspose M.fixedNaimarkEmbedding :=
  rfl

theorem fixedNaimark_trace_projector_eq [Inhabited y]
    (M : POVM y a) (rho : State a) (outcome : y) :
    ((M.fixedNaimarkLiftState rho).matrix * M.fixedNaimarkProjector outcome).trace =
      (rho.matrix * M.effects outcome).trace := by
  calc
    ((M.fixedNaimarkLiftState rho).matrix * M.fixedNaimarkProjector outcome).trace
        =
          (rho.matrix *
            (Matrix.conjTranspose M.fixedNaimarkEmbedding *
              M.fixedNaimarkProjector outcome *
              M.fixedNaimarkEmbedding)).trace := by
            rw [fixedNaimarkLiftState_matrix]
            calc
              ((M.fixedNaimarkEmbedding * rho.matrix *
                      Matrix.conjTranspose M.fixedNaimarkEmbedding) *
                    M.fixedNaimarkProjector outcome).trace
                  =
                    (M.fixedNaimarkEmbedding * rho.matrix *
                      (Matrix.conjTranspose M.fixedNaimarkEmbedding *
                        M.fixedNaimarkProjector outcome)).trace := by
                    rw [Matrix.mul_assoc, Matrix.mul_assoc]
              _ =
                    (rho.matrix *
                      ((Matrix.conjTranspose M.fixedNaimarkEmbedding *
                          M.fixedNaimarkProjector outcome) *
                        M.fixedNaimarkEmbedding)).trace := by
                    rw [Matrix.trace_mul_cycle]
                    rw [Matrix.trace_mul_comm]
              _ =
                    (rho.matrix *
                      (Matrix.conjTranspose M.fixedNaimarkEmbedding *
                        M.fixedNaimarkProjector outcome *
                        M.fixedNaimarkEmbedding)).trace := by
                    rw [Matrix.mul_assoc]
    _ = (rho.matrix * M.effects outcome).trace := by
          rw [M.fixedNaimark_compression_projector outcome]

/-- The fixed-base Naimark dilation preserves Born-rule outcome probabilities. -/
theorem fixedNaimark_prob_eq [Inhabited y] (M : POVM y a) (rho : State a) (outcome : y) :
    (M.fixedNaimarkProjectiveMeasurement.toPOVM).prob
        (M.fixedNaimarkLiftState rho) outcome =
      M.prob rho outcome := by
  apply NNReal.eq
  rw [POVM.prob_eq_trace_re, POVM.prob_eq_trace_re]
  change Complex.re (((M.fixedNaimarkLiftState rho).matrix *
      M.fixedNaimarkProjector outcome).trace) =
    Complex.re ((rho.matrix * M.effects outcome).trace)
  rw [M.fixedNaimark_trace_projector_eq rho outcome]

variable {settings : Type w}

/--
The shared finite Naimark space for a family of POVMs with the same outcome and
system types.  It is the fixed-base space, independent of the setting.
-/
abbrev FamilyNaimarkSpace (_M : settings → POVM y a) : Type (max u v) :=
  a × y

/-- The shared fixed embedding for a finite family of POVMs. -/
def familyNaimarkEmbedding [Inhabited y] (_M : settings → POVM y a) :
    Matrix (FamilyNaimarkSpace _M) a ℂ :=
  fun idx col => if idx = (col, default) then 1 else 0

@[simp]
theorem familyNaimarkEmbedding_apply [Inhabited y] (M : settings → POVM y a)
    (idx : FamilyNaimarkSpace M) (col : a) :
    familyNaimarkEmbedding M idx col = if idx = (col, default) then 1 else 0 :=
  rfl

/-- The shared family embedding is an isometry. -/
theorem familyNaimarkEmbedding_isometry [Inhabited y] (M : settings → POVM y a) :
    Matrix.conjTranspose (familyNaimarkEmbedding M) * familyNaimarkEmbedding M = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single (i, default)]
    · simp [Matrix.conjTranspose_apply]
    · intro idx _ hidx
      simp [Matrix.conjTranspose_apply, hidx]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro idx _
      by_cases hi : idx = (i, default)
      · subst idx
        simp [Matrix.conjTranspose_apply, hij]
      · simp [Matrix.conjTranspose_apply, hi]

/--
The setting-indexed projective measurements of the shared family dilation.
Each setting reuses the fixed-base single-POVM Naimark measurement on
the same definitional space `a × y`.
-/
def familyNaimarkProjectiveMeasurement [Inhabited y]
    (M : settings → POVM y a) (setting : settings) :
    ProjectiveMeasurement y (FamilyNaimarkSpace M) :=
  (M setting).fixedNaimarkProjectiveMeasurement

/-- Compressing a shared-family Naimark projector recovers the selected POVM
effect. -/
theorem familyNaimark_compression_projector_eq [Inhabited y]
    (M : settings → POVM y a) (setting : settings) (outcome : y) :
    Matrix.conjTranspose (familyNaimarkEmbedding M) *
        (familyNaimarkProjectiveMeasurement M setting).effects outcome *
        familyNaimarkEmbedding M =
      (M setting).effects outcome := by
  simpa [familyNaimarkEmbedding, familyNaimarkProjectiveMeasurement, fixedNaimarkEmbedding]
    using (M setting).fixedNaimark_compression_projector outcome

/-- The shared lifted state for a family Naimark dilation. -/
def familyNaimarkLiftState [Inhabited y]
    (M : settings → POVM y a) (rho : State a) :
    State (FamilyNaimarkSpace M) where
  matrix := familyNaimarkEmbedding M * rho.matrix * Matrix.conjTranspose (familyNaimarkEmbedding M)
  pos := rho.pos.mul_mul_conjTranspose_same (familyNaimarkEmbedding M)
  trace_eq_one := by
    rw [Matrix.trace_mul_cycle, familyNaimarkEmbedding_isometry M, Matrix.one_mul,
      rho.trace_eq_one]

@[simp]
theorem familyNaimarkLiftState_matrix [Inhabited y]
    (M : settings → POVM y a) (rho : State a) :
    (familyNaimarkLiftState M rho).matrix =
      familyNaimarkEmbedding M * rho.matrix * Matrix.conjTranspose (familyNaimarkEmbedding M) :=
  rfl

/--
The shared family dilation preserves Born-rule probabilities for every setting
and outcome.
-/
theorem familyNaimark_prob_eq [Inhabited y]
    (M : settings → POVM y a) (rho : State a) (setting : settings) (outcome : y) :
    (familyNaimarkProjectiveMeasurement M setting).toPOVM.prob
        (familyNaimarkLiftState M rho) outcome =
      (M setting).prob rho outcome := by
  simpa [familyNaimarkProjectiveMeasurement, familyNaimarkLiftState, familyNaimarkEmbedding,
    fixedNaimarkLiftState, fixedNaimarkEmbedding] using
      (M setting).fixedNaimark_prob_eq rho outcome

end POVM

end

end QIT
