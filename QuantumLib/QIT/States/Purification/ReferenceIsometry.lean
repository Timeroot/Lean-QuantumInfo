/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.Purification.Predicate

/-!
# Reference-system isometries

This module fixes the matrix convention for an isometry acting only on a
purifying reference register. The source-system convention follows the
purification equivalence route registered from [Wilde2011Qst,
qit-notes.tex:10320-10338] and [Gour2024Resources, BookQRT.tex:2051-2069]:
two purifications of the same target state are compared by an isometry on the
reference system.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

/-- A matrix isometry from reference system `r₁` into reference system `r₂`.

The matrix has rows indexed by the output reference and columns indexed by the
input reference; the convention is `Vᴴ * V = 1`. -/
structure ReferenceIsometry (r₁ : Type u) (r₂ : Type v)
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂] where
  /-- The underlying matrix, with rows indexed by `r₂` and columns by `r₁`. -/
  matrix : Matrix r₂ r₁ ℂ
  /-- The matrix is an isometry. -/
  isometry : Matrix.conjTranspose matrix * matrix = 1

namespace ReferenceIsometry

variable {r₁ : Type u} {r₂ : Type v} {a : Type w}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

variable (V : ReferenceIsometry r₁ r₂)

/-- The transpose of a square reference isometry is unitary. -/
theorem transpose_matrix_mem_unitary (W : ReferenceIsometry r₁ r₁) :
    Matrix.transpose W.matrix ∈ Matrix.unitaryGroup r₁ ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have h := congrFun (congrFun W.isometry j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose, Matrix.one_apply,
    Finset.mul_sum, mul_comm, eq_comm] using h

/-- Entrywise orthonormal-column form of `Vᴴ * V = 1`. -/
theorem sum_mul_star (i j : r₁) :
    (Finset.univ.sum fun k : r₂ => V.matrix k i * star (V.matrix k j)) =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun V.isometry j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.one_apply, eq_comm, mul_comm] using h

/-- An isometry acts injectively on vectors, since `Vᴴ` undoes it. -/
theorem matrix_mulVec_injective : Function.Injective V.matrix.mulVec := by
  intro x y hxy
  have h := congrArg (Matrix.mulVec (Matrix.conjTranspose V.matrix)) hxy
  simpa [Matrix.mulVec_mulVec, V.isometry] using h

/-- The basis embedding isometry induced by an injective finite map. -/
def ofInjective
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) (hf : Function.Injective f) :
    ReferenceIsometry α β where
  matrix := Matrix.of fun y x => if y = f x then 1 else 0
  isometry := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single (f i)]
      · simp [Matrix.conjTranspose]
      · intro y _ hy
        simp [Matrix.conjTranspose, hy]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ (f i)))
    · rw [Matrix.mul_apply]
      rw [Finset.sum_eq_zero]
      · simp [hij]
      · intro y _
        by_cases hyi : y = f i
        · have hfi_ne_fj : f i ≠ f j := by
            intro h
            exact hij (hf h)
          have hyj : y ≠ f j := by
            intro hyj
            exact hfi_ne_fj (hyi.symm.trans hyj)
          simp [Matrix.conjTranspose, hyi, hfi_ne_fj]
        · simp [Matrix.conjTranspose, hyi]

variable {r₃ : Type w} [Fintype r₃] [DecidableEq r₃]

/-- Compose two reference isometries. -/
def comp (W : ReferenceIsometry r₂ r₃) (V : ReferenceIsometry r₁ r₂) :
    ReferenceIsometry r₁ r₃ where
  matrix := W.matrix * V.matrix
  isometry := by
    calc
      Matrix.conjTranspose (W.matrix * V.matrix) * (W.matrix * V.matrix) =
          Matrix.conjTranspose V.matrix *
            (Matrix.conjTranspose W.matrix * W.matrix) * V.matrix := by
            rw [Matrix.conjTranspose_mul]
            rw [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (Matrix.conjTranspose W.matrix) W.matrix V.matrix]
            rw [← Matrix.mul_assoc (Matrix.conjTranspose V.matrix)
              (Matrix.conjTranspose W.matrix * W.matrix) V.matrix]
      _ = Matrix.conjTranspose V.matrix * V.matrix := by
            rw [W.isometry, Matrix.mul_one]
      _ = 1 := V.isometry

/-- The reference-indexed block of a bipartite matrix at fixed target entries. -/
def targetBlock (X : CMatrix (r₁ × a)) (x y : a) : CMatrix r₁ :=
  fun i j => X (i, x) (j, y)

/-- Apply a reference isometry to the reference side of a bipartite matrix. -/
def applyMatrix (X : CMatrix (r₁ × a)) : CMatrix (r₂ × a) :=
  fun x y => (V.matrix * targetBlock X x.2 y.2 * Matrix.conjTranspose V.matrix) x.1 y.1

/-- The reference-indexed block of a bipartite matrix when the reference
register is the right product factor. -/
def rightBlock (X : CMatrix (a × r₁)) (x y : a) : CMatrix r₁ :=
  fun i j => X (x, i) (y, j)

/-- Apply a reference isometry to the right factor of a bipartite matrix.  This
is the input-first counterpart to `applyMatrix`, useful when a channel acts on
the left/input factor and the purifying reference is on the right. -/
def applyMatrixRight (X : CMatrix (a × r₁)) : CMatrix (a × r₂) :=
  fun x y => (V.matrix * rightBlock X x.1 y.1 * Matrix.conjTranspose V.matrix) x.2 y.2

/-- Apply a reference isometry to the reference side of a bipartite amplitude. -/
def applyAmp (ψ : r₁ × a → ℂ) : r₂ × a → ℂ :=
  fun x => V.matrix.mulVec (fun i : r₁ => ψ (i, x.2)) x.1

/-- Apply a reference isometry to the right factor of a bipartite amplitude. -/
def applyAmpRight (ψ : a × r₁ → ℂ) : a × r₂ → ℂ :=
  fun x => V.matrix.mulVec (fun i : r₁ => ψ (x.1, i)) x.2

/-- Applying a reference isometry to amplitudes matches conjugating the rank-one matrix. -/
theorem rankOne_applyAmp (ψ : r₁ × a → ℂ) :
    rankOneMatrix (V.applyAmp ψ) = V.applyMatrix (rankOneMatrix ψ) := by
  ext x y
  simp [rankOneMatrix, applyAmp, applyMatrix, targetBlock, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Applying a right-reference isometry to amplitudes matches conjugating the
right reference blocks of the rank-one matrix. -/
theorem rankOne_applyAmpRight (ψ : a × r₁ → ℂ) :
    rankOneMatrix (V.applyAmpRight ψ) = V.applyMatrixRight (rankOneMatrix ψ) := by
  ext x y
  simp [rankOneMatrix, applyAmpRight, applyMatrixRight, rightBlock, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Conjugating a reference block by an isometry preserves its trace. -/
theorem trace_apply_block (B : CMatrix r₁) :
    (V.matrix * B * Matrix.conjTranspose V.matrix).trace = B.trace := by
  rw [Matrix.trace_mul_cycle, V.isometry, Matrix.one_mul]

/-- Applying a reference isometry is conjugation by `V ⊗ 1`. -/
theorem applyMatrix_eq_kron_conj [Fintype a] [DecidableEq a] (X : CMatrix (r₁ × a)) :
    V.applyMatrix X =
      Matrix.kronecker V.matrix (1 : CMatrix a) * X *
        Matrix.conjTranspose (Matrix.kronecker V.matrix (1 : CMatrix a)) := by
  ext i j
  simp [applyMatrix, targetBlock,
    Matrix.kronecker, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type,
    mul_assoc, mul_comm]

/-- Applying a reference isometry preserves positive semidefiniteness. -/
theorem applyMatrix_posSemidef [Fintype a] [DecidableEq a] {X : CMatrix (r₁ × a)}
    (hX : X.PosSemidef) :
    (V.applyMatrix X).PosSemidef := by
  have h := hX.conjTranspose_mul_mul_same
    (Matrix.conjTranspose (Matrix.kronecker V.matrix (1 : CMatrix a)))
  rw [V.applyMatrix_eq_kron_conj X]
  simpa [Matrix.conjTranspose_conjTranspose] using h

/-- Applying a reference isometry does not change the target marginal. -/
theorem traceLeft_applyMatrix (X : CMatrix (r₁ × a)) :
    Matrix.traceLeft (V.applyMatrix X) =
      Matrix.traceLeft X := by
  ext x y
  exact V.trace_apply_block (targetBlock X x y)

/-- Applying a reference isometry to the left/reference side conjugates the
left marginal by that isometry. -/
theorem traceRight_applyMatrix [Fintype a]
    (X : CMatrix (r₁ × a)) :
    Matrix.traceRight (V.applyMatrix X) =
      V.matrix * Matrix.traceRight X *
        Matrix.conjTranspose V.matrix := by
  ext i j
  simp [Matrix.traceRight, applyMatrix, targetBlock, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- Applying a right-reference isometry does not change the left/input marginal. -/
theorem traceRight_applyMatrixRight [Fintype a] (X : CMatrix (a × r₁)) :
    Matrix.traceRight (V.applyMatrixRight X) =
      Matrix.traceRight X := by
  ext x y
  exact V.trace_apply_block (rightBlock X x y)

/-- Tracing out the left factor after a right-reference isometry conjugates the
right marginal by the isometry. -/
theorem traceLeft_applyMatrixRight [Fintype a] (X : CMatrix (a × r₁)) :
    Matrix.traceLeft (V.applyMatrixRight X) =
      V.matrix * Matrix.traceLeft X * Matrix.conjTranspose V.matrix := by
  ext x y
  simp [Matrix.traceLeft, applyMatrixRight, rightBlock, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- Conjugation by the reference isometry respects matrix multiplication on the
reference block: `(V M V†)(V N V†) = V (M N) V†`. -/
theorem matrix_mul_conjTranspose_mul_matrix (B C : CMatrix r₁) :
    (V.matrix * B * Matrix.conjTranspose V.matrix) *
        (V.matrix * C * Matrix.conjTranspose V.matrix) =
      V.matrix * (B * C) * Matrix.conjTranspose V.matrix := by
  calc
    (V.matrix * B * Matrix.conjTranspose V.matrix) *
        (V.matrix * C * Matrix.conjTranspose V.matrix) =
      V.matrix * B * (Matrix.conjTranspose V.matrix * V.matrix) *
        C * Matrix.conjTranspose V.matrix := by
          simp only [Matrix.mul_assoc]
    _ = V.matrix * B * (1 : CMatrix r₁) * C * Matrix.conjTranspose V.matrix := by
          rw [V.isometry]
    _ = V.matrix * (B * C) * Matrix.conjTranspose V.matrix := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- Applying a reference isometry preserves the trace of a bipartite matrix. -/
theorem trace_applyMatrix [Fintype a] (X : CMatrix (r₁ × a)) :
    (V.applyMatrix X).trace = X.trace := by
  have h := congrArg Matrix.trace (V.traceLeft_applyMatrix X)
  simpa [Matrix.traceLeft_trace] using h

/-- Apply a reference isometry to a bipartite ket. -/
def applyKet [Fintype a] [DecidableEq a] (Ψ : Ket (r₁ × a)) :
    Ket (r₂ × a) :=
  Ket.ofRankOne (V.applyAmp Ψ.vec) <| by
    have h := congrArg Matrix.trace (V.traceLeft_applyMatrix (rankOneMatrix Ψ.vec))
    rw [Matrix.traceLeft_trace, Matrix.traceLeft_trace] at h
    rw [V.rankOne_applyAmp Ψ.vec, h, Ψ.trace_rankOne_eq_one]

/-- The amplitude of `applyKet` unfolds to `applyAmp`. -/
theorem applyKet_vec [Fintype a] [DecidableEq a] (Ψ : Ket (r₁ × a)) :
    (V.applyKet Ψ).vec = V.applyAmp Ψ.vec :=
  rfl

/-- Applying a reference isometry to the left/reference side conjugates the
left marginal of a pure state by that isometry. -/
theorem traceRight_applyKet [Fintype a] [DecidableEq a]
    (Ψ : Ket (r₁ × a)) :
    (V.applyKet Ψ).state.traceRight.m =
      V.matrix * Ψ.state.traceRight.m * Matrix.conjTranspose V.matrix := by
  rw [MState.traceRight_m]
  rw [Ket.state_matrix]
  rw [applyKet_vec]
  rw [V.rankOne_applyAmp]
  rw [V.traceRight_applyMatrix, MState.traceRight_m,
    Ket.state_matrix]

/-- Apply a reference isometry to the right factor of a bipartite ket. -/
def applyKetRight [Fintype a] [DecidableEq a] (Ψ : Ket (a × r₁)) :
    Ket (a × r₂) :=
  (V.applyKet (Ψ.reindex (Equiv.prodComm a r₁))).reindex (Equiv.prodComm r₂ a)

/-- The amplitude of `applyKetRight` unfolds to `applyAmpRight`. -/
theorem applyKetRight_vec [Fintype a] [DecidableEq a] (Ψ : Ket (a × r₁)) :
    (V.applyKetRight Ψ).vec = V.applyAmpRight Ψ.vec :=
  rfl

/-- Right-reference ket action matches `applyMatrixRight` on states. -/
theorem rankOne_applyKetRight [Fintype a] [DecidableEq a]
    (Ψ : Ket (a × r₁)) :
    (V.applyKetRight Ψ).state.m = V.applyMatrixRight Ψ.state.m := by
  rw [Ket.state_matrix, Ket.state_matrix]
  exact V.rankOne_applyAmpRight Ψ.vec

/-- A right-reference isometry preserves the input marginal of a pure state. -/
theorem traceRight_applyKetRight [Fintype a] [DecidableEq a]
    (Ψ : Ket (a × r₁)) :
    (V.applyKetRight Ψ).state.traceRight = Ψ.state.traceRight := by
  apply MState.ext
  rw [MState.traceRight_m, MState.traceRight_m]
  rw [V.rankOne_applyKetRight]
  exact V.traceRight_applyMatrixRight Ψ.state.m

/-- A reference isometry preserves the target state purified by a ket. -/
theorem applyKet_purifies [Fintype a] [DecidableEq a]
    {Ψ : Ket (r₁ × a)} {ρ : MState a} (hΨ : Ψ.Purifies ρ) :
    (V.applyKet Ψ).Purifies ρ := by
  rw [Ket.purifies_iff]
  rw [Ket.state_matrix]
  change Matrix.traceLeft (rankOneMatrix (V.applyAmp Ψ.vec)) = ρ.m
  rw [V.rankOne_applyAmp]
  rw [V.traceLeft_applyMatrix]
  rw [Ket.purifies_iff, Ket.state_matrix] at hΨ
  exact hΨ

variable {r₃ : Type*} {r₄ : Type*}
variable [Fintype r₃] [DecidableEq r₃] [Fintype r₄] [DecidableEq r₄]

/-- Product of two reference isometries, with matrix convention matching the
recursive `TensorPower` convention. -/
def prod (V : ReferenceIsometry r₁ r₂) (W : ReferenceIsometry r₃ r₄) :
    ReferenceIsometry (r₁ × r₃) (r₂ × r₄) where
  matrix := Matrix.kronecker V.matrix W.matrix
  isometry := by
    change (V.matrix.kronecker W.matrix).conjTranspose *
        V.matrix.kronecker W.matrix = 1
    rw [show (V.matrix.kronecker W.matrix).conjTranspose =
        Matrix.kronecker V.matrix.conjTranspose W.matrix.conjTranspose from
      Matrix.conjTranspose_kronecker V.matrix W.matrix]
    rw [show Matrix.kronecker V.matrix.conjTranspose W.matrix.conjTranspose *
          Matrix.kronecker V.matrix W.matrix =
        Matrix.kronecker (V.matrix.conjTranspose * V.matrix)
          (W.matrix.conjTranspose * W.matrix) from by
      exact (Matrix.mul_kronecker_mul V.matrix.conjTranspose V.matrix
        W.matrix.conjTranspose W.matrix).symm]
    rw [V.isometry, W.isometry]
    exact Matrix.one_kronecker_one

/-- Tensor power of a reference isometry on recursive tensor-power labels. -/
def tensorPower (V : ReferenceIsometry r₁ r₂) :
    (n : ℕ) → ReferenceIsometry (TensorPower r₁ n) (TensorPower r₂ n)
  | 0 =>
      { matrix := Matrix.of fun _ _ => 1
        isometry := by
          ext x y
          have hxy : x = y := by
            cases x
            cases y
            rfl
          rw [Matrix.mul_apply]
          simp only [Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
            Matrix.one_apply, if_pos hxy]
          rw [show Fintype.card (TensorPower r₂ 0) = 1 from
            Fintype.card_eq_one_iff.mpr ⟨PUnit.unit, fun _ => rfl⟩]
          norm_num }
  | n + 1 => V.prod (tensorPower V n)

@[simp]
theorem tensorPower_succ (V : ReferenceIsometry r₁ r₂) (n : ℕ) :
    V.tensorPower (n + 1) = V.prod (V.tensorPower n) :=
  rfl

/-- Embed a reference register as the right summand of an enlarged reference
register. This is the finite-dimensional padding used when Uhlmann's theorem
needs a sufficiently large reference space. -/
def sumInr (extra : Type*) [Fintype extra] [DecidableEq extra]
    (r : Type*) [Fintype r] [DecidableEq r] :
    ReferenceIsometry r (extra ⊕ r) where
  matrix := Matrix.of fun x i =>
    match x with
    | Sum.inl _ => 0
    | Sum.inr j => if j = i then 1 else 0
  isometry := by
    classical
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose, Matrix.one_apply, eq_comm]

end ReferenceIsometry

end

end QIT
