/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.Predicate

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
  matrix : Matrix r₂ r₁ Complex
  isometry : Matrix.conjTranspose matrix * matrix = 1

namespace ReferenceIsometry

variable {r₁ : Type u} {r₂ : Type v} {a : Type w}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

variable (V : ReferenceIsometry r₁ r₂)

/-- Entrywise orthonormal-column form of `Vᴴ * V = 1`. -/
theorem sum_mul_star (i j : r₁) :
    (Finset.univ.sum fun k : r₂ => V.matrix k i * star (V.matrix k j)) =
      if i = j then 1 else 0 := by
  have h := congrFun (congrFun V.isometry j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.one_apply, eq_comm, mul_comm] using h

/-- The basis embedding isometry induced by an injective finite map. -/
def ofInjective
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) (hf : Function.Injective f) :
    ReferenceIsometry α β where
  matrix := fun y x => if y = f x then 1 else 0
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
def targetBlock (X : CMatrix (Prod r₁ a)) (x y : a) : CMatrix r₁ :=
  fun i j => X (i, x) (j, y)

/-- Apply a reference isometry to the reference side of a bipartite matrix. -/
def applyMatrix (X : CMatrix (Prod r₁ a)) : CMatrix (Prod r₂ a) :=
  fun x y => (V.matrix * targetBlock X x.2 y.2 * Matrix.conjTranspose V.matrix) x.1 y.1

/-- The reference-indexed block of a bipartite matrix when the reference
register is the right product factor. -/
def rightBlock (X : CMatrix (Prod a r₁)) (x y : a) : CMatrix r₁ :=
  fun i j => X (x, i) (y, j)

/-- Apply a reference isometry to the right factor of a bipartite matrix.  This
is the input-first counterpart to `applyMatrix`, useful when a channel acts on
the left/input factor and the purifying reference is on the right. -/
def applyMatrixRight (X : CMatrix (Prod a r₁)) : CMatrix (Prod a r₂) :=
  fun x y => (V.matrix * rightBlock X x.1 y.1 * Matrix.conjTranspose V.matrix) x.2 y.2

/-- Apply a reference isometry to the reference side of a bipartite amplitude. -/
def applyAmp (ψ : Prod r₁ a -> Complex) : Prod r₂ a -> Complex :=
  fun x => V.matrix.mulVec (fun i : r₁ => ψ (i, x.2)) x.1

/-- Apply a reference isometry to the right factor of a bipartite amplitude. -/
def applyAmpRight (ψ : Prod a r₁ -> Complex) : Prod a r₂ -> Complex :=
  fun x => V.matrix.mulVec (fun i : r₁ => ψ (x.1, i)) x.2

/-- Applying a reference isometry to amplitudes matches conjugating the rank-one matrix. -/
theorem rankOne_applyAmp (ψ : Prod r₁ a -> Complex) :
    rankOneMatrix (V.applyAmp ψ) = V.applyMatrix (rankOneMatrix ψ) := by
  ext x y
  simp [rankOneMatrix, applyAmp, applyMatrix, targetBlock, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Applying a right-reference isometry to amplitudes matches conjugating the
right reference blocks of the rank-one matrix. -/
theorem rankOne_applyAmpRight (ψ : Prod a r₁ -> Complex) :
    rankOneMatrix (V.applyAmpRight ψ) = V.applyMatrixRight (rankOneMatrix ψ) := by
  ext x y
  simp [rankOneMatrix, applyAmpRight, applyMatrixRight, rightBlock, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Conjugating a reference block by an isometry preserves its trace. -/
theorem trace_apply_block (B : CMatrix r₁) :
    (V.matrix * B * Matrix.conjTranspose V.matrix).trace = B.trace := by
  rw [Matrix.trace_mul_cycle, V.isometry, Matrix.one_mul]

/-- Applying a reference isometry does not change the target marginal. -/
theorem partialTraceA_applyMatrix (X : CMatrix (Prod r₁ a)) :
    partialTraceA (a := r₂) (b := a) (V.applyMatrix X) =
      partialTraceA (a := r₁) (b := a) X := by
  ext x y
  exact V.trace_apply_block (targetBlock X x y)

/-- Applying a reference isometry to the left/reference side conjugates the
left marginal by that isometry. -/
theorem partialTraceB_applyMatrix_of_referenceIsometry [Fintype a]
    (X : CMatrix (Prod r₁ a)) :
    partialTraceB (a := r₂) (b := a) (V.applyMatrix X) =
      V.matrix * partialTraceB (a := r₁) (b := a) X *
        Matrix.conjTranspose V.matrix := by
  ext i j
  simp [partialTraceB, applyMatrix, targetBlock, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- Applying a right-reference isometry does not change the left/input marginal. -/
theorem partialTraceB_applyMatrixRight [Fintype a] (X : CMatrix (Prod a r₁)) :
    partialTraceB (a := a) (b := r₂) (V.applyMatrixRight X) =
      partialTraceB (a := a) (b := r₁) X := by
  ext x y
  exact V.trace_apply_block (rightBlock X x y)

/-- Tracing out the left factor after a right-reference isometry conjugates the
right marginal by the isometry. -/
theorem partialTraceA_applyMatrixRight [Fintype a] (X : CMatrix (Prod a r₁)) :
    partialTraceA (a := a) (b := r₂) (V.applyMatrixRight X) =
      V.matrix * partialTraceA (a := a) (b := r₁) X * Matrix.conjTranspose V.matrix := by
  ext x y
  simp [partialTraceA, applyMatrixRight, rightBlock, Matrix.mul_apply,
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
theorem trace_applyMatrix [Fintype a] (X : CMatrix (Prod r₁ a)) :
    (V.applyMatrix X).trace = X.trace := by
  have h := congrArg Matrix.trace (V.partialTraceA_applyMatrix X)
  simpa [partialTraceA_trace] using h

/-- Apply a reference isometry to a bipartite pure vector. -/
def applyPureVector [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod r₁ a)) :
    PureVector (Prod r₂ a) where
  amp := V.applyAmp Ψ.amp
  trace_rankOne_eq_one := by
    have h := congrArg Matrix.trace (V.partialTraceA_applyMatrix (rankOneMatrix Ψ.amp))
    rw [partialTraceA_trace, partialTraceA_trace] at h
    rw [V.rankOne_applyAmp Ψ.amp, h, Ψ.trace_rankOne_eq_one]

/-- The amplitude of `applyPureVector` unfolds to `applyAmp`. -/
theorem applyPureVector_amp [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod r₁ a)) :
    (V.applyPureVector Ψ).amp = V.applyAmp Ψ.amp :=
  rfl

/-- Applying a reference isometry to the left/reference side conjugates the
left marginal of a pure state by that isometry. -/
theorem marginalA_applyPureVector [Fintype a] [DecidableEq a]
    (Ψ : PureVector (Prod r₁ a)) :
    (V.applyPureVector Ψ).state.marginalA.matrix =
      V.matrix * Ψ.state.marginalA.matrix * Matrix.conjTranspose V.matrix := by
  rw [State.marginalA_matrix]
  rw [PureVector.state_matrix]
  rw [applyPureVector_amp]
  rw [V.rankOne_applyAmp]
  rw [V.partialTraceB_applyMatrix_of_referenceIsometry]
  rfl

/-- Apply a reference isometry to the right factor of a bipartite pure vector. -/
def applyPureVectorRight [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod a r₁)) :
    PureVector (Prod a r₂) :=
  (V.applyPureVector (Ψ.reindex (Equiv.prodComm a r₁))).reindex (Equiv.prodComm r₂ a)

/-- The amplitude of `applyPureVectorRight` unfolds to `applyAmpRight`. -/
theorem applyPureVectorRight_amp [Fintype a] [DecidableEq a] (Ψ : PureVector (Prod a r₁)) :
    (V.applyPureVectorRight Ψ).amp = V.applyAmpRight Ψ.amp :=
  rfl

/-- Right-reference pure-vector action matches `applyMatrixRight` on states. -/
theorem rankOne_applyPureVectorRight [Fintype a] [DecidableEq a]
    (Ψ : PureVector (Prod a r₁)) :
    (V.applyPureVectorRight Ψ).state.matrix = V.applyMatrixRight Ψ.state.matrix := by
  rw [PureVector.state_matrix, PureVector.state_matrix]
  exact V.rankOne_applyAmpRight Ψ.amp

/-- A right-reference isometry preserves the input marginal of a pure state. -/
theorem marginalA_applyPureVectorRight [Fintype a] [DecidableEq a]
    (Ψ : PureVector (Prod a r₁)) :
    (V.applyPureVectorRight Ψ).state.marginalA = Ψ.state.marginalA := by
  apply State.ext
  rw [State.marginalA_matrix, State.marginalA_matrix]
  rw [V.rankOne_applyPureVectorRight]
  exact V.partialTraceB_applyMatrixRight Ψ.state.matrix

/-- A reference isometry preserves the target state purified by a pure vector. -/
theorem applyPureVector_purifies [Fintype a] [DecidableEq a]
    {Ψ : PureVector (Prod r₁ a)} {ρ : State a} (hΨ : Ψ.Purifies ρ) :
    (V.applyPureVector Ψ).Purifies ρ := by
  rw [PureVector.purifies_iff]
  rw [PureVector.state_matrix]
  change partialTraceA (a := r₂) (b := a) (rankOneMatrix (V.applyAmp Ψ.amp)) = ρ.matrix
  rw [V.rankOne_applyAmp]
  rw [V.partialTraceA_applyMatrix]
  exact hΨ

variable {r₃ : Type*} {r₄ : Type*}
variable [Fintype r₃] [DecidableEq r₃] [Fintype r₄] [DecidableEq r₄]

/-- Product of two reference isometries, with matrix convention matching the
recursive `TensorPower` convention. -/
def prod (V : ReferenceIsometry r₁ r₂) (W : ReferenceIsometry r₃ r₄) :
    ReferenceIsometry (Prod r₁ r₃) (Prod r₂ r₄) where
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
      { matrix := fun _ _ => 1
        isometry := by
          ext x y
          cases x
          cases y
          rw [Matrix.mul_apply]
          simp [TensorPower, Matrix.conjTranspose]
          change (1 : ℂ) = (1 : ℂ)
          rfl }
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
    ReferenceIsometry r (Sum extra r) where
  matrix := fun x i =>
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
