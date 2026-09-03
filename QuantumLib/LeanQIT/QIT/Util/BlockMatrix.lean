/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Two-by-two block matrix helpers

Small wrappers for the `Sum`-indexed `2 × 2` block decomposition used by the
positive/negative spectral split. Trace-norm and matrix-square-root
specializations live in `QIT.States.TraceNorm.BlockMatrix`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

universe u v

noncomputable section

variable {α : Type u} {β : Type v}

/-- The upper-left block of a matrix indexed by `α ⊕ β`. -/
def sumBlock11 (M : Matrix (Sum α β) (Sum α β) ℂ) : Matrix α α ℂ :=
  M.submatrix Sum.inl Sum.inl

/-- The upper-right block of a matrix indexed by `α ⊕ β`. -/
def sumBlock12 (M : Matrix (Sum α β) (Sum α β) ℂ) : Matrix α β ℂ :=
  M.submatrix Sum.inl Sum.inr

/-- The lower-left block of a matrix indexed by `α ⊕ β`. -/
def sumBlock21 (M : Matrix (Sum α β) (Sum α β) ℂ) : Matrix β α ℂ :=
  M.submatrix Sum.inr Sum.inl

/-- The lower-right block of a matrix indexed by `α ⊕ β`. -/
def sumBlock22 (M : Matrix (Sum α β) (Sum α β) ℂ) : Matrix β β ℂ :=
  M.submatrix Sum.inr Sum.inr

/-- Embed a matrix as the upper-left block of a `Sum`-indexed block matrix. -/
def sumBlockEmbed11 (A : Matrix α α ℂ) : Matrix (Sum α β) (Sum α β) ℂ :=
  Matrix.fromBlocks A 0 0 0

@[simp]
theorem sumBlock11_apply (M : Matrix (Sum α β) (Sum α β) ℂ) (i j : α) :
    sumBlock11 M i j = M (Sum.inl i) (Sum.inl j) :=
  rfl

@[simp]
theorem sumBlock12_apply (M : Matrix (Sum α β) (Sum α β) ℂ) (i : α) (j : β) :
    sumBlock12 M i j = M (Sum.inl i) (Sum.inr j) :=
  rfl

@[simp]
theorem sumBlock21_apply (M : Matrix (Sum α β) (Sum α β) ℂ) (i : β) (j : α) :
    sumBlock21 M i j = M (Sum.inr i) (Sum.inl j) :=
  rfl

@[simp]
theorem sumBlock22_apply (M : Matrix (Sum α β) (Sum α β) ℂ) (i j : β) :
    sumBlock22 M i j = M (Sum.inr i) (Sum.inr j) :=
  rfl

@[simp]
theorem sumBlock11_fromBlocks (A : Matrix α α ℂ) (B : Matrix α β ℂ)
    (C : Matrix β α ℂ) (D : Matrix β β ℂ) :
    sumBlock11 (Matrix.fromBlocks A B C D) = A := by
  ext i j
  rfl

@[simp]
theorem sumBlock22_fromBlocks (A : Matrix α α ℂ) (B : Matrix α β ℂ)
    (C : Matrix β α ℂ) (D : Matrix β β ℂ) :
    sumBlock22 (Matrix.fromBlocks A B C D) = D := by
  ext i j
  rfl

@[simp]
theorem sumBlockEmbed11_apply_inl_inl (A : Matrix α α ℂ) (i j : α) :
    sumBlockEmbed11 (β := β) A (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp]
theorem sumBlockEmbed11_apply_inl_inr (A : Matrix α α ℂ) (i : α) (j : β) :
    sumBlockEmbed11 (β := β) A (Sum.inl i) (Sum.inr j) = 0 := by
  simp [sumBlockEmbed11]

@[simp]
theorem sumBlockEmbed11_apply_inr_inl (A : Matrix α α ℂ) (i : β) (j : α) :
    sumBlockEmbed11 (β := β) A (Sum.inr i) (Sum.inl j) = 0 := by
  simp [sumBlockEmbed11]

@[simp]
theorem sumBlockEmbed11_apply_inr_inr (A : Matrix α α ℂ) (i j : β) :
    sumBlockEmbed11 (β := β) A (Sum.inr i) (Sum.inr j) = 0 := by
  simp [sumBlockEmbed11]

/-- Embedding in the upper-left block preserves trace. -/
theorem trace_sumBlockEmbed11 [Fintype α] [Fintype β] (A : Matrix α α ℂ) :
    (sumBlockEmbed11 (β := β) A).trace = A.trace := by
  simp [sumBlockEmbed11, Matrix.trace]

/-- The trace of a block-diagonal `Sum` matrix is the sum of the diagonal-block
traces. -/
theorem trace_fromBlocks_diagonal [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (D : Matrix β β ℂ) :
    (Matrix.fromBlocks A 0 0 D).trace = A.trace + D.trace := by
  classical
  simp [Matrix.trace]

/-- Reassemble a `Sum`-indexed matrix from its four blocks. -/
theorem fromBlocks_sumBlocks (M : Matrix (Sum α β) (Sum α β) ℂ) :
    Matrix.fromBlocks (sumBlock11 M) (sumBlock12 M) (sumBlock21 M) (sumBlock22 M) = M := by
  ext (_ | _) (_ | _) <;> rfl

/-- The upper-left block of a positive semidefinite block matrix is positive semidefinite. -/
theorem sumBlock11_posSemidef {M : Matrix (Sum α β) (Sum α β) ℂ}
    (hM : M.PosSemidef) :
    (sumBlock11 M).PosSemidef :=
  hM.submatrix Sum.inl

/-- The lower-right block of a positive semidefinite block matrix is positive semidefinite. -/
theorem sumBlock22_posSemidef {M : Matrix (Sum α β) (Sum α β) ℂ}
    (hM : M.PosSemidef) :
    (sumBlock22 M).PosSemidef :=
  hM.submatrix Sum.inr

/-- A block-diagonal matrix with positive semidefinite diagonal blocks is
positive semidefinite. -/
theorem fromBlocks_diagonal_posSemidef [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {A : Matrix α α ℂ} {D : Matrix β β ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.IsHermitian.ext_iff.mp hA.isHermitian,
        Matrix.IsHermitian.ext_iff.mp hD.isHermitian]
  · intro x
    let xl : α → ℂ := fun i => x (Sum.inl i)
    let xr : β → ℂ := fun i => x (Sum.inr i)
    have hleft : 0 ≤ star xl ⬝ᵥ A.mulVec xl :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 xl
    have hright : 0 ≤ star xr ⬝ᵥ D.mulVec xr :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hD).2 xr
    have hsum : 0 ≤ star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr :=
      add_nonneg hleft hright
    have hquad :
        star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D).mulVec x =
          star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_fromBlocks, Matrix.dotProduct_block]
      simp [Matrix.dotProduct_mulVec, xl, xr]
      change
        Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr =
        Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr
      rfl
    simpa [hquad] using hsum

/-- A block-diagonal matrix with positive definite diagonal blocks is positive
definite, even when the two block index types have different dimensions. -/
theorem fromBlocks_diagonal_posDef [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {A : Matrix α α ℂ} {D : Matrix β β ℂ}
    (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ).PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (fromBlocks_diagonal_posSemidef hA.posSemidef hD.posSemidef).isHermitian ?_
  intro x hx
  let xl : α → ℂ := fun i => x (Sum.inl i)
  let xr : β → ℂ := fun i => x (Sum.inr i)
  have hsplit : xl ≠ 0 ∨ xr ≠ 0 := by
    by_cases hxl : xl = 0
    · right
      intro hxr
      apply hx
      funext i
      cases i with
      | inl i =>
          change xl i = 0
          simpa using congrFun hxl i
      | inr i =>
          change xr i = 0
          simpa using congrFun hxr i
    · exact Or.inl hxl
  have hleft : 0 ≤ star xl ⬝ᵥ A.mulVec xl := hA.posSemidef.dotProduct_mulVec_nonneg xl
  have hright : 0 ≤ star xr ⬝ᵥ D.mulVec xr := hD.posSemidef.dotProduct_mulVec_nonneg xr
  have hsum : 0 < star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr := by
    cases hsplit with
    | inl hxl => exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hxl) hright
    | inr hxr => exact add_pos_of_nonneg_of_pos hleft (hD.dotProduct_mulVec_pos hxr)
  have hquad :
      star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D).mulVec x =
        star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_fromBlocks, Matrix.dotProduct_block]
    simp [Matrix.dotProduct_mulVec, xl, xr]
    change
      Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr =
      Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr
    rfl
  simpa [hquad] using hsum

/-- A Gram/congruence block matrix is positive semidefinite.

This is the block factorization
`[RᴴDR RᴴD; DR D] = [Rᴴ 1] D [R; 1]`, expressed with `Sum` blocks. -/
theorem fromBlocks_gram_posSemidef [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {D : Matrix β β ℂ} (hD : D.PosSemidef)
    (R : Matrix β α ℂ) :
    (Matrix.fromBlocks (Rᴴ * D * R) (Rᴴ * D) (D * R) D :
      Matrix (Sum α β) (Sum α β) ℂ).PosSemidef := by
  classical
  let diagD : Matrix (Sum α β) (Sum α β) ℂ := Matrix.fromBlocks 0 0 0 D
  let T : Matrix (Sum α β) (Sum α β) ℂ := Matrix.fromBlocks 1 0 R 1
  have hdiagD : diagD.PosSemidef := by
    simpa [diagD] using
      fromBlocks_diagonal_posSemidef
        (A := (0 : Matrix α α ℂ)) (D := D) Matrix.PosSemidef.zero hD
  have hconj : (Tᴴ * diagD * T).PosSemidef :=
    hdiagD.conjTranspose_mul_mul_same T
  have hfactor :
      Tᴴ * diagD * T =
        (Matrix.fromBlocks (Rᴴ * D * R) (Rᴴ * D) (D * R) D :
          Matrix (Sum α β) (Sum α β) ℂ) := by
    ext (_ | _) (_ | _) <;>
      simp [diagD, T, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
  simpa [hfactor] using hconj

/-- The lower-right Schur complement of a positive semidefinite block matrix is
positive semidefinite when the lower-right block is positive definite. -/
theorem fromBlocks_posSemidef_schurComplement22 [Fintype α] [Fintype β] [DecidableEq β]
    {A : Matrix α α ℂ} {B : Matrix α β ℂ} {D : Matrix β β ℂ}
    (hD : D.PosDef)
    (hM : (Matrix.fromBlocks A B Bᴴ D : Matrix (Sum α β) (Sum α β) ℂ).PosSemidef) :
    letI : Invertible D := hD.isUnit.invertible
    (A - B * D⁻¹ * Bᴴ).PosSemidef := by
  classical
  letI : Invertible D := hD.isUnit.invertible
  exact (Matrix.PosDef.fromBlocks₂₂ A B (D := D) hD).mp hM

/-- Parallel sum in the asymmetric Schur-complement form used by the
Frank--Lieb route. For Hermitian `X`, this is the usual
`X : (Y) = X - X (X + Y)⁻¹ X`. -/
def parallelSum [Fintype α] [DecidableEq α] (X Y : QIT.CMatrix α) : QIT.CMatrix α :=
  X - X * (X + Y)⁻¹ * X

/-- Hypograph block characterization for `parallelSum`.

Under the positive-definite lower-right block `X + Y`, `Z ≤ X : Y` is
equivalent to positivity of the Schur block
`[[X - Z, X], [X, X + Y]]`. -/
theorem le_parallelSum_iff_fromBlocks_posSemidef [Fintype α] [DecidableEq α]
    {X Y Z : QIT.CMatrix α} (hX : X.IsHermitian) (hXY : (X + Y).PosDef) :
    Z ≤ parallelSum X Y ↔
      (Matrix.fromBlocks (X - Z) X X (X + Y) : QIT.CMatrix (Sum α α)).PosSemidef := by
  classical
  letI : Invertible (X + Y) := hXY.isUnit.invertible
  rw [Matrix.le_iff]
  have hschur :
      (Matrix.fromBlocks (X - Z) X X (X + Y) : QIT.CMatrix (Sum α α)).PosSemidef ↔
        (X - Z - X * (X + Y)⁻¹ * X).PosSemidef := by
    simpa [hX.eq] using
      (Matrix.PosDef.fromBlocks₂₂ (X - Z) X (D := X + Y) hXY)
  rw [hschur]
  simp [parallelSum, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Positive definite matrices are closed under binary convex combinations. -/
theorem PosDef.convexCombination [Fintype α] {A B : QIT.CMatrix α}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • A + (1 - t) • B).PosDef := by
  by_cases ht_zero : t = 0
  · subst t
    simpa using hB
  by_cases ht_one : t = 1
  · subst t
    simpa using hA
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
  have h1tpos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 ht_one)
  exact Matrix.PosDef.add
    (Matrix.PosDef.smul hA htpos)
    (Matrix.PosDef.smul hB h1tpos)

/-- Convex combinations preserve the Schur-block hypograph condition for
`parallelSum`. This is the block-PSD closure step behind concavity. -/
theorem fromBlocks_parallelSum_hypograph_convex_posSemidef [Fintype α] [DecidableEq α]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : QIT.CMatrix α}
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h₁ :
      (Matrix.fromBlocks (X₁ - Z₁) X₁ X₁ (X₁ + Y₁) :
        QIT.CMatrix (Sum α α)).PosSemidef)
    (h₂ :
      (Matrix.fromBlocks (X₂ - Z₂) X₂ X₂ (X₂ + Y₂) :
        QIT.CMatrix (Sum α α)).PosSemidef) :
    (Matrix.fromBlocks
        ((t • X₁ + (1 - t) • X₂) - (t • Z₁ + (1 - t) • Z₂))
        (t • X₁ + (1 - t) • X₂)
        (t • X₁ + (1 - t) • X₂)
        ((t • X₁ + (1 - t) • X₂) + (t • Y₁ + (1 - t) • Y₂)) :
      QIT.CMatrix (Sum α α)).PosSemidef := by
  have hconv :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul h₁ ht0)
      (Matrix.PosSemidef.smul h₂ (sub_nonneg.mpr ht1))
  convert hconv using 1
  ext (_ | _) (_ | _) <;>
    simp [Matrix.fromBlocks_smul, sub_eq_add_neg] <;>
    ring

/-- Concavity of the parallel sum on PSD/PD pairs, obtained from the
Schur-complement hypograph block and PSD closure under convex combinations. -/
theorem parallelSum_concave_posDef [Fintype α] [DecidableEq α]
    {X₁ X₂ Y₁ Y₂ : QIT.CMatrix α}
    (hX₁ : X₁.PosSemidef) (hX₂ : X₂.PosSemidef)
    (hY₁ : Y₁.PosDef) (hY₂ : Y₂.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • parallelSum X₁ Y₁ + (1 - t) • parallelSum X₂ Y₂ ≤
      parallelSum
        (t • X₁ + (1 - t) • X₂)
        (t • Y₁ + (1 - t) • Y₂) := by
  have hXY₁ : (X₁ + Y₁).PosDef :=
    Matrix.PosDef.posSemidef_add hX₁ hY₁
  have hXY₂ : (X₂ + Y₂).PosDef :=
    Matrix.PosDef.posSemidef_add hX₂ hY₂
  have hblock₁ :
      (Matrix.fromBlocks (X₁ - parallelSum X₁ Y₁) X₁ X₁ (X₁ + Y₁) :
        QIT.CMatrix (Sum α α)).PosSemidef :=
    (le_parallelSum_iff_fromBlocks_posSemidef hX₁.isHermitian hXY₁).mp (le_refl _)
  have hblock₂ :
      (Matrix.fromBlocks (X₂ - parallelSum X₂ Y₂) X₂ X₂ (X₂ + Y₂) :
        QIT.CMatrix (Sum α α)).PosSemidef :=
    (le_parallelSum_iff_fromBlocks_posSemidef hX₂.isHermitian hXY₂).mp (le_refl _)
  have hXbar :
      (t • X₁ + (1 - t) • X₂).PosSemidef :=
    Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul hX₁ ht0)
      (Matrix.PosSemidef.smul hX₂ (sub_nonneg.mpr ht1))
  have hYbar :
      (t • Y₁ + (1 - t) • Y₂).PosDef :=
    Matrix.PosDef.convexCombination hY₁ hY₂ ht0 ht1
  have hXYbar :
      ((t • X₁ + (1 - t) • X₂) + (t • Y₁ + (1 - t) • Y₂)).PosDef :=
    Matrix.PosDef.posSemidef_add hXbar hYbar
  have hblock :
      (Matrix.fromBlocks
          ((t • X₁ + (1 - t) • X₂) -
            (t • parallelSum X₁ Y₁ + (1 - t) • parallelSum X₂ Y₂))
          (t • X₁ + (1 - t) • X₂)
          (t • X₁ + (1 - t) • X₂)
          ((t • X₁ + (1 - t) • X₂) + (t • Y₁ + (1 - t) • Y₂)) :
        QIT.CMatrix (Sum α α)).PosSemidef :=
    fromBlocks_parallelSum_hypograph_convex_posSemidef
      ht0 ht1 hblock₁ hblock₂
  exact
    (le_parallelSum_iff_fromBlocks_posSemidef hXbar.isHermitian hXYbar).mpr hblock

section AndoResolvent

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Ando's resolvent integrand for the tensorized parallel-sum route:
`A ⊗ I * (A ⊗ I + r • (I ⊗ B))⁻¹ * (I ⊗ B)`. -/
def andoResolventIntegrand
    (r : ℝ) (A : QIT.CMatrix a) (B : QIT.CMatrix b) : QIT.CMatrix (a × b) :=
  Matrix.kronecker A (1 : QIT.CMatrix b) *
    (Matrix.kronecker A (1 : QIT.CMatrix b) +
      r • Matrix.kronecker (1 : QIT.CMatrix a) B)⁻¹ *
    Matrix.kronecker (1 : QIT.CMatrix a) B

/-- The Ando resolvent denominator is positive definite when `A ≥ 0`, `B > 0`,
and `r > 0`. -/
theorem andoDenom_posDef
    {r : ℝ} {A : QIT.CMatrix a} {B : QIT.CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosDef) (hr : 0 < r) :
    (Matrix.kronecker A (1 : QIT.CMatrix b) +
      r • Matrix.kronecker (1 : QIT.CMatrix a) B).PosDef := by
  have hleft :
      (Matrix.kronecker A (1 : QIT.CMatrix b)).PosSemidef :=
    hA.kronecker Matrix.PosSemidef.one
  have hright₀ :
      (Matrix.kronecker (1 : QIT.CMatrix a) B).PosDef :=
    Matrix.PosDef.one.kronecker hB
  have hright :
      (r • Matrix.kronecker (1 : QIT.CMatrix a) B).PosDef :=
    Matrix.PosDef.smul hright₀ hr
  exact Matrix.PosDef.posSemidef_add hleft hright

/-- Resolvent-complement form of the tensorized Ando integrand:
`r * (A ⊗ I) (A ⊗ I + r I ⊗ B)⁻¹ (I ⊗ B)` is the Schur-complement
expression `X - X (X + rZ)⁻¹ X` with `X = A ⊗ I` and `Z = I ⊗ B`. -/
theorem andoResolventIntegrand_smul_eq_resolventComplement
    {r : ℝ} {A : QIT.CMatrix a} {B : QIT.CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosDef) (hr : 0 < r) :
    r • andoResolventIntegrand (a := a) (b := b) r A B =
      Matrix.kronecker A (1 : QIT.CMatrix b) -
        Matrix.kronecker A (1 : QIT.CMatrix b) *
          (Matrix.kronecker A (1 : QIT.CMatrix b) +
            r • Matrix.kronecker (1 : QIT.CMatrix a) B)⁻¹ *
          Matrix.kronecker A (1 : QIT.CMatrix b) := by
  let X : QIT.CMatrix (a × b) := Matrix.kronecker A (1 : QIT.CMatrix b)
  let Z : QIT.CMatrix (a × b) := Matrix.kronecker (1 : QIT.CMatrix a) B
  let D : QIT.CMatrix (a × b) := X + r • Z
  have hD : D.PosDef := by
    simpa [X, Z, D] using andoDenom_posDef (a := a) (b := b) hA hB hr
  have hdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hright : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hdet
  have hXD : X * D⁻¹ * D = X := by
    rw [Matrix.mul_assoc, hright, Matrix.mul_one]
  calc
    r • andoResolventIntegrand (a := a) (b := b) r A B
        = X * D⁻¹ * (r • Z) := by
          simp [andoResolventIntegrand, X, Z, D, Matrix.mul_assoc]
    _ = X * D⁻¹ * (D - X) := by
          congr 2
          simp [D, sub_eq_add_neg, add_assoc, add_comm]
    _ = X - X * D⁻¹ * X := by
          rw [mul_sub, hXD]
    _ = Matrix.kronecker A (1 : QIT.CMatrix b) -
        Matrix.kronecker A (1 : QIT.CMatrix b) *
          (Matrix.kronecker A (1 : QIT.CMatrix b) +
            r • Matrix.kronecker (1 : QIT.CMatrix a) B)⁻¹ *
          Matrix.kronecker A (1 : QIT.CMatrix b) := by
          simp [X, Z, D]

/-- Pointwise concavity of Ando's resolvent integrand in the positive
definite reference argument.

This is the Schur-complement/parallel-sum step needed before integrating the
Audenaert representation in the Lieb--Ando trace concavity route. -/
theorem andoResolventIntegrand_concave_posDef
    {A₁ A₂ : QIT.CMatrix a} {B₁ B₂ : QIT.CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {r t : ℝ} (hr : 0 < r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • andoResolventIntegrand (a := a) (b := b) r A₁ B₁ +
        (1 - t) • andoResolventIntegrand (a := a) (b := b) r A₂ B₂ ≤
      andoResolventIntegrand (a := a) (b := b) r
        (t • A₁ + (1 - t) • A₂)
        (t • B₁ + (1 - t) • B₂) := by
  let X₁ : QIT.CMatrix (a × b) := Matrix.kronecker A₁ (1 : QIT.CMatrix b)
  let X₂ : QIT.CMatrix (a × b) := Matrix.kronecker A₂ (1 : QIT.CMatrix b)
  let Z₁ : QIT.CMatrix (a × b) := Matrix.kronecker (1 : QIT.CMatrix a) B₁
  let Z₂ : QIT.CMatrix (a × b) := Matrix.kronecker (1 : QIT.CMatrix a) B₂
  have hX₁ : X₁.PosSemidef := by
    simpa [X₁] using hA₁.kronecker Matrix.PosSemidef.one
  have hX₂ : X₂.PosSemidef := by
    simpa [X₂] using hA₂.kronecker Matrix.PosSemidef.one
  have hY₁ : (r • Z₁).PosDef := by
    have hZ₁ : Z₁.PosDef := by
      simpa [Z₁] using Matrix.PosDef.one.kronecker hB₁
    exact Matrix.PosDef.smul hZ₁ hr
  have hY₂ : (r • Z₂).PosDef := by
    have hZ₂ : Z₂.PosDef := by
      simpa [Z₂] using Matrix.PosDef.one.kronecker hB₂
    exact Matrix.PosDef.smul hZ₂ hr
  have hYbar :
      r • (t • Z₁ + (1 - t) • Z₂) =
        t • (r • Z₁) + (1 - t) • (r • Z₂) := by
    ext i j
    simp [Matrix.smul_apply]
    ring
  have hps :
      t • Matrix.parallelSum X₁ (r • Z₁) +
          (1 - t) • Matrix.parallelSum X₂ (r • Z₂) ≤
        Matrix.parallelSum
          (t • X₁ + (1 - t) • X₂)
          (t • (r • Z₁) + (1 - t) • (r • Z₂)) :=
    Matrix.parallelSum_concave_posDef hX₁ hX₂ hY₁ hY₂ ht0 ht1
  have hscale :
      r • (t • andoResolventIntegrand (a := a) (b := b) r A₁ B₁ +
          (1 - t) • andoResolventIntegrand (a := a) (b := b) r A₂ B₂) ≤
        r • andoResolventIntegrand (a := a) (b := b) r
          (t • A₁ + (1 - t) • A₂)
          (t • B₁ + (1 - t) • B₂) := by
    have hAbar : (t • A₁ + (1 - t) • A₂).PosSemidef :=
      Matrix.PosSemidef.add
        (Matrix.PosSemidef.smul hA₁ ht0)
        (Matrix.PosSemidef.smul hA₂ (sub_nonneg.mpr ht1))
    have hBbar : (t • B₁ + (1 - t) • B₂).PosDef :=
      Matrix.PosDef.convexCombination hB₁ hB₂ ht0 ht1
    have hXbar :
        Matrix.kronecker (t • A₁ + (1 - t) • A₂) (1 : QIT.CMatrix b) =
          t • X₁ + (1 - t) • X₂ := by
      ext i j
      simp [X₁, X₂, Matrix.kronecker, Matrix.kroneckerMap_apply, add_mul,
        mul_comm, mul_left_comm, mul_assoc]
    have hZbar :
        Matrix.kronecker (1 : QIT.CMatrix a) (t • B₁ + (1 - t) • B₂) =
          t • Z₁ + (1 - t) • Z₂ := by
      ext i j
      simp [Z₁, Z₂, Matrix.kronecker, Matrix.kroneckerMap_apply, add_mul,
        mul_comm, mul_left_comm, mul_assoc]
    have hleft₁ :
        r • andoResolventIntegrand (a := a) (b := b) r A₁ B₁ =
          Matrix.parallelSum X₁ (r • Z₁) := by
      rw [andoResolventIntegrand_smul_eq_resolventComplement hA₁ hB₁ hr]
      simp [Matrix.parallelSum, X₁, Z₁]
    have hleft₂ :
        r • andoResolventIntegrand (a := a) (b := b) r A₂ B₂ =
          Matrix.parallelSum X₂ (r • Z₂) := by
      rw [andoResolventIntegrand_smul_eq_resolventComplement hA₂ hB₂ hr]
      simp [Matrix.parallelSum, X₂, Z₂]
    have hright :
        r • andoResolventIntegrand (a := a) (b := b) r
            (t • A₁ + (1 - t) • A₂)
            (t • B₁ + (1 - t) • B₂) =
          Matrix.parallelSum
            (t • X₁ + (1 - t) • X₂)
            (t • (r • Z₁) + (1 - t) • (r • Z₂)) := by
      rw [andoResolventIntegrand_smul_eq_resolventComplement hAbar hBbar hr]
      rw [hXbar, hZbar, hYbar]
      rfl
    have hleft_scaled :
        r • (t • andoResolventIntegrand (a := a) (b := b) r A₁ B₁ +
            (1 - t) • andoResolventIntegrand (a := a) (b := b) r A₂ B₂) =
          t • Matrix.parallelSum X₁ (r • Z₁) +
            (1 - t) • Matrix.parallelSum X₂ (r • Z₂) := by
      rw [smul_add]
      calc
        r • (t • andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
            r • ((1 - t) • andoResolventIntegrand (a := a) (b := b) r A₂ B₂) =
          t • (r • andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
            (1 - t) • (r • andoResolventIntegrand (a := a) (b := b) r A₂ B₂) := by
            ext i j
            simp [Matrix.smul_apply]
            ring
        _ = t • Matrix.parallelSum X₁ (r • Z₁) +
            (1 - t) • Matrix.parallelSum X₂ (r • Z₂) := by
            rw [hleft₁, hleft₂]
    rw [hleft_scaled, hright]
    exact hps
  let L : QIT.CMatrix (a × b) :=
    t • andoResolventIntegrand (a := a) (b := b) r A₁ B₁ +
      (1 - t) • andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let R : QIT.CMatrix (a × b) :=
    andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have hdiff : (r • R - r • L).PosSemidef := by
    exact Matrix.le_iff.mp (by simpa [L, R] using hscale)
  have hdiff_scaled : ((r⁻¹ : ℝ) • (r • R - r • L)).PosSemidef :=
    Matrix.PosSemidef.smul hdiff (inv_nonneg.mpr hr.le)
  have hdiff_eq : (r⁻¹ : ℝ) • (r • R - r • L) = R - L := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply]
    field_simp [hr.ne']
  rw [hdiff_eq] at hdiff_scaled
  exact Matrix.le_iff.mpr (by simpa [L, R] using hdiff_scaled)

/-- Nonnegative scalar multiples preserve the pointwise concavity of Ando's
resolvent integrand. This is the exact shape used under the positive
Audenaert integral weight. -/
theorem andoResolventIntegrand_weighted_concave_posDef
    {A₁ A₂ : QIT.CMatrix a} {B₁ B₂ : QIT.CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {r t w : ℝ} (hr : 0 < r) (hw : 0 ≤ w) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • (w • andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
        (1 - t) • (w • andoResolventIntegrand (a := a) (b := b) r A₂ B₂) ≤
      w • andoResolventIntegrand (a := a) (b := b) r
        (t • A₁ + (1 - t) • A₂)
        (t • B₁ + (1 - t) • B₂) := by
  let L : QIT.CMatrix (a × b) :=
    t • andoResolventIntegrand (a := a) (b := b) r A₁ B₁ +
      (1 - t) • andoResolventIntegrand (a := a) (b := b) r A₂ B₂
  let R : QIT.CMatrix (a × b) :=
    andoResolventIntegrand (a := a) (b := b) r
      (t • A₁ + (1 - t) • A₂)
      (t • B₁ + (1 - t) • B₂)
  have h : L ≤ R :=
    andoResolventIntegrand_concave_posDef hA₁ hA₂ hB₁ hB₂ hr ht0 ht1
  have hdiff : (R - L).PosSemidef := Matrix.le_iff.mp h
  have hscaled : (w • (R - L)).PosSemidef :=
    Matrix.PosSemidef.smul hdiff hw
  have hdiff_eq :
      w • R -
          (t • (w • andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
            (1 - t) • (w • andoResolventIntegrand (a := a) (b := b) r A₂ B₂)) =
        w • (R - L) := by
    ext i j
    simp [L, Matrix.sub_apply, Matrix.smul_apply]
    ring
  exact Matrix.le_iff.mpr (by simpa [hdiff_eq, R] using hscaled)

/-- Positive fractional-power weights preserve Ando's pointwise
resolvent-integrand concavity. -/
theorem andoResolventIntegrand_rpow_weighted_concave_posDef
    {A₁ A₂ : QIT.CMatrix a} {B₁ B₂ : QIT.CMatrix b}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    {p r t : ℝ} (hr : 0 < r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • ((r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r A₁ B₁) +
        (1 - t) •
          ((r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r A₂ B₂) ≤
      (r ^ (p - 1)) • andoResolventIntegrand (a := a) (b := b) r
        (t • A₁ + (1 - t) • A₂)
        (t • B₁ + (1 - t) • B₂) :=
  andoResolventIntegrand_weighted_concave_posDef
    hA₁ hA₂ hB₁ hB₂ hr (Real.rpow_nonneg hr.le (p - 1)) ht0 ht1

end AndoResolvent

/-- Off-diagonal blocks of a Hermitian block matrix are adjoints. -/
theorem sumBlock21_eq_conjTranspose_sumBlock12_of_isHermitian
    {M : Matrix (Sum α β) (Sum α β) ℂ} (hM : M.IsHermitian) :
    sumBlock21 M = (sumBlock12 M)ᴴ := by
  rw [Matrix.IsHermitian] at hM
  ext i j
  have h := congrArg (fun N : Matrix (Sum α β) (Sum α β) ℂ =>
    N (Sum.inr i) (Sum.inl j)) hM
  simpa [sumBlock21, sumBlock12, Matrix.conjTranspose_apply] using h.symm

end

end Matrix

namespace QIT

universe u

/-- The block matrix `[[A, A], [A, C]]` is positive semidefinite when `A` and
`C - A` are: it factors as `Tᴴ * D * T` with `T = [[I, I], [0, I]]` and
`D = [[A, 0], [0, C - A]]`. -/
theorem cMatrix_fromBlocks_self_le_posSemidef {e : Type u}
    [Fintype e] [DecidableEq e] {A C : CMatrix e}
    (hA : A.PosSemidef) (hCminusA : (C - A).PosSemidef) :
    (Matrix.fromBlocks A A A C : CMatrix (Sum e e)).PosSemidef := by
  classical
  let D : CMatrix (Sum e e) := Matrix.fromBlocks A 0 0 (C - A)
  let T : CMatrix (Sum e e) := Matrix.fromBlocks 1 1 0 1
  have hD : D.PosSemidef := by
    simpa [D] using
      Matrix.fromBlocks_diagonal_posSemidef (A := A) (D := C - A) hA hCminusA
  have hconj : (T.conjTranspose * D * T).PosSemidef := by
    simpa [Matrix.mul_assoc] using hD.mul_mul_conjTranspose_same T.conjTranspose
  have hfactor :
      T.conjTranspose * D * T =
        (Matrix.fromBlocks A A A C : CMatrix (Sum e e)) := by
    (ext i j; cases i) <;> cases j <;>
      simp [D, T, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
        sub_eq_add_neg]
  simpa [hfactor] using hconj

end QIT
