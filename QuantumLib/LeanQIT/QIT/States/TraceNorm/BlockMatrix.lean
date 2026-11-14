/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.TraceNorm.Distance
public import QIT.Util.BlockMatrix

/-!
# Trace norm of block matrices

State-layer specializations of the generic block-matrix algebra to positive
semidefinite square roots and the trace norm.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

universe u v

noncomputable section

variable {α : Type u} {β : Type v}

/-- The positive square root of a block-diagonal positive semidefinite matrix is
the block diagonal of the positive square roots. -/
theorem fromBlocks_diagonal_psdSqrt [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {A : Matrix α α ℂ} {D : Matrix β β ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    QIT.psdSqrt (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ) =
      Matrix.fromBlocks (QIT.psdSqrt A) 0 0 (QIT.psdSqrt D) := by
  classical
  let S : Matrix (Sum α β) (Sum α β) ℂ :=
    Matrix.fromBlocks (QIT.psdSqrt A) 0 0 (QIT.psdSqrt D)
  have hSpos : S.PosSemidef := by
    dsimp [S]
    exact fromBlocks_diagonal_posSemidef (QIT.psdSqrt_pos A) (QIT.psdSqrt_pos D)
  have hSsq : S * S = (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ) := by
    dsimp [S]
    rw [Matrix.fromBlocks_multiply]
    simp [QIT.psdSqrt_mul_self_of_posSemidef hA,
      QIT.psdSqrt_mul_self_of_posSemidef hD]
  simpa [QIT.psdSqrt, S] using
    (CFC.sqrt_unique (a := (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ))
      (b := S) hSsq hSpos.nonneg)

/-- The trace norm of a block-diagonal matrix is the sum of the trace norms of
the diagonal blocks. -/
theorem traceNorm_fromBlocks_diagonal [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (X : Matrix α α ℂ) (Y : Matrix β β ℂ) :
    QIT.traceNorm (Matrix.fromBlocks X 0 0 Y : Matrix (Sum α β) (Sum α β) ℂ) =
      QIT.traceNorm X + QIT.traceNorm Y := by
  classical
  have hgram :
      (Matrix.fromBlocks X 0 0 Y : Matrix (Sum α β) (Sum α β) ℂ)ᴴ *
          (Matrix.fromBlocks X 0 0 Y : Matrix (Sum α β) (Sum α β) ℂ) =
        Matrix.fromBlocks (Xᴴ * X) 0 0 (Yᴴ * Y) := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp
  rw [QIT.traceNorm, hgram,
    fromBlocks_diagonal_psdSqrt (Matrix.posSemidef_conjTranspose_mul_self X)
      (Matrix.posSemidef_conjTranspose_mul_self Y),
    trace_fromBlocks_diagonal]
  simp [QIT.traceNorm]

end

end Matrix
