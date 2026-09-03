/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Finite support projections

This module exposes the finite-dimensional range projection of a complex
matrix as a matrix again.  The API is intentionally small: it gives the
projection laws and the state-support equality criterion needed by the
Yang-Navascues Bob-local orthogonalization route.
-/

@[expose] public section

namespace QIT

noncomputable section

namespace Matrix

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- Orthogonal projection onto the range of a finite matrix, represented again
as a matrix in the computational basis. -/
def rangeProjection (M : CMatrix a) : CMatrix a :=
  Matrix.toEuclideanLin.symm ((LinearMap.range M.toEuclideanLin).starProjection.toLinearMap)

@[simp]
theorem rangeProjection_toEuclideanLin (M : CMatrix a) :
    (rangeProjection M).toEuclideanLin =
      (LinearMap.range M.toEuclideanLin).starProjection.toLinearMap := by
  simp [rangeProjection]

/-- The range projection is Hermitian. -/
theorem rangeProjection_isHermitian (M : CMatrix a) :
    (rangeProjection M).IsHermitian := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mp
    (by
      simpa [rangeProjection_toEuclideanLin] using
        (LinearMap.range M.toEuclideanLin).starProjection_isSymmetric)

/-- The range projection is idempotent. -/
theorem rangeProjection_idempotent (M : CMatrix a) :
    rangeProjection M * rangeProjection M = rangeProjection M := by
  apply Matrix.toEuclideanLin.injective
  have hlin := rangeProjection_toEuclideanLin M
  rw [Matrix.toLpLin_mul]
  ext x i
  rw [hlin]
  simp only [LinearMap.comp_apply]
  exact congrArg (fun v : EuclideanSpace ℂ a => v i)
    ((LinearMap.range M.toEuclideanLin).starProjection_eq_self_iff.mpr
      ((LinearMap.range M.toEuclideanLin).starProjection_apply_mem x))

/-- The range projection fixes the range of the original matrix. -/
theorem rangeProjection_mul_self (M : CMatrix a) :
    rangeProjection M * M = M := by
  apply Matrix.toEuclideanLin.injective
  have hlin := rangeProjection_toEuclideanLin M
  rw [Matrix.toLpLin_mul]
  ext x i
  rw [hlin]
  simp only [LinearMap.comp_apply]
  exact congrArg (fun v : EuclideanSpace ℂ a => v i)
    ((LinearMap.range M.toEuclideanLin).starProjection_eq_self_iff.mpr
      (LinearMap.mem_range_self M.toEuclideanLin x))

/--
If two matrices have ranges supported inside orthogonal Hermitian effects, then
their range projections are orthogonal.
-/
theorem rangeProjection_mul_rangeProjection_eq_zero_of_fixed_orthogonal
    {P Q M N : CMatrix a}
    (hPherm : P.IsHermitian) (hPQ : P * Q = 0)
    (hPM : P * M = M) (hQN : Q * N = N) :
    rangeProjection M * rangeProjection N = 0 := by
  have hPMlin : P.toEuclideanLin.comp M.toEuclideanLin = M.toEuclideanLin := by
    have hm := congrArg Matrix.toEuclideanLin hPM
    rw [Matrix.toLpLin_mul] at hm
    exact hm
  have hQNlin : Q.toEuclideanLin.comp N.toEuclideanLin = N.toEuclideanLin := by
    have hn := congrArg Matrix.toEuclideanLin hQN
    rw [Matrix.toLpLin_mul] at hn
    exact hn
  have hMle : LinearMap.range M.toEuclideanLin ≤ LinearMap.range P.toEuclideanLin := by
    intro v hv
    rcases hv with ⟨x, rfl⟩
    exact ⟨M.toEuclideanLin x, DFunLike.congr_fun hPMlin x⟩
  have hNle : LinearMap.range N.toEuclideanLin ≤ LinearMap.range Q.toEuclideanLin := by
    intro v hv
    rcases hv with ⟨x, rfl⟩
    exact ⟨N.toEuclideanLin x, DFunLike.congr_fun hQNlin x⟩
  have hPQlin : P.toEuclideanLin.comp Q.toEuclideanLin = 0 := by
    ext x i
    rw [← Matrix.toLpLin_mul]
    simp [hPQ]
  have hPorthoQ : LinearMap.range P.toEuclideanLin ⟂ LinearMap.range Q.toEuclideanLin := by
    intro x hx y hy
    rcases hx with ⟨x0, rfl⟩
    rcases hy with ⟨y0, rfl⟩
    have hPsym : P.toEuclideanLin.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hPherm
    calc
      inner ℂ (Q.toEuclideanLin y0) (P.toEuclideanLin x0)
          = inner ℂ (P.toEuclideanLin (Q.toEuclideanLin y0)) x0 :=
              (hPsym (Q.toEuclideanLin y0) x0).symm
      _ = inner ℂ ((P.toEuclideanLin.comp Q.toEuclideanLin) y0) x0 := rfl
      _ = 0 := by simp [hPQlin]
  have hMNortho : LinearMap.range M.toEuclideanLin ⟂ LinearMap.range N.toEuclideanLin :=
    hPorthoQ.mono hMle hNle
  have hstar := Submodule.starProjection_comp_starProjection_eq_zero_iff.mpr hMNortho
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul, rangeProjection_toEuclideanLin, rangeProjection_toEuclideanLin]
  simpa using congrArg ContinuousLinearMap.toLinearMap hstar

/--
Two operators have the same left action on the support of a state matrix when
they give the same unnormalized left action on that matrix.
-/
def sameOnStateSupport {b : Type*} [Fintype b] (rho Q R : CMatrix b) : Prop :=
  Q * rho = R * rho

/-- State-support equality is reflexive. -/
theorem sameOnStateSupport_refl {b : Type*} [Fintype b] (rho Q : CMatrix b) :
    sameOnStateSupport rho Q Q :=
  rfl

/-- Equal left action on a Hermitian state matrix gives equal post-selected
density matrices. -/
theorem postMatrix_eq_of_sameOnStateSupport {b : Type*} [Fintype b] {rho Q R : CMatrix b}
    (hrho : rho.IsHermitian) (h : sameOnStateSupport rho Q R) :
    Q * rho * Matrix.conjTranspose Q = R * rho * Matrix.conjTranspose R := by
  have hright : rho * Matrix.conjTranspose Q = rho * Matrix.conjTranspose R := by
    have hc := congrArg Matrix.conjTranspose h
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hrho] at hc
    exact hc
  calc
    Q * rho * Matrix.conjTranspose Q = R * rho * Matrix.conjTranspose Q := by rw [h]
    _ = R * (rho * Matrix.conjTranspose Q) := by rw [Matrix.mul_assoc]
    _ = R * (rho * Matrix.conjTranspose R) := by rw [hright]
    _ = R * rho * Matrix.conjTranspose R := by rw [Matrix.mul_assoc]

end Matrix

end

end QIT
