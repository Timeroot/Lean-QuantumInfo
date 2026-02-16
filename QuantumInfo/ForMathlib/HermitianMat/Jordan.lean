/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Jordan.Basic

import QuantumInfo.ForMathlib.HermitianMat.CFC
import QuantumInfo.ForMathlib.HermitianMat.Order

/-!
Hermitian matrices have a Jordan algebra structure given by
`A * B := 2⁻¹ • (A.toMat * B.toMat + B.toMat * A.toMat)`. We call this operation
`HermitianMat.symmMul`, but it's available as `*` multiplication scoped under
`HermMul`. When `A` and `B` commute, this reduces to standard matrix multiplication.
-/

noncomputable section

section starRing

variable {d 𝕜 : Type*} [Fintype d] [Field 𝕜] [StarRing 𝕜]
variable (A B : HermitianMat d 𝕜)

namespace HermitianMat

def symmMul : HermitianMat d 𝕜 :=
  ⟨(2 : 𝕜)⁻¹ • (A.mat * B.mat + B.mat * A.mat),
    by simp [selfAdjoint, IsSelfAdjoint, add_comm, Matrix.star_eq_conjTranspose]⟩

theorem symmMul_comm : A.symmMul B = B.symmMul A := by
  rw [symmMul, symmMul, Subtype.mk.injEq, add_comm]

@[simp]
theorem symmMul_zero : A.symmMul 0 = 0:= by
  simp [symmMul]

@[simp]
theorem zero_symmMul : symmMul 0 A = 0 := by
  simp [symmMul]

theorem symmMul_toMat : (A.symmMul B).mat =
    (2 : 𝕜)⁻¹ • (A.mat * B.mat + B.mat * A.mat) := by
  rfl

variable [Invertible (2 : 𝕜)]

variable {A B} in
@[simp]
theorem symmMul_of_commute (hAB : Commute A.mat B.mat) :
    (A.symmMul B).mat = A.mat * B.mat := by
  rw [symmMul_toMat, hAB]
  rw [smul_add, ← add_smul, inv_eq_one_div, ← add_div]
  rw [add_self_div_two, one_smul]

theorem symmMul_self : (symmMul A A).mat = A.mat * A.mat := by
  simp

variable [DecidableEq d]

@[simp]
theorem symmMul_one : A.symmMul 1 = A := by
  ext1; simp

@[simp]
theorem one_symmMul : symmMul 1 A = A := by
  ext1; simp

@[simp]
theorem symmMul_neg_one : A.symmMul (-1) = -A := by
  ext1; simp

@[simp]
theorem neg_one_symmMul : symmMul (-1) A = -A := by
  ext1; simp

end HermitianMat
end starRing

namespace HermMul

section starRing

variable {d 𝕜 : Type*} [Fintype d] [Field 𝕜] [StarRing 𝕜]
variable (A B : HermitianMat d 𝕜)

scoped instance : CommMagma (HermitianMat d 𝕜) where
  mul := HermitianMat.symmMul
  mul_comm := HermitianMat.symmMul_comm

-- --Stupid shortcut that might actually help a lot
-- scoped instance : Mul (HermitianMat d 𝕜) :=
  -- CommMagma.toMul

theorem mul_eq_symmMul : A * B = A.symmMul B := by
  rfl

scoped instance : IsCommJordan (HermitianMat d 𝕜) where
  lmul_comm_rmul_rmul a b := by
    ext1
    simp only [mul_eq_symmMul, HermitianMat.symmMul_toMat, smul_add,
      mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    abel

scoped instance : MulZeroClass (HermitianMat d 𝕜) where
  zero_mul := by simp [mul_eq_symmMul]
  mul_zero := by simp [mul_eq_symmMul]

variable [DecidableEq d] [Invertible (2 : 𝕜)]

scoped instance : MulZeroOneClass (HermitianMat d 𝕜) where
  one_mul := by simp [mul_eq_symmMul]
  mul_one := by simp [mul_eq_symmMul]

end starRing

section field

variable {d 𝕜 : Type*} [Fintype d] [Field 𝕜] [StarRing 𝕜]

scoped instance : NonUnitalNonAssocRing (HermitianMat d 𝕜) where
  left_distrib a b c := by
    ext1
    simp [mul_eq_symmMul, HermitianMat.symmMul_toMat, mul_add, add_mul]
    abel
  right_distrib a b c := by
    ext1
    simp [mul_eq_symmMul, HermitianMat.symmMul_toMat, mul_add, add_mul]
    abel

variable [Invertible (2 : 𝕜)] [DecidableEq d]

--TODO: Upgrade this to NonAssocCommRing, see #28604 in Mathlib
scoped instance : NonAssocRing (HermitianMat d 𝕜) where

end field

section rclike

variable {d 𝕜 : Type*} [Fintype d] [RCLike 𝕜]

scoped instance : IsScalarTower ℝ (HermitianMat d 𝕜) (HermitianMat d 𝕜) where
  smul_assoc r x y := by
    ext : 2
    simp only [smul_eq_mul, mul_eq_symmMul, HermitianMat.symmMul_toMat,
      HermitianMat.mat_smul, smul_add]
    simp

end rclike

end HermMul
