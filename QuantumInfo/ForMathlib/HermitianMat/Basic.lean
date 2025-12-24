/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.Matrix
import QuantumInfo.ForMathlib.IsMaximalSelfAdjoint
import QuantumInfo.ForMathlib.ContinuousLinearMap

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix

/-- The type of Hermitian matrices, as a `Subtype`. Equivalent to a `Matrix n n α` bundled
with the fact that `Matrix.IsHermitian`. -/
abbrev HermitianMat (n : Type*) (α : Type*) [AddGroup α] [StarAddMonoid α] :=
  (selfAdjoint (Matrix n n α) : Type (max u_1 u_2))

namespace HermitianMat

variable {α : Type*} {m n : Type*}

section addgroup

variable [AddGroup α] [StarAddMonoid α]

theorem eq_IsHermitian : HermitianMat n α  = { m : Matrix n n α // m.IsHermitian} := by
  rfl

@[coe, reducible] def toMat : HermitianMat n α → Matrix n n α :=
  Subtype.val

instance : Coe (HermitianMat n α) (Matrix n n α) := ⟨toMat⟩

@[simp]
theorem val_eq_coe (A : HermitianMat n α) : A.val = A := by
  rfl

@[simp]
theorem mk_toMat (x : Matrix n n α) (h) : HermitianMat.toMat (Subtype.mk x h) = x := by
  rfl

/-- Alias for HermitianMat.property or HermitianMat.2, this gets the fact that the value
  is actually `IsHermitian`.-/
theorem H (A : HermitianMat n α) : A.toMat.IsHermitian :=
  A.2

@[ext] protected theorem ext {A B : HermitianMat n α} : A.toMat = B.toMat → A = B :=
  Subtype.eq

instance instFun : FunLike (HermitianMat n α) n (n → α) where
  coe M := (M : Matrix n n α)
  coe_injective' _ _ h := HermitianMat.ext h

instance instStar : Star (HermitianMat n α) :=
  ⟨(·)⟩

instance instTrivialStar : TrivialStar (HermitianMat n α) :=
  ⟨(refl ·)⟩

@[simp]
theorem conjTranspose_toMat (A : HermitianMat n α) :
    A.toMat.conjTranspose = A :=
  A.H

@[simp]
theorem smul_toMat (A : HermitianMat n ℂ) (c : ℝ) :
  ((Complex.ofReal c) • A.toMat) = (c • A).toMat := by
  rfl

end addgroup
section commring

variable [CommRing α] [StarRing α] [DecidableEq n] [Fintype n]

noncomputable instance instInv : Inv (HermitianMat n α) :=
  ⟨fun x ↦ ⟨x⁻¹, Matrix.IsHermitian.inv x.H⟩⟩

noncomputable instance instZPow : Pow (HermitianMat n α) ℤ :=
  ⟨fun x z ↦ ⟨x^z, Matrix.IsHermitian.zpow x.H z⟩⟩

/-
--There is already a `One` instance when `n` is a `Fintype` (it comes through the fact that we have a
-- (`Ring`) but in principle we shouldn't need that (only DecidableEq!). But, the fact that trying
-- `simp` in `coe_one` below causes a defeq timeout is worrying. So, we keep this commented out, we'll
-- use `Fintype` everywhere we want a `1`.
variable {n : Type*} [DecidableEq n]

instance : One (HermitianMat n α) :=
  ⟨1, by
    simp [selfAdjoint.mem_iff, ← Matrix.ext_iff, Matrix.one_apply, apply_ite (β := α), eq_comm]⟩

@[simp]
theorem coe_one : (1 : HermitianMat n α).toMat = 1 := by
  rfl
-/

end commring
section rclike

variable [RCLike α]

@[simp]
theorem im_eq_zero (A : HermitianMat n α) (x : n) :
    RCLike.im (A x x) = 0 := by
  simpa [CharZero.eq_neg_self_iff] using congrArg (RCLike.im <| · x x) A.H.symm

--Repeat it explicitly for ℂ so that simp can find it
@[simp]
theorem Complex_im_eq_zero (A : HermitianMat n ℂ) (x : n) :
    (A x x).im = 0 :=
  A.im_eq_zero x

variable [Fintype n] [DecidableEq n]

end rclike

section conj

variable [CommRing α] [StarRing α] [Fintype n]
variable (A : HermitianMat n α)

/-- The Hermitian matrix given by conjugating by a (possibly rectangular) Matrix. If we required `B` to be
square, this would apply to any `Semigroup`+`StarMul` (as proved by `IsSelfAdjoint.conjugate`). But this lets
us conjugate to other sizes too, as is done in e.g. Kraus operators. That is, it's a _heterogeneous_ conjguation.
-/
def conj {m} (B : Matrix m n α) : HermitianMat n α →+ HermitianMat m α where
  toFun A :=
    ⟨B * A.toMat * B.conjTranspose, by
    ext
    simp only [Matrix.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      star_sum, star_mul', star_star, show ∀ (a b : n), star (A.toMat b a) = A.toMat a b from congrFun₂ A.property]
    rw [Finset.sum_comm]
    congr! 2
    ring⟩
  map_add' _ _ := by ext1; simp [Matrix.mul_add, Matrix.add_mul]
  map_zero' := by simp

theorem conj_apply (B : Matrix m n α) (A : HermitianMat n α) :
    conj B A = ⟨B * A.toMat * B.conjTranspose, (conj B A).2⟩ := by
  rfl

@[simp]
theorem conj_apply_toMat (B : Matrix m n α) (A : HermitianMat n α) :
    (conj B A).toMat = B * A.toMat * B.conjTranspose := by
  rfl

theorem conj_conj {m l} [Fintype m] (B : Matrix m n α) (C : Matrix l m α) :
    (A.conj B).conj C = A.conj (C * B) := by
  ext1
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

variable (B : HermitianMat n α)

@[simp]
theorem conj_zero [DecidableEq n] : A.conj (0 : Matrix n n α) = 0 := by
  simp [conj_apply]

@[simp]
theorem conj_one [DecidableEq n] : A.conj (1 : Matrix n n α) = A := by
  simp [conj_apply]

variable (R : Type*) [Star R] [TrivialStar R] [CommSemiring R] [Algebra R α] [StarModule R α]

/-- `HermitianMat.conj` as an `R`-linear map, where `R` is the ring of relevant reals. -/
def conjLinear {m} (B : Matrix m n α) : HermitianMat n α →ₗ[R] HermitianMat m α where
  toAddHom := conj B
  map_smul' _ _ := by
    ext1
    --Squeezing this simp because otherwise we run out of heartbeats fast
    simp only [AddHom.toFun_eq_coe, AddHom.coe_coe, conj_apply_toMat,
      selfAdjoint.val_smul, val_eq_coe, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp]
theorem conjLinear_apply (B : Matrix m n α) : conjLinear R B A = conj B A  := by
  rfl

end conj

section eigenspace

variable {𝕜} [RCLike 𝕜] [Fintype n] [DecidableEq n] (A : HermitianMat n 𝕜)

instance [i : Nonempty n] : FaithfulSMul ℝ (HermitianMat n 𝕜) where
  eq_of_smul_eq_smul h := by
    simpa [RCLike.smul_re] using congr(RCLike.re ($(h 1).val i.some i.some))

/-- The continuous linear map associated with a Hermitian matrix. -/
def lin : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n where
  toLinearMap := A.toMat.toEuclideanLin
  cont := LinearMap.continuous_of_finiteDimensional _

@[simp]
theorem isSymmetric : A.lin.IsSymmetric :=
  Matrix.isHermitian_iff_isSymmetric.mp A.H

@[simp]
theorem lin_zero : (0 : HermitianMat n 𝕜).lin = 0 := by
  simp [lin]; rfl

@[simp]
theorem lin_one : (1 : HermitianMat n 𝕜).lin = 1 := by
  simp [lin]; rfl

noncomputable def eigenspace (μ : 𝕜) : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  Module.End.eigenspace A.lin μ

/-- The kernel of a Hermitian matrix `A` as a submodule of Euclidean space, defined by
`LinearMap.ker A.toMat.toEuclideanLin`. Equivalently, the zero-eigenspace. -/
def ker : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  LinearMap.ker A.lin

theorem mem_ker_iff_mulVec_zero (x : EuclideanSpace 𝕜 n) : x ∈ A.ker ↔ A.toMat.mulVec x = 0 := by
  simp [ker, LinearMap.mem_ker, lin, Matrix.toEuclideanLin_apply]
  norm_cast

/-- The kernel of a Hermitian matrix is its zero eigenspace. -/
theorem ker_eq_eigenspace_zero : A.ker = A.eigenspace 0 := by
  ext
  simp [ker, eigenspace]

@[simp]
theorem ker_zero : (0 : HermitianMat n 𝕜).ker = ⊤ := by
  simp [ker]

@[simp]
theorem ker_one : (1 : HermitianMat n 𝕜).ker = ⊥ := by
  simp [ker]; rfl

theorem ker_pos_smul {c : ℝ} (hc : 0 < c) : (c • A).ker = A.ker := by
  ext x
  simp [mem_ker_iff_mulVec_zero, Matrix.smul_mulVec, hc.ne']

/-- The support of a Hermitian matrix `A` as a submodule of Euclidean space, defined by
`LinearMap.range A.toMat.toEuclideanLin`. Equivalently, the sum of all nonzero eigenspaces. -/
def support : Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  LinearMap.range A.lin

/-- The support of a Hermitian matrix is the sum of its nonzero eigenspaces. -/
theorem support_eq_sup_eigenspace_nonzero : A.support = ⨆ μ ≠ 0, A.eigenspace μ := by
  exact A.lin.support_eq_sup_eigenspace_nonzero A.isSymmetric

@[simp]
theorem support_zero : (0 : HermitianMat n 𝕜).support = ⊥ := by
  simp [support]

@[simp]
theorem support_one : (1 : HermitianMat n 𝕜).support = ⊤ := by
  simpa [support] using LinearMap.ker_eq_bot_iff_range_eq_top.mp rfl

@[simp]
theorem ker_orthogonal_eq_support : A.kerᗮ = A.support := by
  rw [ker, support]
  convert ContinuousLinearMap.orthogonal_ker A.lin
  simp

@[simp]
theorem support_orthogonal_eq_range : A.supportᗮ = A.ker := by
  rw [ker, support]
  convert ContinuousLinearMap.orthogonal_range A.lin
  simp

end eigenspace

section diagonal

--TODO: Generalize this more types than ℝ/ℂ
def diagonal [DecidableEq n] (f : n → ℝ) : HermitianMat n ℂ :=
  ⟨Matrix.diagonal (f ·),
    by simp [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]⟩

theorem diagonal_conj_diagonal [Fintype n] [DecidableEq n] (f g : n → ℝ) :
    (diagonal f).conj (diagonal g) =
    diagonal (fun i ↦ f i * (g i)^2) := by
  simp [diagonal, conj]
  intro
  ring

end diagonal

section kronecker
open Kronecker

variable [CommRing α] [StarRing α]

/-- The kronecker product of two HermitianMats, see `Matrix.kroneckerMap`. -/
@[simps]
def kronecker (A : HermitianMat m α) (B : HermitianMat n α) : HermitianMat (m × n) α where
  val := A.toMat ⊗ₖ B.toMat
  property := Matrix.kroneckerMap_IsHermitian A.H B.H

@[inherit_doc HermitianMat.kronecker]
scoped[HermitianMat] infixl:100 " ⊗ₖ " => HermitianMat.kronecker

@[simp]
theorem zero_kronecker (A : HermitianMat m α) : (0 : HermitianMat n α) ⊗ₖ A = 0 := by
  ext1; simp

@[simp]
theorem kronecker_zero (A : HermitianMat m α) : A ⊗ₖ (0 : HermitianMat n α) = 0 := by
  ext1; simp

variable [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] in
@[simp]
theorem kronecker_one_one : (1 : HermitianMat m α) ⊗ₖ (1 : HermitianMat n α) = 1 := by
  ext1; simp

variable (A B : HermitianMat m α) (C : HermitianMat n α) in
theorem add_kronecker : (A + B) ⊗ₖ C = A ⊗ₖ C + B ⊗ₖ C := by
  ext1; simp [Matrix.add_kronecker]

variable (A : HermitianMat m α) (B C : HermitianMat n α) in
theorem kronecker_add : A ⊗ₖ (B + C) = A ⊗ₖ B + A ⊗ₖ C := by
  ext1; simp [Matrix.kronecker_add]

end kronecker

open scoped Pointwise in
theorem spectrum_prod [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {A : HermitianMat m ℂ} {B : HermitianMat n ℂ} :
    spectrum ℝ (A ⊗ₖ B).toMat = spectrum ℝ A.toMat * spectrum ℝ B.toMat :=
  Matrix.spectrum_prod A.H B.H

--Shortcut instance
noncomputable instance : AddCommMonoid (HermitianMat d ℂ) :=
  inferInstance
