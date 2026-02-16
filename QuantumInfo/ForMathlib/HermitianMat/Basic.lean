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
def HermitianMat (n : Type*) (α : Type*) [AddGroup α] [StarAddMonoid α] :=
  (selfAdjoint (Matrix n n α) : Type (max u_1 u_2))

namespace HermitianMat

variable {α R 𝕜 : Type*} {m n : Type*}
variable [Star R] [TrivialStar R]
variable [RCLike 𝕜]

section addgroup

variable [AddGroup α] [StarAddMonoid α]

theorem eq_IsHermitian : HermitianMat n α  = { m : Matrix n n α // m.IsHermitian} := by
  rfl

@[coe] def mat : HermitianMat n α → Matrix n n α :=
  Subtype.val

instance : Coe (HermitianMat n α) (Matrix n n α) := ⟨mat⟩

@[simp]
theorem val_eq_coe (A : HermitianMat n α) : A.val = A := by
  rfl

@[simp]
theorem mat_mk (x : Matrix n n α) (h) : mat ⟨x, h⟩ = x := by
  rfl

@[simp]
theorem mk_mat {A : HermitianMat n α} (h : A.mat.IsHermitian) : ⟨A.mat, h⟩ = A := by
  rfl

/-- Alias for HermitianMat.property or HermitianMat.2, this gets the fact that the value
  is actually `IsHermitian`.-/
theorem H (A : HermitianMat n α) : A.mat.IsHermitian :=
  A.2

@[ext] protected theorem ext {A B : HermitianMat n α} : A.mat = B.mat → A = B :=
  Subtype.eq

instance instFun : FunLike (HermitianMat n α) n (n → α) where
  coe M := (M : Matrix n n α)
  coe_injective' _ _ h := HermitianMat.ext h

@[simp]
theorem mat_apply {A : HermitianMat n α} {i j : n} : A.mat i j = A i j := by
  rfl

@[simp]
theorem conjTranspose_mat (A : HermitianMat n α) :
    A.mat.conjTranspose = A.mat :=
  A.H

instance : AddGroup (HermitianMat n α) :=
  AddSubgroup.toAddGroup _

instance [IsEmpty n] : Unique (HermitianMat n α) where
  default := 0
  uniq a := by ext; exact (IsEmpty.false ‹_›).elim

@[simp, norm_cast]
theorem mat_zero : (0 : HermitianMat n α).mat = 0 := by
  rfl

@[simp]
theorem mk_zero (h : (0 : Matrix n n α).IsHermitian) : ⟨0, h⟩ = (0 : HermitianMat n α) := by
  rfl

@[simp, norm_cast]
theorem mat_add (A B : HermitianMat n α) :
    (A + B).mat = A.mat + B.mat := by
  rfl

@[simp, norm_cast]
theorem mat_sub (A B : HermitianMat n α) :
    (A - B).mat = A.mat - B.mat := by
  rfl

@[simp, norm_cast]
theorem mat_neg (A : HermitianMat n α) :
    (-A).mat = -A.mat := by
  rfl

section smul
variable [SMul R α] [StarModule R α]

instance : SMul R (HermitianMat n α) :=
  ⟨fun c A ↦ ⟨c • A.mat, (IsSelfAdjoint.all _).smul A.H⟩⟩

@[simp, norm_cast]
theorem mat_smul (c : R) (A : HermitianMat n α) :
    (c • A).mat = c • A.mat := by
  rfl

@[simp]
theorem smul_apply (c : R) (A : HermitianMat n α) (i j : n) :
    (c • A) i j = c • A i j := by
  rfl
end smul
section topology

variable [TopologicalSpace α]

instance : TopologicalSpace (HermitianMat n α) :=
  inferInstanceAs (TopologicalSpace (selfAdjoint _))

/- Bizarrely, if we don't tag this fun_prop, then fun_prop fails to prove other things! It's because
it will look through and see that `HermitianMat.mat` is `Subtype.val` *here*, but not in downstream
applications of the tactic. -/
@[fun_prop]
theorem continuous_mat : Continuous (HermitianMat.mat : HermitianMat n α → Matrix n n α) := by
  fun_prop

variable [IsTopologicalAddGroup α]

--In principle, ContinuousAdd and ContinuousNeg just need corresponding instances for α,
-- not all of IsTopologicalAddGroup.

instance : ContinuousAdd (HermitianMat n α) :=
  inferInstanceAs (ContinuousAdd (selfAdjoint _))

instance : ContinuousNeg (HermitianMat n α) :=
  inferInstanceAs (ContinuousNeg (selfAdjoint _))

instance : IsTopologicalAddGroup (HermitianMat n α) where

variable  [TopologicalSpace R] [SMul R α] [ContinuousSMul R α] [StarModule R α]

instance : ContinuousSMul R (HermitianMat n α) where
  continuous_smul := by
    rw [continuous_induced_rng]
    fun_prop

--Shorcut instances:
instance : IsTopologicalAddGroup (HermitianMat n 𝕜) := inferInstance
instance : ContinuousSMul ℝ (HermitianMat n ℂ) := inferInstance

--TODO: Would be good to figure out the general (not just RCLike) version of this.
instance : T3Space (HermitianMat n 𝕜) :=
  inferInstanceAs (T3Space (selfAdjoint _))

end topology

section mulAction
variable [Monoid R] [MulAction R α] [StarModule R α]

instance : MulAction R (HermitianMat n α) :=
  Function.Injective.mulAction Subtype.val Subtype.coe_injective mat_smul

end mulAction
end addgroup
section addcommgroup

variable [AddCommGroup α] [StarAddMonoid α]

instance : AddCommGroup (HermitianMat n α) :=
  AddSubgroup.toAddCommGroup _

@[simp, norm_cast]
theorem mat_finset_sum (f : ι → HermitianMat n α) (s : Finset ι) :
    (∑ i ∈ s, f i).mat = ∑ i ∈ s, (f i).mat := by
  apply AddSubgroup.val_finset_sum

section module

variable [Semiring R] [Module R α] [StarModule R α]
instance : Module R (HermitianMat n α) :=
  inferInstanceAs (Module R (selfAdjoint (Matrix n n α)))

variable [TopologicalSpace α]

/-- The projection from HermitianMat to Matrix, as a continuous linear map. -/
@[simps]
def matₗ : HermitianMat n α →L[R] Matrix n n α where
  toFun := mat
  cont := by fun_prop
  map_add' := by simp
  map_smul' := by simp

end module
end addcommgroup
section ring

variable [NonAssocRing α] [StarRing α] [DecidableEq n]

instance : One (HermitianMat n α) :=
  ⟨1, by
    simp [selfAdjoint.mem_iff, ← Matrix.ext_iff,
      Matrix.one_apply, apply_ite (β := α), eq_comm]⟩

@[simp, norm_cast]
theorem mat_one : (1 : HermitianMat n α).mat = 1 := by
  rfl

@[simp]
theorem mk_one (h : (1 : Matrix n n α).IsHermitian) : ⟨1, h⟩ = (1 : HermitianMat n α) := by
  rfl

@[simp]
theorem one_apply (i j : n) : (1 : HermitianMat n α) i j = (1 : Matrix n n α) i j := by
  rfl

end ring
section commring

variable [CommRing α] [StarRing α] [DecidableEq m] [Fintype m]
variable (A : HermitianMat m α) (n : ℕ) (z : ℤ)

noncomputable instance instInv : Inv (HermitianMat m α) :=
  ⟨fun x ↦ ⟨x⁻¹, x.H.inv⟩⟩

@[simp, norm_cast]
theorem mat_inv : (A⁻¹).mat = A.mat⁻¹ := by
  rfl

@[simp]
theorem zero_inv : ((0 : HermitianMat m α)⁻¹) = 0 := by
  ext1; simp

@[simp]
theorem one_inv : ((1 : HermitianMat m α)⁻¹) = 1 := by
  ext1; simp

noncomputable instance instPow : Pow (HermitianMat m α) ℕ :=
  ⟨fun x n ↦ ⟨x ^ n, x.H.pow n⟩⟩

@[simp, norm_cast]
theorem mat_pow (n : ℕ) : (A ^ n).mat = A.mat ^ n := by
  rfl

@[simp]
theorem pow_zero : A ^ 0 = 1 := by
  ext1; simp

@[simp]
theorem zero_pow (hn : n ≠ 0): (0 : HermitianMat m α) ^ n = 0 := by
  ext1; simp [hn]

@[simp]
theorem one_pow : ((1 : HermitianMat m α) ^ n) = 1 := by
  ext1; simp

noncomputable instance instZPow : Pow (HermitianMat m α) ℤ :=
  ⟨fun x z ↦ ⟨x ^ z, x.H.zpow z⟩⟩

@[simp]
theorem mat_zpow (z : ℤ) : (A ^ z).mat = A.mat ^ z := by
  rfl

@[simp, norm_cast]
theorem zpow_natCast : A ^ (n : ℤ) = A ^ n := by
  rfl

@[simp]
theorem zpow_zero : A ^ (0 : ℤ) = 1 := by
  ext1; simp

@[simp]
theorem zpow_one : A ^ (1 : ℤ) = A := by
  ext1; simp

@[simp]
theorem one_zpow : ((1 : HermitianMat m α) ^ z) = 1 := by
  ext1; simp

@[simp]
theorem zpow_neg_one : A ^ (-1) = A⁻¹ := by
  ext1; exact A.mat.zpow_neg_one

@[simp]
theorem inv_zpow : A⁻¹ ^ z = (A ^ z)⁻¹ := by
  ext1; exact A.mat.inv_zpow z

end commring
section rclike

variable [Finite n] in
instance FiniteDimensional : FiniteDimensional ℝ (HermitianMat n 𝕜) :=
  FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Matrix n n 𝕜))

@[simp]
theorem im_diag_eq_zero (A : HermitianMat n 𝕜) (x : n) :
    RCLike.im (A x x) = 0 := by
  simpa [CharZero.eq_neg_self_iff] using congrArg (RCLike.im <| · x x) A.H.symm

--Repeat it explicitly for Complex.im so that simp can find it
@[simp]
theorem complex_im_eq_zero (A : HermitianMat n ℂ) (x : n) :
    (A x x).im = 0 :=
  A.im_diag_eq_zero x

variable [DecidableEq n] [Fintype n]

/-- Unlike for `Matrix`, this is always true for `HermitianMat`: the 0 eigenvalue
gets mapped to 0 and then back again to 0. --/
@[simp]
theorem inv_inv (A : HermitianMat n 𝕜) : (A⁻¹)⁻¹ = A := by
  sorry

noncomputable instance : InvolutiveInv (HermitianMat n 𝕜) :=
  ⟨inv_inv⟩

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
    ⟨B * A.mat * B.conjTranspose, by
    ext
    simp only [Matrix.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      star_sum, star_mul', star_star, show ∀ (a b : n), star (A.mat b a) = A.mat a b from congrFun₂ A.property]
    rw [Finset.sum_comm]
    congr! 2
    ring⟩
  map_add' _ _ := by ext1; simp [Matrix.mul_add, Matrix.add_mul]
  map_zero' := by simp

theorem conj_apply (B : Matrix m n α) (A : HermitianMat n α) :
    conj B A = ⟨B * A.mat * B.conjTranspose, (conj B A).2⟩ := by
  rfl

@[simp]
theorem conj_apply_mat (B : Matrix m n α) (A : HermitianMat n α) :
    (A.conj B).mat = B * A.mat * B.conjTranspose := by
  rfl

theorem conj_conj {m l} [Fintype m] (B : Matrix m n α) (C : Matrix l m α) :
    (A.conj B).conj C = A.conj (C * B) := by
  ext1
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

variable (B : HermitianMat n α)

@[simp]
theorem conj_zero [DecidableEq n] : A.conj (0 : Matrix m n α) = 0 := by
  simp [conj_apply]

@[simp]
theorem conj_one [DecidableEq n] : A.conj 1 = A := by
  simp [conj_apply]

@[simp]
lemma conj_one_unitary [DecidableEq n] (U : Matrix.unitaryGroup n α) :
    conj U.val 1 = 1 := by
  ext1
  have h : U * U.val.conjTranspose = 1 := U.prop.2
  simp [h]

variable (R : Type*) [Star R] [TrivialStar R] [CommSemiring R] [Algebra R α] [StarModule R α]

/-- `HermitianMat.conj` as an `R`-linear map, where `R` is the ring of relevant reals. -/
def conjLinear {m} (B : Matrix m n α) : HermitianMat n α →ₗ[R] HermitianMat m α where
  toAddHom := conj B
  map_smul' _ _ := by
    ext1
    simp

@[simp]
theorem conjLinear_apply (B : Matrix m n α) : conjLinear R B A = conj B A  := by
  rfl

end conj

section eigenspace

variable [Fintype n] [DecidableEq n] (A : HermitianMat n 𝕜)

instance [i : Nonempty n] : FaithfulSMul ℝ (HermitianMat n 𝕜) where
  eq_of_smul_eq_smul h := by
    simpa [RCLike.smul_re, -mat_apply] using congr(RCLike.re ($(h 1).val i.some i.some))

/-- The continuous linear map associated with a Hermitian matrix. -/
def lin : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n where
  toLinearMap := A.mat.toEuclideanLin
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

theorem mem_ker_iff_mulVec_zero (x : EuclideanSpace 𝕜 n) : x ∈ A.ker ↔ A.mat.mulVec x = 0 := by
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

theorem ker_pos_smul {c : ℝ} (hc : c ≠ 0) : (c • A).ker = A.ker := by
  ext x
  simp [mem_ker_iff_mulVec_zero, Matrix.smul_mulVec, hc]

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

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq n]

variable (𝕜) in
def diagonal (f : n → ℝ) : HermitianMat n 𝕜 :=
  ⟨Matrix.diagonal (f ·),
    by simp [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]⟩

variable (f g : n → ℝ)

@[simp]
theorem diagonal_mat : (diagonal 𝕜 f).mat = Matrix.diagonal (f · : n → 𝕜) := by
  rfl

@[simp]
theorem diagonal_zero : (diagonal 𝕜 0) = (0 : HermitianMat n 𝕜) := by
  ext1; simp

@[simp]
theorem diagonal_one : (diagonal 𝕜 1) = (1 : HermitianMat n 𝕜) := by
  ext; rw [diagonal_mat]; simp

lemma diagonal_add : diagonal 𝕜 (f + g) = diagonal 𝕜 f + diagonal 𝕜 g := by
  ext1; simp

lemma diagonal_add_apply : diagonal 𝕜 (fun x ↦ f x + g x) = diagonal 𝕜 f + diagonal 𝕜 g := by
  ext1; simp

lemma diagonal_sub : diagonal 𝕜 (f - g) = diagonal 𝕜 f - diagonal 𝕜 g := by
  ext1; simp

theorem diagonal_mul (c : ℝ) : diagonal 𝕜 (fun x ↦ c * f x) = c • diagonal 𝕜 f := by
  ext1; simp [← Matrix.diagonal_smul]

theorem diagonal_conj_diagonal [Fintype n] :
    (diagonal 𝕜 f).conj (diagonal 𝕜 g) = diagonal 𝕜 (fun i ↦ f i * (g i)^2) := by
  ext1
  simp [diagonal, conj]
  intro
  ring

/--
A Hermitian matrix is equal to its diagonalization conjugated by its eigenvector unitary matrix.
-/
lemma eq_conj_diagonal [Fintype n] (A : HermitianMat n 𝕜) :
    A = (diagonal 𝕜 A.H.eigenvalues).conj A.H.eigenvectorUnitary := by
  ext1
  exact Matrix.IsHermitian.spectral_theorem A.2

end diagonal

section kronecker
open Kronecker

variable {p q : Type*}
variable [CommRing α] [StarRing α]

/-- The kronecker product of two HermitianMats, see `Matrix.kroneckerMap`. -/
def kronecker (A : HermitianMat m α) (B : HermitianMat n α) : HermitianMat (m × n) α where
  val := A.mat ⊗ₖ B.mat
  property := Matrix.kroneckerMap_IsHermitian A.H B.H

@[inherit_doc HermitianMat.kronecker]
scoped[HermitianMat] infixl:100 " ⊗ₖ " => HermitianMat.kronecker

@[simp, norm_cast]
theorem kronecker_mat (A : HermitianMat m α) (B : HermitianMat n α) :
    (A ⊗ₖ B).mat = A.mat ⊗ₖ B.mat := by
  rfl

@[simp]
theorem zero_kronecker (A : HermitianMat m α) : (0 : HermitianMat n α) ⊗ₖ A = 0 := by
  ext1; simp

@[simp]
theorem kronecker_zero (A : HermitianMat m α) : A ⊗ₖ (0 : HermitianMat n α) = 0 := by
  ext1; simp

variable [DecidableEq m] [DecidableEq n] in
@[simp]
theorem kronecker_one_one : (1 : HermitianMat m α) ⊗ₖ (1 : HermitianMat n α) = 1 := by
  ext1; simp

variable (A B : HermitianMat m α) (C : HermitianMat n α) in
theorem add_kronecker : (A + B) ⊗ₖ C = A ⊗ₖ C + B ⊗ₖ C := by
  ext1; simp [Matrix.add_kronecker]

variable (A : HermitianMat m α) (B C : HermitianMat n α) in
theorem kronecker_add : A ⊗ₖ (B + C) = A ⊗ₖ B + A ⊗ₖ C := by
  ext1; simp [Matrix.kronecker_add]

lemma kronecker_diagonal [DecidableEq m] [DecidableEq n] (d₁ : m → ℝ) (d₂ : n → ℝ) :
    (diagonal 𝕜 d₁ ⊗ₖ diagonal 𝕜 d₂) = diagonal 𝕜 (fun (i : m × n) => d₁ i.1 * d₂ i.2) := by
  ext1
  simp [Matrix.diagonal_kronecker_diagonal]

/--
A ⊗ₖ 1 always commutes with 1 ⊗ₖ B
-/
theorem kron_id_commute_id_kro [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : HermitianMat m α) (B : HermitianMat n α) :
    Commute (A ⊗ₖ (1 : HermitianMat n α)).mat ((1 : HermitianMat m α) ⊗ₖ B).mat := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [kronecker_mat, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    one_apply, Matrix.one_apply, mat_apply]
  rw [Finset.sum_eq_single (k, j), Finset.sum_eq_single (i, l)] <;> grind

/-
The conjugate of a Kronecker product by a Kronecker product is the Kronecker product of the conjugates.
-/
lemma kronecker_conj [Fintype m] [Fintype n]
    (A : HermitianMat m α) (B : HermitianMat n α) (C : Matrix p m α) (D : Matrix q n α) :
    (A ⊗ₖ B).conj (C ⊗ₖ D) = (A.conj C) ⊗ₖ (B.conj D) := by
  ext1
  exact Matrix.kronecker_conj_eq A.mat B.mat C D

end kronecker

open scoped Pointwise in
theorem spectrum_prod [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {A : HermitianMat m 𝕜} {B : HermitianMat n 𝕜} :
    spectrum ℝ (A ⊗ₖ B).mat = spectrum ℝ A.mat * spectrum ℝ B.mat :=
  Matrix.spectrum_prod A.H B.H

--Shortcut instance
noncomputable instance : AddCommMonoid (HermitianMat d ℂ) :=
  inferInstance
