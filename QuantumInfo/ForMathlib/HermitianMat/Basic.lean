import QuantumInfo.ForMathlib.Matrix
import QuantumInfo.ForMathlib.IsMaximalSelfAdjoint
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix

/-- The type of Hermitian matrices, as a `Subtype`. Equivalent to a `Matrix n n α` bundled
with the fact that `Matrix.IsHermitian`. -/
abbrev HermitianMat (n : Type*) (α : Type*) [AddGroup α] [StarAddMonoid α] :=
  (selfAdjoint (Matrix n n α) : Type (max u_1 u_2))

namespace HermitianMat

variable {α : Type*} {n : Type*}

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

end addgroup
section commring

variable [CommRing α] [StarRing α] [DecidableEq n] [Fintype n]

noncomputable instance instInv : Inv (HermitianMat n α) :=
  ⟨fun x ↦ ⟨x⁻¹, Matrix.IsHermitian.inv x.H⟩⟩

noncomputable instance instZPow : Pow (HermitianMat n α) ℤ :=
  ⟨fun x z ↦ ⟨x^z, Matrix.IsHermitian.zpow x.H z⟩⟩

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

/-- The Hermitian matrix given by conjugating by a (possibly rectangular) Matrix. If we required `B` to be
square, this would apply to any `Semigroup`+`StarMul` (as proved by `IsSelfAdjoint.conjugate`). But this lets
us conjugate to other sizes too, as is done in e.g. Kraus operators. That is, it's a _heterogeneous_ conjguation.
-/
def conj {m} (A : HermitianMat n α) (B : Matrix m n α) : HermitianMat m α :=
  ⟨B * A.toMat * B.conjTranspose, by
  ext
  simp only [Matrix.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    star_sum, star_mul', star_star, show ∀ (a b : n), star (A.toMat b a) = A.toMat a b from congrFun₂ A.property]
  rw [Finset.sum_comm]
  congr! 2
  ring⟩

theorem conj_conj {m l} [Fintype m] (A : HermitianMat n α) (B : Matrix m n α) (C : Matrix l m α) :
    (A.conj B).conj C = A.conj (C * B) := by
  ext1
  simp only [conj, mk_toMat, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end conj

section eigenspace

variable [RCLike α] [Fintype n] [DecidableEq n] (A : HermitianMat n α)

--PULLOUT
@[simp]
theorem _root_.Matrix.toEuclideanLin_one : Matrix.toEuclideanLin (1 : Matrix n n α) = .id := by
  ext1 x
  simp [Matrix.toEuclideanLin]

namespace ContinuousLinearMap

variable {R : Type u_1} {S : Type u_2} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type u_3) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type u_4) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module S M₂]

@[simp]
theorem _root_.ContinuousLinearMap.range_zero [RingHomSurjective σ] : LinearMap.range (0 : M →SL[σ] M₂) = ⊥ := by
  convert LinearMap.range_zero
  assumption

@[simp]
theorem _root_.ContinuousLinearMap.ker_zero : LinearMap.ker (0 : M →SL[σ] M₂) = ⊤ :=
  LinearMap.ker_zero

end ContinuousLinearMap

/-- The continuous linear map associated with a Hermitian matrix. -/
def lin : EuclideanSpace α n →L[α] EuclideanSpace α n where
  toLinearMap := A.toMat.toEuclideanLin
  cont := LinearMap.continuous_of_finiteDimensional _

@[simp]
theorem IsSymmetric : A.lin.IsSymmetric :=
  Matrix.isHermitian_iff_isSymmetric.mp A.H

@[simp]
theorem lin_zero : (0 : HermitianMat n α).lin = 0 := by
  simp [lin]; rfl

@[simp]
theorem lin_one : (1 : HermitianMat n α).lin = 1 := by
  simp [lin]; rfl

noncomputable def eigenspace (μ : α) : Submodule α (EuclideanSpace α n) :=
  Module.End.eigenspace A.lin μ

/-- The kernel of a Hermitian matrix `A` as a submodule of Euclidean space, defined by
`LinearMap.ker A.toMat.toEuclideanLin`. Equivalently, the zero-eigenspace. -/
def ker : Submodule α (EuclideanSpace α n) :=
  LinearMap.ker A.lin

/-- The kernel of a Hermitian matrix is its zero eigenspace. -/
theorem ker_eq_eigenspace_zero : A.ker = A.eigenspace 0 := by
  ext
  simp [ker, eigenspace]

@[simp]
theorem ker_zero : (0 : HermitianMat n α).ker = ⊤ := by
  simp [ker]

@[simp]
theorem ker_one : (1 : HermitianMat n α).ker = ⊥ := by
  simp [ker]; rfl

/-- The support of a Hermitian matrix `A` as a submodule of Euclidean space, defined by
`LinearMap.range A.toMat.toEuclideanLin`. Equivalently, the sum of all nonzero eigenspaces. -/
def support : Submodule α (EuclideanSpace α n) :=
  LinearMap.range A.lin

/-- The support of a Hermitian matrix is the sum of its nonzero eigenspaces. -/
theorem support_eq_sup_eigenspace_nonzero : A.support = ⨆ μ ≠ 0, A.eigenspace μ := by
  sorry

@[simp]
theorem support_zero : (0 : HermitianMat n α).support = ⊥ := by
  simp [support]

@[simp]
theorem support_one : (1 : HermitianMat n α).support = ⊤ := by
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
