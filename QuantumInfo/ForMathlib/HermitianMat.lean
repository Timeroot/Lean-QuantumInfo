import QuantumInfo.ForMathlib.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix

section IsMaximalSelfAdjoint

/- We want to have `HermitianMat.trace` give 𝕜 when 𝕜 is already a TrivialStar field, but give the "clean" type
otherwise -- for instance, ℝ when the input field is ℂ. This typeclass lets us do so. -/
class IsMaximalSelfAdjoint (R : outParam Type*) (α : Type*) [Star α] [Star R] [CommSemiring R]
    [Semiring α] [TrivialStar R] [Algebra R α] where
  selfadjMap : α →+ R
  selfadj_smul : ∀ (r : R) (a : α), selfadjMap (r • a) = r * (selfadjMap a)
  selfadj_algebra : ∀ {a : α}, IsSelfAdjoint a → algebraMap _ _ (selfadjMap a) = a

/-- Every `TrivialStar` `CommSemiring` is its own maximal self adjoints. -/
instance instTrivialStar_IsMaximalSelfAdjoint [Star R] [TrivialStar R] [CommSemiring R] : IsMaximalSelfAdjoint R R where
  selfadjMap := AddMonoidHom.id R
  selfadj_smul _ __ := rfl
  selfadj_algebra {_} _ := rfl

/-- ℝ is the maximal self adjoint elements over RCLike -/
instance instRCLike_IsMaximalSelfAdjoint [RCLike α] : IsMaximalSelfAdjoint ℝ α where
  selfadjMap := RCLike.re
  selfadj_smul := RCLike.smul_re
  selfadj_algebra := RCLike.conj_eq_iff_re.mp

end IsMaximalSelfAdjoint
---------

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

@[ext] protected theorem ext {A B : HermitianMat n α} : A.val = B.val → A = B :=
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

-- This belongs in Mathlib
section rclike
variable {α : Type*} [RCLike α]
instance : StarModule ℝ α where
  star_smul r a := by simp [RCLike.real_smul_eq_coe_mul]

end rclike
-- /mathlib

section conj

variable [CommRing α] [StarRing α] [DecidableEq n] [Fintype n]

/-- The Hermitian matrix given by conjugating by a (possibly rectangular) Matrix. If we required `B` to be
square, this would apply to any `Semigroup`+`StarMul` (as proved by `IsSelfAdjoint.conjugate`). But this lets
us conjugate to other sizes too, as is done in e.g. Kraus operators. That is, it's a _heterogeneous_ conjguation.
-/
def conj (A : HermitianMat n α) (B : Matrix m n α) : HermitianMat m α :=
  ⟨B * A.toMat * B.conjTranspose, by
  ext
  simp only [Matrix.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    star_sum, star_mul', star_star, show ∀ (a b : n), star (A.toMat b a) = A.toMat a b from congrFun₂ A.property]
  rw [Finset.sum_comm]
  congr! 2
  ring⟩

end conj

section trace

variable [Star R] [TrivialStar R] [Fintype n]

section star
variable [AddGroup α] [StarAddMonoid α] [CommSemiring R] [Semiring α] [Algebra R α] [IsMaximalSelfAdjoint R α]

/-- The trace of the matrix. This requires a `IsMaximalSelfAdjoint R α` instance, and then maps from
  `HermitianMat n α` to `R`. This means that the trace of (say) a `HermitianMat n ℤ` gives values in ℤ,
  but that the trace of a `HermitianMat n ℂ` gives values in ℝ. The fact that traces are "automatically"
  real reduces coercions down the line. -/
def trace (A : HermitianMat n α) : R :=
  IsMaximalSelfAdjoint.selfadjMap (A.toMat.trace)

/-- `HermitianMat.trace` reduces to `Matrix.trace` in the algebra.-/
theorem trace_eq_trace (A : HermitianMat n α) : algebraMap R α A.trace = Matrix.trace A.toMat := by
  rw [HermitianMat.trace, Matrix.trace, map_sum, map_sum]
  congr! 1
  exact IsMaximalSelfAdjoint.selfadj_algebra (Matrix.IsHermitian.apply A.H _ _)

variable [StarModule R α] in
@[simp]
theorem trace_smul (A : HermitianMat n α) (r : R) : (r • A).trace = r * A.trace := by
  simp [trace, Finset.mul_sum, IsMaximalSelfAdjoint.selfadj_smul]

end star
section semiring
variable [CommSemiring R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]

@[simp]
theorem trace_zero : (0 : HermitianMat n α).trace = 0 := by
  simp [trace]

@[simp]
theorem trace_add (A B : HermitianMat n α) : (A + B).trace = A.trace + B.trace := by
  simp [trace]

end semiring
section ring

variable [CommRing R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]
@[simp]
theorem trace_neg (A : HermitianMat n α) : (-A).trace = -A.trace := by
  simp [trace]

@[simp]
theorem trace_sub (A B : HermitianMat n α) : (A - B).trace = A.trace - B.trace := by
  simp [trace]

end ring
end trace

section trivialstar

variable [Star α] [TrivialStar α] [CommSemiring α] [Fintype n]

/-- `HermitianMat.trace` reduces to `Matrix.trace` when the elements are a `TrivialStar`. -/
@[simp]
theorem trace_eq_trace_trivial (A : HermitianMat n ℝ) : A.trace = Matrix.trace A.toMat := by
  rw [← trace_eq_trace]
  rfl

end trivialstar

section RCLike

variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]

theorem trace_eq_re_trace (A : HermitianMat n 𝕜) : A.trace = RCLike.re (Matrix.trace A.toMat) := by
  rfl

/-- `HermitianMat.trace` reduces to `Matrix.trace` when the elements are `RCLike`. -/
@[simp]
theorem trace_eq_trace_rc (A : HermitianMat n 𝕜) : A.trace = Matrix.trace A.toMat := by
  rw [trace, Matrix.trace, map_sum, RCLike.ofReal_sum]
  congr 1
  exact Matrix.IsHermitian.coe_re_diag A.H

end RCLike

section inner

variable [Star R] [TrivialStar R] [Fintype n]

variable [Ring α] [StarAddMonoid α] [CommSemiring R] [Algebra R α] [IsMaximalSelfAdjoint R α] in
/-- The Hermitian inner product, `Tr[AB]`. This is equal to `Matrix.trace (A * B)`, but gives real
  values when the matrices are complex, using `IsMaximalSelfAdjoint`. -/
def inner (A B : HermitianMat n α) : R :=
  IsMaximalSelfAdjoint.selfadjMap ((A.toMat * B.toMat).trace)

section ring

variable [CommRing R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]
variable (A B : HermitianMat n α)

@[simp]
theorem inner_left_neg : (-A).inner B = -A.inner B := by
  simp [inner]

@[simp]
theorem inner_right_neg : A.inner (-B) = -A.inner B := by
  simp [inner]

theorem inner_left_sub : A.inner (B - C) = A.inner B - A.inner C := by
  simp [inner, mul_sub]

theorem inner_right_sub : (A - B).inner C = A.inner C - B.inner C := by
  simp [inner, sub_mul]

@[simp]
theorem inner_zero : A.inner 0 = 0 := by
  simp [inner]

@[simp]
theorem zero_inner : HermitianMat.inner 0 A = 0 := by
  simp [inner]

theorem inner_left_distrib : A.inner (B + C) = A.inner B + A.inner C := by
  simp [inner, left_distrib]

theorem inner_right_distrib : (A + B).inner C = A.inner C + B.inner C := by
  simp [inner, right_distrib]

variable [StarModule R α]

@[simp]
theorem smul_inner (r : R) : (r • A).inner B = r * A.inner B := by
  simp [inner, IsMaximalSelfAdjoint.selfadj_smul]

@[simp]
theorem inner_smul (r : R) : A.inner (r • B) = r * A.inner B := by
  simp [inner, IsMaximalSelfAdjoint.selfadj_smul]

end ring
section starring

variable [CommRing R] [Ring α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α] [DecidableEq n]
variable (A B : HermitianMat n α)

@[simp]
theorem inner_one : A.inner 1 = A.trace := by
  simp only [inner, selfAdjoint.val_one,  mul_one, trace]

@[simp]
theorem one_inner : HermitianMat.inner 1 A = A.trace := by
  simp only [inner, one_mul, selfAdjoint.val_one, trace]

end starring
section commring

variable [CommSemiring R] [CommRing α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α]
variable (A B : HermitianMat n α)

/-- The inner product for Hermtian matrices is equal to the trace of the product. -/
theorem inner_eq_trace_mul : algebraMap R α (A.inner B) = (A.toMat * B.toMat).trace := by
  apply IsMaximalSelfAdjoint.selfadj_algebra
  rw [IsSelfAdjoint, Matrix.trace]
  simp_rw [star_sum, Matrix.diag_apply, Matrix.mul_apply, star_sum, star_mul, mul_comm]
  rw [Finset.sum_comm]
  congr! <;> apply congrFun₂ (H _)

theorem inner_comm : A.inner B = B.inner A := by
  rw [inner, inner, Matrix.trace_mul_comm]

end commring

section trivialstar
variable [CommRing α] [StarRing α] [TrivialStar α]

/-- `HermitianMat.inner` reduces to `Matrix.trace (A * B)` when the elements are a `TrivialStar`. -/
theorem inner_eq_trace_trivial (A B : HermitianMat n α) : A.inner B = Matrix.trace (A.toMat * B.toMat) := by
  rw [← inner_eq_trace_mul]
  rfl

end trivialstar

section RCLike
variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]

theorem inner_eq_re_trace (A B : HermitianMat n 𝕜) : A.inner B = RCLike.re (Matrix.trace (A.toMat * B.toMat)) := by
  rfl

theorem inner_eq_trace_rc (A B : HermitianMat n 𝕜) : A.inner B = Matrix.trace (A.toMat * B.toMat) := by
  change RCLike.ofReal (RCLike.re _) = _
  rw [← RCLike.conj_eq_iff_re]
  convert (Matrix.trace_conjTranspose (A.toMat * B.toMat)).symm using 1
  rw [Matrix.conjTranspose_mul, A.H, B.H, Matrix.trace_mul_comm]

end RCLike

section possemidef
open ComplexOrder

variable [RCLike α]
variable {A B C : HermitianMat n α} {M N : Matrix n n α}

theorem le_iff : A ≤ B ↔ (B - A).toMat.PosSemidef := by
  rfl

theorem zero_le_iff : 0 ≤ A ↔ A.toMat.PosSemidef := by
  rw [← propext_iff]
  apply congrArg Matrix.PosSemidef (sub_zero _)

variable [DecidableEq n]

theorem le_trace_smul_one (hA : 0 ≤ A) : A ≤ (A.trace : ℝ) • 1 := by
  --mostly a copy of Matrix.PosSemidef.le_trace_smul_one from ForMathlib.Matrix.lean
  sorry
  -- have h : ∀ i, hA.1.eigenvalues i ≤ hA.1.rtrace := fun i ↦ by
  --   rw [←IsHermitian.sum_eigenvalues_eq_rtrace hA.1]
  --   convert @Finset.sum_le_sum_of_subset_of_nonneg n ℝ _ hA.1.eigenvalues {i} Finset.univ _ _
  --   · rw [Finset.sum_singleton]
  --   · exact Finset.subset_univ {i}
  --   · exact fun j _ _ ↦ eigenvalues_nonneg hA j
  -- exact (le_smul_one_of_eigenvalues_iff hA hA.1.rtrace).mp h

/-- The inner product for PSD matrices is nonnegative. -/
theorem inner_ge_zero (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ A.inner B := by
  rw [zero_le_iff] at hA hB
  open Classical in
  rw [inner_eq_re_trace, ← hA.sqrt_mul_self, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  nth_rewrite 1 [← hA.posSemidef_sqrt.left]
  exact (RCLike.nonneg_iff.mp (hB.conjTranspose_mul_mul_same _).trace_nonneg).left

theorem inner_mono (hA : 0 ≤ A) (B C) : B ≤ C → A.inner B ≤ A.inner C := fun hBC ↦ by
  have hTr : 0 ≤ A.inner (C - B) := inner_ge_zero hA (zero_le_iff.mpr hBC)
  rw [inner_left_sub] at hTr
  linarith

/-- The inner product for PSD matrices is at most the product of their traces. -/
theorem inner_le_mul_trace (hA : 0 ≤ A) (hB : 0 ≤ B) : A.inner B ≤ A.trace * B.trace := by
  convert inner_mono hA _ _ (le_trace_smul_one hB)
  simp [mul_comm]

--There's a lot of facts about PosSemidef matrices that are convenient to come bundled with the HermitiatMat
--type too.
omit [DecidableEq n] in
theorem convex_cone (hA : 0 ≤ A) (hB : 0 ≤ B) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    : 0 ≤ (c₁ • A + c₂ • B) := by
  rw [zero_le_iff] at hA hB ⊢
  convert (hA.smul (RCLike.ofReal_nonneg.mpr hc₁)).add (hB.smul (RCLike.ofReal_nonneg.mpr hc₂))
  simp

omit [DecidableEq n] in
theorem conj_le (hA : 0 ≤ A) [Fintype m] (M : Matrix m n α) : 0 ≤ A.conj M := by
  rw [zero_le_iff] at hA ⊢
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hA M

end possemidef

--Matrix operations on RCLike matrices with the CFC
noncomputable section CFC

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Matrix power of a positive semidefinite matrix, as given by the elementwise
  real power of the diagonal in a diagonalized form.

  Note that this has the usual `Real.rpow` caveats, such as 0 to the power -1 giving 0. -/
def rpow (A : HermitianMat n 𝕜) (p : ℝ) : HermitianMat n 𝕜 :=
  ⟨cfc (Real.rpow · p) A.toMat, cfc_predicate _ _⟩

noncomputable instance instRPow : Pow (HermitianMat n 𝕜) ℝ :=
  ⟨rpow⟩

open ComplexOrder in
theorem rpow_PosSemidef {A : HermitianMat n 𝕜} (hA : A.val.PosSemidef) (p : ℝ) : (A ^ p).val.PosSemidef := by
  --TODO: Should prove the more general versions for f mapping ℝ≥0 → ℝ≥0 (if hA is PSD) or ℝ → ℝ≥0.
  change (cfc _ A.toMat).PosSemidef
  rw [A.H.cfc_eq, Matrix.IsHermitian.cfc]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  refine Matrix.posSemidef_diagonal_iff.mpr fun i ↦ ?_
  rw [Function.comp_apply, RCLike.nonneg_iff]
  constructor
  · simp only [RCLike.ofReal_re]
    exact Real.rpow_nonneg (hA.eigenvalues_nonneg i) p
  · simp only [RCLike.ofReal_im]

/-- Matrix logarithm (base e) of a Hermitian matrix, as given by the elementwise
  real logarithm of the diagonal in a diagonalized form, using `Real.log`

  Note that this means that the nullspace of the image includes all of the nullspace of the
  original matrix. This contrasts to the standard definition, which is only defined for positive
  *definite* matrices, and the nullspace of the image is exactly the (λ=1)-eigenspace of the
  original matrix. It coincides with the standard definition if A is positive definite. -/
def log (A : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  let _ : NormedRing (Matrix n n 𝕜) := Matrix.frobeniusNormedRing
  let _ : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.frobeniusNormedAlgebra
  ⟨CFC.log A.toMat, IsSelfAdjoint.log⟩

end CFC
