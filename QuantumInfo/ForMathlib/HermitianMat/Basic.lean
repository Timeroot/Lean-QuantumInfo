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

section diagonal

--TODO: Generalize this more types than ℝ/ℂ
def diagonal [DecidableEq n] (f : n → ℝ) : HermitianMat n ℂ :=
  ⟨Matrix.diagonal (f ·), by simp [selfAdjoint.mem_iff, Matrix.star_diagonal]⟩

theorem diagonal_conj_diagonal [Fintype n] [DecidableEq n] (f g : n → ℝ) :
    (diagonal f).conj (diagonal g) =
    diagonal (fun i ↦ f i * (g i)^2) := by
  simp [diagonal, conj]
  intro
  ring

end diagonal

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

--strictly speaking this works over any division ring, not just ℝ + RCLike
instance FiniteDimensional : FiniteDimensional ℝ (HermitianMat n 𝕜) :=
  FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Matrix n n 𝕜))

theorem trace_eq_re_trace (A : HermitianMat n 𝕜) : A.trace = RCLike.re (Matrix.trace A.toMat) := by
  rfl

theorem trace_eq_rtrace (A : HermitianMat n 𝕜) : A.trace = A.H.rtrace := by
  rfl

/-- `HermitianMat.trace` reduces to `Matrix.trace` when the elements are `RCLike`. -/
@[simp]
theorem trace_eq_trace_rc (A : HermitianMat n 𝕜) : ↑A.trace = Matrix.trace A.toMat := by
  rw [trace, Matrix.trace, map_sum, RCLike.ofReal_sum]
  congr 1
  exact Matrix.IsHermitian.coe_re_diag A.H

theorem trace_diagonal {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℝ) :
    (diagonal f).trace = ∑ i, f i := by
  rw [trace_eq_re_trace]
  simp [HermitianMat.diagonal, Matrix.trace]

theorem sum_eigenvalues_eq_trace [DecidableEq n] (A : HermitianMat n 𝕜) :
    ∑ i, A.H.eigenvalues i = A.trace := by
  convert congrArg RCLike.re A.H.sum_eigenvalues_eq_trace
  rw [RCLike.ofReal_re]

--Proving that traces are 0 or 1 is common enough that we have a convenience lemma here for turning
--statements about HermitianMat traces into Matrix traces.
theorem trace_eq_zero_iff (A : HermitianMat n 𝕜) : A.trace = 0 ↔ A.toMat.trace = 0 := by
  rw [← trace_eq_trace_rc]
  use mod_cast id, mod_cast id

theorem trace_eq_one_iff (A : HermitianMat n 𝕜) : A.trace = 1 ↔ A.toMat.trace = 1 := by
  rw [← trace_eq_trace_rc]
  use mod_cast id, mod_cast id

end RCLike

section inner

variable [Star R] [TrivialStar R] [Fintype n]

variable [Ring α] [StarAddMonoid α] [CommSemiring R] [Algebra R α] [IsMaximalSelfAdjoint R α] in
/-- The Hermitian inner product, `Tr[AB]`. This is equal to `Matrix.trace (A * B)`, but gives real
  values when the matrices are complex, using `IsMaximalSelfAdjoint`. -/
def inner (A B : HermitianMat n α) : R :=
  IsMaximalSelfAdjoint.selfadjMap ((A.toMat * B.toMat).trace)

section semiring

variable [CommSemiring R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]
variable (A B C : HermitianMat n α)

theorem inner_left_distrib : A.inner (B + C) = A.inner B + A.inner C := by
  simp [inner, left_distrib]

theorem inner_right_distrib : (A + B).inner C = A.inner C + B.inner C := by
  simp [inner, right_distrib]

@[simp]
theorem inner_zero : A.inner 0 = 0 := by
  simp [inner]

@[simp]
theorem zero_inner : HermitianMat.inner 0 A = 0 := by
  simp [inner]

end semiring

section ring

variable [CommRing R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]
variable (A B C : HermitianMat n α)

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

variable [StarModule R α]

@[simp]
theorem smul_inner (r : R) : (r • A).inner B = r * A.inner B := by
  simp [inner, IsMaximalSelfAdjoint.selfadj_smul]

@[simp]
theorem inner_smul (r : R) : A.inner (r • B) = r * A.inner B := by
  simp [inner, IsMaximalSelfAdjoint.selfadj_smul]

/-- The Hermitian inner product as bilinear form. -/
def inner_BilinForm : LinearMap.BilinForm R (HermitianMat n α) := {
      toFun A := {
        toFun := A.inner
        map_add' := A.inner_left_distrib
        map_smul' r B := inner_smul A B r
      }
      map_add' := by intros; ext1; apply inner_right_distrib
      map_smul' := by intros; ext1; apply smul_inner
    }

@[simp]
theorem inner_BilinForm_coe_apply : ⇑(inner_BilinForm A) = A.inner :=
  rfl

@[simp]
theorem inner_BilinForm_apply : inner_BilinForm A B = A.inner B :=
  rfl

end ring
section starring

variable [CommSemiring R] [Ring α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α] [DecidableEq n]
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

theorem inner_mul_nonneg (h : 0 ≤ A.toMat * B.toMat) : 0 ≤ A.inner B := by
  rw [Matrix.PosSemidef.zero_le_iff_posSemidef] at h
  classical exact (RCLike.nonneg_iff.mp h.trace_nonneg).left


instance [DecidableEq n] : ZeroLEOneClass (HermitianMat n ℂ) where
  zero_le_one := by
    rw [HermitianMat.zero_le_iff]
    exact Matrix.PosSemidef.one

/-- The inner product for PSD matrices is nonnegative. -/
theorem inner_ge_zero (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ A.inner B := by
  rw [zero_le_iff] at hA hB
  open Classical in
  rw [inner_eq_re_trace, ← hA.sqrt_mul_self, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  nth_rewrite 1 [← hA.posSemidef_sqrt.left]
  exact (RCLike.nonneg_iff.mp (hB.conjTranspose_mul_mul_same _).trace_nonneg).left

theorem le_trace_smul_one [DecidableEq n] (hA : 0 ≤ A) : A ≤ (A.trace : ℝ) • 1 := by
  --mostly a copy of Matrix.PosSemidef.le_trace_smul_one from ForMathlib.Matrix.lean
  sorry
  -- have h : ∀ i, hA.1.eigenvalues i ≤ hA.1.rtrace := fun i ↦ by
  --   rw [←IsHermitian.sum_eigenvalues_eq_rtrace hA.1]
  --   convert @Finset.sum_le_sum_of_subset_of_nonneg n ℝ _ hA.1.eigenvalues {i} Finset.univ _ _
  --   · rw [Finset.sum_singleton]
  --   · exact Finset.subset_univ {i}
  --   · exact fun j _ _ ↦ eigenvalues_nonneg hA j
  -- exact (le_smul_one_of_eigenvalues_iff hA hA.1.rtrace).mp h

theorem inner_mono (hA : 0 ≤ A) (B C) : B ≤ C → A.inner B ≤ A.inner C := fun hBC ↦ by
  classical have hTr : 0 ≤ A.inner (C - B) := inner_ge_zero hA (zero_le_iff.mpr hBC)
  rw [inner_left_sub] at hTr
  linarith

theorem conj_le (hA : 0 ≤ A) [Fintype m] (M : Matrix m n α) : 0 ≤ A.conj M := by
  rw [zero_le_iff] at hA ⊢
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hA M

/-- The inner product for PSD matrices is at most the product of their traces. -/
theorem inner_le_mul_trace (hA : 0 ≤ A) (hB : 0 ≤ B) : A.inner B ≤ A.trace * B.trace := by
  classical convert inner_mono hA _ _ (le_trace_smul_one hB)
  simp [mul_comm]

/-- The inner product of two PSD matrices is zero iff they have disjoint support, i.e., each lives entirely
in the other's kernel. -/
theorem inner_zero_iff [DecidableEq n] (hA₁ : 0 ≤ A) (hB₁ : 0 ≤ B)
  : A.inner B = 0 ↔
    (LinearMap.range A.toMat.toLin' ≤ LinearMap.ker B.toMat.toLin') ∧
    (LinearMap.range B.toMat.toLin' ≤ LinearMap.ker A.toMat.toLin') :=
  sorry
--There's a lot of facts about PosSemidef matrices that are convenient to come bundled with the HermitiatMat
--type too.
theorem convex_cone (hA : 0 ≤ A) (hB : 0 ≤ B) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    : 0 ≤ (c₁ • A + c₂ • B) := by
  rw [zero_le_iff] at hA hB ⊢
  convert (hA.smul (RCLike.ofReal_nonneg.mpr hc₁)).add (hB.smul (RCLike.ofReal_nonneg.mpr hc₂))
  simp

theorem sq_nonneg [DecidableEq n] : 0 ≤ A^2 := by
  simp [zero_le_iff, pow_two]
  nth_rewrite 1 [←Matrix.IsHermitian.eq A.H]
  exact Matrix.posSemidef_conjTranspose_mul_self A.toMat

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

theorem pow_eq_rpow (A : HermitianMat n 𝕜) (p : ℝ) : A ^ p = A.rpow p :=
  rfl

theorem diagonal_pow (f : n → ℝ) (p : ℝ) :
    (diagonal f) ^ p = diagonal fun i => (f i) ^ p := by
  simp [HermitianMat.ext_iff, pow_eq_rpow, diagonal, rpow]
  --Missing simp theorem: `cfc f (Matrix.diagonal g) = Matrix.diagonal (f ∘ g)`
  sorry

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
