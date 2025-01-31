import QuantumInfo.ForMathlib.Matrix

section IsMaximalSelfAdjoint

/- We want to have `HermitianMat.trace` give 𝕜 when 𝕜 is already a TrivialStar field, but give the "clean" type
otherwise -- for instance, ℝ when the input field is ℂ. This typeclass lets us do so. -/
class IsMaximalSelfAdjoint (R : outParam Type*) (α : Type*) [Star α] [Star R] [CommSemiring R]
    [Semiring α] [TrivialStar R] [Algebra R α] where
  selfadjMap : α →+ R
  selfadj_smul : ∀ (r : R) (a : α), selfadjMap (r • a) = r * (selfadjMap a)
  selfadj_algebra : ∀ {a : α}, IsSelfAdjoint a → algebraMap _ _ (selfadjMap a) = a
  /-
  protected algebraMap : R →+* A
  commutes' : ∀ r x, algebraMap r * x = x * algebraMap r
  smul_def' : ∀ r x, r • x = algebraMap r * x
  -/

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
def HermitianMat (n : Type*) (α : Type*) [Star α] := { m : Matrix n n α // m.IsHermitian }

namespace HermitianMat

variable {α : Type*} {n : Type*}

section star
variable [Star α]

@[coe, reducible] def toMat : HermitianMat n α → Matrix n n α :=
  Subtype.val

instance : Coe (HermitianMat n α) (Matrix n n α) := ⟨toMat⟩

@[simp]
theorem val_eq_coe (A : HermitianMat n α) : A.val = A := by
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

end star

section addmonoid
variable [AddMonoid α] [StarAddMonoid α]

instance instAddMonoid : AddMonoid (HermitianMat n α) :=
  let _ : Zero (HermitianMat n α) := ⟨0, Matrix.isHermitian_zero⟩
  let _ : Add (HermitianMat n α) := ⟨fun a b ↦
    ⟨a + b, Matrix.IsHermitian.add a.H b.H⟩⟩
  {
  add_assoc a b c :=
    HermitianMat.ext (add_assoc (G := Matrix n n α) a b c)
  zero_add a :=
    HermitianMat.ext (zero_add (M := Matrix n n α) a)
  add_zero a :=
    HermitianMat.ext (add_zero (M := Matrix n n α) a)
  nsmul := nsmulRec
  }

@[simp]
theorem val_zero : (0 : HermitianMat n α).toMat = 0 :=
  rfl

@[simp]
theorem val_add (A B : HermitianMat n α) : (A + B).toMat = A.toMat + B.toMat :=
  rfl

end addmonoid

section addgroup
variable [AddGroup α] [StarAddMonoid α]
instance instAddGroup : AddGroup (HermitianMat n α) :=
  let _ : Neg (HermitianMat n α) := ⟨fun a ↦ ⟨-a, Matrix.IsHermitian.neg a.H⟩⟩
  {
    neg_add_cancel a :=
      HermitianMat.ext (neg_add_cancel (G := Matrix n n α) a)
    zsmul := zsmulRec
  }

@[simp]
theorem val_neg (B : HermitianMat n α) : (-B).toMat = -B.toMat :=
  rfl

@[simp]
theorem val_sub (A B : HermitianMat n α) : (A - B).toMat = A.toMat - B.toMat := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rfl

end addgroup

section semiring
variable [Semiring α] [StarRing α] [DecidableEq n]

instance instOne : One (HermitianMat n α) :=
  ⟨1, Matrix.isHermitian_one⟩

@[simp]
theorem one_val : (1 : HermitianMat n α) = (1 : Matrix n n α) := by
  rfl

variable [Fintype n]
instance instNPow : NatPow (HermitianMat n α) :=
  ⟨fun x n ↦ ⟨x^n, Matrix.IsHermitian.pow x.H n⟩⟩

@[simp]
theorem npow_val (A : HermitianMat n α) (p : ℕ) : ↑(A^p) = A.toMat^p := by
  rfl

@[simp]
theorem npow_add (A : HermitianMat n α) (p q : ℕ) :
    (A^(p + q)).toMat = (A^p).toMat * (A^q).toMat := by
  rw [npow_val]
  apply pow_add

end semiring
section commring

variable [CommRing α] [StarRing α] [DecidableEq n]  [Fintype n]

noncomputable instance instZPow : Pow (HermitianMat n α) ℤ :=
  ⟨fun x z ↦ ⟨x^z, Matrix.IsHermitian.zpow x.H z⟩⟩

noncomputable instance instInv : Inv (HermitianMat n α) :=
  ⟨fun x ↦ ⟨x⁻¹, Matrix.IsHermitian.inv x.H⟩⟩

end commring

section smul

variable  {R : Type*} [Star R] [Star α] [SMul R α] [StarModule R α] [TrivialStar R]

instance instSmul : SMul R (HermitianMat n α) :=
  ⟨fun c A ↦ ⟨c • A,
  by rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, TrivialStar.star_trivial, A.H]⟩⟩

@[simp]
theorem smul_val (A : HermitianMat n α) (c : R) : ↑(c • A) = c • (A.toMat) := by
  rfl

@[simp]
theorem smul_apply (A : HermitianMat n α) (c : R) (i j : n) : (c • A) i j = c • (A i j) := by
  rfl

end smul

noncomputable section RCLike

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Matrix power of a positive semidefinite matrix, as given by the elementwise
  real power of the diagonal in a diagonalized form.

  Note that this has the usual `Real.rpow` caveats, such as 0 to the power -1 giving 0. -/
def rpow (A : HermitianMat n 𝕜) (p : ℝ) : HermitianMat n 𝕜 :=
  ⟨A.H.eigenvectorUnitary * .diagonal (RCLike.ofReal ∘ (· ^ p) ∘ A.H.eigenvalues) * _,
  Matrix.isHermitian_mul_mul_conjTranspose _ (by simp [Matrix.isHermitian_diagonal_iff, RCLike.isSelfAdjoint_re_iff])⟩

noncomputable instance instRPow : Pow (HermitianMat n 𝕜) ℝ :=
  ⟨rpow⟩

open ComplexOrder in
theorem rpow_PosSemidef {A : HermitianMat n 𝕜} (hA : A.val.PosSemidef) (p : ℝ) : (A.rpow p).val.PosSemidef := by
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
  ⟨A.H.eigenvectorUnitary * .diagonal (RCLike.ofReal ∘ Real.log ∘ A.H.eigenvalues) * _,
  Matrix.isHermitian_mul_mul_conjTranspose _ (by simp [Matrix.isHermitian_diagonal_iff, RCLike.isSelfAdjoint_re_iff])⟩

end RCLike

section trace

variable [Star R] [TrivialStar R] [Fintype n]

section star
variable [Star α] [CommSemiring R] [Semiring α] [Algebra R α] [IsMaximalSelfAdjoint R α]

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
variable [CommSemiring R] [Semiring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]

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

variable [Star α] [CommSemiring R] [Semiring α] [Algebra R α] [IsMaximalSelfAdjoint R α] in
/-- The Hermitian inner product, `Tr[AB]`. This is equal to `Matrix.trace (A * B)`, but gives real
  values when the matrices are complex, using `IsMaximalSelfAdjoint`. -/
def inner (A B : HermitianMat n α) : R :=
  IsMaximalSelfAdjoint.selfadjMap ((A.toMat * B.toMat).trace)

section commsemiring

variable [CommSemiring R] [CommSemiring α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α]
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

@[simp]
theorem inner_zero : A.inner 0 = 0 := by
  simp [inner]

@[simp]
theorem zero_inner : HermitianMat.inner 0 A = 0 := by
  simp [inner]

variable [DecidableEq n] in
@[simp]
theorem inner_one : A.inner 1 = A.trace := by
  simp only [inner, mul_one, one_val, trace]

variable [DecidableEq n] in
@[simp]
theorem one_inner : HermitianMat.inner 1 A = A.trace := by
  simp only [inner, one_mul, one_val, trace]

variable [StarModule R α] in
@[simp]
theorem smul_inner (r : R) : (r • A).inner B = r * A.inner B := by
  simp [inner, IsMaximalSelfAdjoint.selfadj_smul]

variable [StarModule R α] in
@[simp]
theorem inner_smul (r : R) : A.inner (r • B) = r * A.inner B := by
  simp [inner, IsMaximalSelfAdjoint.selfadj_smul]

theorem inner_left_distrib : A.inner (B + C) = A.inner B + A.inner C := by
  simp [inner, left_distrib]

theorem inner_right_distrib : (A + B).inner C = A.inner C + B.inner C := by
  simp [inner, right_distrib]

end commsemiring
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

end ring
