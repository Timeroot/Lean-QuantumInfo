import QuantumInfo.ForMathlib.HermitianMat.Trace

import Mathlib.Analysis.Convex.Contractible

/-! # Inner product of Hermitian Matrices

For general matrices there are multiple reasonable notions of "inner product" (Hilbert–Schmidt inner product,
Frobenius inner product), and so Mathlib avoids giving a canonical `InnerProductSpace` instance. But for the
particular case of Hermitian matrices, these all coincide, so we can put a canonical `InnerProductSpace`
instance.

This _does_ however induce a `Norm` on `HermitianMat` as well, the Frobenius norm, and this is less obviously
a uniquely correct choice. It is something that one essentially has to live with, with the way that Mathlib
currently structures the instances. (Thankfully, all norms induce the same _topology and bornology_ on
finite-dimensional matrices.)

Some care to be taken so that the topology induced by the InnerProductSpace is defeq with the Subtype
topology that HermitianMat inherits from the topology on Matrix. This can be done via
`InnerProductSpace.ofCoreOfTopology`.

-/

namespace HermitianMat

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

theorem inner_self_nonneg (A : HermitianMat n 𝕜) : 0 ≤ A.inner A := by
  have (i j) := congrFun₂ A.H i j
  simp_rw [Matrix.conjTranspose_apply] at this
  simp_rw [inner_eq_re_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum]
  refine Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
  rw [← this]
  refine And.left <| RCLike.nonneg_iff.mp ?_
  open ComplexOrder in
  exact star_mul_self_nonneg (A.toMat j i)

end RCLike

section topology
/-!
Theorems about `HermitianMat`s that have to do with the topological structure. Pretty much everything here will
assume these are matrices over ℂ, but changes to upgrade this to other types are welcome.
-/
open ComplexOrder

variable {d : Type*} [Fintype d] {𝕜 : Type*} [RCLike 𝕜]

--Using `#guard_msgs(drop info) in #synth` to check that certain instances already exist here

#guard_msgs(drop info) in
#synth ContinuousAdd (HermitianMat d ℂ)

instance ContinuousSMul : ContinuousSMul ℝ (HermitianMat d 𝕜) := by
  sorry

instance OrderedSMul : OrderedSMul ℝ (HermitianMat d 𝕜) := by
  sorry

#guard_msgs(drop info) in
#synth ContractibleSpace (HermitianMat d ℂ)

/-- The PSD matrices that are `≤ 1` are a compact set. More generally, this is true of any closed interval,
but stating that is a bit different because of how numerals are treated. The `0` and `1` here are already
directly matrices, putting in an `(a : ℝ) ≤ m ∧ m ≤ (b : ℝ)` involves casts. But that theorem should follow
easily from this.
-/
theorem unitInterval_IsCompact [DecidableEq d] : IsCompact {m : HermitianMat d 𝕜 | 0 ≤ m ∧ m ≤ 1} := by
  sorry

@[fun_prop] --fun_prop can actually prove this, should I leave this on or not?
theorem inner_bilinForm_Continuous (A : HermitianMat d 𝕜) : Continuous ⇑(HermitianMat.inner_BilinForm A) :=
  LinearMap.continuous_of_finiteDimensional _

@[fun_prop]
theorem inner_continuous (A : HermitianMat d 𝕜) : Continuous (A.inner) := by
  exact inner_bilinForm_Continuous A

instance : CompleteSpace (HermitianMat d 𝕜) :=
  FiniteDimensional.complete ℝ _

#guard_msgs(drop info) in
#synth CompleteSpace (HermitianMat d ℂ)

#guard_msgs(drop info) in
#synth CompleteSpace (HermitianMat d ℝ)

end topology

section innerproductspace

variable {d : Type*} [Fintype d] {𝕜 : Type*} [RCLike 𝕜]

/-- We define the Hermitian inner product as our "canonical" inner product, which does induce a norm.
This disagrees slightly with Mathlib convention on the `Matrix` type, which avoids asserting one norm
as there are several reasonable ones; for Hermitian matrices, though, this seem to be the right choice. -/
noncomputable def InnerProductCore : InnerProductSpace.Core (𝕜 := ℝ) (F := HermitianMat d 𝕜) :=
   {
    inner A B := A.inner B
    conj_inner_symm := fun x y ↦ by
      simpa using inner_comm y x
    re_inner_nonneg := inner_self_nonneg
    add_left := by simp [inner, add_mul]
    smul_left x y r := by simp
    definite x h := by
      replace h : ∑ j, ∑ i, (RCLike.re (x i j) ^ 2 + RCLike.im (x i j) ^ 2) = 0 := by
        convert h
        simp only [inner_eq_re_trace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum,
          RCLike.mul_re, sub_eq_add_neg]
        congr! 2 with i _ j
        simp [← congrFun₂ x.H i j, pow_two]
        rfl
      ext i j
      rw [Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)] at h
      replace h := congrFun h j
      rw [Pi.zero_apply, Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ by positivity)] at h
      replace h := congrFun h i
      rw [Pi.zero_apply] at h
      rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity), sq_eq_zero_iff, sq_eq_zero_iff] at h
      apply RCLike.ext (h.left.trans RCLike.zero_re.symm) (h.right.trans (map_zero _).symm)
  }

private theorem topo_compat_1 :
    let _ : Inner ℝ (HermitianMat d 𝕜) := InnerProductCore.toInner;
    ContinuousAt (fun v : HermitianMat d 𝕜 ↦ Inner.inner ℝ v v) 0 := by
  sorry

private theorem topo_compat_2 :
    let _ : Inner ℝ (HermitianMat d 𝕜) := InnerProductCore.toInner;
    Bornology.IsVonNBounded ℝ {v : HermitianMat d 𝕜 | RCLike.re (Inner.inner ℝ v v) < 1} := by
  sorry

noncomputable instance instNormed : NormedAddCommGroup (HermitianMat d 𝕜) :=
  InnerProductCore.toNormedAddCommGroupOfTopology topo_compat_1 topo_compat_2

noncomputable instance instInnerProductSpace : InnerProductSpace ℝ (HermitianMat d 𝕜) :=
  InnerProductSpace.ofCoreOfTopology InnerProductCore topo_compat_1 topo_compat_2

--Shortcut instances
noncomputable instance : NormedAddCommGroup (HermitianMat d ℝ) :=
  inferInstance

noncomputable instance : NormedAddCommGroup (HermitianMat d ℂ) :=
  inferInstance

end innerproductspace
