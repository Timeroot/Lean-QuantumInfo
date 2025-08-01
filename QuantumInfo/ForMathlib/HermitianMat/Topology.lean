import QuantumInfo.ForMathlib.HermitianMat.Basic

import Mathlib.Analysis.Convex.Contractible

/-!
Theorems about `HermitianMat`s that have to do with the topological structure. Pretty much everything here will
assume these are matrices over ℂ, but changes to upgrade this to other types are welcome.
-/

namespace HermitianMat
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

noncomputable instance instNormed : NormedAddCommGroup (HermitianMat d 𝕜) :=
  InnerProductCore.toNormedAddCommGroup

noncomputable instance instInnerProductSpace : InnerProductSpace ℝ (HermitianMat d 𝕜) :=
  InnerProductSpace.ofCore InnerProductCore
