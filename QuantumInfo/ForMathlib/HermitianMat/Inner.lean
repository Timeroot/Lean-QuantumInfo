import QuantumInfo.ForMathlib.HermitianMat.Order

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
variable {α} [CommRing α] [StarRing α] [TrivialStar α]

/-- `HermitianMat.inner` reduces to `Matrix.trace (A * B)` when the elements are a `TrivialStar`. -/
theorem inner_eq_trace_trivial (A B : HermitianMat n α) : A.inner B = Matrix.trace (A.toMat * B.toMat) := by
  rw [← inner_eq_trace_mul]
  rfl

end trivialstar

section RCLike
open ComplexOrder
variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] (A B C : HermitianMat n 𝕜)

theorem inner_eq_re_trace : A.inner B = RCLike.re (Matrix.trace (A.toMat * B.toMat)) := by
  rfl

theorem inner_eq_trace_rc : A.inner B = Matrix.trace (A.toMat * B.toMat) := by
  change RCLike.ofReal (RCLike.re _) = _
  rw [← RCLike.conj_eq_iff_re]
  convert (Matrix.trace_conjTranspose (A.toMat * B.toMat)).symm using 1
  rw [Matrix.conjTranspose_mul, A.H, B.H, Matrix.trace_mul_comm]

theorem inner_self_nonneg: 0 ≤ A.inner A := by
  simp_rw [inner_eq_re_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum]
  refine Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
  rw [← congrFun₂ A.H, Matrix.conjTranspose_apply]
  refine And.left <| RCLike.nonneg_iff.mp ?_
  open ComplexOrder in
  exact star_mul_self_nonneg (A.toMat j i)

variable {A B C}

theorem inner_mul_nonneg (h : 0 ≤ A.toMat * B.toMat) : 0 ≤ A.inner B := by
  rw [Matrix.PosSemidef.zero_le_iff_posSemidef] at h
  exact (RCLike.nonneg_iff.mp h.trace_nonneg).left

/-- The inner product for PSD matrices is nonnegative. -/
theorem inner_ge_zero (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ A.inner B := by
  rw [zero_le_iff] at hA hB
  open Classical in
  rw [inner_eq_re_trace, ← hA.sqrt_mul_self, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  nth_rewrite 1 [← hA.posSemidef_sqrt.left]
  exact (RCLike.nonneg_iff.mp (hB.conjTranspose_mul_mul_same _).trace_nonneg).left

theorem inner_mono (hA : 0 ≤ A) : B ≤ C → A.inner B ≤ A.inner C := fun hBC ↦ by
  classical have hTr : 0 ≤ A.inner (C - B) := inner_ge_zero hA (zero_le_iff.mpr hBC)
  rw [inner_left_sub] at hTr
  linarith

theorem inner_mono' (hA : 0 ≤ A) : B ≤ C → B.inner A ≤ C.inner A := fun hBC ↦ by
  rw [inner_comm B A, inner_comm C A]
  exact inner_mono hA hBC

/-- The inner product for PSD matrices is at most the product of their traces. -/
theorem inner_le_mul_trace (hA : 0 ≤ A) (hB : 0 ≤ B) : A.inner B ≤ A.trace * B.trace := by
  classical convert inner_mono hA (le_trace_smul_one hB)
  simp [mul_comm]

/-- The inner product of two PSD matrices is zero iff they have disjoint support, i.e., each lives entirely
in the other's kernel. -/
theorem inner_zero_iff [DecidableEq n] (hA₁ : 0 ≤ A) (hB₁ : 0 ≤ B)
    : A.inner B = 0 ↔ A.support ≤ B.ker :=
  sorry

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

instance : ContinuousSMul ℝ (HermitianMat d 𝕜) where
  continuous_smul := by
    rw [continuous_induced_rng]
    exact continuous_smul.comp <| continuous_fst.prodMk (by fun_prop)

#guard_msgs(drop info) in
#synth ContractibleSpace (HermitianMat d ℂ)

@[fun_prop] --fun_prop can actually prove this, should I leave this on or not?
theorem inner_bilinForm_Continuous (A : HermitianMat d 𝕜) : Continuous ⇑(HermitianMat.inner_BilinForm A) :=
  LinearMap.continuous_of_finiteDimensional _

@[fun_prop]
theorem inner_continuous (A : HermitianMat d 𝕜) : Continuous (A.inner) := by
  exact inner_bilinForm_Continuous A

end topology

section innerproductspace

variable {d : Type*} [Fintype d] {𝕜 : Type*} [RCLike 𝕜]

/-- We define the Hermitian inner product as our "canonical" inner product, which does induce a norm.
This disagrees slightly with Mathlib convention on the `Matrix` type, which avoids asserting one norm
as there are several reasonable ones; for Hermitian matrices, though, this seem to be the right choice. -/
noncomputable def InnerProductCore : InnerProductSpace.Core ℝ (HermitianMat d 𝕜) :=
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

/-
It *should* be easier than this to construct the resulting `InnerProductSpace`. But there's a rub!

An InnerProductSpace gives a natural topology, uniformity, and bornology (all of which carry data);
but `HermitianMat` already inherits a topology and uniformity from `Matrix` and `Subtype`. (Thankfully,
not a Bornology, although that could change in the future as Mathlib develops.) This can lead to
issues where many theorems (or other types, like `CompleteSpace`) expect the uniformity structure
to be defeq to the one coming from the `InnerProductSpace`.

This is why constructors like `InnerProductSpace.ofCoreOfTopology` exist, which let you override the
topology when you create it. You need to give a proof that it's propositionally equivalent, which
is what the `topo_compat_1` / `2` / `uniformity_compat` theorems do.

But there's a second issue. There a function for overriding the uniformity, or the bornology, or
"all" of them ... which, oddly, means just the uniformity + bornology. Probably a relic of how it
developed, and topology overrides were added later. This means we can't override the topology
_and_ the uniformity, even though we need both.

Eventually this should be fixed in Mathlib. But for now, it means we have to recreate the `ofCore`
somewhat, adding in the overrides to the construction manually. This is why
`instNormedGroup`, `instNormedSpace`, and `instInnerProductSpace` are so long and messy, and each
repeats some proof from Mathlib.
-/

private theorem topo_compat_1 :
    letI : Inner ℝ (HermitianMat d 𝕜) := InnerProductCore.toInner;
    ContinuousAt (fun v : HermitianMat d 𝕜 ↦ Inner.inner ℝ v v) 0 := by
  sorry

private theorem topo_compat_2 :
    letI : Inner ℝ (HermitianMat d 𝕜) := InnerProductCore.toInner;
    Bornology.IsVonNBounded ℝ {v : HermitianMat d 𝕜 | RCLike.re (Inner.inner ℝ v v) < 1} := by
  sorry

private theorem uniformity_compat (s : Set (HermitianMat d 𝕜 × HermitianMat d 𝕜)) :
  letI : Norm (HermitianMat d 𝕜) :=
    InnerProductSpace.Core.toNorm (c := InnerProductCore.toCore);
  (∃ t ∈ (@UniformSpace.uniformity (Matrix d d 𝕜) _), (fun p => (↑p.1, ↑p.2)) ⁻¹' t ⊆ s) ↔
    s ∈ ⨅ r, ⨅ (_ : 0 < r), Filter.principal {x | ‖x.1 - x.2‖ < r} := by
  sorry

noncomputable instance instNormedGroup : NormedAddCommGroup (HermitianMat d 𝕜) :=
  letI : Norm (HermitianMat d 𝕜) :=
    InnerProductSpace.Core.toNorm (c := InnerProductCore.toCore);
  letI : PseudoMetricSpace (HermitianMat d 𝕜) :=
    ((
      PseudoMetricSpace.ofSeminormedSpaceCore InnerProductCore.toNormedSpaceCore.toCore
    ).replaceTopology
      (InnerProductCore.topology_eq topo_compat_1 topo_compat_2)).replaceUniformity
      (by ext s; exact uniformity_compat s);
  { eq_of_dist_eq_zero := by
      --This proof is from NormedAddCommGroup.ofCore
      intro x y h
      rw [← sub_eq_zero, ← InnerProductCore.toNormedSpaceCore.norm_eq_zero_iff]
      exact h }

noncomputable instance instNormedSpace : NormedSpace ℝ (HermitianMat d 𝕜) where
  norm_smul_le r x := by
    letI : InnerProductSpace.Core ℝ (HermitianMat d 𝕜) := InnerProductCore;
    --This proof is from InnerProductSpace.Core.toNormedSpaceOfTopology
    rw [InnerProductSpace.Core.norm_eq_sqrt_re_inner, InnerProductSpace.Core.inner_smul_left,
      InnerProductSpace.Core.inner_smul_right, ← mul_assoc]
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, Real.sqrt_mul,
      ← InnerProductSpace.Core.ofReal_normSq_eq_inner_self, RCLike.ofReal_re]
    · simp [-Real.norm_eq_abs, InnerProductSpace.Core.sqrt_normSq_eq_norm]
    · positivity

noncomputable instance instInnerProductSpace : InnerProductSpace ℝ (HermitianMat d 𝕜) :=
   letI : Inner ℝ (HermitianMat d 𝕜) := InnerProductCore.toInner;
   letI : NormedSpace ℝ (HermitianMat d 𝕜) := instNormedSpace;
  { InnerProductCore with
    norm_sq_eq_re_inner := fun x => by
      --This proof is from InnerProductSpace.ofCoreOfTopology
      have h₁ : ‖x‖ ^ 2 = √(RCLike.re (InnerProductCore.inner x x)) ^ 2 := rfl
      have h₂ : 0 ≤ RCLike.re (InnerProductCore.inner x x) :=
        (letI : InnerProductSpace.Core ℝ (HermitianMat d 𝕜) := InnerProductCore;
        InnerProductSpace.Core.inner_self_nonneg)
      rwa [h₁, Real.sq_sqrt] }

instance : CompleteSpace (HermitianMat d 𝕜) :=
  inferInstance

--Shortcut instances
noncomputable instance : NormedAddCommGroup (HermitianMat d ℝ) :=
  inferInstance

noncomputable instance : NormedAddCommGroup (HermitianMat d ℂ) :=
  inferInstance

/-- Equivalently: the matrices `X` such that `X - A` is PSD and `B - X` is PSD, form a compact set. -/
instance : CompactIccSpace (HermitianMat d 𝕜) where
  isCompact_Icc := by
    intros
    --One option:
    -- apply IsSeqCompact.isCompact
    -- intro s n
    --Another:
    -- apply Metric.isCompact_of_isClosed_isBounded
    sorry

/-- The PSD matrices that are `≤ 1` are a compact set. More generally, this is true of any closed interval,
but stating that is a bit different because of how numerals are treated. The `0` and `1` here are already
directly matrices, putting in an `(a : ℝ) • 1 ≤ m ∧ m ≤ (b : ℝ) • 1` involves casts. But that theorem should follow
easily from this. More generally `A ≤ m ∧ m ≤ B` is compact.
-/
theorem unitInterval_IsCompact [DecidableEq d] :
    IsCompact {m : HermitianMat d 𝕜 | 0 ≤ m ∧ m ≤ 1} :=
  CompactIccSpace.isCompact_Icc

end innerproductspace
