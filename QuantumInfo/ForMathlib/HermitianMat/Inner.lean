import QuantumInfo.ForMathlib.HermitianMat.Order
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Instances.Real.Lemmas

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

variable {R n α : Type*} [Star R] [TrivialStar R] [Fintype n]

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

--TODO cleanup
private theorem inner_zero_iff_aux_lemma [DecidableEq n] (hA₁ : A.val.PosSemidef) (hB₁ : B.val.PosSemidef) :
  RCLike.re (A.val * B.val).trace = 0 ↔
    LinearMap.range (Matrix.toEuclideanLin A.val) ≤
      LinearMap.ker (Matrix.toEuclideanLin B.val) := by
  --Thanks Aristotle
  have h_trace_zero : (RCLike.re ((A.val * B.val).trace)) = 0 ↔ (A.val * B.val) = 0 := by
    -- Since $A$ and $B$ are positive semidefinite, we can write them as $A = C^* C$ and $B = D^* D$ for some matrices $C$ and $D$.
    obtain ⟨C, hC⟩ : ∃ C : Matrix n n 𝕜, A.val = C.conjTranspose * C := by
      exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hA₁
    obtain ⟨D, hD⟩ : ∃ D : Matrix n n 𝕜, B.val = D.conjTranspose * D := by
      exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hB₁
    have h_trace_zero_iff : (RCLike.re ((A.val * B.val).trace)) = 0 ↔ (D * C.conjTranspose) = 0 := by
      -- Since $\operatorname{Tr}((DC)^* DC) = \sum_{i,j} |(DC)_{ij}|^2$, and this sum is zero if and only if each term is zero, we have $\operatorname{Tr}((DC)^* DC) = 0$ if and only if $DC = 0$.
      have h_trace_zero_iff : (RCLike.re ((D * C.conjTranspose).conjTranspose * (D * C.conjTranspose)).trace) = 0 ↔ (D * C.conjTranspose) = 0 := by
        have h_trace_zero_iff : ∀ (M : Matrix n n 𝕜), (RCLike.re (M.conjTranspose * M).trace) = 0 ↔ M = 0 := by
          simp [ Matrix.trace, Matrix.mul_apply ];
          intro M
          simp_all only
          obtain ⟨val, property⟩ := A
          obtain ⟨val_1, property_1⟩ := B
          subst hD hC
          apply Iff.intro
          · intro a
            rw [ Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ )] at a
            ext i j
            specialize a j
            rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ ) ] at a
            simp_all only [Finset.mem_univ, forall_const, Matrix.zero_apply]
            exact RCLike.ext ( by norm_num; nlinarith only [ a i ] ) ( by norm_num; nlinarith only [ a i ] );
          · intro a
            subst a
            simp_all only [Matrix.zero_apply, map_zero, mul_zero, add_zero, Finset.sum_const_zero]
        exact h_trace_zero_iff _;
      convert h_trace_zero_iff using 3 ; simp [ hC, hD, Matrix.mul_assoc ];
      rw [ ← Matrix.trace_mul_comm ] ; simp [ Matrix.mul_assoc ];
    simp_all only
    obtain ⟨val, property⟩ := A
    obtain ⟨val_1, property_1⟩ := B
    subst hD hC
    apply Iff.intro
    · intro a
      simp_all only [iff_true]
      simp ( config := { decide := Bool.true } ) [ ← Matrix.mul_assoc, ← Matrix.conjTranspose_inj, a ];
    · intro a
      simp_all only [Matrix.trace_zero, map_zero, true_iff]
  have h_range_ker : (LinearMap.range (Matrix.toEuclideanLin A.val)) ≤ (LinearMap.ker (Matrix.toEuclideanLin B.val)) → (A.val * B.val) = 0 := by
    intro h_range_ker
    have hAB_zero : ∀ v, (Matrix.toEuclideanLin B.val) ((Matrix.toEuclideanLin A.val) v) = 0 := by
      exact fun v => h_range_ker ( LinearMap.mem_range_self _ v )
    have h_herm : A.val * B.val = (B.val * A.val).conjTranspose := by
      simp [Matrix.conjTranspose_mul]
    have hBA_zero : (B.val * A.val) = 0 := by
      ext i j
      specialize hAB_zero (Pi.single j 1)
      convert congr_fun hAB_zero i using 1
      simp [Matrix.toEuclideanLin, dotProduct, Matrix.mulVec, Matrix.mul_apply, Pi.single_apply]
    rw [h_herm, hBA_zero, Matrix.conjTranspose_zero]
  simp_all only
  obtain ⟨val, property⟩ := A
  obtain ⟨val_1, property_1⟩ := B
  simp_all only
  apply Iff.intro
  · rintro a _ ⟨y, rfl⟩
    have h_comm : val_1 * val = 0 := by
      rw [← Matrix.conjTranspose_inj]
      have h_conj_transpose : val.conjTranspose = val ∧ val_1.conjTranspose = val_1 := by
        aesop
      simp [h_conj_transpose, Matrix.conjTranspose_mul, a]
    simp only [LinearMap.mem_ker]
    convert congr_arg (fun x => Matrix.mulVec x y) h_comm using 1
    · simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
      rfl
    · simp
  · grind

/-- The inner product of two PSD matrices is zero iff they have disjoint support, i.e., each lives entirely
in the other's kernel. -/
theorem inner_zero_iff [DecidableEq n] (hA₁ : 0 ≤ A) (hB₁ : 0 ≤ B)
    : A.inner B = 0 ↔ A.support ≤ B.ker := by
  rw [zero_le_iff] at hA₁ hB₁
  dsimp [support, ker, lin]
  rw [inner_eq_re_trace]
  change selfAdjoint (Matrix n n 𝕜) at A B
  exact inner_zero_iff_aux_lemma hA₁ hB₁

variable {d d₂ : Type*} (A B : HermitianMat d 𝕜) [Fintype d₂] [Fintype d]

@[simp]
theorem reindex_inner (e : d ≃ d₂) (B : HermitianMat d₂ 𝕜) :
    (A.reindex e).inner B = A.inner (B.reindex e.symm) := by
  dsimp [inner]
  congr
  rw (occs := [3,4]) [← e.symm_symm]
  rw [← Matrix.submatrix_id_mul_right]
  rw (occs := [2]) [Matrix.trace_mul_comm]
  rw [Matrix.submatrix_id_mul_right, Matrix.trace_mul_comm, Equiv.symm_symm]

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
theorem inner_continuous : Continuous ((HermitianMat.inner (n := d) (α := 𝕜)).uncurry) := by
  rw [funext₂ inner_eq_re_trace]
  fun_prop

end topology

section innerproductspace

variable {d d₂ : Type*} [Fintype d] [Fintype d₂] {𝕜 : Type*} [RCLike 𝕜]

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

open Matrix.Norms.Frobenius in
/-- The `HermitianMat` type inherits the Frobenius necessarily, since it's going to need the
Hermitian inner product, and in Mathlib an `InnerProductSpace` always carries the corresponding
norm. -/
noncomputable instance instNormedGroup : NormedAddCommGroup (HermitianMat d 𝕜) :=
  AddSubgroupClass.normedAddCommGroup _

theorem norm_eq_frobenius (A : HermitianMat d 𝕜) :
    ‖A‖ = (∑ i : d, ∑ j : d, ‖A i j‖ ^ 2) ^ (1 / 2 : ℝ) := by
  convert ← Matrix.frobenius_norm_def A.toMat
  exact Real.rpow_ofNat _ 2

--PULLOUT
omit [Fintype d] in
@[simp]
theorem toMat_apply {A : HermitianMat d 𝕜} {i j : d} : A.toMat i j = A i j := by
  rfl

theorem norm_eq_sqrt_inner_self (A : HermitianMat d 𝕜) : ‖A‖ = √(A.inner A) := by
  rw [norm_eq_frobenius, ← Real.sqrt_eq_rpow]
  congr
  simp_rw [inner_eq_re_trace, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp only [map_sum]
  congr! with i _ j _
  simp only [RCLike.norm_sq_eq_def, RCLike.mul_re, sub_eq_add_neg,
    neg_mul_eq_mul_neg]
  congr 2 <;> (rw [← A.H]; simp)

noncomputable instance instNormedSpace : NormedSpace ℝ (HermitianMat d 𝕜) where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_inner_self, norm_eq_sqrt_inner_self]
    simp only [inner_smul, smul_inner, ← mul_assoc, Real.norm_eq_abs]
    rw [Real.sqrt_mul' _ (inner_self_nonneg x), Real.sqrt_mul_self_eq_abs]

noncomputable instance instInnerProductSpace : InnerProductSpace ℝ (HermitianMat d 𝕜) :=
   letI : Inner ℝ (HermitianMat d 𝕜) := InnerProductCore.toInner;
   letI : NormedSpace ℝ (HermitianMat d 𝕜) := instNormedSpace;
  { InnerProductCore with
    norm_sq_eq_re_inner := fun x => by
      rw [norm_eq_sqrt_inner_self, Real.sq_sqrt (inner_self_nonneg x), RCLike.re_to_real]
      rfl
  }

theorem inner_eq (A B : HermitianMat d 𝕜) : Inner.inner ℝ A B = A.inner B := by
  rfl

open scoped RealInnerProductSpace

instance : CompleteSpace (HermitianMat d 𝕜) :=
  inferInstance

--Shortcut instances
noncomputable instance : NormedAddCommGroup (HermitianMat d ℝ) :=
  inferInstance

noncomputable instance : NormedAddCommGroup (HermitianMat d ℂ) :=
  inferInstance

--TODO: PULLOUT, PR
open ComplexOrder in
def _root_.RCLike.instOrderClosed : OrderClosedTopology 𝕜 where
  isClosed_le' := by
    conv => enter [1, 1, p]; rw [RCLike.le_iff_re_im]
    simp_rw [Set.setOf_and]
    refine IsClosed.inter (isClosed_le ?_ ?_) (isClosed_eq ?_ ?_) <;> continuity

scoped[ComplexOrder] attribute [instance] RCLike.instOrderClosed

variable (A B : HermitianMat d 𝕜)

--TODO: Eventually deprecated HermitianMat.inner and switch to this primed version everywhere.
/-- The inner product for PSD matrices is nonnegative. -/
theorem inner_ge_zero' (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ ⟪A, B⟫ :=
  inner_ge_zero hA hB

variable {A B} in
theorem dist_le_of_mem_Icc (x : HermitianMat d 𝕜) (hA : A ≤ x) (hB : x ≤ B) :
    ‖x - A‖ ≤ ‖B - A‖ := by
  classical
  conv => enter [2, 1]; equals (B - x) + (x - A) => abel
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_add_pow_two_real, le_add_iff_nonneg_left]
  suffices 0 ≤ ⟪B - x, x - A⟫ by positivity
  apply inner_ge_zero' <;> rwa [sub_nonneg]

omit [Fintype n] in
theorem Matrix.IsHermitian_isClosed : IsClosed { A : Matrix n n 𝕜 | A.IsHermitian } := by
  conv =>
    enter [1, 1, A]
    rw [Matrix.IsHermitian, ← sub_eq_zero]
  convert isClosed_singleton.preimage (f := fun (x : Matrix n n 𝕜) ↦ (x.conjTranspose - x))
    (by fun_prop) using 1

open ComplexOrder

theorem Matrix.PosSemiDef_isClosed : IsClosed { A : Matrix n n 𝕜 | A.PosSemidef } := by
  refine IsHermitian_isClosed.inter ?_
  suffices IsClosed (⋂ x : n → 𝕜, { A : Matrix n n 𝕜 | 0 ≤ star x ⬝ᵥ A.mulVec x }) by
    rwa [← Set.setOf_forall] at this
  exact isClosed_iInter fun _ ↦ (isClosed_Ici (a := 0)).preimage (by fun_prop)

theorem isClosed_nonneg : IsClosed { A : HermitianMat n 𝕜 | 0 ≤ A } := by
  simp_rw [zero_le_iff]
  exact Matrix.PosSemiDef_isClosed.preimage_val

--TODO: The PosDef matrices are open *within* the HermitianMat space (not in the ambient space of matrices.)

instance : OrderClosedTopology (HermitianMat d 𝕜) where
  isClosed_le' := by
    classical
    convert IsClosed.preimage (X := (HermitianMat d 𝕜 × HermitianMat d 𝕜))
      (f := fun xy ↦ (xy.2 - xy.1)) (by fun_prop) isClosed_nonneg
    ext ⟨x, y⟩
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ← sub_nonneg (b := x)]

/-- Equivalently: the matrices `X` such that `X - A` is PSD and `B - X` is PSD, form a compact set. -/
instance : CompactIccSpace (HermitianMat d 𝕜) where
  isCompact_Icc := by
    intros A B
    apply Metric.isCompact_of_isClosed_isBounded isClosed_Icc
    rw [Metric.isBounded_iff]
    use 2 * ‖B - A‖
    rintro x ⟨hxA, hxB⟩ y ⟨hyA, hyB⟩
    grw [dist_triangle_right (z := A), dist_eq_norm, dist_eq_norm]
    grw [dist_le_of_mem_Icc x hxA hxB, dist_le_of_mem_Icc y hyA hyB]
    rw [two_mul]

/-- The PSD matrices that are `≤ 1` are a compact set. More generally, this is true of any closed interval,
but stating that is a bit different because of how numerals are treated. The `0` and `1` here are already
directly matrices, putting in an `(a : ℝ) • 1 ≤ m ∧ m ≤ (b : ℝ) • 1` involves casts. But that theorem should follow
easily from this. More generally `A ≤ m ∧ m ≤ B` is compact.
-/
theorem unitInterval_IsCompact [DecidableEq d] :
    IsCompact {m : HermitianMat d 𝕜 | 0 ≤ m ∧ m ≤ 1} :=
  CompactIccSpace.isCompact_Icc

end innerproductspace
