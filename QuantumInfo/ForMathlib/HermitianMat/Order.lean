/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Trace

namespace HermitianMat

open ComplexOrder
open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι]
variable {A B C : HermitianMat n 𝕜}
variable {M : Matrix m n 𝕜} {N : Matrix n n 𝕜}

open MatrixOrder in
/-- The `MatrixOrder` instance for Matrix (the Loewner order) we keep open for
HermitianMat, always. -/
instance : PartialOrder (HermitianMat n 𝕜) :=
  inferInstanceAs (PartialOrder (selfAdjoint _))

open MatrixOrder in
instance : IsOrderedAddMonoid (HermitianMat n 𝕜) :=
  inferInstanceAs (IsOrderedAddMonoid (selfAdjoint _))

theorem le_iff : A ≤ B ↔ (B - A).mat.PosSemidef := by
  rfl

theorem zero_le_iff : 0 ≤ A ↔ A.mat.PosSemidef := by
  rw [le_iff, sub_zero]

theorem le_iff_mulVec_le : A ≤ B ↔
    ∀ x, star x ⬝ᵥ A.mat *ᵥ x ≤ star x ⬝ᵥ B.mat *ᵥ x := by
  simp [le_iff, Matrix.PosSemidef, B.H.sub A.H, Matrix.sub_mulVec]

instance [DecidableEq n] : ZeroLEOneClass (HermitianMat n 𝕜) where
  zero_le_one := by
    rw [zero_le_iff]
    exact Matrix.PosSemidef.one

theorem lt_iff_posdef : A < B ↔ (B - A).mat.PosSemidef ∧ A ≠ B :=
  lt_iff_le_and_ne

instance : IsStrictOrderedModule ℝ (HermitianMat n 𝕜) where
  smul_lt_smul_of_pos_left a ha b b₂ hb := by
    rw [HermitianMat.lt_iff_posdef] at hb ⊢
    simp only [← smul_sub, ne_eq, smul_right_inj ha.ne']
    exact ⟨hb.left.smul ha.le, hb.right⟩
  smul_lt_smul_of_pos_right a ha b b2 hb := by
    rw [HermitianMat.lt_iff_posdef] at ha ⊢
    rw [sub_zero] at ha
    rw [← sub_pos] at hb
    convert And.intro (ha.left.smul hb.le) ha.right using 1
    · simp [← sub_smul]
    simp only [ne_eq, not_iff_not]
    constructor
    · intro h
      rw [eq_comm, ← sub_eq_zero, ← sub_smul] at h
      simpa [eq_comm, hb.ne'] using h
    · rintro rfl; simp

theorem posSemidef_iff_spectrum_Ici [DecidableEq n] (A : HermitianMat n 𝕜) :
    0 ≤ A ↔ spectrum ℝ A.mat ⊆ Set.Ici 0 := by
  rw [zero_le_iff, Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
  simp [A.H, Set.Ici.eq_1]

theorem posSemidef_iff_spectrum_nonneg [DecidableEq n] (A : HermitianMat n 𝕜) :
    0 ≤ A ↔ ∀ x ∈ spectrum ℝ A.mat, 0 ≤ x := by
  exact A.posSemidef_iff_spectrum_Ici

theorem trace_nonneg (hA : 0 ≤ A) : 0 ≤ A.trace := by
  --TODO Cleanup
  -- Since A is positive semidefinite, each term in the sum is non-negative. Therefore, the sum itself is non-negative.
  have h_diag_nonneg : ∀ i, 0 ≤ (A.mat i i) := by
    -- Since A is positive semidefinite, for any vector v, v* A v ≥ 0. Taking v to be the standard basis vector e_i, we get e_i* A e_i = A i i ≥ 0.
    have h_diag_nonneg : ∀ i, 0 ≤ (A.mat i i) := by
      intro i
      have h_inner : ∀ v : n → 𝕜, 0 ≤ (star v) ⬝ᵥ (A.mat.mulVec v) := by
        -- Since A is positive semidefinite, by definition, for any vector v, v* A v is non-negative.
        have h_pos_semidef : ∀ v : n → 𝕜, 0 ≤ (star v) ⬝ᵥ (A.mat.mulVec v) := by
          intro v
          exact (by
          convert hA.2 v using 1;
          simp +decide [ Matrix.mulVec, dotProduct ]);
        exact h_pos_semidef
      classical
      convert h_inner ( Pi.single i 1 ) using 1
      simp [ dotProduct, Pi.single_apply ];
    exact h_diag_nonneg;
  simp +zetaDelta at *;
  convert Finset.sum_nonneg (s := .univ) fun i _ => h_diag_nonneg i;
  have h_trace_eq_sum : A.trace = ∑ i, A i i := by
    simp [Matrix.trace]
  rw [← h_trace_eq_sum, RCLike.ofReal_nonneg]

theorem trace_pos (hA : 0 < A) : 0 < A.trace := by
  open ComplexOrder in
  have hA' := hA.le
  rw [HermitianMat.zero_le_iff] at hA'
  have h_pos := Matrix.PosSemidef.trace_pos hA' (by simpa [HermitianMat.ext_iff] using hA.ne')
  rw [HermitianMat.trace_eq_re_trace]
  rw [RCLike.pos_iff] at h_pos
  exact h_pos.left

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.trace`: nonneg when the matrix is nonneg,
positive when the matrix is positive. -/
@[positivity HermitianMat.trace _]
def evalHermitianMatTrace : PositivityExt where eval {_u _α} _zα _pα e := do
  let .app _tr (A : Expr) ← whnfR e | throwError "not HermitianMat.trace"
  let (isStrict, pfA) ← bestResult A
  if isStrict then
    pure (.positive (← mkAppM ``HermitianMat.trace_pos #[pfA]))
  else
    pure (.nonnegative (← mkAppM ``HermitianMat.trace_nonneg #[pfA]))

--Without these shortcut instances, `gcongr` fails to close certain goals...? Why? TODO
instance : PosSMulMono ℝ (HermitianMat n 𝕜) := inferInstance
instance : SMulPosMono ℝ (HermitianMat n 𝕜) := inferInstance

--Without explicitly giving this instance, Lean times out trying to find it sometimes.
instance : PosSMulReflectLE ℝ (HermitianMat n 𝕜) :=
  PosSMulMono.toPosSMulReflectLE

theorem le_trace_smul_one [DecidableEq n] (hA : 0 ≤ A) : A ≤ A.trace • 1 := by
  have hA' : A.mat.PosSemidef := zero_le_iff.mp hA
  refine (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hA'.1 A.trace).mp ?_
  rw [← A.sum_eigenvalues_eq_trace]
  intro i
  exact Finset.single_le_sum (fun j _ ↦ hA'.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- The Kronecker product of two nonnegative Hermitian matrices is nonnegative. -/
theorem kronecker_nonneg {A : HermitianMat m 𝕜} (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ A ⊗ₖ B := by
  rw [zero_le_iff, kronecker_mat]
  classical exact (zero_le_iff.mp hA).PosSemidef_kronecker (zero_le_iff.mp hB)

/-- The Kronecker product of two positive Hermitian matrices is positive. -/
theorem kronecker_pos {A : HermitianMat m 𝕜} (hA : 0 < A) (hB : 0 < B) : 0 < A ⊗ₖ B := by
  apply lt_of_le_of_ne (kronecker_nonneg hA.le hB.le)
  intro h
  replace h := congr(trace $h)
  simp only [trace_zero, trace_kronecker, zero_eq_mul] at h
  apply trace_pos at hA
  apply trace_pos at hB
  grind only [cases Or]

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.kronecker`: nonneg when both factors are. -/
@[positivity HermitianMat.kronecker _ _]
def evalHermitianMatKronecker : PositivityExt where eval {_u _α} _zα _pα e := do
  let .app (.app _kron A) B ← whnfR e | throwError "not HermitianMat.kronecker"
  let (isStrictA, pfA) ← bestResult A
  let (isStrictB, pfB) ← bestResult B
  if isStrictA && isStrictB then
    pure (.positive (← mkAppM ``HermitianMat.kronecker_pos #[pfA, pfB]))
  else
    let pfA' ← try mkAppM ``le_of_lt #[pfA] catch _ => pure pfA
    let pfB' ← try mkAppM ``le_of_lt #[pfB] catch _ => pure pfB
    let pfAB' ← mkAppM ``HermitianMat.kronecker_nonneg #[pfA', pfB']
    pure (.nonnegative pfAB')

variable (M) in
open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.conj`: nonneg when the inner matrix is. -/
theorem conj_nonneg (hA : 0 ≤ A) : 0 ≤ A.conj M := by
  rw [zero_le_iff] at hA ⊢
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hA M

theorem conj_pos [DecidableEq n] {A : HermitianMat n 𝕜} {M : Matrix m n 𝕜} (hA : 0 < A)
    (h : LinearMap.ker M.toEuclideanLin ≤ A.ker) : 0 < A.conj M := by
  classical exact (A.conj_nonneg M hA.le).lt_of_ne' (A.conj_ne_zero hA.ne' h)

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.conj`: nonneg when the inner matrix is. -/
@[positivity HermitianMat.conj _ _]
def evalHermitianMatConj : PositivityExt where eval {_u _α} _zα _pα e := do
  let .app (.app _coe conjM) (A : Expr) ← whnfR e | throwError "not conj application"
  let M := conjM.appArg!
  let (_, pfA) ← bestResult A
  let pfNonneg ← try mkAppM ``le_of_lt #[pfA] catch _ => pure pfA
  pure (.nonnegative (← mkAppM ``HermitianMat.conj_nonneg #[M, pfNonneg]))

example [DecidableEq n] [DecidableEq m] [Nonempty n] [Nonempty m]
  (A B : HermitianMat n ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B) (M : Matrix m n ℂ) :
    0 < (2 : HermitianMat (n × m) ℂ) + (3 • A) ⊗ₖ (Real.pi • B).conj M := by
  positivity

example (A B : HermitianMat n ℂ) (hA : 0 < A) (hB : 0 < B) :
    0 < ((37 • A) ⊗ₖ ((38 : ℝ) • B)).trace := by
  positivity

theorem convex_cone (hA : 0 ≤ A) (hB : 0 ≤ B) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    0 ≤ (c₁ • A + c₂ • B) := by
  rw [zero_le_iff] at hA hB ⊢
  exact (hA.smul hc₁).add (hB.smul hc₂)

theorem sq_nonneg [DecidableEq n] : 0 ≤ A ^ 2 := by
  simp [zero_le_iff, pow_two]
  nth_rewrite 1 [←Matrix.IsHermitian.eq A.H]
  exact Matrix.posSemidef_conjTranspose_mul_self A.mat

theorem ker_antitone [DecidableEq n] (hA : 0 ≤ A) : A ≤ B → B.ker ≤ A.ker := by
  intro h x hB
  replace h := (le_iff_mulVec_le.mp h) x
  rw [HermitianMat.mem_ker_iff_mulVec_zero] at hB ⊢
  rw [hB, dotProduct_zero] at h
  rw [zero_le_iff] at hA
  rw [← hA.dotProduct_mulVec_zero_iff]
  exact le_antisymm h (hA.right x)

theorem conj_mono (h : A ≤ B) : A.conj M ≤ B.conj M := by
  have h_conj_pos : (M * (B - A).mat * Mᴴ).PosSemidef :=
    Matrix.PosSemidef.mul_mul_conjTranspose_same h M
  constructor;
  · simp [conj, Matrix.IsHermitian, Matrix.mul_assoc]
  · simpa [Matrix.mul_sub, Matrix.sub_mul] using h_conj_pos.2

lemma conj_posDef [DecidableEq n] (hA : A.mat.PosDef) (hN : IsUnit N) :
    (A.conj N).mat.PosDef := by
  use HermitianMat.H _
  intro x hx_ne_zero
  open Matrix in
  have h_pos : 0 < star (Nᴴ *ᵥ x) ⬝ᵥ A *ᵥ (Nᴴ *ᵥ x) := by
    apply hA.2
    intro h
    apply hx_ne_zero
    simpa [ hN ] using Matrix.eq_zero_of_mulVec_eq_zero
      (by simpa [Matrix.det_conjTranspose] using hN.map Matrix.detMonoidHom) h
  convert h_pos using 1
  simp only [conj_apply_mat, mulVec_mulVec, Matrix.mul_assoc]
  simp [dotProduct_mulVec, mulVec_conjTranspose]

lemma inv_conj [DecidableEq n] {M : Matrix n n 𝕜} (hM : IsUnit M) :
    (A.conj M)⁻¹ = A⁻¹.conj (M⁻¹)ᴴ := by
  have h_inv : (M⁻¹)ᴴ * Mᴴ = 1 := by
    simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq] at hM
    simp [Matrix.conjTranspose_nonsing_inv, hM]
  ext1
  simp only [conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.conjTranspose_conjTranspose]
  simp only [mat_inv, mat_mk]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv h_inv, mul_assoc]

theorem le_iff_mulVec_le_mulVec (A B : HermitianMat n 𝕜) :
    A ≤ B ↔ ∀ v : n → 𝕜, star v ⬝ᵥ A.mat *ᵥ v ≤ star v ⬝ᵥ B.mat *ᵥ v := by
  rw [← sub_nonneg, HermitianMat.zero_le_iff]
  conv_rhs => enter [v]; rw [← sub_nonneg]
  have h := (B - A).H
  simp only [HermitianMat.mat_sub] at h
  simp [Matrix.PosSemidef, Matrix.sub_mulVec, h]

theorem inner_mulVec_nonneg (hA : 0 ≤ A) (v : n → 𝕜) :
    0 ≤ star v ⬝ᵥ A.mat *ᵥ v := by
  rw [le_iff_mulVec_le_mulVec] at hA
  simpa using hA v

theorem mem_ker_of_inner_mulVec_zero [DecidableEq n] (hA : 0 ≤ A) (v : n → 𝕜)
    (h : star v ⬝ᵥ A.mat *ᵥ v = 0) : v ∈ A.ker := by
  --TODO Cleanup
  -- Since $A$ is positive semidefinite, there exists a matrix $B$ such that $A = B^* B$.
  obtain ⟨B, hB⟩ : ∃ B : Matrix n n 𝕜, A.mat = B.conjTranspose * B := by
    have h_pos_semidef : Matrix.IsHermitian A.mat ∧ ∀ v : n → 𝕜, 0 ≤ star v ⬝ᵥ A.mat *ᵥ v := by
      exact ⟨ A.H, fun v => by simpa [ Matrix.mulVec, dotProduct ] using hA.2 v ⟩;
    exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp h_pos_semidef;
  -- Since $v^* A v = 0$, we have $v^* B^* B v = 0$, which implies $B v = 0$.
  have hBv : B.mulVec v = 0 := by
    have hBv : star (B.mulVec v) ⬝ᵥ (B.mulVec v) = 0 := by
      simp_all [  Matrix.dotProduct_mulVec];
      simp_all [ Matrix.vecMul, dotProduct, mul_comm ];
      simp_all [ Matrix.mul_apply, Matrix.mulVec, dotProduct ];
      convert h using 3 ; simp [ mul_comm, mul_left_comm, Finset.mul_sum];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
    simp_all [ dotProduct, RCLike.ext_iff (K := 𝕜)];
    funext x
    norm_num [ RCLike.ext_iff (K := 𝕜) ]
    have := hBv.1 ▸ Finset.single_le_sum ( fun x _ => add_nonneg ( mul_self_nonneg ( ( B *ᵥ v ) x |> RCLike.re ) ) ( mul_self_nonneg ( ( B *ᵥ v ) x |> RCLike.im ) ) ) ( Finset.mem_univ x )
    constructor <;> nlinarith only [ this ]
  simp_all [← Matrix.mulVec_mulVec]
  replace hB := congr_arg ( fun m => m.mulVec v ) hB; simp_all [ ← Matrix.mulVec_mulVec ] ;
  exact hB

theorem ker_add [DecidableEq n] (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A + B).ker = A.ker ⊓ B.ker := by
  --TODO Cleanup
  -- If $(A + B)v = 0$, then $Av + Bv = 0$. Since $A$ and $B$ are positive semidefinite, this implies $Av = 0$ and $Bv = 0$.
  have h_subset : ∀ v : n → 𝕜, (A + B).mat *ᵥ v = 0 → A.mat *ᵥ v = 0 ∧ B.mat *ᵥ v = 0 := by
    intro v hv
    have h_pos : 0 ≤ star v ⬝ᵥ A.mat *ᵥ v ∧ 0 ≤ star v ⬝ᵥ B.mat *ᵥ v := by
      exact ⟨inner_mulVec_nonneg hA v, inner_mulVec_nonneg hB v⟩
    have h_eq_zero : star v ⬝ᵥ A.mat *ᵥ v + star v ⬝ᵥ B.mat *ᵥ v = 0 := by
      convert congr_arg ( fun w => star v ⬝ᵥ w ) hv using 1 ;
      simp [ Matrix.add_mulVec ] ; ring_nf!;
      aesop;
    have h_eq_zero : star v ⬝ᵥ A.mat *ᵥ v = 0 ∧ star v ⬝ᵥ B.mat *ᵥ v = 0 := by
      exact ⟨ by simpa using le_antisymm ( le_trans ( le_add_of_nonneg_right h_pos.2 ) h_eq_zero.le ) h_pos.1, by simpa using le_antisymm ( le_trans ( le_add_of_nonneg_left h_pos.1 ) h_eq_zero.le ) h_pos.2 ⟩
    exact ⟨mem_ker_of_inner_mulVec_zero hA v h_eq_zero.1, mem_ker_of_inner_mulVec_zero hB v h_eq_zero.2 ⟩
  apply le_antisymm
  · exact fun v hv => ⟨ h_subset v hv |>.1, h_subset v hv |>.2 ⟩;
  · rintro v ⟨hvA, hvB⟩
    change (A + B).mat *ᵥ v = 0
    convert congr_arg₂ ( · + · ) hvA hvB using 1
    · ext1
      simp [ Matrix.add_mulVec ]
      ring!
    · norm_num +zetaDelta at *

theorem ker_sum [DecidableEq n] (f : ι → HermitianMat n 𝕜) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f i).ker = ⨅ i, (f i).ker := by
  --TODO Cleanup
  -- By definition of sum, we know that if $v \in \ker(\sum_{i \in s} f_i)$, then $\sum_{i \in s} (f_i v, v) = 0$.
  have h_sum_zero : ∀ v : n → 𝕜, (∑ i, f i).mat *ᵥ v = 0 ↔ ∀ i, (f i).mat *ᵥ v = 0 := by
    intro v
    constructor
    · intro hv_zero
      have h_inner_zero : ∑ i, star v ⬝ᵥ (f i).mat *ᵥ v = 0 := by
        have h_inner_zero : star v ⬝ᵥ (∑ i, (f i).mat) *ᵥ v = 0 := by
          aesop
        convert h_inner_zero using 1
        simp [Matrix.mulVec, dotProduct];
        simp only [Finset.mul_sum _ _ _, Matrix.sum_apply, Finset.sum_mul];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm )
      have h_inner_zero_i : ∀ i, star v ⬝ᵥ (f i).mat *ᵥ v = 0 := by
        have h_inner_zero_i : ∀ i, 0 ≤ star v ⬝ᵥ (f i).mat *ᵥ v := by
          exact fun i => inner_mulVec_nonneg (hf i) v;
        exact fun i => le_antisymm ( le_trans ( Finset.single_le_sum ( fun i _ => h_inner_zero_i i ) ( Finset.mem_univ i ) ) h_inner_zero.le ) ( h_inner_zero_i i )
      exact fun i ↦ mem_ker_of_inner_mulVec_zero (hf i) v (h_inner_zero_i i)
    · simp +contextual [Matrix.sum_mulVec]
  ext v
  simp
  exact h_sum_zero v

theorem ker_conj [DecidableEq n] (hA : 0 ≤ A) (B : Matrix n n 𝕜) :
    (A.conj B).ker = Submodule.comap (Matrix.toEuclideanLin B.conjTranspose) A.ker := by
  --TODO Cleanup
  ext v; simp [HermitianMat.conj];
  constructor <;> intro h;
  · -- By definition of $A$, we know that $⟨w, A w⟩ = 0$ implies $w \in \ker A$.
    have h_inner_zero : ∀ w : EuclideanSpace 𝕜 n, 0 ≤ A → (star w ⬝ᵥ A.mat *ᵥ w) = 0 → w ∈ A.ker := by
      intro w hw h_zero
      apply HermitianMat.mem_ker_of_inner_mulVec_zero hw w h_zero;
    convert h_inner_zero ( Bᴴ *ᵥ v ) hA _;
    convert congr_arg ( fun w => star v ⬝ᵥ w ) h using 1;
    · simp [ Matrix.mulVec_mulVec,dotProduct_comm ];
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, HermitianMat.lin ];
      simp [ Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm, Matrix.mul_apply ];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
    · simp [ dotProduct ];
  · simp_all [ HermitianMat.ker, Matrix.mul_assoc ];
    convert congr_arg ( Matrix.toEuclideanLin B ) h using 1;
    · simp [HermitianMat.lin, Matrix.toEuclideanLin];
    · exact Eq.symm (LinearMap.map_zero (Matrix.toEuclideanLin B))

theorem ker_le_of_le_smul {α : ℝ} [DecidableEq n] (hα : α ≠ 0) (hA : 0 ≤ A) (hAB : A ≤ α • B) : B.ker ≤ A.ker := by
  rw [← ker_pos_smul B hα]
  exact ker_antitone hA hAB

--TODO: Positivity extensions for traceLeft, traceRight, rpow, nat powers, inverse function,
-- the various `proj` function (in Proj.lean), and the inner product.
