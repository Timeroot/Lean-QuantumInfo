/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.IsDiag

import QuantumInfo.ForMathlib.Matrix

open scoped Matrix

variable {d d₂ d₃ R : Type*}
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]

variable [CommRing R] [StarRing R]

variable {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix d d 𝕜}

/-- An isometry is a matrix `A` such that `AAᴴ = 1`. Compare with a unitary, which
requires `AAᴴ = AᴴA = 1`. It is common to claim that, in a finite-dimensional vector
space, a two-sided isometry (`A.Isometry ∧ Aᴴ.Isometry`) must be square and therefore unitary;
this is does not work out so well here, since a `Matrix m n R` can be a two-sided isometry,
but cannot be a `unitary` since the rows and columns are index by different labels. -/
def Matrix.Isometry (A : Matrix d d₂ R) : Prop :=
  Aᴴ * A = 1

omit [Fintype d₃] [DecidableEq d₂] in
theorem Matrix.submatrix_one_isometry {e : d₂ → d} {f : d₃ → d} (he : e.Bijective) (hf : f.Injective) :
    (submatrix (α := R) 1 e f).Isometry := by
  -- Since $e$ is injective and $f$ is bijective, the submatrix of the identity matrix formed by $e$ and $f$ is a permutation matrix.
  have h_perm : ∀ i j, (Matrix.submatrix (1 : Matrix d d R) e f) i j = if e i = f j then 1 else 0 := by
    -- By definition of the identity matrix, the entry (i, j) in the submatrix is 1 if e i = f j and 0 otherwise.
    simp [Matrix.submatrix, Matrix.one_apply]
  ext i j
  -- Since $e$ is injective and $f$ is bijective, the product $A * Aᴴ$ will have 1s on the diagonal and 0s elsewhere, which is the identity matrix.
  change ∑ k, (Matrix.conjTranspose (Matrix.submatrix (1 : Matrix d d R) e f)) i k *
    (Matrix.submatrix (1 : Matrix d d R) e f) k j = if i = j then 1 else 0
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, submatrix_apply, conjTranspose_apply, one_apply]
  symm; split <;> symm
  next h =>
    subst h
    simp_all only [implies_true, mul_ite, ↓reduceIte, star_one, mul_one, star_zero, mul_zero,
      Finset.sum_boole]
    have h_unique : ∀ i, ∃! x, e x = f i := by
      intro i
      obtain ⟨x, hx⟩ : ∃ x, e x = f i := by
        replace he := congr_arg Multiset.toFinset he; rw [Finset.ext_iff] at he; specialize he ( f i ) ; aesop;
      use x
      simp_all only [true_and]
      intro y a
      have := Fintype.bijective_iff_injective_and_card e
      aesop
    obtain ⟨ x, hx ⟩ := h_unique i;
    rw [show ( Finset.univ.filter fun y => e y = f i ) = { x } from Finset.eq_singleton_iff_unique_mem.2 ⟨ by aesop, fun y hy => hx.2 y <| Eq.symm <| Finset.mem_filter.1 hy |>.2.symm ⟩] ; simp ;
  next h => -- Since $e$ is injective and $e i \neq e j$, there is no $x$ such that $e i = f x$ and $e j = f x$.
    have h_no_x : ∀ x : d₂, ¬(e x = f i ∧ e x = f j) := by
      exact fun x hx => h ( hf ( hx.1.symm.trans hx.2 ) );
    exact Finset.sum_eq_zero fun x hx => by specialize h_no_x x; aesop

omit [DecidableEq d₂] in
theorem Matrix.submatrix_one_id_left_isometry {e : d₂ → d} (he : e.Bijective) :
    (submatrix (1 : Matrix d d R) e id).Isometry :=
  submatrix_one_isometry he Function.injective_id

omit [Fintype d₂] in
theorem Matrix.submatrix_one_id_right_isometry {e : d₂ → d} (he : e.Injective) :
    (submatrix (1 : Matrix d d R) id e).Isometry :=
  submatrix_one_isometry Function.bijective_id he

theorem Matrix.mem_unitaryGroup_iff_isometry (A : Matrix d d R) :
    A ∈ unitaryGroup d R ↔ A.Isometry ∧ Aᴴ.Isometry := by
  rw [Isometry, Isometry, conjTranspose_conjTranspose]
  rfl

theorem Equiv.Perm.permMatrix_mem_unitaryGroup (e : Perm d) :
    e.permMatrix R ∈ Matrix.unitaryGroup d R := by
  -- Since $e$ is a permutation, its permutation matrix $P_e$ is orthogonal, meaning $P_e * P_e^T = I$.
  have h_perm_ortho : (Equiv.Perm.permMatrix R e) * (Equiv.Perm.permMatrix R e)ᵀ = 1 := by
    ext i j; rw [Matrix.mul_apply] ; aesop;
  constructor
  · simp_all only [Matrix.transpose_permMatrix]
    -- Since the conjugate transpose of a permutation matrix is the permutation matrix of the inverse permutation, we have:
    have h_conj_transpose : star (Equiv.Perm.permMatrix R e) = (Equiv.Perm.permMatrix R e)ᵀ := by
      ext i j; simp [Equiv.Perm.permMatrix] ; aesop;
    simp_all  [Matrix.mul_eq_one_comm]
  · simp_all only [Matrix.transpose_permMatrix]
    convert h_perm_ortho using 2;
    simp [Matrix.star_eq_conjTranspose, Equiv.Perm.permMatrix]

omit [Fintype d₃] [DecidableEq d₂] in
theorem Matrix.reindex_one_isometry (e : d ≃ d₂) (f : d ≃ d₃) :
    (reindex (α := R) e f 1).Isometry := by
  -- Since $e$ and $f$ are bijections, the reindexing of the identity matrix by $e$ and $f$ is a permutation matrix, which is unitary.
  have h_perm : ∀ (e : d ≃ d₂) (f : d ≃ d₃), (Matrix.reindex e f (1 : Matrix d d R)).Isometry := by
    intro e f
    simp [Matrix.Isometry]
  exact h_perm e f

omit [Fintype d] in
theorem Matrix.reindex_one_mem_unitaryGroup (e : d ≃ d₂)  :
    reindex (α := R) e e 1 ∈ unitaryGroup d₂ R := by
  -- The reindex of the identity matrix under an equivalence e is just the identity matrix on d₂.
  have h_reindex_id : Matrix.reindex e e (1 : Matrix d d R) = 1 := by
    -- By definition of reindex, the entry at (i, j) in the reindexed matrix is 1 if i = j and 0 otherwise.
    ext i j
    simp [Matrix.reindex, Matrix.one_apply]
  simp only [h_reindex_id, one_mem]

omit [Fintype d₂] [DecidableEq d₂] [StarRing R] in
theorem Matrix.reindex_eq_conj (A : Matrix d d R) (e : d ≃ d₂) : reindex e e A =
    (reindex (α := R) e (.refl d) 1) * A * (reindex (α := R) (.refl d) e 1) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex]
  simp [Matrix.one_apply]

theorem Matrix.reindex_eq_conj_unitaryGroup' (A : Matrix d d R) (e : Equiv.Perm d) : reindex e e A =
    (⟨_, e⁻¹.permMatrix_mem_unitaryGroup⟩ : unitaryGroup d R) * A * (⟨_, e.permMatrix_mem_unitaryGroup⟩ : unitaryGroup d R) := by
  ext i j;
  simp [Matrix.mul_apply]
  rw [Finset.sum_eq_single ( e.symm j )] <;> aesop

theorem Matrix.IsHermitian.eigenvalue_ext (hA : A.IsHermitian)
  (h : ∀ (v : d → 𝕜) (lam : 𝕜), A *ᵥ v = lam • v → B *ᵥ v = lam • v) :
    A = B := by
  -- Since A is Hermitian, it is diagonalizable, and its eigenvectors form a complete basis. Therefore, for any vector v, we have Av = Bv.
  have h_diag : ∀ v : d → 𝕜, (A *ᵥ v) = (B *ᵥ v) := by
    -- Since A is Hermitian, it is diagonalizable, and its eigenvectors form a complete basis. Therefore, for any vector v, we can express it as a linear combination of eigenvectors.
    have h_diag : ∀ v : d → 𝕜, ∃ (c : d → 𝕜) (lam : d → 𝕜), v = ∑ i, c i • (Matrix.IsHermitian.eigenvectorBasis hA i) ∧ ∀ i, A *ᵥ (Matrix.IsHermitian.eigenvectorBasis hA i) = lam i • (Matrix.IsHermitian.eigenvectorBasis hA i) := by
      intro v
      obtain ⟨c, hc⟩ : ∃ c : d → 𝕜, v = ∑ i, c i • (hA.eigenvectorBasis i) := by
        have h_diag : ∀ v : EuclideanSpace 𝕜 d, ∃ c : d → 𝕜, v = ∑ i, c i • (hA.eigenvectorBasis i) := by
          intro v
          set c := fun i => innerₛₗ 𝕜 (hA.eigenvectorBasis i) v
          have hv : v = ∑ i, c i • (hA.eigenvectorBasis i) := by
            exact Eq.symm (OrthonormalBasis.sum_repr' hA.eigenvectorBasis v)
          use c;
        exact h_diag v;
      refine' ⟨ c, fun i => ( hA.eigenvalues i ), hc, fun i => _ ⟩;
      convert hA.mulVec_eigenvectorBasis i;
      ext
      simp only [PiLp.smul_apply, smul_eq_mul, Pi.smul_apply]
      symm
      exact RCLike.real_smul_eq_coe_mul (hA.eigenvalues i) _
    -- By linearity of A and B, we can distribute them over the sum.
    intros v
    obtain ⟨c, lam, hv, hlam⟩ := h_diag v
    have hAv : A *ᵥ v = ∑ i, c i • lam i • (hA.eigenvectorBasis i) := by
      -- By linearity of matrix multiplication, we can distribute A over the sum.
      have hAv : A *ᵥ (∑ i, c i • (hA.eigenvectorBasis i)) = ∑ i, c i • A *ᵥ (hA.eigenvectorBasis i) := by
        simp [funext_iff]
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _]
        exact fun _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      aesop
    have hBv : B *ᵥ v = ∑ i, c i • lam i • (hA.eigenvectorBasis i) := by
      have hBv : B *ᵥ v = ∑ i, c i • (B *ᵥ (hA.eigenvectorBasis i)) := by
        -- By linearity of matrix multiplication, we can distribute $B$ over the sum.
        have hBv : B *ᵥ v = B *ᵥ (∑ i, c i • (hA.eigenvectorBasis i)) := by
          rw [hv]
        simp [hBv, funext_iff]
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _]
        exact fun _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      exact hBv.trans ( Finset.sum_congr rfl fun i _ => by rw [h _ _ ( hlam i )] )
    rw [hAv, hBv]
  -- By the definition of matrix equality, if $A * v = B * v$ for all $v$, then $A = B$.
  apply Matrix.ext; intro i j; exact (by
  simpa using congr_fun ( h_diag ( Pi.single j 1 ) ) i)

/-- Generalizes `Matrix.IsHermitian.cfc.eq_1`, which gives a definition for the matrix CFC in terms of
`Matrix.IsHermitian.eigenvalues` and `Matrix.IsHermitian.eigenvectorUnitary`, to show that the CFC works
similarly for _any_ diagonalization by a two-sided isometry.
-/
theorem Matrix.IsHermitian.cfc_eq_any_isometry {n m 𝕜 : Type*} [RCLike 𝕜]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  {A : Matrix n n 𝕜} (hA : A.IsHermitian) {U : Matrix n m 𝕜}
  (hU₁ : U * Uᴴ = 1) (hU₂ : Uᴴ * U = 1) {D : m → ℝ}
  (hUD : A = (U * diagonal (RCLike.ofReal ∘ D) : Matrix _ _ _) * Uᴴ) (f : ℝ → ℝ) :
    hA.cfc f = (U * diagonal (RCLike.ofReal ∘ f ∘ D) : Matrix _ _ _) * Uᴴ := by
  --Thanks Aristotle
  rw [Matrix.IsHermitian.cfc]
  have hUV := hA.spectral_theorem
  set V := hA.eigenvectorUnitary with hV; clear_value V
  set D2 := hA.eigenvalues with hD; clear_value D2
  rcases V with ⟨V, hV₁, hV₂⟩
  dsimp only at *; clear hV hD
  subst A; clear hA
  have h_diag_eq : diagonal (RCLike.ofReal ∘ D) * (Uᴴ * V) = (Uᴴ * V) * diagonal (RCLike.ofReal ∘ D2) := by
    have h_mul : (Uᴴ * U * diagonal (RCLike.ofReal ∘ D) * Uᴴ : Matrix m n 𝕜) * V = Uᴴ * V * (diagonal (RCLike.ofReal ∘ D2) * star V * V) := by
      simp only [Matrix.mul_assoc, hUV]
    simp_all [ Matrix.mul_assoc ];
  have h_diag_eq_f : diagonal (RCLike.ofReal ∘ f ∘ D) * (Uᴴ * V) = (Uᴴ * V) * diagonal (RCLike.ofReal ∘ f ∘ D2) := by
    ext i j
    simp_all only [diagonal_mul, Function.comp_apply, mul_diagonal]
    replace h_diag_eq := congr_fun ( congr_fun h_diag_eq i ) j
    by_cases hi : D i = D2 j <;> simp_all [ mul_comm ] ;
  have h_final : U * diagonal (RCLike.ofReal ∘ f ∘ D) * Uᴴ * V = V * diagonal (RCLike.ofReal ∘ f ∘ D2) := by
    have h_final : U * diagonal (RCLike.ofReal ∘ f ∘ D) * (Uᴴ * V) = U * (Uᴴ * V) * diagonal (RCLike.ofReal ∘ f ∘ D2) := by
      rw [ Matrix.mul_assoc, h_diag_eq_f, Matrix.mul_assoc ];
      rw [ Matrix.mul_assoc, Matrix.mul_assoc ];
    simp_all +decide [ ← Matrix.mul_assoc ];
  rw [ ← h_final, Matrix.mul_assoc ];
  rw [hV₂, mul_one ]

/-- Generalizes `Matrix.IsHermitian.cfc.eq_1`, which gives a definition for the matrix CFC in terms of
`Matrix.IsHermitian.eigenvalues` and `Matrix.IsHermitian.eigenvectorUnitary`, to show that the CFC works
similarly for _any_ diagonalization.
-/
theorem Matrix.IsHermitian.cfc_eq_any_unitary {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  {A : Matrix n n 𝕜} (hA : A.IsHermitian) {U : unitaryGroup n 𝕜} {D : n → ℝ}
  (hUD : A = U.val * diagonal (RCLike.ofReal ∘ D) * star U.val) (f : ℝ → ℝ) :
    hA.cfc f = U.val * diagonal (RCLike.ofReal ∘ f ∘ D) * star U.val :=
  Matrix.IsHermitian.cfc_eq_any_isometry hA U.2.2 U.2.1 hUD f

private theorem Matrix.cfc_conj_isometry' (hA : A.IsHermitian) (f : ℝ → ℝ) {u : Matrix d₂ d 𝕜}
  (hu₁ : u.Isometry) (hu₂ : uᴴ.Isometry) :
    cfc f (u * A * uᴴ) = u * (cfc f A) * uᴴ := by
  let D := hA.eigenvalues
  let U' := u * hA.eigenvectorUnitary.val
  have := IsHermitian.cfc_eq_any_isometry
    (A := u * A * uᴴ) (D := D) (n := d₂) (m := d) (U := U') ?_ ?_ ?_ ?_ f; rotate_left
  · simpa using isHermitian_conjTranspose_mul_mul uᴴ hA
  · dsimp [U']
    rw [conjTranspose_mul, Matrix.mul_assoc]
    nth_rw 2 [← Matrix.mul_assoc]
    rw [show _ * _ᴴ = 1 from hA.eigenvectorUnitary.2.2, Matrix.one_mul]
    simpa [Isometry] using hu₂
  · dsimp [U']
    rw [conjTranspose_mul, Matrix.mul_assoc]
    nth_rw 2 [← Matrix.mul_assoc]
    rw [hu₁, Matrix.one_mul]
    exact hA.eigenvectorUnitary.2.1
  · rw [hA.spectral_theorem]
    simp [U', Matrix.mul_assoc]
    rfl
  rw [Matrix.IsHermitian.cfc_eq, this]
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc.eq_1]
  simp only [Matrix.mul_assoc, conjTranspose_mul, star_eq_conjTranspose, U', D]
  exact isHermitian_mul_mul_conjTranspose _ hA

theorem Matrix.cfc_conj_isometry (f : ℝ → ℝ) {u : Matrix d₂ d 𝕜}
  (hu₁ : u.Isometry) (hu₂ : uᴴ.Isometry) :
    cfc f (u * A * uᴴ) = u * (cfc f A) * uᴴ := by
  by_cases hA : A.IsHermitian
  · exact cfc_conj_isometry' hA f hu₁ hu₂
  rw [cfc_apply_of_not_predicate, cfc_apply_of_not_predicate]
  · simp
  · exact hA
  · contrapose! hA
    convert isHermitian_conjTranspose_mul_mul u hA
    have hu₃ : uᴴ * u = 1 := by simpa [Isometry] using hu₁
    simp only [Matrix.mul_assoc, hu₃]
    simp [← Matrix.mul_assoc, hu₃]

theorem Matrix.cfc_conj_unitary (f : ℝ → ℝ) (u : unitaryGroup d 𝕜) :
    cfc f (u * A * u⁻¹) = u * (cfc f A) * u⁻¹ := by
  have hu := u.prop
  rw [mem_unitaryGroup_iff_isometry] at hu
  exact Matrix.cfc_conj_isometry f hu.left hu.right

theorem Matrix.cfc_conj_unitary' (f : ℝ → ℝ) (u : unitaryGroup d 𝕜) :
    cfc f (uᴴ * A * u.val) = uᴴ * (cfc f A) * u.val := by
  simpa only [inv_inv] using cfc_conj_unitary f u⁻¹

theorem Matrix.cfc_reindex (f : ℝ → ℝ) (e : d ≃ d₂) :
    cfc f (reindex e e A) = reindex e e (cfc f A) := by
  rw [reindex_eq_conj, reindex_eq_conj]
  convert Matrix.cfc_conj_isometry f (u := (Matrix.reindex e (Equiv.refl d) : Matrix d d 𝕜 → Matrix d₂ d 𝕜) 1) ?_ ?_
  · simp
  · simp
  · apply reindex_one_isometry
  · rw [conjTranspose_reindex, conjTranspose_one]
    apply reindex_one_isometry

theorem Matrix.commute_euclideanLin (hAB : Commute A B) :
    Commute A.toEuclideanLin B.toEuclideanLin := by
  rw [commute_iff_eq] at hAB ⊢
  ext v i
  convert congr(($hAB).mulVec (WithLp.ofLp v) i) using 0
  simp only [Module.End.mul_apply, ← Matrix.mulVec_mulVec];
  simp only [← Matrix.ofLp_toEuclideanLin_apply, PiLp.ofLp_apply]

section commute_module
open Module.End

--TODO: All of these have Pi versions (instead of the "just two" operators versions below),
--  see the tail end of `JointEigenspace.lean` to see how it should generalize. This would
--  also give a Pi version for Matrix. That would be useful for e.g. we have a large number
--  of projectors that all pairwise commute, and we want to simultaneously diagonalize all
--  of them.

/-- Similar to `LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace`, but here the direct sum
is indexed by only the pairs of eigenvalues, as opposed to all pairs of `𝕜` values, giving a finite
decomposition. -/
theorem LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace' {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {A B : E →ₗ[𝕜] E}
  (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun (μ₁₂ : Eigenvalues A × Eigenvalues B) ↦
      ↥(eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2)) fun μ₁₂ ↦
    (eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2).subtypeₗᵢ := by
  have h := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB
  simp only [OrthogonalFamily, Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply,
    Subtype.forall, Submodule.mem_inf, mem_genEigenspace_one, and_imp] at h ⊢
  intro i j hij a ha hb a' ha' hb'
  contrapose! h
  simp only [Pairwise, ne_eq, Prod.forall, Prod.mk.injEq, not_and, not_forall]
  refine ⟨_, _, _, _, ?_, a, ha, hb, a', ha', hb', h⟩
  intro h' h''
  exact hij (Prod.ext (Subtype.ext h'') (Subtype.ext h'))

/-- Variant of `iSup_mono'` that allows for an easier handling of bottom elements. -/
theorem iSup_mono_bot {α : Type*} {ι ι' : Sort*} [CompleteLattice α]
  {f : ι → α} {g : ι' → α} (h : ∀ (i : ι), f i = ⊥ ∨ ∃ i', f i ≤ g i') :
    iSup f ≤ iSup g := by
  rcases isEmpty_or_nonempty ι'
  · simp only [IsEmpty.exists_iff, or_false] at h
    simp [h]
  · refine iSup_mono' (fun i ↦ ?_)
    rcases h i with h | h <;> simp [h]

noncomputable def Commute.isSymmetric_directSumDecomposition  {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {A B : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E]
  (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    DirectSum.Decomposition fun (μ₁₂ : Eigenvalues A × Eigenvalues B) ↦
      (eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2) := by
  apply (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace' hA hB).decomposition
  have h := LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
    hA hB hAB
  rw [iSup_prod'] at h
  apply le_antisymm le_top
  rw [← h, iSup_le_iff]
  rintro ⟨fst, snd⟩
  by_cases h₁ : Module.End.HasEigenvalue A fst
  · by_cases h₂ : Module.End.HasEigenvalue B snd
    · exact le_iSup_of_le ⟨⟨fst, h₁⟩, ⟨snd, h₂⟩⟩ le_rfl
    · replace h₂ : eigenspace B snd = ⊥ := by simpa [Module.End.HasUnifEigenvalue] using h₂
      simp [h₂]
  · replace h₁ : eigenspace A fst = ⊥ := by simpa [Module.End.HasUnifEigenvalue] using h₁
    simp [h₁]

/-- Similar to `LinearMap.IsSymmetric.directSum_isInternal_of_commute`, but here the direct sum
is indexed by only the pairs of eigenvalues, as opposed to all pairs of `𝕜` values, giving a finite
decomposition. -/
theorem LinearMap.IsSymmetric.directSum_isInternal_of_commute' {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {A B : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E]
  (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    DirectSum.IsInternal fun (μ₁₂ : Eigenvalues A × Eigenvalues B) ↦
      eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2 := by
  classical
  have h := LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  constructor
  · intro x y hxy
    -- Since the subspaces are orthogonal, the only way their sum can be zero is if each component is zero. Hence, x - y = 0, which implies x = y.
    rw [← sub_eq_zero]
    suffices h_diff_zero : ∀ (x : DirectSum (Eigenvalues A × Eigenvalues B) fun μ₁₂ ↦ ↥(eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2)), x.coeAddMonoidHom _ = 0 → x = 0 from
      h_diff_zero (x - y) (by simp [hxy])
    clear x y hxy; intro x hx;
    ext μ₁₂
    simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero]
    rw [← inner_self_eq_zero (𝕜 := 𝕜)]
    have h_inner_zero : inner 𝕜 (x μ₁₂ : E) (x.coeAddMonoidHom _) = 0 := by
      simp [hx]
    rw [← h_inner_zero]
    simp only [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, ZeroMemClass.coe_zero, implies_true,
      DFinsupp.sum_eq_sum_fintype, DFinsupp.equivFunOnFintype_apply]
    -- Since the decomposition is orthogonal, the inner product of x μ₁₂ with any other component is zero. Therefore, the sum simplifies to just the inner product of x μ₁₂ with itself.
    rw [inner_sum, Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ μ₁₂)]
    rw [Finset.sdiff_singleton_eq_erase, left_eq_add]
    apply Finset.sum_eq_zero
    intro μ hμ
    exact orthogonalFamily_eigenspace_inf_eigenspace' hA hB (Finset.ne_of_mem_erase hμ).symm _ _
  · -- Since the decomposition is orthogonal, the direct sum of the intersections is isomorphic to their sum. Therefore, the isomorphism implies that the sum is equal to E.
    have h_sum : ⨆ (μ₁₂ : Eigenvalues A × Eigenvalues B), eigenspace A μ₁₂.1 ⊓ eigenspace B μ₁₂.2 = ⊤ := by
      rw [eq_top_iff]
      intro x hx
      obtain ⟨y, rfl⟩ := h.2 x
      rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
      refine Submodule.sum_mem _ fun i hi ↦ ?_
      have hyi := Submodule.coe_mem (y i)
      simp only [Submodule.mem_inf, mem_genEigenspace_one] at hyi
      refine Submodule.mem_iSup_of_mem ⟨⟨i.2, ?_⟩, ⟨i.1, ?_⟩⟩ (by simp)
      <;> simp only [HasUnifEigenvalue, ne_eq, Submodule.eq_bot_iff, mem_genEigenspace_one, not_forall]
      <;> refine ⟨y i, by tauto, by simpa using hi⟩
    intro x
    rw [Submodule.eq_top_iff'] at h_sum
    specialize h_sum x
    rw [Submodule.mem_iSup_iff_exists_finsupp] at h_sum
    rcases h_sum with ⟨f, hf₁, hf₂⟩
    exact ⟨∑ i ∈ f.support, .of _ i ⟨f i, hf₁ i⟩, by simpa using hf₂⟩

end commute_module

theorem Commute.exists_unitary (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ U : Matrix.unitaryGroup d 𝕜, (U.val * A * Uᴴ).IsDiag ∧ (U.val * B * Uᴴ).IsDiag := by
  replace hA := Matrix.isHermitian_iff_isSymmetric.mp hA
  replace hB := Matrix.isHermitian_iff_isSymmetric.mp hB
  replace hAB := Matrix.commute_euclideanLin hAB
  have h_eigensum := LinearMap.IsSymmetric.directSum_isInternal_of_commute' hA hB hAB
  let sharedBasis : OrthonormalBasis _ 𝕜 (EuclideanSpace 𝕜 d) :=
    (h_eigensum.subordinateOrthonormalBasis rfl)
      (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace' hA hB)
  let sharedBasis_d : OrthonormalBasis d 𝕜 (EuclideanSpace 𝕜 d) :=
    sharedBasis.reindex (Fintype.equivOfCardEq (by simp))
  use ⟨(EuclideanSpace.basisFun d 𝕜).toBasis.toMatrix sharedBasis_d.toBasis,
    (EuclideanSpace.basisFun d 𝕜).toMatrix_orthonormalBasis_mem_unitary sharedBasis_d⟩
  constructor
  --These two goals are identical up to the A/B swap
  · sorry
  · sorry

instance instInvertibleUnitaryGroup (U : Matrix.unitaryGroup d 𝕜) : Invertible U :=
  invertibleOfGroup U

instance (U : Matrix.unitaryGroup d 𝕜) : Invertible U.val :=
  ⟨star U.val, U.2.1, U.2.2⟩

--TODO: Make Iff version.
/-- If two Hermitian matrices commute, there exists a common matrix that they are both a CFC of. -/
theorem Commute.exists_cfc (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ C : Matrix d d 𝕜, (∃ f : ℝ → ℝ, A = cfc f C) ∧ (∃ g : ℝ → ℝ, B = cfc g C) := by
  obtain ⟨U, hU₁, hU₂⟩ := hAB.exists_unitary hA hB
  let e := Fintype.equivFin d
  let D : Matrix d d 𝕜 := Matrix.diagonal (e ·) --index d into a ℕ, then a 𝕜
  use Uᴴ * D * U.val
  suffices h : ∀{M}, M.IsHermitian → (U.val * M * (U)ᴴ).IsDiag →
      ∃ f : ℝ → ℝ, M = cfc f (Uᴴ * D * U.val) by
    constructor
    · exact h hA hU₁
    · exact h hB hU₂
  clear * -
  intro M hM hU
  use fun x ↦ if hn : ∃ n : Fin (Fintype.card d), n = x
    then RCLike.re (Matrix.diag (U.val * M * Uᴴ : Matrix d d 𝕜) (e.symm hn.choose)) else 0
  rw [Matrix.cfc_conj_unitary']
  rw [Matrix.isDiag_iff_diagonal_diag] at hU
  rw [← Matrix.mul_inv_eq_iff_eq_mul_of_invertible] at hU
  rw [← Matrix.inv_mul_eq_iff_eq_mul_of_invertible] at hU
  rw [← hU, ← Matrix.mul_assoc]
  congr; rotate_right
  · exact Matrix.inv_eq_right_inv U.2.1
  · exact Matrix.inv_eq_left_inv U.2.1
  have hD : D = Matrix.diagonal (RCLike.ofReal <| e ·) := by simp [D]
  rw [hD, Matrix.cfc_diagonal]
  congr
  ext i
  simp only [Matrix.diag_apply, Function.comp_apply, Nat.cast_inj, exists_apply_eq_apply,
    ↓reduceDIte]
  rw [← (Matrix.isHermitian_mul_mul_conjTranspose U.val hM).coe_re_apply_self i]
  congr!
  · rw [mul_assoc, hU]
  all_goals
  ( rw [e.eq_symm_apply]
    symm; convert Classical.choose_eq _
    exact Fin.val_inj)
