import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Permutation

open scoped Matrix

variable {d d₂ d₃ R : Type*}
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]

variable [CommRing R] [StarRing R]

variable {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix d d 𝕜}

/-- An isometry is a matrix `A` such that `AAᴴ = 1`. Compare with a
unitary, which requires `AAᴴ = AᴴA = 1`. -/
def Matrix.Isometry (A : Matrix d d₂ R) : Prop :=
  A * Aᴴ = 1

omit [Fintype d₂] [DecidableEq d₃] in
theorem Matrix.submatrix_one_isometry {e : d₂ → d} {f : d₃ → d} (he : e.Injective) (hf : f.Bijective) :
    (submatrix (α := R) 1 e f).Isometry := by
  -- Since $e$ is injective and $f$ is bijective, the submatrix of the identity matrix formed by $e$ and $f$ is a permutation matrix.
  have h_perm : ∀ i j, (Matrix.submatrix (1 : Matrix d d R) e f) i j = if e i = f j then 1 else 0 := by
    -- By definition of the identity matrix, the entry (i, j) in the submatrix is 1 if e i = f j and 0 otherwise.
    simp [Matrix.submatrix, Matrix.one_apply];
  ext i j
  -- Since $e$ is injective and $f$ is bijective, the product $A * Aᴴ$ will have 1s on the diagonal and 0s elsewhere, which is the identity matrix.
  change ∑ k, (Matrix.submatrix (1 : Matrix d d R) e f) i k * (Matrix.conjTranspose (Matrix.submatrix (1 : Matrix d d R) e f)) k j = if i = j then 1 else 0
  simp_all only [Multiset.bijective_iff_map_univ_eq_univ, submatrix_apply, conjTranspose_apply, ite_mul, one_mul,
      zero_mul]
  split
  next h =>
    subst h
    simp_all only [↓reduceIte, star_one, Finset.sum_boole]
    have h_unique : ∀ i, ∃! x, f x = e i := by
      intro i
      obtain ⟨x, hx⟩ : ∃ x, f x = e i := by
        replace hf := congr_arg Multiset.toFinset hf; rw [ Finset.ext_iff ] at hf; specialize hf ( e i ) ; aesop;
      use x
      simp_all only [true_and]
      intro y a
      have := Fintype.bijective_iff_injective_and_card f
      aesop
    obtain ⟨ x, hx ⟩ := h_unique i;
    rw [ show ( Finset.univ.filter fun y => e i = f y ) = { x } from Finset.eq_singleton_iff_unique_mem.2 ⟨ by aesop, fun y hy => hx.2 y <| Eq.symm <| Finset.mem_filter.1 hy |>.2 ⟩ ] ; simp ( config := { decide := Bool.true } );
  next h => -- Since $e$ is injective and $e i \neq e j$, there is no $x$ such that $e i = f x$ and $e j = f x$.
    have h_no_x : ∀ x : d₃, ¬(e i = f x ∧ e j = f x) := by
      exact fun x hx => h ( he ( hx.1.trans hx.2.symm ) );
    exact Finset.sum_eq_zero fun x hx => by specialize h_no_x x; aesop

omit [DecidableEq d₂] in
theorem Matrix.submatrix_one_id_left_isometry {e : d₂ → d} (he : e.Bijective) :
    (submatrix (1 : Matrix d d R) id e).Isometry :=
  submatrix_one_isometry Function.injective_id he

omit [Fintype d₂] in
theorem Matrix.submatrix_one_id_right_isometry {e : d₂ → d} (he : e.Injective) :
    (submatrix (1 : Matrix d d R) e id).Isometry :=
  submatrix_one_isometry he Function.bijective_id

theorem Matrix.mem_unitaryGroup_iff_isometry (A : Matrix d d R) :
    A ∈ unitaryGroup d R ↔ A.Isometry ∧ Aᴴ.Isometry := by
  rw [Isometry, Isometry, and_comm, conjTranspose_conjTranspose]
  rfl

theorem Equiv.Perm.permMatrix_mem_unitaryGroup (e : Perm d) :
    e.permMatrix R ∈ Matrix.unitaryGroup d R := by
  -- Since $e$ is a permutation, its permutation matrix $P_e$ is orthogonal, meaning $P_e * P_e^T = I$.
  have h_perm_ortho : (Equiv.Perm.permMatrix R e) * (Equiv.Perm.permMatrix R e)ᵀ = 1 := by
    ext i j; rw [ Matrix.mul_apply ] ; aesop;
  constructor
  · simp_all only [Matrix.transpose_permMatrix]
    -- Since the conjugate transpose of a permutation matrix is the permutation matrix of the inverse permutation, we have:
    have h_conj_transpose : star (Equiv.Perm.permMatrix R e) = (Equiv.Perm.permMatrix R e)ᵀ := by
      ext i j; simp ( config := { decide := Bool.true } ) [ Equiv.Perm.permMatrix ] ; aesop;
    simp_all ( config := { decide := Bool.true } ) [ Matrix.mul_eq_one_comm ];
  · simp_all only [Matrix.transpose_permMatrix]
    convert h_perm_ortho using 2;
    simp ( config := { decide := Bool.true } ) [ Matrix.star_eq_conjTranspose, Equiv.Perm.permMatrix ]

omit [Fintype d₂] [DecidableEq d₃] in
theorem Matrix.reindex_one_isometry (e : d ≃ d₂) (f : d ≃ d₃) :
    (reindex (α := R) e f 1).Isometry := by
  -- Since $e$ and $f$ are bijections, the reindexing of the identity matrix by $e$ and $f$ is a permutation matrix, which is unitary.
  have h_perm : ∀ (e : d ≃ d₂) (f : d ≃ d₃), (Matrix.reindex e f (1 : Matrix d d R)).Isometry := by
    intro e f
    simp [Matrix.Isometry];
  exact h_perm e f

omit [Fintype d] in
theorem Matrix.reindex_one_mem_unitaryGroup (e : d ≃ d₂)  :
    reindex (α := R) e e 1 ∈ unitaryGroup d₂ R := by
  -- The reindex of the identity matrix under an equivalence e is just the identity matrix on d₂.
  have h_reindex_id : Matrix.reindex e e (1 : Matrix d d R) = 1 := by
    -- By definition of reindex, the entry at (i, j) in the reindexed matrix is 1 if i = j and 0 otherwise.
    ext i j; simp [Matrix.reindex, Matrix.one_apply];
  -- Since the identity matrix is unitary, its conjugate transpose is also the identity matrix.
  simp [h_reindex_id];

omit [Fintype d₂] [DecidableEq d₂] [StarRing R] in
theorem Matrix.reindex_eq_conj (A : Matrix d d R) (e : d ≃ d₂) : reindex e e A =
    (reindex (α := R) e (.refl d) 1) * A * (reindex (α := R) (.refl d) e 1) := by
  -- By definition of matrix multiplication and reindexing, we can show that the two matrices are equal.
  ext i j; simp [Matrix.mul_apply, Matrix.reindex];
  -- The inner sum simplifies to $A (e.symm i) x$ because $1 (e.symm i) x$ is $1$ if $x = e.symm i$ and $0$ otherwise.
  simp [Matrix.one_apply]

theorem Matrix.reindex_eq_conj_unitaryGroup' (A : Matrix d d R) (e : Equiv.Perm d) : reindex e e A =
    (⟨_, e⁻¹.permMatrix_mem_unitaryGroup⟩ : unitaryGroup d R) * A * (⟨_, e.permMatrix_mem_unitaryGroup⟩ : unitaryGroup d R) := by
  ext i j;
  simp ( config := { decide := Bool.true } ) [ Matrix.mul_apply ];
  rw [ Finset.sum_eq_single ( e.symm j ) ] <;> aesop

theorem Matrix.IsHermitian.conj_isometry {A : Matrix d d R} {u : Matrix d d₂ R}
  (hA : A.IsHermitian) (hu : u.Isometry) :
    (uᴴ * A * u).IsHermitian := by
  sorry

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
      ext; simp ( config := { decide := Bool.true } ) [ Matrix.mulVec, dotProduct ];
      (expose_names; exact Eq.symm (RCLike.real_smul_eq_coe_mul (hA.eigenvalues i) (x i_1)));
    -- By linearity of A and B, we can distribute them over the sum.
    intros v
    obtain ⟨c, lam, hv, hlam⟩ := h_diag v
    have hAv : A *ᵥ v = ∑ i, c i • lam i • (hA.eigenvectorBasis i) := by
      -- By linearity of matrix multiplication, we can distribute A over the sum.
      have hAv : A *ᵥ (∑ i, c i • (hA.eigenvectorBasis i)) = ∑ i, c i • A *ᵥ (hA.eigenvectorBasis i) := by
        simp ( config := { decide := Bool.true } ) [ funext_iff, Matrix.mulVec_smul ];
        simp ( config := { decide := Bool.true } ) [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ];
        exact fun _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      aesop
    have hBv : B *ᵥ v = ∑ i, c i • lam i • (hA.eigenvectorBasis i) := by
      have hBv : B *ᵥ v = ∑ i, c i • (B *ᵥ (hA.eigenvectorBasis i)) := by
        -- By linearity of matrix multiplication, we can distribute $B$ over the sum.
        have hBv : B *ᵥ v = B *ᵥ (∑ i, c i • (hA.eigenvectorBasis i)) := by
          rw [hv];
        simp ( config := { decide := Bool.true } ) [ hBv, funext_iff, Matrix.mulVec_smul ];
        simp ( config := { decide := Bool.true } ) [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ];
        exact fun _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      exact hBv.trans ( Finset.sum_congr rfl fun i _ => by rw [ h _ _ ( hlam i ) ] )
    rw [hAv, hBv];
  -- By the definition of matrix equality, if $A * v = B * v$ for all $v$, then $A = B$.
  apply Matrix.ext; intro i j; exact (by
  simpa using congr_fun ( h_diag ( Pi.single j 1 ) ) i)

private theorem Matrix.cfc_conj_isometry' (hA : A.IsHermitian) (f : ℝ → ℝ) {u : Matrix d₂ d 𝕜}
  (hu₁ : u.Isometry) (hu₂ : uᴴ.Isometry) :
    cfc f (u * A * uᴴ) = u * (cfc f A) * uᴴ := by
  apply Matrix.IsHermitian.eigenvalue_ext
  · exact cfc_predicate f (u * A * uᴴ)
  intro v lam h
  sorry

theorem Matrix.cfc_conj_isometry (f : ℝ → ℝ) {u : Matrix d₂ d 𝕜}
  (hu₁ : u.Isometry) (hu₂ : uᴴ.Isometry) :
    cfc f (u * A * uᴴ) = u * (cfc f A) * uᴴ := by
  by_cases hA : A.IsHermitian
  · exact cfc_conj_isometry' hA f hu₁ hu₂
  rw [cfc_apply_of_not_predicate, cfc_apply_of_not_predicate]
  · simp
  · exact hA
  · contrapose! hA
    convert Matrix.IsHermitian.conj_isometry (A := u * A * uᴴ) (u := u) hA hu₁
    have hu₃ : uᴴ * u = 1 := by rw [← hu₂]; simp
    simp only [Matrix.mul_assoc, hu₃]
    simp [← Matrix.mul_assoc, hu₃]

theorem Matrix.cfc_conj_unitary (f : ℝ → ℝ) (u : unitaryGroup d 𝕜) :
    cfc f (u * A * u⁻¹) = u * (cfc f A) * u⁻¹ := by
  have hu := u.prop
  rw [mem_unitaryGroup_iff_isometry] at hu
  exact Matrix.cfc_conj_isometry f hu.left hu.right

theorem Matrix.cfc_reindex (f : ℝ → ℝ) (e : d ≃ d₂) :
    cfc f (reindex e e A) = reindex e e (cfc f A) := by
  rw [reindex_eq_conj, reindex_eq_conj]
  convert Matrix.cfc_conj_isometry f (u := (Matrix.reindex e (Equiv.refl d) : Matrix d d 𝕜 → Matrix d₂ d 𝕜) 1) ?_ ?_
  · simp
  · simp
  · apply reindex_one_isometry
  · rw [conjTranspose_reindex, conjTranspose_one]
    apply reindex_one_isometry
