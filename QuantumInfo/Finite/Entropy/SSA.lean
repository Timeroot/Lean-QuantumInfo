/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann
import QuantumInfo.ForMathlib.HermitianMat.Sqrt

/-!
Quantities of quantum _relative entropy_, namely the (standard) quantum relative
entropy, and generalizations such as sandwiched Rényi relative entropy.
-/

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}


open scoped InnerProductSpace RealInnerProductSpace Kronecker Matrix

/-
The operator norm of a matrix is the operator norm of the linear map it represents, with respect to the Euclidean norm.
-/
/-- The operator norm of a matrix, with respect to the Euclidean norm (l2 norm) on the domain and codomain. -/
noncomputable def Matrix.opNorm {m n 𝕜 : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [RCLike 𝕜] (A : Matrix m n 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-
An isometry preserves the Euclidean norm.
-/
theorem Matrix.isometry_preserves_norm {n m 𝕜 : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [RCLike 𝕜]
    (A : Matrix n m 𝕜) (hA : A.Isometry) (x : EuclideanSpace 𝕜 m) :
    ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
  rw [ ← sq_eq_sq₀ ( by positivity ) ( by positivity ), Matrix.Isometry ] at *;
  simp [ EuclideanSpace.norm_eq]
  have h_inner : ∀ x y : EuclideanSpace 𝕜 m, inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x y := by
    intro x y
    have h_inner_eq : inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x (toEuclideanLin A.conjTranspose (toEuclideanLin A y)) := by
      simp [ Matrix.toEuclideanLin, inner ];
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, ];
      simp [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
    simp_all [ Matrix.toEuclideanLin];
  convert congr_arg Real.sqrt ( congr_arg ( fun z => ‖z‖ ) ( h_inner x x ) ) using 1;
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ];
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ]

/-
The operator norm of an isometry is 1 (assuming the domain is non-empty).
-/
theorem Matrix.opNorm_isometry {n m 𝕜 : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [RCLike 𝕜] [Nonempty m]
    (A : Matrix n m 𝕜) (hA : A.Isometry) : Matrix.opNorm A = 1 := by
  have h_opNorm : ∀ x : EuclideanSpace 𝕜 m, ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
    convert Matrix.isometry_preserves_norm A hA;
  refine' le_antisymm ( csInf_le _ _ ) ( le_csInf _ _ );
  · exact ⟨ 0, fun c hc => hc.1 ⟩;
  · aesop;
  · exact ⟨ 1, ⟨zero_le_one, fun x => le_of_eq (by simp [h_opNorm])⟩ ⟩;
  · norm_num +zetaDelta at *;
    intro b hb h; specialize h ( EuclideanSpace.single ( Classical.arbitrary m ) 1 ) ; aesop;

/-- The matrix representation of the map $v \mapsto v \otimes \sum_k |k\rangle|k\rangle$.
    The output index is `(d1 \times d2) \times d2`. -/
def map_to_tensor_MES (d1 d2 : Type*) [Fintype d1] [Fintype d2] [DecidableEq d1] [DecidableEq d2] :
    Matrix ((d1 × d2) × d2) d1 ℂ :=
  Matrix.of fun ((i, j), k) l => if i = l ∧ j = k then 1 else 0

theorem map_to_tensor_MES_prop (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    (map_to_tensor_MES d₁ d₂).conjTranspose * (Matrix.kronecker A (1 : Matrix d₂ d₂ ℂ)) * (map_to_tensor_MES d₁ d₂) =
    A.traceRight := by
  ext i j; simp [map_to_tensor_MES, Matrix.mul_apply]
  simp [ Finset.sum_ite, Matrix.one_apply]
  rw [ Finset.sum_sigma' ];
  rw [ Finset.sum_congr rfl (g := fun x => A ( i, x.1.2 ) ( j, x.1.2 ))]
  · apply Finset.sum_bij (fun x _ => x.1.2)
    · simp
    · aesop
    · simp
    · simp
  · aesop

/-- The isometry V_rho from the paper. -/
noncomputable def V_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix ((dA × dB) × dB) dA ℂ :=
  let ρA_inv_sqrt := ρAB.traceRight⁻¹.sqrt
  let ρAB_sqrt := ρAB.sqrt
  let I_B := (1 : Matrix dB dB ℂ)
  let term1 := ρAB_sqrt.mat ⊗ₖ I_B
  let term2 := map_to_tensor_MES dA dB
  term1 * term2 * ρA_inv_sqrt.mat

open scoped MatrixOrder ComplexOrder

/-- The isometry V_sigma from the paper. -/
noncomputable def V_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dB × (dB × dC)) dC ℂ :=
  (V_rho (σBC.reindex (Equiv.prodComm dB dC))).reindex
    ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)))
    (Equiv.refl _)

/--
V_rho^H * V_rho simplifies to sandwiching the traceRight by the inverse square root.
-/
lemma V_rho_conj_mul_self_eq (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    let ρA := ρAB.traceRight
    let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
    (V_rho ρAB)ᴴ * (V_rho ρAB) = ρA_inv_sqrt * ρAB.traceRight.mat * ρA_inv_sqrt := by
  sorry

/--
The partial trace (left) of a positive definite matrix is positive definite.
-/
lemma PosDef_traceRight [Nonempty dB] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceRight.mat.PosDef := by
  have h_trace_right_pos_def : ∀ (x : EuclideanSpace ℂ dA), x ≠ 0 → 0 < ∑ k : dB, (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) := by
    intro x hx_ne_zero
    have h_inner_pos : ∀ k : dB, 0 ≤ (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) := by
      have := hA.2;
      intro k
      specialize this ( fun i => if h : i.2 = k then x i.1 else 0 )
      simp_all only [ne_eq, dite_eq_ite, dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec,
        HermitianMat.mat_apply, mul_ite, mul_zero, HermitianMat.val_eq_coe, Matrix.submatrix_apply]
      convert this ( show ( fun i : dA × dB => if i.2 = k then x i.1 else 0 ) ≠ 0 from fun h => hx_ne_zero <| by ext i; simpa using congr_fun h ( i, k ) ) |> le_of_lt using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i : dA => ( i, k ) ) Finset.univ ) ) ] <;> simp [ Finset.sum_image, Finset.sum_ite ];
      · refine' Finset.sum_congr rfl fun i hi => _;
        refine' congr_arg _ ( Finset.sum_bij ( fun j _ => ( j, k ) ) _ _ _ _ ) <;> simp
      · exact fun a b hb => Or.inl fun h => False.elim <| hb <| h.symm;
    obtain ⟨k, hk⟩ : ∃ k : dB, (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) > 0 := by
      have := hA.2 ( fun i => x i.1 * ( if i.2 = Classical.arbitrary dB then 1 else 0 ) )
      simp_all only [ne_eq, dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec,
        HermitianMat.val_eq_coe, Matrix.submatrix_apply, HermitianMat.mat_apply, mul_ite, mul_one, mul_zero]
      contrapose! this
      simp_all only [ne_eq, funext_iff, Pi.zero_apply, ite_eq_right_iff, Prod.forall, forall_eq,
        not_forall, Finset.sum_ite, Finset.sum_const_zero, add_zero] ;
      refine' ⟨ Function.ne_iff.mp hx_ne_zero, _ ⟩;
      convert this ( Classical.arbitrary dB ) using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.univ.image fun i : dA => ( i, Classical.arbitrary dB ) ) ) ]
      · simp only [Finset.coe_univ, Prod.mk.injEq, and_true, implies_true, Set.injOn_of_eq_iff_eq,
          Finset.sum_image, ↓reduceIte, gt_iff_lt]
        congr! 3;
        refine' Finset.sum_bij ( fun y hy => y.1 ) _ _ _ _ <;> simp
      · simp only [Finset.mem_univ, Finset.mem_image, true_and, not_exists, ne_eq, mul_eq_zero,
          map_eq_zero, ite_eq_right_iff, forall_const, Prod.forall, Prod.mk.injEq, not_and, forall_eq]
        exact fun a b hb => Or.inl fun h => False.elim <| hb <| h.symm ▸ rfl
    exact lt_of_lt_of_le hk ( Finset.single_le_sum ( fun k _ => h_inner_pos k ) ( Finset.mem_univ k ) );
  refine' ⟨A.traceRight.2, fun x hx => _ ⟩;
  · convert h_trace_right_pos_def x hx using 1;
    unfold HermitianMat.traceRight
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, HermitianMat.mat_mk, HermitianMat.val_eq_coe]
    simp only [Matrix.mulVec, dotProduct, mul_comm, Matrix.submatrix_apply, HermitianMat.mat_apply];
    simp only [Matrix.traceRight, HermitianMat.mat_apply, Matrix.of_apply, mul_comm, Finset.mul_sum]
    rw [Finset.sum_comm_cycle]

lemma PosDef_traceLeft [Nonempty dA] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceLeft.mat.PosDef := by
  exact PosDef_traceRight (A.reindex (Equiv.prodComm _ _)) (hA.reindex _)

/--
V_rho is an isometry.
-/
theorem V_rho_isometry [Nonempty dB] (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    (V_rho ρAB)ᴴ * (V_rho ρAB) = 1 := by
  -- Since ρA is positive definite, we can use the fact that ρA_inv_sqrt * ρA * ρA_inv_sqrt = I.
  have h_pos_def : (ρAB.traceRight⁻¹.sqrt : Matrix dA dA ℂ) * (ρAB.traceRight : Matrix dA dA ℂ) * (ρAB.traceRight⁻¹.sqrt : Matrix dA dA ℂ) = 1 := by
    convert HermitianMat.sqrt_inv_mul_self_mul_sqrt_inv_eq_one _;
    exact PosDef_traceRight _ hρ
  rw [← h_pos_def]
  sorry

/--
V_sigma is an isometry.
-/
theorem V_sigma_isometry [Nonempty dB] (σBC : HermitianMat (dB × dC) ℂ) (hσ : σBC.mat.PosDef) :
    (V_sigma σBC).conjTranspose * (V_sigma σBC) = 1 := by
  simp [V_sigma]
  exact V_rho_isometry _ (hσ.reindex _)

/-
Definition of W_mat with correct reindexing.
-/
open HermitianMat
open scoped MatrixOrder

variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC]

/-- The operator W from the paper, defined as a matrix product. -/
noncomputable def W_mat (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) : Matrix ((dA × dB) × dC) ((dA × dB) × dC) ℂ :=
  let ρA := ρAB.traceRight
  let σC := σBC.traceLeft
  let ρAB_sqrt := (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ)
  let σC_inv_sqrt := (σC⁻¹.sqrt : Matrix dC dC ℂ)
  let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
  let σBC_sqrt := (σBC.sqrt : Matrix (dB × dC) (dB × dC) ℂ)

  let term1 := ρAB_sqrt ⊗ₖ σC_inv_sqrt
  let term2 := ρA_inv_sqrt ⊗ₖ σBC_sqrt
  let term2_reindexed := term2.reindex (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm

  term1 * term2_reindexed

/--
The operator norm of a matrix product is at most the product of the operator norms.
-/
theorem Matrix.opNorm_mul_le {l m n 𝕜 : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [RCLike 𝕜]
    (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    Matrix.opNorm (A * B) ≤ Matrix.opNorm A * Matrix.opNorm B := by
  have h_opNorm_mul_le : ∀ (A : Matrix l m 𝕜) (B : Matrix m n 𝕜), Matrix.opNorm (A * B) ≤ Matrix.opNorm A * Matrix.opNorm B := by
    intro A B
    have h_comp : Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
      ext; simp [toEuclideanLin]
    convert ContinuousLinearMap.opNorm_comp_le ( Matrix.toEuclideanLin A |> LinearMap.toContinuousLinearMap ) ( Matrix.toEuclideanLin B |> LinearMap.toContinuousLinearMap ) using 1;
    unfold Matrix.opNorm;
    exact congr_arg _ ( by aesop );
  exact h_opNorm_mul_le A B

theorem Matrix.opNorm_reindex_proven {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (e : m ≃ l) (f : n ≃ p) (A : Matrix m n 𝕜) :
    Matrix.opNorm (A.reindex e f) = Matrix.opNorm A := by
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ 0, fun c hc => hc.1 ⟩;
    · refine' ⟨ norm_nonneg _, fun x => _ ⟩;
      convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( Matrix.toEuclideanLin A ) ) ( fun i => x ( f i ) ) using 1;
      · simp [ Matrix.toEuclideanLin, EuclideanSpace.norm_eq ];
        rw [ ← Equiv.sum_comp e.symm ] ; aesop;
      · simp [ EuclideanSpace.norm_eq, Matrix.opNorm ];
        exact Or.inl ( by rw [ ← Equiv.sum_comp f ] );
  · refine' ContinuousLinearMap.opNorm_le_bound _ _ fun a => _;
    · exact ContinuousLinearMap.opNorm_nonneg _;
    · convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( toEuclideanLin ( Matrix.reindex e f A ) ) ) ( fun i => a ( f.symm i ) ) using 1;
      · simp [ EuclideanSpace.norm_eq, Matrix.toEuclideanLin ];
        rw [ ← Equiv.sum_comp e.symm ] ; simp [ Matrix.mulVec, dotProduct ] ;
        grind;
      · congr! 2;
        simp [ EuclideanSpace.norm_eq]
        conv_lhs => rw [ ← Equiv.sum_comp f.symm ] ;

/--
Define U_rho as the Kronecker product of V_rho and the identity.
-/
noncomputable def U_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix (((dA × dB) × dB) × dC) (dA × dC) ℂ :=
  Matrix.kronecker (V_rho ρAB) (1 : Matrix dC dC ℂ)

/--
Define U_sigma as the Kronecker product of the identity and V_sigma.
-/
noncomputable def U_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dA × (dB × (dB × dC))) (dA × dC) ℂ :=
  Matrix.kronecker (1 : Matrix dA dA ℂ) (V_sigma σBC)

/--
The operator norm of the conjugate transpose is equal to the operator norm.
-/
theorem Matrix.opNorm_conjTranspose_eq_opNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) :
    Matrix.opNorm Aᴴ = Matrix.opNorm A := by
  unfold Matrix.opNorm
  rw [← ContinuousLinearMap.adjoint.norm_map (toEuclideanLin A).toContinuousLinearMap]
  rw [toEuclideanLin_conjTranspose_eq_adjoint]
  rfl
