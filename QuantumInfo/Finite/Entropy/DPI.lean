/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.Relative
import QuantumInfo.ForMathlib.HermitianMat.Sqrt

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ} {ρ σ : MState d}

open scoped InnerProductSpace RealInnerProductSpace HermitianMat

/-!
# DPI (Data Processing Inequality)

The Data Processing Inequality (DPI) for the sandwiched Rényi relative entropy, and
as a consequence, the quantum relative entropy.
-/

open scoped Matrix ComplexOrder
open BigOperators

/-- The Schatten p-norm of a matrix for p \in [1, \infty). -/
noncomputable def schattenNorm (p : ℝ) (A : Matrix d d ℂ) : ℝ :=
  let A_dag_A : HermitianMat d ℂ := ⟨A.conjTranspose * A, by
    have h := Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose
    rwa [Matrix.conjTranspose_conjTranspose] at h⟩
  (A_dag_A.cfc (fun x => x ^ (p/2))).trace ^ (1/p)

/-- The weighted norm \|X\|_{p, σ} defined in the paper. -/
noncomputable def weighted_norm (p : ℝ) (σ : MState d) (X : Matrix d d ℂ) : ℝ :=
  let σ_pow : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (1 / (2 * p)))
  schattenNorm p (σ_pow.mat * X * σ_pow.mat)

/-- The spectral norm (operator norm) of a matrix. -/
noncomputable def spectralNorm_mat (A : Matrix d d ℂ) : ℝ :=
  if h : Finset.univ.Nonempty then
    let A_dag_A : HermitianMat d ℂ := ⟨A.conjTranspose * A, by
      have h := Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose
      rwa [Matrix.conjTranspose_conjTranspose] at h⟩
    Real.sqrt ((Finset.univ.image A_dag_A.H.eigenvalues).max' (Finset.Nonempty.image h _))
  else 0

/-- The weighted norm for p = \infty. -/
noncomputable def weighted_norm_infty (_ : MState d) (X : Matrix d d ℂ) : ℝ :=
  spectralNorm_mat X

/-- The map Γ_σ(X) = σ^{1/2} X σ^{1/2}. -/
noncomputable def Gamma (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  let σ_half : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (1/2 : ℝ))
  σ_half.mat * X * σ_half.mat

/-- The inverse map Γ_σ^{-1}(X) = σ^{-1/2} X σ^{-1/2}. -/
noncomputable def Gamma_inv (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  let σ_inv_half : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (-1/2 : ℝ))
  σ_inv_half.mat * X * σ_inv_half.mat

/-- The operator T = Γ_{Φ(σ)}^{-1} ∘ Φ ∘ Γ_σ. -/
noncomputable def T_op (Φ : CPTPMap d d₂) (σ : MState d) (X : Matrix d d ℂ) : Matrix d₂ d₂ ℂ :=
  Gamma_inv (Φ σ) (Φ.map (Gamma σ X))

/-- The induced norm of a map Ψ: M_d -> M_d2 with respect to weighted norms. -/
noncomputable def induced_norm (p : ℝ) (σ : MState d) (Φ : CPTPMap d d₂) (Ψ : Matrix d d ℂ → Matrix d₂ d₂ ℂ) : ℝ :=
  sSup { weighted_norm p (Φ σ) (Ψ X) / weighted_norm p σ X | (X : Matrix d d ℂ) (_ : weighted_norm p σ X ≠ 0) }

/-
The induced norm of a map Ψ with respect to the weighted infinity norm.
-/
noncomputable def induced_norm_infty_map (σ : MState d) (Φ : CPTPMap d d₂) (Ψ : Matrix d d ℂ → Matrix d₂ d₂ ℂ) : ℝ :=
  sSup { weighted_norm_infty (Φ σ) (Ψ X) / weighted_norm_infty σ X | (X : Matrix d d ℂ) (_ : weighted_norm_infty σ X ≠ 0) }

/-
The operator T = Γ_{Φ(σ)}^{-1} ∘ Φ ∘ Γ_σ as a linear map.
-/
noncomputable def T_map (σ : MState d) (Φ : CPTPMap d d₂) : MatrixMap d d₂ ℂ :=
  { toFun := fun X => T_op Φ σ X,
    map_add' := fun X Y => by
      unfold T_op Gamma Gamma_inv
      simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := fun c X => by
      unfold T_op
      simp
      unfold Gamma Gamma_inv
      simp [mul_assoc]
  }

/-
Gamma_map is the conjugation by the square root of sigma.
-/
noncomputable def Gamma_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M.cfc (fun x => x ^ (1/2 : ℝ))).mat

lemma Gamma_map_eq (σ : MState d) (X : Matrix d d ℂ) :
    Gamma_map σ X = Gamma σ X := by
  ext; simp [ Gamma_map, Gamma ];
  apply_rules [ IsSelfAdjoint.cfc ]

/-
Gamma_map is completely positive.
-/
lemma Gamma_map_CP (σ : MState d) : (Gamma_map σ).IsCompletelyPositive := by
  have := @MatrixMap.conj_isCompletelyPositive;
  exact this _

/-
Gamma_inv_map is the conjugation by the inverse square root of sigma.
-/
noncomputable def Gamma_inv_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat

lemma Gamma_inv_map_eq (σ : MState d) (X : Matrix d d ℂ) :
    Gamma_inv_map σ X = Gamma_inv σ X := by
  simp [Gamma_inv_map, Gamma_inv];
  congr;
  apply IsSelfAdjoint.cfc

/-
The inverse square root of sigma.
-/
noncomputable def sigma_inv_sqrt (σ : MState d) : Matrix d d ℂ :=
  (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat

/-
Gamma_inv_map is conjugation by sigma_inv_sqrt.
-/
lemma Gamma_inv_map_eq_conj (σ : MState d) :
    Gamma_inv_map σ = MatrixMap.conj (sigma_inv_sqrt σ) := by
  exact rfl

/-
Gamma_inv_map is completely positive.
-/
lemma Gamma_inv_map_CP (σ : MState d) : (Gamma_inv_map σ).IsCompletelyPositive := by
  convert MatrixMap.conj_isCompletelyPositive _;
  · infer_instance;
  · infer_instance

/-
T_map is the composition of Gamma_inv_map, Phi, and Gamma_map.
-/
lemma T_map_eq_comp (σ : MState d) (Φ : CPTPMap d d₂) :
    T_map σ Φ = (Gamma_inv_map (Φ σ)).comp (Φ.map.comp (Gamma_map σ)) := by
  ext;
  unfold T_map;
  simp [T_op]
  congr! 1;
  · exact funext fun x => Gamma_inv_map_eq ( Φ σ ) x ▸ rfl;
  · rw [ Gamma_map_eq ]

/-
T_map is completely positive.
-/
lemma T_is_CP (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsCompletelyPositive := by
  rw [ T_map_eq_comp ];
  apply MatrixMap.IsCompletelyPositive.comp;
  · apply MatrixMap.IsCompletelyPositive.comp;
    · exact Gamma_map_CP σ;
    · exact Φ.cp;
  · exact Gamma_inv_map_CP (Φ σ)

/-
T_map is positive.
-/
lemma T_is_positive (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsPositive := by
  exact T_is_CP σ Φ |> fun h => h.IsPositive

/-
The weighted 1-norm of X is the trace norm of Gamma(X).
-/
lemma weighted_norm_one_eq_trace_norm_Gamma (σ : MState d) (X : Matrix d d ℂ) :
    weighted_norm 1 σ X = schattenNorm 1 (Gamma σ X) := by
  unfold weighted_norm Gamma;
  norm_num

/-
The induced norm of a super-operator between weighted Schatten spaces.
-/
noncomputable def general_induced_norm
    (p q : ℝ) (σ : MState d) (σ' : MState d₂)
    (Ψ : MatrixMap d d₂ ℂ) : ℝ :=
  sSup { weighted_norm q σ' (Ψ X) / weighted_norm p σ X | (X : Matrix d d ℂ) (_ : weighted_norm p σ X ≠ 0) }

/-
Multiplication property for HermitianMat functional calculus.
-/
lemma HermitianMat.cfc_mul {d : Type*} [Fintype d] [DecidableEq d]
    (A : HermitianMat d ℂ) (f g : ℝ → ℝ) :
    (A.cfc f).mat * (A.cfc g).mat = (A.cfc (fun x => f x * g x)).mat := by
  symm
  apply mat_cfc_mul

/-
Gamma of identity is sigma.
-/
lemma Gamma_one (σ : MState d) : Gamma σ 1 = σ.M.mat := by
  have h_gamma_one : (σ.M.cfc (fun x => x^(1/2 : ℝ))).mat * (σ.M.cfc (fun x => x^(1/2 : ℝ))).mat = σ.M.cfc (fun x => x^(1/2 : ℝ) * x^(1/2 : ℝ)) := by
    symm
    exact HermitianMat.mat_cfc_mul σ.M ( fun x => x ^ ( 1 / 2 : ℝ ) ) ( fun x => x ^ ( 1 / 2 : ℝ ) )
  convert h_gamma_one using 1;
  · unfold Gamma; aesop;
  · norm_num [ ← Real.sqrt_eq_rpow, Real.sqrt_mul_self ( show 0 ≤ _ from _ ) ];
    have h_gamma_one : ∀ x ∈ spectrum ℝ σ.m, Real.sqrt x * Real.sqrt x = x := by
      intro x hx; rw [ Real.mul_self_sqrt ] ; exact (by
      rw [ spectrum.mem_iff ] at hx;
      exact Matrix.PosSemidef.pos_of_mem_spectrum σ.psd x hx);
    rw [ cfc ];
    split_ifs <;> simp_all
    · convert rfl;
      convert cfcHom_id _;
      ext x; aesop;
    · exact False.elim ( ‹IsSelfAdjoint σ.m → ¬ContinuousOn ( fun x => Real.sqrt x * Real.sqrt x ) ( spectrum ℝ σ.m ) › σ.M.prop <| ContinuousOn.mul ( Real.continuous_sqrt.continuousOn ) ( Real.continuous_sqrt.continuousOn ) )

/-
Gamma inverse of sigma is identity.
-/
lemma Gamma_inv_self (σ : MState d) (hσ : σ.m.PosDef) :
    Gamma_inv σ σ.M.mat = 1 := by
  -- We use `HermitianMat.cfc_mul` and the fact that $x^{-1/2} * x * x^{-1/2} = 1$ for $x > 0$.
  have h_gamma_inv_sigma : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => x ^ (-1/2 : ℝ) * x * x ^ (-1/2 : ℝ))).mat := by
    have h_gamma_inv_sigma : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.cfc id).mat * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => x ^ (-1/2 : ℝ) * x * x ^ (-1/2 : ℝ))).mat := by
      have h_gamma_inv_sigma : ∀ (f g h : ℝ → ℝ), ContinuousOn f (spectrum ℝ σ.M.mat) → ContinuousOn g (spectrum ℝ σ.M.mat) → ContinuousOn h (spectrum ℝ σ.M.mat) → (σ.M.cfc f).mat * (σ.M.cfc g).mat * (σ.M.cfc h).mat = (σ.M.cfc (fun x => f x * g x * h x)).mat := by
        intro f g h hf hg hh
        have h_gamma_inv_sigma : (σ.M.cfc f).mat * (σ.M.cfc g).mat = (σ.M.cfc (fun x => f x * g x)).mat := by
          symm
          convert HermitianMat.mat_cfc_mul σ.M f g using 1;
        rw [ h_gamma_inv_sigma, ← HermitianMat.mat_cfc_mul ];
        congr! 2
      apply_rules [ ContinuousOn.rpow, continuousOn_id, continuousOn_const ];
      · norm_num +zetaDelta at *;
        intro x hx h_zero
        have h_eigenvalue : ∃ v : d → ℂ, v ≠ 0 ∧ σ.m.mulVec v = x • v := by
          simp_all [ spectrum.mem_iff]
          contrapose! hx;
          exact Matrix.PosDef.isUnit hσ;
        obtain ⟨ v, hv_ne_zero, hv_eigenvalue ⟩ := h_eigenvalue; have := hσ.2 v; simp_all
      · norm_num +zetaDelta at *;
        intro x hx h_zero
        have h_eigenvalue : ∃ v : d → ℂ, v ≠ 0 ∧ σ.m.mulVec v = x • v := by
          simp_all [ spectrum.mem_iff]
          contrapose! hx;
          exact Matrix.PosDef.isUnit hσ;
        obtain ⟨ v, hv_ne_zero, hv_eigenvalue ⟩ := h_eigenvalue; have := hσ.2 v; simp_all
    convert h_gamma_inv_sigma using 1;
    ext i j ; simp [ Matrix.mul_apply]
  -- Since $x^{-1/2} * x * x^{-1/2} = 1$ for $x > 0$, we have $(σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => 1)).mat$.
  have h_gamma_inv_sigma_simplified : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => 1)).mat := by
    convert h_gamma_inv_sigma using 1;
    congr! 1;
    -- Since $x^{-1/2} * x * x^{-1/2} = 1$ for all $x > 0$, the functions are equal.
    have h_eq : ∀ x : ℝ, 0 < x → x ^ (-1 / 2 : ℝ) * x * x ^ (-1 / 2 : ℝ) = 1 := by
      intro x hx
      ring_nf
      norm_num [ hx.ne' ];
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul hx.le ] ; norm_num [ hx.ne' ];
      rw [ Real.rpow_neg_one, inv_mul_cancel₀ hx.ne' ];
    exact Eq.symm (HermitianMat.cfc_congr_of_posDef hσ h_eq);
  convert h_gamma_inv_sigma_simplified using 1;
  ext i j
  simp

/-
The matrix of the output state is the map applied to the input matrix.
-/
lemma CPTPMap_apply_MState_M (Φ : CPTPMap d d₂) (σ : MState d) :
    (Φ σ).M.mat = Φ.map σ.M.mat := by
  exact rfl

/-
The map T is unital.
-/
theorem T_map_unital (σ : MState d) (Φ : CPTPMap d d₂) (hΦσ : (Φ σ).m.PosDef) :
    (T_map σ Φ) 1 = 1 := by
  dsimp [T_map, T_op]
  rw [Gamma_one σ]
  rw [← CPTPMap_apply_MState_M]
  rw [Gamma_inv_self (Φ σ) hΦσ]

/-
The map T is completely positive.
-/
theorem T_map_is_CP_proof (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsCompletelyPositive := by
  apply T_is_CP

/-
Gamma composed with Gamma inverse is identity.
-/
lemma Gamma_Gamma_inv (σ : MState d) (hσ : σ.m.PosDef) (X : Matrix d d ℂ) :
    Gamma σ (Gamma_inv σ X) = X := by
  -- By definition of Gamma and Gamma_inv, we can simplify the expression.
  have h_simp : (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat * (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat = 1 := by
    symm
    convert HermitianMat.mat_cfc_mul _ _ _ using 1;
    · have h_gamma_gamma_inv : ∀ x ∈ spectrum ℝ σ.M.mat, x ^ (1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) = 1 := by
        intro x hx
        have hx_pos : 0 < x := by
          have := hσ.2;
          obtain ⟨v, hv⟩ : ∃ v : d → ℂ, v ≠ 0 ∧ σ.m.mulVec v = x • v := by
            rw [ spectrum.mem_iff ] at hx;
            simp_all [ Matrix.isUnit_iff_isUnit_det ];
            obtain ⟨ v, hv ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hx;
            simp_all [ sub_eq_iff_eq_add, Matrix.sub_mulVec ];
            exact ⟨ v, hv.1, hv.2.symm.trans ( by ext i; erw [ Matrix.mulVec_diagonal ] ; aesop ) ⟩;
          specialize this v hv.1;
          simp_all [ dotProduct];
          simp_all [ mul_assoc, mul_comm];
          simp_all [ mul_left_comm ( v _ ), Complex.mul_conj, Complex.normSq_eq_norm_sq ];
          norm_cast at this;
          exact lt_of_not_ge fun hx' => this.not_ge <| Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg hx' <| sq_nonneg _;
        rw [ ← Real.rpow_add hx_pos ] ; norm_num;
      rw [HermitianMat.cfc_congr (g := fun x ↦ 1)]
      · rw [ HermitianMat.cfc_const ]
        norm_num
      · exact fun x hx => h_gamma_gamma_inv x hx;
  unfold Gamma Gamma_inv; simp_all [ ← mul_assoc ] ;
  simp_all [ mul_assoc, Matrix.mul_eq_one_comm.mp h_simp ]

/-
If a Hermitian matrix is bounded by M*I, then all its eigenvalues are at most M.
-/
theorem HermitianMat.le_smul_one_imp_eigenvalues_le (A : HermitianMat d ℂ) (M : ℝ)
    (h : A ≤ M • (1 : HermitianMat d ℂ)) (i : d) :
    A.H.eigenvalues i ≤ M := by
  -- By definition of eigenvalues, for any unit vector $v$, we have $\langle v, A v \rangle \leq M$.
  have h_eigenvalue_le_M_step : ∀ (v : EuclideanSpace ℂ d), ‖v‖ = 1 → ⟪v, A.mat.mulVec v⟫_ℂ ≤ M := by
    intro v hv
    have h_inner : ⟪v, A.mat.mulVec v⟫_ℂ ≤ ⟪v, (M • 1 : Matrix d d ℂ).mulVec v⟫_ℂ := by
      have h_inner : ⟪v, ((M • 1 : Matrix d d ℂ) - A.mat).mulVec v⟫_ℂ ≥ 0 := by
        have h_inner_le_M : ∀ (X : HermitianMat d ℂ), X ≥ 0 → ∀ (v : EuclideanSpace ℂ d), ⟪v, X.mat.mulVec v⟫_ℂ ≥ 0 := by
          intro X hX v; exact (by
          have := hX.2 v; simp_all [ Matrix.mulVec, dotProduct ] ;
          convert this using 1;
          exact Finset.sum_congr rfl fun _ _ => by rw [ Matrix.mulVec, dotProduct ] ; simp [  mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;);
        convert h_inner_le_M ⟨ _, _ ⟩ _ v;
        all_goals norm_num [ HermitianMat.le_iff ] at *;
        · convert h.1;
        · exact h;
      simp_all [ Matrix.sub_mulVec]
    simp_all [ EuclideanSpace.norm_eq ];
    convert h_inner using 1;
    simp [ Matrix.mulVec, dotProduct, inner ];
    simp [ Matrix.one_apply,mul_assoc, mul_comm];
    simp [ mul_left_comm ( v _ ), ← Finset.mul_sum _ _ _ ];
    simp [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    norm_cast ; aesop;
  have := A.H.eigenvectorBasis.orthonormal;
  have := this.1 i;
  have := h_eigenvalue_le_M_step ( A.H.eigenvectorBasis i ) this;
  rw [ show A.mat.mulVec _ = ( Matrix.IsHermitian.eigenvalues A.H i : ℂ ) • ( Matrix.IsHermitian.eigenvectorBasis A.H i ) from ?_ ] at this;
  · simp_all
  · convert A.H.mulVec_eigenvectorBasis i using 1

set_option maxHeartbeats 0 in
open MatrixOrder in
/-
If all eigenvalues of a Hermitian matrix are at most M, then the matrix is bounded by M*I.
-/
theorem HermitianMat.eigenvalues_le_imp_le_smul_one (A : HermitianMat d ℂ) (M : ℝ)
    (h : ∀ i, A.H.eigenvalues i ≤ M) :
    A ≤ M • (1 : HermitianMat d ℂ) := by
  have := A.H.spectral_theorem.symm;
  -- Since $A$ is Hermitian, we can write it as $A = UDU^*$ where $U$ is unitary and $D$ is diagonal with eigenvalues $\lambda_i$.
  have h_decomp : ∃ U : Matrix d d ℂ, U * star U = 1 ∧ ∃ D : Matrix d d ℂ, D.IsDiag ∧ A = U * D * star U ∧ ∀ i, D i i ≤ M := by
    refine' ⟨ _, _, _, _, this.symm, _ ⟩;
    · simp
    · exact Matrix.isDiag_diagonal (RCLike.ofReal ∘ (H A).eigenvalues);
    · aesop;
  obtain ⟨U, hU_unitary, D, hD_diag, hA_eq, hD_le⟩ := h_decomp;
  have hA_le : U * D * star U ≤ U * (M • 1) * star U := by
    constructor;
    · replace hA_eq := congr_arg Star.star hA_eq; simp_all [ Matrix.IsHermitian, Matrix.mul_assoc ] ;
      convert congr_arg Star.star hA_eq using 1 ; simp
      · convert hA_eq.symm using 1;
        · ext i j; simp [ Matrix.mul_apply ] ;
        · exact A.2.symm;
      · simp [ ← Matrix.mul_assoc];
    · intro x
      have h_inner : star x ⬝ᵥ (U * M • 1 * star U - U * D * star U) *ᵥ x = star (star U *ᵥ x) ⬝ᵥ (M • 1 - D) *ᵥ (star U *ᵥ x) := by
        simp [ Matrix.mul_assoc, Matrix.sub_mul, Matrix.dotProduct_mulVec]
        simp [ Matrix.vecMul, dotProduct];
        simp [ Matrix.mul_apply, mul_sub, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        simp [ Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        exact congrArg₂ _ ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) ) ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) ) );
      have h_inner_nonneg : ∀ y : d → ℂ, 0 ≤ star y ⬝ᵥ (M • 1 - D) *ᵥ y := by
        intro y
        have h_inner_nonneg : ∀ i, 0 ≤ (M - D i i) * (star (y i) * y i) := by
          intro i
          have h_inner_nonneg : 0 ≤ (M - D i i) * (star (y i) * y i) := by
            have h_inner_nonneg : 0 ≤ (M - D i i) * (y i * star (y i)) := by
              have h_inner_nonneg : 0 ≤ (M - D i i) * (y i * star (y i)) := by
                have h_inner_nonneg : 0 ≤ (M - D i i) := by
                  exact sub_nonneg_of_le ( hD_le i )
                have h_inner_nonneg' : 0 ≤ (y i * star (y i)) := by
                  simp [ Complex.mul_conj, Complex.normSq_eq_norm_sq ]
                exact mul_nonneg h_inner_nonneg h_inner_nonneg';
              exact h_inner_nonneg
            simpa only [ mul_comm ] using h_inner_nonneg;
          exact h_inner_nonneg;
        simp_all [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
        rw [ Finset.sum_comm ];
        refine' Finset.sum_nonneg fun i _ => _;
        rw [ Finset.sum_eq_single i ] <;> simp_all [ Matrix.one_apply ];
        exact fun j hj => Or.inr <| Or.inl <| hD_diag hj;
      exact h_inner.symm ▸ h_inner_nonneg _;
  convert hA_le using 1;
  constructor <;> intro h <;> rw [ ← hA_eq ] at * <;> simp_all [ Matrix.mul_assoc ];
  exact hA_le

/-- The block matrix [[1, X], [X†, X†X]] is positive semidefinite. -/
theorem block_matrix_posSemidef {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix k n ℂ) (Y : Matrix k m ℂ):
    (Matrix.fromBlocks (Yᴴ * Y) (Yᴴ * X) (Xᴴ * Y) (Xᴴ * X)).PosSemidef := by
  set Z : Matrix (m ⊕ n) (m ⊕ n) ℂ := Matrix.fromBlocks (Yᴴ * Y) (Yᴴ * X) (Xᴴ * Y) (Xᴴ * X)
  have hZ : Z = Matrix.fromBlocks (m := k) Yᴴ 0 Xᴴ 0 * Matrix.fromBlocks Y X 0 0 := by
    simp +zetaDelta [Matrix.fromBlocks_multiply]
  have hZ : Z = (Matrix.fromBlocks (o := k) Y X 0 0)ᴴ * Matrix.fromBlocks Y X 0 0 := by
    rw [hZ]
    ext i j ; simp [ Matrix.mul_apply];
    cases i <;> cases j <;> simp [ Matrix.fromBlocks ];
  rw [hZ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem block_matrix_one_posSemidef {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (X : Matrix m n ℂ) :
    (Matrix.fromBlocks 1 X Xᴴ (Xᴴ * X)).PosSemidef := by
  simpa using block_matrix_posSemidef X (1 : Matrix m m ℂ)

/-- The Data Processing Inequality for the Sandwiched Renyi relative entropy.
Proved in `https://arxiv.org/pdf/1306.5920`. Seems kind of involved. -/
theorem sandwichedRenyiEntropy_DPI (hα : 1 ≤ α) (ρ σ : MState d) (Φ : CPTPMap d d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  --If we want, we can prove this just for 1 < α, and then use continuity (above) to take the limit as
  -- α → 1.
  sorry
