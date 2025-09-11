import QuantumInfo.ForMathlib.HermitianMat.Basic

--Matrix operations on RCLike matrices with the CFC

namespace HermitianMat

section CFC

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]

noncomputable nonrec def cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) : HermitianMat d 𝕜 :=
  ⟨cfc f A.toMat, cfc_predicate _ _⟩

@[simp]
theorem cfc_diagonal (g : d → ℝ) (f : ℝ → ℝ) :
    cfc (HermitianMat.diagonal g) f = HermitianMat.diagonal (f ∘ g) := by
  ext1
  dsimp [cfc, HermitianMat, HermitianMat.diagonal, HermitianMat.toMat]
  --Thanks Aristotle, for this mess
  rw [ _root_.cfc ];
  split_ifs;
  · -- By definition of the continuous functional calculus for diagonal matrices, we have that the cfc of a diagonal matrix is the diagonal matrix with the function applied to each entry.
    change cfcHom (show IsSelfAdjoint (Matrix.diagonal (fun x => (g x : ℂ))) from by
      -- Since $g(x)$ is real, the diagonal matrix with entries $g(x)$ is Hermitian.
      -- Since the entries of the diagonal matrix are real, the conjugate transpose of the diagonal matrix is the same as the original matrix.
      simp [IsSelfAdjoint, Star.star, Matrix.conjTranspose]
      ext i j; by_cases hij : i = j <;> aesop) ⟨fun x => f x, continuous_of_discreteTopology⟩ = Matrix.diagonal (fun x => (f (g x) : ℂ))
    erw [ cfcHom_eq_of_continuous_of_map_id ];
    rotate_left;
    refine' { .. };
    use fun f => Matrix.diagonal fun x => f ⟨ g x, by
      intro h;
      obtain ⟨ u, hu ⟩ := h.exists_left_inv;
      replace hu := congr_arg ( fun m => m x x ) hu ; simp_all ( config := { decide := Bool.true } ) [ Matrix.mul_apply ];
      simp_all ( config := { decide := Bool.true } ) [ Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply ] ⟩;
    simp +zetaDelta only [ContinuousMap.one_apply, Complex.ofReal_one, Matrix.diagonal_one] at *;
    all_goals norm_num [ funext_iff, Matrix.diagonal ];
    all_goals norm_num [ ← Matrix.ext_iff, Finset.mul_sum _ _ _, Finset.sum_mul, Matrix.mul_apply, Matrix.diagonal ];
    · intros
      split <;> simp_all only
    · intros
      split <;> simp_all only [add_zero]
    · exact fun r i j => rfl;
    · intros
      split
      · simp_all only [↓reduceIte, Complex.conj_ofReal]
      · split <;> simp_all only [not_true_eq_false, map_zero]
    · refine' continuous_pi_iff.mpr fun i => _
      exact continuous_apply i |> Continuous.comp <| by continuity;
  · rename_i h
    rw [not_and] at h
    -- Since the matrix is diagonal with real entries, it is self-adjoint.
    have h_self_adjoint : IsSelfAdjoint (Matrix.diagonal (fun x => (g x : ℂ))) := by
      change Matrix.conjTranspose _ = _
      simp [Matrix.conjTranspose]
    apply_mod_cast False.elim ( h h_self_adjoint _ );
    exact continuousOn_iff_continuous_restrict.mpr continuous_of_discreteTopology

theorem cfc_eigenvalues (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    ∃ (e : d ≃ d), (A.cfc f).H.eigenvalues = f ∘ A.H.eigenvalues ∘ e :=
  A.H.cfc_eigenvalues f

open ComplexOrder in
theorem cfc_PosDef (A : HermitianMat d ℂ) (f : ℝ → ℝ) :
    (A.cfc f).toMat.PosDef ↔ ∀ i, 0 < f (A.H.eigenvalues i) := by
  rw [(A.cfc f).H.posDef_iff_eigenvalues_pos]
  obtain ⟨e, he⟩ := A.cfc_eigenvalues f
  rw [he]
  refine ⟨fun h i ↦ ?_, fun h i ↦ h (e i)⟩
  convert h (e.symm i)
  simp

end CFC

noncomputable section CFC

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Matrix power of a positive semidefinite matrix, as given by the elementwise
  real power of the diagonal in a diagonalized form.

  Note that this has the usual `Real.rpow` caveats, such as 0 to the power -1 giving 0. -/
def rpow (A : HermitianMat n 𝕜) (p : ℝ) : HermitianMat n 𝕜 :=
  cfc A (Real.rpow · p)

noncomputable instance instRPow : Pow (HermitianMat n 𝕜) ℝ :=
  ⟨rpow⟩

theorem pow_eq_rpow (A : HermitianMat n 𝕜) (p : ℝ) : A ^ p = A.rpow p :=
  rfl

theorem diagonal_pow (f : n → ℝ) (p : ℝ) :
    (diagonal f) ^ p = diagonal fun i => (f i) ^ p := by
  simp [pow_eq_rpow, rpow]
  rfl

open ComplexOrder in
theorem rpow_PosSemidef {A : HermitianMat n 𝕜} (hA : A.val.PosSemidef) (p : ℝ) : (A ^ p).val.PosSemidef := by
  --TODO: Should prove the more general versions for f mapping ℝ≥0 → ℝ≥0 (if hA is PSD) or ℝ → ℝ≥0.
  change (_root_.cfc _ A.toMat).PosSemidef
  rw [A.H.cfc_eq, Matrix.IsHermitian.cfc]
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
  cfc A Real.log

end CFC
