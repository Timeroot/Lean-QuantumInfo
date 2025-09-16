import QuantumInfo.ForMathlib.HermitianMat.Order

--Matrix operations on HermitianMats with the CFC

namespace Matrix

open ComplexOrder

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]

@[simp]
theorem cfc_diagonal (g : d → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun x ↦ (g x : 𝕜))) = diagonal (RCLike.ofReal ∘ f ∘ g) := by
  --Thanks Aristotle
  have h_self_adjoint : _root_.IsSelfAdjoint (diagonal (fun x => (g x : 𝕜))) := by
      change Matrix.conjTranspose _ = _
      simp [Matrix.conjTranspose]
  --TODO cfc_cont_tac
  rw [cfc, dif_pos ⟨h_self_adjoint, continuousOn_iff_continuous_restrict.mpr <| by fun_prop⟩]
  rw [cfcHom_eq_of_continuous_of_map_id]
  rotate_left
  · refine' { .. }
    use fun f ↦ Matrix.diagonal fun x ↦ f ⟨g x, (by
      simpa [algebraMap_eq_diagonal, diagonal_apply] using
        congr_arg (· x x) ·.exists_left_inv.choose_spec
      )⟩
    · simp
    · simp [diagonal, ← Matrix.ext_iff, mul_apply]
      grind
    · simp
    · simp [diagonal, funext_iff]
      grind [add_zero]
    · simp [← ext_iff, diagonal]
      exact fun r i j ↦ rfl
    · simp [← ext_iff, diagonal]
      grind [RCLike.conj_ofReal, map_zero]
  · dsimp [diagonal]
    continuity
  · simp [diagonal]
  · simp [diagonal]

--PULLOUT
theorem PosSemidef.pos_of_mem_spectrum {A : Matrix d d 𝕜} (hA : A.PosSemidef) (r : ℝ) :
    r ∈ spectrum ℝ A → 0 ≤ r := by
  intro hr
  rw [hA.left.spectrum_real_eq_range_eigenvalues] at hr
  rcases hr with ⟨i, rfl⟩
  exact hA.eigenvalues_nonneg i

--PULLOUT
theorem PosSemidef.pow_add {A : Matrix d d 𝕜} (hA : A.PosSemidef) {x y : ℝ} (hxy : x + y ≠ 0) :
    cfc (· ^ (x + y) : ℝ → ℝ) A = cfc (fun r ↦ r ^ x * r ^ y : ℝ → ℝ) A := by
  refine cfc_congr fun r hr ↦ ?_
  exact Real.rpow_add' (hA.pos_of_mem_spectrum r hr) hxy

--PULLOUT
theorem PosSemidef.pow_mul {A : Matrix d d 𝕜} {x y : ℝ} (hA : A.PosSemidef) :
    cfc (· ^ (x * y) : ℝ → ℝ) A = cfc (fun r ↦ (r ^ x) ^ y : ℝ → ℝ) A := by
  refine cfc_congr fun r hr ↦ ?_
  exact Real.rpow_mul (hA.pos_of_mem_spectrum r hr) x y

end Matrix


namespace HermitianMat

section CFC

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]

noncomputable nonrec def cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) : HermitianMat d 𝕜 :=
  ⟨cfc f A.toMat, cfc_predicate _ _⟩

@[simp]
theorem cfc_diagonal (g : d → ℝ) (f : ℝ → ℝ) :
    cfc (HermitianMat.diagonal g) f = HermitianMat.diagonal (f ∘ g) := by
  ext1
  exact Matrix.cfc_diagonal g f

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

theorem coe_pow_eq_cfc (A : HermitianMat n 𝕜) (p : ℝ) :
    (A ^ p).toMat = _root_.cfc (· ^ p : ℝ → ℝ) A.toMat :=
  rfl

theorem diagonal_pow (f : n → ℝ) (p : ℝ) :
    (diagonal f) ^ p = diagonal fun i => (f i) ^ p := by
  simp [pow_eq_rpow, rpow]
  rfl

@[simp]
theorem pow_one (A : HermitianMat n 𝕜) : A ^ (1 : ℝ) = A := by
  rw [HermitianMat.ext_iff, coe_pow_eq_cfc]
  convert cfc_id ℝ A.toMat using 2
  simp; rfl

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

theorem coe_rpow_add {A : HermitianMat n 𝕜} (hA : 0 ≤ A) {p q : ℝ} (hpq : p + q ≠ 0) :
    (A ^ (p + q)).toMat = (A ^ p).toMat * (A ^ q).toMat := by
  rw [zero_le_iff] at hA
  rw [coe_pow_eq_cfc, coe_pow_eq_cfc, coe_pow_eq_cfc]
  rw [hA.pow_add hpq]
  apply cfc_mul
  --TODO cfc_cont_tac
  · exact continuousOn_iff_continuous_restrict.mpr <| by fun_prop
  · exact continuousOn_iff_continuous_restrict.mpr <| by fun_prop

theorem coe_rpow_mul {A : HermitianMat n 𝕜} (hA : 0 ≤ A) {p q : ℝ} :
    (A ^ (p * q)) = ((A ^ p) ^ q) := by
  rw [zero_le_iff] at hA
  rw [HermitianMat.ext_iff, coe_pow_eq_cfc, coe_pow_eq_cfc, coe_pow_eq_cfc]
  rw [hA.pow_mul]
  apply cfc_comp (g := (· ^ q : ℝ → ℝ)) (f := (· ^ p : ℝ → ℝ)) A.toMat (hg := ?_) (hf := ?_)
  --TODO cfc_cont_tac
  · exact continuousOn_iff_continuous_restrict.mpr <| by fun_prop
  · exact continuousOn_iff_continuous_restrict.mpr <| by fun_prop

--PULLOUT
@[simp]
theorem conjTranspose_toMat {n α : Type*} [AddGroup α] [StarAddMonoid α]
  (A : HermitianMat n α) :
    A.toMat.conjTranspose = A :=
  A.H

theorem conj_rpow {A : HermitianMat n 𝕜} (hA : 0 ≤ A) {p q : ℝ}
  (h₁ : p + q ≠ 0) (h₂ : p + 2 * q ≠ 0) :
    (A ^ p).conj (A ^ q) = A ^ (p + 2 * q) := by
  simp only [HermitianMat.ext_iff, conj, val_eq_coe, mk_toMat, conjTranspose_toMat]
  rw [← coe_rpow_add hA, ← coe_rpow_add hA]
  <;> ring_nf at * <;> assumption

/-- Matrix logarithm (base e) of a Hermitian matrix, as given by the elementwise
  real logarithm of the diagonal in a diagonalized form, using `Real.log`

  Note that this means that the nullspace of the image includes all of the nullspace of the
  original matrix. This contrasts to the standard definition, which is only defined for positive
  *definite* matrices, and the nullspace of the image is exactly the (λ=1)-eigenspace of the
  original matrix. It coincides with the standard definition if A is positive definite. -/
def log (A : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  cfc A Real.log

end CFC
