import QuantumInfo.ForMathlib.HermitianMat.Order
import QuantumInfo.ForMathlib.Isometry

noncomputable section

attribute [instance] invertibleOne

namespace Matrix

variable {d R S F 𝕜 : Type*} [Fintype d] [DecidableEq d]
variable [CommSemiring R] [Semiring S] [Algebra R S] [Field F] [RCLike 𝕜]

theorem isUnit_smul {c : R} (hA : IsUnit c) {M : Matrix d d S} (hM : IsUnit M) :
    IsUnit (c • M : Matrix d d S) := by
  obtain ⟨d, rfl⟩ := hA
  obtain ⟨M', rfl⟩ := hM
  use d • M'
  rfl

theorem isUnit_natCast {n : ℕ} (hn : n ≠ 0) [CharZero F] : IsUnit (n : Matrix d d F) := by
  exact (IsUnit.mk0 (n : F) (mod_cast hn)).map (algebraMap F _)

theorem isUnit_real_smul {r : ℝ} (hr : r ≠ 0) {M : Matrix d d 𝕜} (hM : IsUnit M) :
    IsUnit (r • M : Matrix d d 𝕜) :=
  isUnit_smul hr.isUnit hM

theorem isUnit_real_cast {r : ℝ} (hr : r ≠ 0) : IsUnit (r • 1 : Matrix d d 𝕜) := by
  exact isUnit_real_smul hr isUnit_one

end Matrix

namespace HermitianMat

variable {n m R 𝕜 : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable [CommRing R] [StarRing R] [RCLike 𝕜]
variable (A : HermitianMat n R) (B : HermitianMat m R)

class NonSingular (A : HermitianMat n R) : Prop where
  isUnit : IsUnit A.mat

@[simp]
theorem isUnit_mat_of_nonSingular [NonSingular A] : IsUnit A.mat :=
  NonSingular.isUnit

theorem nonsingular_iff_isUnit : NonSingular A ↔ IsUnit A.mat := by
  exact Iff.intro (fun h ↦ h.isUnit) NonSingular.mk

instance instHasInv_of_invertible [i : Invertible A.mat] : NonSingular A :=
  ⟨isUnit_of_invertible _⟩

instance instInvertible_of_hasInv [h : NonSingular A] : Invertible A.mat :=
  h.isUnit.invertible

instance : NonSingular (1 : HermitianMat n R) :=
  instHasInv_of_invertible (i := invertibleOne)

variable {A : HermitianMat n 𝕜} {B : HermitianMat m 𝕜} {C : Matrix n n 𝕜}
open ComplexOrder

theorem nonSingular_of_posDef (hA : A.mat.PosDef) : NonSingular A :=
  ⟨hA.isUnit⟩

theorem nonSingular_iff_posDef_of_PSD (hA : 0 ≤ A) :
    NonSingular A ↔ A.mat.PosDef := by
  refine ⟨fun h ↦ ?_, fun hA₂ ↦ nonSingular_of_posDef hA₂⟩
  have : IsUnit A.mat := h.isUnit
  grind [zero_le_iff]

theorem nonSingular_smul [i : NonSingular A] {c : ℝ} (hc : IsUnit c) : NonSingular (c • A) :=
  ⟨Matrix.isUnit_smul hc i.isUnit⟩

theorem nonSingular_iff_zero_notMem_spectrum : NonSingular A ↔ 0 ∉ spectrum ℝ A.mat := by
  simp [nonsingular_iff_isUnit, spectrum, resolventSet]

theorem nonSingular_iff_eigenvalue_ne_zero : NonSingular A ↔ ∀ i, A.H.eigenvalues i ≠ 0 := by
  simp [nonSingular_iff_zero_notMem_spectrum, A.H.spectrum_real_eq_range_eigenvalues]

theorem nonSingular_iff_det_ne_zero : NonSingular A ↔ A.mat.det ≠ 0 := by
  simp [Matrix.isUnit_iff_isUnit_det, nonsingular_iff_isUnit]

theorem nonSingular_iff_ker_bot : NonSingular A ↔ A.ker = ⊥ := by
  rw [nonSingular_iff_det_ne_zero];
  have h_det_nonzero_to_ker_trivial : A.mat.det ≠ 0 → A.ker = ⊥ := by
    intro h_det_nonzero
    rw [Submodule.eq_bot_iff]
    have h_inv : Invertible A.mat := by
      convert Matrix.invertibleOfDetInvertible A.mat
      exact invertibleOfNonzero h_det_nonzero
    have h_ker_trivial (x : n → 𝕜) (hx : A.mat.mulVec x = 0) : x = 0 := by
      simpa using congr_arg (h_inv.1.mulVec) hx
    exact h_ker_trivial
  refine ⟨h_det_nonzero_to_ker_trivial, fun h h' => ?_⟩
  obtain ⟨x, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h'
  have h_inj : Function.Injective (Matrix.mulVecLin A.mat) := by
    rw [← LinearMap.ker_eq_bot]
    simpa [Submodule.eq_bot_iff] using h
  specialize @h_inj x 0
  simp_all

theorem nonSingular_iff_support_top : NonSingular A ↔ A.support = ⊤ := by
  simp only [support, Submodule.eq_top_iff']
  refine ⟨fun hA ↦ ?_, fun hA ↦ ?_⟩
  · intro x
    have hA_inv : IsUnit A.mat :=  hA.isUnit
    rcases hA_inv.exists_right_inv with ⟨ y, hy ⟩
    use y.mulVec x
    change A.mat.mulVecLin _ = _
    simp [hy]
  · constructor
    exact Matrix.mulVec_surjective_iff_isUnit.mp hA

@[simp]
theorem nonSingular_iff_neg : NonSingular (-A) ↔ NonSingular A := by
  simp [nonSingular_iff_det_ne_zero, Matrix.det_neg]

@[simp]
theorem nonSingular_iff_inv : NonSingular (A⁻¹) ↔ NonSingular A := by
  rw [nonsingular_iff_isUnit, nonsingular_iff_isUnit]
  exact Matrix.isUnit_nonsing_inv_iff

@[simp]
theorem nonSingular_iff_kronecker [Nonempty n] [Nonempty m] :
    NonSingular (A ⊗ₖ B) ↔ NonSingular A ∧ NonSingular B := by
  simp [nonSingular_iff_det_ne_zero, Matrix.det_kronecker]

theorem nonSingular_iff_conj (hC : IsUnit C) : NonSingular (A.conj C) ↔ NonSingular A := by
  simp_all [Matrix.isUnit_iff_isUnit_det, nonsingular_iff_isUnit]

@[simp]
theorem nonSingular_iff_reindex (e : n ≃ m) : NonSingular (A.reindex e) ↔ NonSingular A := by
  rw [nonSingular_iff_det_ne_zero, nonSingular_iff_det_ne_zero]
  rw [reindex_eq_conj, ← Matrix.det_reindex_self e, conj_apply_mat]
  congr! 2
  ext : 2
  simp [Matrix.mul_apply, Matrix.one_apply]

section fwd

theorem nonSingular_empty [IsEmpty n] : NonSingular A := by
  rw [Subsingleton.eq_one A]
  infer_instance

variable [NonSingular A] [NonSingular B]

theorem nonSingular_det_ne_zero : A.mat.det ≠ 0 := by
  rwa [← nonSingular_iff_det_ne_zero]

@[simp]
theorem nonSingular_ker_bot : A.ker = ⊥ := by
  rwa [← nonSingular_iff_ker_bot]

@[simp]
theorem nonSingular_support_top : A.support = ⊤ := by
  rwa [← nonSingular_iff_support_top]

instance nonSingular_neg : NonSingular (-A) := by
  rwa [nonSingular_iff_neg]

instance nonSingular_inv : NonSingular (A⁻¹) := by
  rwa [nonSingular_iff_inv]

instance nonSingular_kron [Nonempty n] [Nonempty m] : NonSingular (A ⊗ₖ B) :=
  nonSingular_iff_kronecker.mpr ⟨inferInstance, inferInstance⟩

theorem nonSingular_conj (hC : IsUnit C) : NonSingular (A.conj C) := by
  rwa [nonSingular_iff_conj hC]

instance nonSingular_conj_isometry {B : HermitianMat n 𝕜} [NonSingular B] :
    NonSingular (A.conj B.mat) := by
  simpa [nonSingular_iff_conj]

theorem nonSingular_zero_notMem_spectrum : 0 ∉ spectrum ℝ A.mat := by
  rwa [← nonSingular_iff_zero_notMem_spectrum]

theorem nonSingular_eigenvalue_ne_zero : ∀ i, A.H.eigenvalues i ≠ 0 := by
  rwa [← nonSingular_iff_eigenvalue_ne_zero]

end fwd

end HermitianMat
