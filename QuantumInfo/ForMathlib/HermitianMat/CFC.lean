import QuantumInfo.ForMathlib.HermitianMat.Order
import QuantumInfo.ForMathlib.HermitianMat.Reindex
import QuantumInfo.ForMathlib.Isometry

/-! Matrix operations on HermitianMats with the CFC -/

namespace HermitianMat

noncomputable section CFC

macro "herm_cont":term => `(term|
  by simp only [continuousOn_iff_continuous_restrict, continuous_of_discreteTopology])

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]

@[simp]
theorem conjTranspose_cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    (cfc f A.toMat).conjTranspose = cfc f A.toMat := by
  exact cfc_predicate f A.toMat

noncomputable nonrec def cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) : HermitianMat d 𝕜 :=
  ⟨cfc f A.toMat, cfc_predicate _ _⟩

variable (A : HermitianMat d 𝕜) (f : ℝ → ℝ) (g : ℝ → ℝ) (r : ℝ)

@[simp]
theorem cfc_toMat : (cfc A f).toMat = _root_.cfc f A.toMat := by
  rfl

/-- Reindexing a matrix commutes with applying the CFC. -/
@[simp]
theorem cfc_reindex (e : d ≃ d₂) : cfc (A.reindex e) f = (cfc A f).reindex e := by
  rw [HermitianMat.ext_iff]
  simp only [cfc_toMat, reindex_coe]
  exact Matrix.cfc_reindex f e

-- @[fun_prop]
-- protected theorem cfc_continuous (hf : Continuous f) :
--     Continuous (cfc · f : HermitianMat d 𝕜 → HermitianMat d 𝕜) := by
--   unfold cfc
--   have := Continuous.cfc
--   fun_prop

/-! Here we give HermitianMat versions of many cfc theorems, like `cfc_id`, `cfc_sub`, `cfc_comp`,
etc. We need these because (as above) `HermitianMat.cfc` is different from `_root_.cfc`. -/

@[simp]
nonrec theorem cfc_id : cfc A id = A := by
  simp [HermitianMat.ext_iff, cfc_id]

@[simp]
nonrec theorem cfc_id' : cfc A (·) = A :=
  cfc_id A

nonrec theorem cfc_add : cfc A (f + g) = cfc A f + cfc A g := by
  rw [HermitianMat.ext_iff]
  exact cfc_add (hf := herm_cont) (hg := herm_cont)

nonrec theorem cfc_sub : cfc A (f - g) = cfc A f - cfc A g := by
  rw [HermitianMat.ext_iff]
  exact cfc_sub (hf := herm_cont) (hg := herm_cont)

nonrec theorem cfc_neg : cfc A (-f) = -cfc A f := by
  rw [HermitianMat.ext_iff]
  exact cfc_neg f A.toMat

/-- We don't have a direct analog of `cfc_mul`, since we can't generally multiply
to HermitianMat's to get another one, so the theorem statement wouldn't be well-typed.
But, we can say that the matrices are always equal. See `cfc_conj` for the coe-free
analog to multiplication. -/
theorem coe_cfc_mul : (cfc A (f * g)).toMat = cfc A f * cfc A g := by
  simp only [cfc_toMat]
  exact cfc_mul (hf := herm_cont) (hg := herm_cont)

nonrec theorem cfc_comp : cfc A (g ∘ f) = cfc (cfc A f) g := by
  rw [HermitianMat.ext_iff]
  exact cfc_comp (hf := herm_cont) (hg := herm_cont)

nonrec theorem cfc_conj : (cfc A f).conj (cfc A g) = cfc A (f * g^2) := by
  rw [HermitianMat.ext_iff, conj]
  simp only [cfc_toMat, val_eq_coe, mk_toMat, conjTranspose_cfc]
  rw [← cfc_mul (hf := herm_cont) (hg := herm_cont)]
  rw [← cfc_mul (hf := herm_cont) (hg := herm_cont)]
  rw [Pi.mul_def, Pi.pow_def]
  congr! 2; ring

@[simp]
nonrec theorem cfc_const : (cfc A (fun _ ↦ r)) = r • 1 := by
  rw [HermitianMat.ext_iff]
  simp only [cfc_toMat, selfAdjoint.val_smul, val_eq_coe, selfAdjoint.val_one]
  rw [cfc_const r A.toMat]
  exact Algebra.algebraMap_eq_smul_one r

@[simp]
nonrec theorem cfc_const_mul_id : cfc A (fun x => r * x) = r • A := by
  rw [HermitianMat.ext_iff]
  simp only [cfc_toMat, selfAdjoint.val_smul, val_eq_coe]
  exact cfc_const_mul_id r A.toMat

@[simp]
nonrec theorem cfc_const_mul : cfc A (fun x => r * f x) = r • cfc A f := by
  rw [← cfc_const_mul_id, ← cfc_comp]
  rfl

@[simp]
nonrec theorem cfc_apply_zero : cfc (0 : HermitianMat d 𝕜) f = f 0 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

@[simp]
nonrec theorem cfc_apply_one : cfc (1 : HermitianMat d 𝕜) f = f 1 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

variable {f g} in
nonrec theorem cfc_congr (hfg : Set.EqOn f g (spectrum ℝ A.toMat)) :
    cfc A f = cfc A g := by
  rw [HermitianMat.ext_iff]
  exact cfc_congr hfg

variable {f g A} in
/-- Version of `cfc_congr` specialized to PSD matrices. -/
nonrec theorem cfc_congr_of_zero_le (hA : 0 ≤ A) (hfg : Set.EqOn f g (Set.Ici 0)) :
    cfc A f = cfc A g := by
  refine cfc_congr A (hfg.mono ?_)
  exact fun i hi ↦ spectrum_nonneg_of_nonneg hA hi

open ComplexOrder

variable {f g A} in
/-- Version of `cfc_congr` specialized to positive definite matrices. -/
nonrec theorem cfc_congr_of_posDef (hA : A.toMat.PosDef) (hfg : Set.EqOn f g (Set.Ioi 0)) :
    cfc A f = cfc A g := by
  refine cfc_congr A (hfg.mono ?_)
  rw [A.H.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

@[simp]
theorem cfc_diagonal (g : d → ℝ) :
    cfc (HermitianMat.diagonal g) f = HermitianMat.diagonal (f ∘ g) := by
  ext1
  exact Matrix.cfc_diagonal g f

theorem cfc_eigenvalues (A : HermitianMat d 𝕜) :
    ∃ (e : d ≃ d), (A.cfc f).H.eigenvalues = f ∘ A.H.eigenvalues ∘ e :=
  A.H.cfc_eigenvalues f

theorem zero_le_cfc : 0 ≤ A.cfc f ↔ ∀ i, 0 ≤ f (A.H.eigenvalues i) := by
  rw [cfc, ← Subtype.coe_le_coe]
  dsimp
  rw [cfc_nonneg_iff (hf := herm_cont), A.H.spectrum_real_eq_range_eigenvalues]
  grind

variable {A f} in
theorem zero_le_cfc_of_zero_le (hA : 0 ≤ A) (hf : ∀ i ≥ 0, 0 ≤ f i) :
    0 ≤ A.cfc f := by
  rw [zero_le_cfc]
  intro i
  rw [zero_le_iff, A.H.posSemidef_iff_eigenvalues_nonneg] at hA
  exact hf _ (hA i)

theorem cfc_PosDef : (A.cfc f).toMat.PosDef ↔ ∀ i, 0 < f (A.H.eigenvalues i) := by
  rw [(A.cfc f).H.posDef_iff_eigenvalues_pos]
  obtain ⟨e, he⟩ := A.cfc_eigenvalues f
  rw [he]
  refine ⟨fun h i ↦ ?_, fun h i ↦ h (e i)⟩
  convert h (e.symm i)
  simp

/-- Matrix power of a positive semidefinite matrix, as given by the elementwise
  real power of the diagonal in a diagonalized form.

  Note that this has the usual `Real.rpow` caveats, such as 0 to the power -1 giving 0. -/
def rpow (p : ℝ) : HermitianMat d 𝕜 :=
  cfc A (Real.rpow · p)

instance instRPow : Pow (HermitianMat d 𝕜) ℝ :=
  ⟨rpow⟩

theorem pow_eq_rpow (p : ℝ) : A ^ p = A.rpow p :=
  rfl

theorem pow_eq_cfc (p : ℝ) : A ^ p = cfc A (· ^ p) :=
  rfl

--TODO Commented out because don't think I need it. Keeping it around a bit in case I need it later though...
-- theorem coe_pow_eq_cfc (p : ℝ) :
--     (A ^ p).toMat = _root_.cfc (· ^ p : ℝ → ℝ) A.toMat :=
--   rfl

theorem diagonal_pow (f : d → ℝ) (p : ℝ) :
    (diagonal f) ^ p = diagonal fun i => (f i) ^ p := by
  simp [pow_eq_cfc]
  rfl

@[simp]
theorem pow_one : A ^ (1 : ℝ) = A := by
  simp [pow_eq_cfc]

@[simp]
theorem reindex_pow (A : HermitianMat d ℂ) (e : d ≃ d₂) (p : ℝ) :
    A.reindex e ^ p = (A ^ p).reindex e := by
  apply A.cfc_reindex

--TODO Commented out because don't think I need it. Keeping it around a bit in case I need it later though...
-- open ComplexOrder in
-- theorem rpow_PosSemidef {A : HermitianMat n 𝕜} (hA : A.val.PosSemidef) (p : ℝ) : (A ^ p).val.PosSemidef := by
--   --TODO: Should prove the more general versions for f mapping ℝ≥0 → ℝ≥0 (if hA is PSD) or ℝ → ℝ≥0.
--   change (_root_.cfc _ A.toMat).PosSemidef
--   rw [A.H.cfc_eq, Matrix.IsHermitian.cfc]
--   apply Matrix.PosSemidef.mul_mul_conjTranspose_same
--   refine Matrix.posSemidef_diagonal_iff.mpr fun i ↦ ?_
--   rw [Function.comp_apply, RCLike.nonneg_iff]
--   constructor
--   · simp only [RCLike.ofReal_re]
--     exact Real.rpow_nonneg (hA.eigenvalues_nonneg i) p
--   · simp only [RCLike.ofReal_im]

variable {A} in
theorem coe_rpow_add (hA : 0 ≤ A) {p q : ℝ} (hpq : p + q ≠ 0) :
    (A ^ (p + q)).toMat = (A ^ p).toMat * (A ^ q).toMat := by
  simp only [pow_eq_cfc, ← coe_cfc_mul, ← HermitianMat.ext_iff]
  exact cfc_congr_of_zero_le hA (fun i hi ↦ Real.rpow_add' hi hpq)

variable {A} in
theorem rpow_mul (hA : 0 ≤ A) {p q : ℝ} :
    (A ^ (p * q)) = ((A ^ p) ^ q) := by
  simp only [pow_eq_cfc, ← cfc_comp]
  exact cfc_congr_of_zero_le hA (fun i hi ↦ Real.rpow_mul hi p q)

variable {A} in
theorem conj_rpow (hA : 0 ≤ A) {p q : ℝ}
  (hq : q ≠ 0) (hpq : p + 2 * q ≠ 0) :
    (A ^ p).conj (A ^ q) = A ^ (p + 2 * q) := by
  simp only [pow_eq_cfc, cfc_conj]
  refine cfc_congr_of_zero_le hA (fun i hi ↦ ?_)
  rw [pow_two, Real.rpow_add' hi hpq, two_mul, Real.rpow_add' hi (by simpa)]
  rfl

/-- Matrix logarithm (base e) of a Hermitian matrix, as given by the elementwise
  real logarithm of the diagonal in a diagonalized form, using `Real.log`

  Note that this means that the nullspace of the image includes all of the nullspace of the
  original matrix. This contrasts to the standard definition, which is only defined for positive
  *definite* matrices, and the nullspace of the image is exactly the (λ=1)-eigenspace of the
  original matrix. It coincides with the standard definition if A is positive definite. -/
def log : HermitianMat d 𝕜 :=
  cfc A Real.log

@[simp]
theorem reindex_log (e : d ≃ d₂) : (A.reindex e).log = A.log.reindex e :=
  cfc_reindex A Real.log e

end CFC
