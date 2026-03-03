/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.ForMathlib.HermitianMat.NonSingular
import QuantumInfo.ForMathlib.Isometry
import QuantumInfo.ForMathlib.Unitary

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Topology.TietzeExtension

/-! Matrix operations on HermitianMats with the CFC -/
namespace HermitianMat

noncomputable section CFC

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]
variable {X : Type*} [TopologicalSpace X]
variable (A : HermitianMat d 𝕜) (f : ℝ → ℝ) (g : ℝ → ℝ) (q r : ℝ)

/- Adding this to the `CStarAlgebra` aesop set allows `cfc_tac` to use it. -/
omit [Fintype d] [DecidableEq d] in
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem isSelfAdjoint : IsSelfAdjoint A.mat := by
  exact A.H

/- Adding this to `fun_prop` allows `cfc_cont_tac` to use it. -/
@[fun_prop]
theorem continuousOn_finite {α β : Type*} (f : α → β) (S : Set α)
    [TopologicalSpace α] [TopologicalSpace β] [T1Space α] [Finite S] : ContinuousOn f S := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_of_discreteTopology

@[simp]
theorem conjTranspose_cfc : (cfc f A.mat).conjTranspose = cfc f A.mat := by
  exact cfc_predicate f A.mat

protected def cfc : HermitianMat d 𝕜 :=
  ⟨cfc f A.mat, cfc_predicate _ _⟩

theorem cfc_eq : A.cfc f = ⟨cfc f A.mat, cfc_predicate f A.mat⟩ := by
  rfl

@[simp]
theorem mat_cfc : (A.cfc f).mat = _root_.cfc f A.mat := by
  rfl

section congr

variable {f g A}

theorem cfc_eq_cfc_iff_eqOn (f g : ℝ → ℝ) :
    A.cfc f = A.cfc g ↔ Set.EqOn f g (spectrum ℝ A.mat) := by
  rw [HermitianMat.ext_iff, mat_cfc, mat_cfc]
  exact _root_.cfc_eq_cfc_iff_eqOn A.H

@[gcongr]
nonrec theorem cfc_congr (hfg : Set.EqOn f g (spectrum ℝ A.mat)) :
    A.cfc f = A.cfc g := by
  ext1
  exact cfc_congr hfg

/-- Version of `cfc_congr` specialized to PSD matrices. -/
nonrec theorem cfc_congr_of_nonneg (hA : 0 ≤ A) (hfg : Set.EqOn f g (Set.Ici 0)) :
    A.cfc f = A.cfc g := by
  refine cfc_congr (hfg.mono ?_)
  open MatrixOrder in
  exact spectrum_nonneg_of_nonneg (a := A.mat) hA

open ComplexOrder in
/-- Version of `cfc_congr` specialized to positive definite matrices. -/
nonrec theorem cfc_congr_of_posDef (hA : A.mat.PosDef) (hfg : Set.EqOn f g (Set.Ioi 0)) :
    A.cfc f = A.cfc g := by
  refine cfc_congr (hfg.mono ?_)
  rw [A.H.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

end congr
section commute
variable {A B : HermitianMat d 𝕜}

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem _root_.Commute.cfc_left (hAB : Commute A.mat B.mat) :
    Commute (A.cfc f).mat B.mat := by
  exact hAB.cfc_real f

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem _root_.Commute.cfc_right (hAB : Commute A.mat B.mat) :
    Commute A.mat (B.cfc f).mat :=
  (hAB.symm.cfc_left f).symm

theorem cfc_commute (f g : ℝ → ℝ) (hAB : Commute A.mat B.mat) :
    Commute (A.cfc f).mat (B.cfc g).mat := by
  exact (hAB.cfc_right g).cfc_left f

@[aesop safe apply (rule_sets := [Commutes])]
theorem cfc_self_commute (A : HermitianMat d 𝕜) (f g : ℝ → ℝ) :
    Commute (A.cfc f).mat (A.cfc g).mat := by
  commutes

end commute

/-- Reindexing a matrix commutes with applying the CFC. -/
@[simp]
theorem cfc_reindex (e : d ≃ d₂) : (A.reindex e).cfc f = (A.cfc f).reindex e := by
  rw [HermitianMat.ext_iff]
  simp only [mat_cfc, mat_reindex]
  exact Matrix.cfc_reindex f e

theorem spectrum_cfc_eq_image (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    spectrum ℝ (A.cfc f).mat = f '' (spectrum ℝ A.mat) := by
  exact cfc_map_spectrum f A.mat

/--
Spectral decomposition of `A.cfc f` as a sum of scaled projections (matrix version).
-/
theorem cfc_toMat_eq_sum_smul_proj : (A.cfc f).mat =
    ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
  rw [A.mat_cfc, A.H.cfc_eq, Matrix.IsHermitian.cfc]
  have h : ( Matrix.diagonal ( RCLike.ofReal ∘ f ∘ Matrix.IsHermitian.eigenvalues A.H ) : Matrix d d 𝕜 ) = ∑ i, f ( A.H.eigenvalues i ) • Matrix.single i i 1 := by
    ext i j ; by_cases hij : i = j <;> simp [ hij ];
    · simp [ Matrix.sum_apply, Matrix.single ];
      simp [ Algebra.smul_def ];
    · rw [Finset.sum_apply, Finset.sum_apply]
      simp_all
  rw [h]
  simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.single, Matrix.mul_assoc]
  congr! 1
  ext j k
  simp [Matrix.mul_apply,Finset.mul_sum, Finset.smul_sum, smul_ite, smul_zero]

--Ensure we get this instance:
/-- info: locallyCompact_of_proper -/
#guard_msgs in
#synth LocallyCompactSpace (HermitianMat d 𝕜)

theorem cfc_eigenvalues (A : HermitianMat d 𝕜) :
    ∃ (e : d ≃ d), (A.cfc f).H.eigenvalues = f ∘ A.H.eigenvalues ∘ e :=
  A.H.cfc_eigenvalues f

/-! Here we give HermitianMat versions of many cfc theorems, like `cfc_id`, `cfc_sub`, `cfc_comp`,
etc. We need these because (as above) `HermitianMat.cfc` is different from `_root_.cfc`. -/

@[simp]
nonrec theorem cfc_id : A.cfc id = A := by
  simpa [HermitianMat.ext_iff] using cfc_id ℝ A.mat

@[simp]
nonrec theorem cfc_id' : A.cfc (·) = A :=
  cfc_id A

nonrec theorem cfc_add : A.cfc (f + g) = A.cfc f + A.cfc g := by
  ext1; exact cfc_add ..

theorem cfc_add_apply : A.cfc (fun x ↦ f x + g x) = A.cfc f + A.cfc g :=
  cfc_add A f g

nonrec theorem cfc_sub : A.cfc (f - g) = A.cfc f - A.cfc g := by
  ext1; exact cfc_sub ..

theorem cfc_sub_apply : A.cfc (fun x ↦ f x - g x) = A.cfc f - A.cfc g :=
  cfc_sub A f g

nonrec theorem cfc_neg : A.cfc (-f) = -A.cfc f := by
  ext1; exact cfc_neg ..

theorem cfc_neg_apply : A.cfc (fun x ↦ -f x) = -A.cfc f :=
  cfc_neg A f

/-- We don't have a direct analog of `cfc_mul`, since we can't generally multiply
to HermitianMat's to get another one, so the theorem statement wouldn't be well-typed.
But, we can say that the matrices are always equal. See `cfc_conj` for the coe-free
analog to multiplication. -/
theorem mat_cfc_mul : (A.cfc (f * g)).mat = A.cfc f * A.cfc g := by
  simp only [mat_cfc]
  exact cfc_mul ..

theorem mat_cfc_mul_apply : (A.cfc (fun x ↦ f x * g x)).mat = A.cfc f * A.cfc g := by
  exact mat_cfc_mul ..

nonrec theorem cfc_comp : A.cfc (g ∘ f) = (A.cfc f).cfc g := by
  ext1; exact cfc_comp ..

theorem cfc_comp_apply : A.cfc (fun x ↦ g (f x)) = (A.cfc f).cfc g :=
  cfc_comp A f g

nonrec theorem cfc_conj : (A.cfc f).conj (A.cfc g) = A.cfc (f * g^2) := by
  ext1
  simp only [conj_apply, mat_cfc, mat_mk, conjTranspose_cfc]
  rw [← cfc_mul, ← cfc_mul, Pi.mul_def, Pi.pow_def]
  grind only

@[simp]
theorem cfc_diagonal (g : d → ℝ) : (diagonal 𝕜 g).cfc f = diagonal 𝕜 (f ∘ g) := by
  ext1
  exact Matrix.cfc_diagonal g f

theorem cfc_conj_unitary (U : Matrix.unitaryGroup d 𝕜) :
    (A.conj U.val).cfc f = (A.cfc f).conj U := by
  ext1
  exact Matrix.cfc_conj_unitary f U

@[simp]
nonrec theorem cfc_const : (A.cfc (fun _ ↦ r)) = r • 1 := by
  ext1
  simp only [mat_cfc, mat_smul, mat_one]
  rw [cfc_const r A.mat]
  exact Algebra.algebraMap_eq_smul_one r

@[simp]
nonrec theorem cfc_const_mul_id : A.cfc (fun x ↦ r * x) = r • A := by
  ext1
  rw [mat_cfc, mat_smul, cfc_const_mul_id r A.mat]

@[simp]
nonrec theorem cfc_const_mul : A.cfc (fun x ↦ r * f x) = r • A.cfc f := by
  rw [← cfc_const_mul_id, ← cfc_comp]
  rfl

@[simp]
nonrec theorem cfc_apply_zero : (0 : HermitianMat d 𝕜).cfc f = f 0 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

@[simp]
nonrec theorem cfc_apply_one : (1 : HermitianMat d 𝕜).cfc f = f 1 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

theorem cfc_pow {n : ℕ} : A.cfc (· ^ n) = A ^ n := by
  ext1
  induction n
  · simp
  · simp_rw [pow_succ, mat_pow, mat_cfc_mul_apply, pow_succ, cfc_id']
    congr

theorem cfc_nonneg_iff : 0 ≤ A.cfc f ↔ ∀ i, 0 ≤ f (A.H.eigenvalues i) := by
  open MatrixOrder in
  rw [cfc_eq, ← Subtype.coe_le_coe, ZeroMemClass.coe_zero]
  rw [_root_.cfc_nonneg_iff f A.mat, A.H.spectrum_real_eq_range_eigenvalues]
  grind

open ComplexOrder in
theorem cfc_posDef : (A.cfc f).mat.PosDef ↔ ∀ i, 0 < f (A.H.eigenvalues i) := by
  rw [(A.cfc f).H.posDef_iff_eigenvalues_pos]
  obtain ⟨e, he⟩ := A.cfc_eigenvalues f
  rw [he]
  refine ⟨fun h i ↦ ?_, fun h i ↦ h (e i)⟩
  simpa using h (e.symm i)

variable {A f} in
/-- If a rael function preserves nonnegativity, the CFC preserves PSDness. -/
theorem cfc_nonneg_of_nonneg (hA : 0 ≤ A) (hf : ∀ i ≥ 0, 0 ≤ f i) :
    0 ≤ A.cfc f := by
  rw [cfc_nonneg_iff]
  rw [zero_le_iff, A.H.posSemidef_iff_eigenvalues_nonneg] at hA
  exact fun i ↦ hf _ (hA i)

theorem cfc_nonSingular (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0) : NonSingular (A.cfc f) := by
  rw [nonSingular_iff_eigenvalue_ne_zero]
  obtain ⟨e, he⟩ := cfc_eigenvalues f A
  simpa [he] using fun i ↦ hf (e i)


theorem trace_mul_cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    (A.mat * (A.cfc f).mat).trace = ∑ i, A.H.eigenvalues i * f (A.H.eigenvalues i) := by
  conv_lhs => rw [A.eq_conj_diagonal]
  rw [cfc_conj_unitary]
  simp [conj, Matrix.mul_assoc, A.H.eigenvectorUnitary.val.trace_mul_comm]
  simp [← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ]

theorem norm_eq_sum_eigenvalues_sq (A : HermitianMat d 𝕜) :
    ‖A‖ ^ 2 = ∑ i, (A.H.eigenvalues i)^2 := by
  rw [← RCLike.ofReal_inj (K := 𝕜), RCLike.ofReal_pow, norm_eq_trace_sq]
  conv_lhs => change (A ^ 2).mat.trace; rw [(A ^ 2).H.trace_eq_sum_eigenvalues]
  simp only [map_sum, map_pow]
  rw [← cfc_pow]
  obtain ⟨e, he⟩ := cfc_eigenvalues (· ^ 2) A
  simp only [he, Function.comp_apply, map_pow]
  exact e.sum_comp (fun x ↦ (algebraMap ℝ 𝕜) (A.H.eigenvalues x) ^ 2)

variable {A} in
theorem lt_smul_of_norm_lt {r : ℝ} (h : ‖A‖ ≤ r) : A ≤ r • 1 := by
  rcases lt_or_ge r 0 with _ | hr
  · have := norm_nonneg A
    order
  rcases isEmpty_or_nonempty d
  · exact le_of_subsingleton
  have h' := (sq_le_sq₀ (by positivity) (by positivity)).mpr h
  rw [norm_eq_sum_eigenvalues_sq] at h'
  nth_rw 1 [← cfc_const A, ← cfc_id A]
  rw [le_iff, ← cfc_sub]
  rw [(HermitianMat.H _).posSemidef_iff_eigenvalues_nonneg]
  intro i; rw [Pi.zero_apply]
  obtain ⟨e, he⟩ := cfc_eigenvalues ((fun x ↦ r) - id) A
  rw [he]; clear he
  dsimp only [Function.comp_apply, Pi.sub_apply, id_eq]
  rw [sub_nonneg]
  apply le_of_sq_le_sq _ hr
  refine le_trans ?_ h'
  exact Finset.single_le_sum (f := fun x ↦ (A.H.eigenvalues x)^2) (by intros; positivity) (Finset.mem_univ _)

theorem ball_subset_Icc : Metric.ball A r ⊆ Set.Icc (A - r • 1) (A + r • 1) := by
  intro x
  simp only [Metric.mem_ball, dist_eq_norm, Set.mem_Icc, tsub_le_iff_right]
  intro h
  constructor
  · rw [← norm_neg] at h
    grw [← lt_smul_of_norm_lt h.le]
    simp
  · grw [← lt_smul_of_norm_lt h.le]
    simp

theorem spectrum_subset_of_mem_Icc (A B : HermitianMat d 𝕜) :
    ∃ a b, ∀ x, A ≤ x ∧ x ≤ B → spectrum ℝ x.mat ⊆ Set.Icc a b := by
  use ⨅ i, A.H.eigenvalues i, ⨆ i, B.H.eigenvalues i
  rintro x ⟨hl, hr⟩
  exact A.H.spectrum_subset_of_mem_Icc B.H hl hr

--TODO: Generalize this to real matrices (really, RCLike) too. The theorem below
-- gives it for complex matrices only.
-- @[fun_prop]
-- protected theorem cfc_continuous {f : ℝ → ℝ} (hf : Continuous f) :
--     Continuous (cfc · f : HermitianMat d 𝕜 → HermitianMat d 𝕜) := by
--   rcases isEmpty_or_nonempty d
--   · sorry
--   rw [Metric.continuous_iff] at hf ⊢
--   intro x ε hε
--   have _ : Nonempty (spectrum ℝ x.toMat) := by
--     sorry
--   replace hf b := hf b ε hε
--   choose fc hfc₀ hfc using hf
--   let δ : ℝ := ⨆ e : spectrum ℝ x.toMat, fc e
--   refine ⟨δ, ?_, ?_⟩
--   · --This whole block should just be `positivity`. TODO fix.
--     dsimp [δ]
--     --Why doesn't just `classical` make ths happen automatically?
--     replace h_fin := Fintype.ofFinite (spectrum ℝ x.toMat)
--     rw [← Finset.sup'_univ_eq_ciSup, gt_iff_lt, Finset.lt_sup'_iff]
--     simp [hfc₀]
--   intro a ha
--   simp only [dist, AddSubgroupClass.subtype_apply, val_eq_coe, cfc_toMat] at ha ⊢
--   sorry

@[fun_prop]
protected theorem cfc_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (HermitianMat.cfc · f : HermitianMat d ℂ → HermitianMat d ℂ) := by
  unfold HermitianMat.cfc
  suffices Continuous (fun A : HermitianMat d ℂ ↦ _root_.cfc f A.mat) by
    fun_prop
  have h_compact_cover := LocallyCompactSpace.local_compact_nhds (X := HermitianMat d ℂ)
  apply continuous_of_continuousOn_iUnion_of_isOpen (ι := HermitianMat d ℂ × {x : ℝ // 0 < x})
    (s := fun ab ↦ Metric.ball ab.1 ab.2)
  · rintro ⟨A, r, hr⟩
    apply ContinuousOn.mono ?_ (ball_subset_Icc A r)
    obtain ⟨a, b, hab⟩ := spectrum_subset_of_mem_Icc (A - r • 1) (A + r • 1)
    open ComplexOrder in
    have := ContinuousOn.cfc (A := CStarMatrix d d ℂ) isCompact_Icc f (by fun_prop) hab (fun x _ ↦ x.H)
    exact this
  · simp
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    use ⟨x, 1⟩
    simp

open ComplexOrder in
theorem Matrix.PosDef.spectrum_subset_Ioi {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
    {A : Matrix d d 𝕜} (hA : A.PosDef) : spectrum ℝ A ⊆ Set.Ioi 0 := by
  --TODO Cleanup. Surely SURELY this is already in Mathlib? (Esp. as an Iff)
  intro x hx
  obtain ⟨v, hv⟩ : ∃ v : d → 𝕜, v ≠ 0 ∧ A.mulVec v = x • v := by
    have h_eigenvalue : ∃ v : d → 𝕜, v ≠ 0 ∧ (A - x • 1).mulVec v = 0 := by
      rw [ spectrum.mem_iff ] at hx;
      simp_all [ Matrix.isUnit_iff_isUnit_det ];
      have := Matrix.exists_mulVec_eq_zero_iff.mpr hx;
      obtain ⟨ v, hv, hv' ⟩ := this; use v; simp_all [ Matrix.sub_mulVec ] ;
      simp_all [ sub_eq_zero, Algebra.algebraMap_eq_smul_one ];
    obtain ⟨ v, hv, hv' ⟩ := h_eigenvalue; use v; simp_all [ sub_eq_iff_eq_add, Matrix.sub_mulVec ] ;
    ext i
    simp [ Matrix.mulVec, dotProduct]
    simp [ Matrix.one_apply]
  have := hA.2 v hv.1
  aesop

/--
If f is a continuous family of functions parameterized by x, then (fun x => A.cfc (f x)) is also continuous.
-/
@[fun_prop]
theorem continuous_cfc_fun {f : X → ℝ → ℝ} (hf : ∀ i, Continuous (f · i)) :
    Continuous (fun x ↦ A.cfc (f x)) := by
  apply Continuous.subtype_mk
  conv => enter [1, x]; apply A.cfc_toMat_eq_sum_smul_proj (f x)
  fun_prop

variable {f : X → ℝ → ℝ} {S : Set X}
/--
ContinuousOn variant for when all the matrices (A x) have a spectrum in a set T, and f is continuous on a set S.
-/
@[fun_prop]
theorem continuousOn_cfc_fun {T : Set ℝ}
  (hf : ∀ i ∈ T, ContinuousOn (f · i) S) (hA : spectrum ℝ A.mat ⊆ T) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  simp_rw [continuousOn_iff_continuous_restrict] at hf ⊢
  apply Continuous.subtype_mk
  conv => enter [1, x]; apply A.cfc_toMat_eq_sum_smul_proj (f x)
  unfold Set.restrict at hf
  apply continuous_finset_sum _
  rw [A.H.spectrum_real_eq_range_eigenvalues] at hA
  refine fun i _ ↦ Continuous.smul (hf _ (by grind)) (by fun_prop)

section joint_continuity

--TODO Cleanup

/--
Bound the Frobenius norm of a functional calculus application.
-/
lemma norm_cfc_le_sqrt_card_mul_bound {A : HermitianMat d ℂ} {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x ∈ spectrum ℝ A.mat, ‖f x‖ ≤ C) :
    ‖A.cfc f‖ ≤ Real.sqrt (Fintype.card d) * C := by
  rw [ ← Real.sqrt_sq ( norm_nonneg _ ) ];
  -- Recall that the Frobenius norm of a Hermitian matrix is the square root of the sum of the squares of its eigenvalues.
  have h_frobenius_eigenvalues : ∀ (M : HermitianMat d ℂ), ‖M‖ ^ 2 = ∑ i ∈ Finset.univ, (M.H.eigenvalues i) ^ 2 := by
    exact fun M => norm_eq_sum_eigenvalues_sq M;
  -- Applying the bound on the eigenvalues to the Frobenius norm.
  have h_bound : ∑ i ∈ Finset.univ, ((A.cfc f).H.eigenvalues i) ^ 2 ≤ (Fintype.card d) * C ^ 2 := by
    have h_bound : ∀ i, ((A.cfc f).H.eigenvalues i) ^ 2 ≤ C ^ 2 := by
      intro i
      have h_eigenvalue_bound : |(A.cfc f).H.eigenvalues i| ≤ C := by
        obtain ⟨ x, hx, hx' ⟩ : (A.cfc f).H.eigenvalues i ∈ f '' spectrum ℝ A.mat := by
          have h_bound := (A.cfc f).H.eigenvalues_mem_spectrum_real i
          rwa [spectrum_cfc_eq_image A f] at h_bound
        specialize hf x hx
        aesop;
      nlinarith only [ abs_le.mp h_eigenvalue_bound ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => h_bound _ ) ( by simp );
  rw [ h_frobenius_eigenvalues, Real.sqrt_le_left ] <;> nlinarith [ Real.sqrt_nonneg ( Fintype.card d : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg ( Fintype.card d ) ) ]

/-
The norm of the difference of two functional calculus applications is bounded by `sqrt(d)` times the sup norm of the difference of the functions.
-/
lemma norm_cfc_sub_cfc_le_sqrt_card {A : HermitianMat d ℂ} {f g : ℝ → ℝ} :
    ‖A.cfc f - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ⨆ x ∈ spectrum ℝ A.mat, ‖f x - g x‖ := by
  rw [ ← HermitianMat.cfc_sub ];
  refine' le_trans ( norm_cfc_le_sqrt_card_mul_bound _ _ ) _;
  exact ⨆ x ∈ spectrum ℝ A.mat, ‖f x - g x‖;
  · exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _;
  · intro x hx
    apply le_csSup;
    · -- The supremum of a finite set of real numbers is finite.
      have h_finite : Set.Finite (spectrum ℝ A.mat) := by
        exact Set.toFinite _;
      obtain ⟨ M, hM ⟩ := h_finite.exists_finset_coe;
      refine' ⟨ ∑ x ∈ M, ‖f x - g x‖, Set.forall_mem_range.2 fun x => _ ⟩;
      rw [ ← hM ];
      rw [ @ciSup_eq_ite ];
      split_ifs <;> [ exact Finset.single_le_sum ( fun x _ => norm_nonneg ( f x - g x ) ) ( by assumption ) ; exact le_trans ( by norm_num ) ( Finset.sum_nonneg fun x _ => norm_nonneg ( f x - g x ) ) ];
    · exact ⟨ x, by aesop ⟩;
  · rfl

/-
If f and g are close on T, and the spectrum of A is in T, then A.cfc f and A.cfc g are close.
-/
lemma norm_cfc_sub_le_of_sup_le {A : HermitianMat d ℂ} {f g : ℝ → ℝ} {T : Set ℝ} {ε : ℝ}
    (hT : spectrum ℝ A.mat ⊆ T) (hε : 0 ≤ ε) (h_sup : ∀ x ∈ T, ‖f x - g x‖ ≤ ε) :
    ‖A.cfc f - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ε := by
  refine' le_trans ( norm_cfc_sub_cfc_le_sqrt_card ) _;
  gcongr;
  refine' ciSup_le fun x => _;
  exact Real.iSup_le (fun i => h_sup x (hT i)) hε

/--
If $f$ is jointly continuous on $S \times T$ and $T$ is compact, then $x \mapsto f(x, \cdot)$ is continuous into the space of bounded functions on $T$ with the uniform norm.
-/
lemma dist_lt_of_continuous' {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {S : Set X} {T : Set ℝ}
    (hT : IsCompact T)
    (hf : ContinuousOn (fun (p : X × ℝ) ↦ f p.1 p.2) (S ×ˢ T))
    {x₀ : X} (hx₀ : x₀ ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ nhds x₀, ∀ x ∈ U ∩ S, ∀ t ∈ T, ‖f x t - f x₀ t‖ < ε := by
  by_contra h_contra;
  -- For each $t \in T$, by continuity at $(x₀, t)$, there exist neighborhoods $U_t$ of $x₀$ and $V_t$ of $t$ such that for all $x \in U_t \cap S$ and $t' \in V_t \cap T$, $|f(x, t') - f(x₀, t)| < \epsilon/2$.
  have h_cont : ∀ t ∈ T, ∃ U_t ∈ nhds x₀, ∃ V_t ∈ nhds t, ∀ x ∈ U_t ∩ S, ∀ t' ∈ V_t ∩ T, ‖f x t' - f x₀ t‖ < ε / 2 := by
    intro t ht
    have h_cont_t : ∀ᶠ (p : X × ℝ) in nhds (x₀, t), p ∈ S ×ˢ T → ‖f p.1 p.2 - f x₀ t‖ < ε / 2 := by
      have := hf ( x₀, t ) ⟨ hx₀, ht ⟩;
      have := this.eventually ( Metric.ball_mem_nhds _ ( half_pos hε ) );
      rw [ eventually_nhdsWithin_iff ] at this; aesop;
    rcases mem_nhds_prod_iff.mp h_cont_t with ⟨ U, hU, V, hV, hUV ⟩;
    exact ⟨ U, hU, V, hV, fun x hx t' ht' => hUV ( Set.mk_mem_prod hx.1 ht'.1 ) ⟨ hx.2, ht'.2 ⟩ ⟩;
  choose! U hU V hV hUV using h_cont;
  -- Since $T$ is compact, cover it by finitely many $V_{t_i}$. Let $U = \bigcap U_{t_i}$.
  obtain ⟨t_fin, ht_fin⟩ : ∃ t_fin : Finset ℝ, (∀ t ∈ t_fin, t ∈ T) ∧ T ⊆ ⋃ t ∈ t_fin, V t := by
    have := hT.elim_nhds_subcover V fun t ht => hV t ht;
    tauto;
  refine h_contra ⟨⋂ t ∈ t_fin, U t, ?_, ?_⟩
  · exact Filter.biInter_mem ( Finset.finite_toSet t_fin ) |>.2 fun t ht => hU t ( ht_fin.1 t ht );
  · intro x hx t ht
    obtain ⟨t', ht'_fin, ht'_t⟩ : ∃ t' ∈ t_fin, t ∈ V t' := by
      simpa using ht_fin.2 ht;
    have := hUV t' ( ht_fin.1 t' ht'_fin ) x ⟨ Set.mem_iInter₂.1 hx.1 t' ht'_fin, hx.2 ⟩ t ⟨ ht'_t, ht ⟩;
    have := hUV t' ( ht_fin.1 t' ht'_fin ) x₀ ⟨ mem_of_mem_nhds ( hU t' ( ht_fin.1 t' ht'_fin ) ), hx₀ ⟩ t ⟨ ht'_t, ht ⟩;
    exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp ‹‖f x t - f x₀ t'‖ < ε / 2›, abs_lt.mp ‹‖f x₀ t - f x₀ t'‖ < ε / 2› ], by linarith [ abs_lt.mp ‹‖f x t - f x₀ t'‖ < ε / 2›, abs_lt.mp ‹‖f x₀ t - f x₀ t'‖ < ε / 2› ] ⟩

/--
The functional calculus is continuous on matrices with spectrum in a compact set.
-/
lemma continuousOn_cfc_of_compact {K : Set ℝ} {g : ℝ → ℝ} (hK : IsCompact K) (hg : ContinuousOn g K) :
    ContinuousOn (fun (A : HermitianMat d ℂ) ↦ A.cfc g) {A | spectrum ℝ A.mat ⊆ K} := by
  by_contra! h_contra;
  -- By Stone-Weierstrass, there exists a sequence of polynomials `p_n` converging uniformly to `g` on `K`.
  obtain ⟨p_n, hp_n⟩ : ∃ p_n : ℕ → Polynomial ℝ, (∀ n, ∀ x ∈ K, |(p_n n).eval x - g x| ≤ 1 / (n + 1)) := by
    have h_stone_weierstrass : ∀ ε > 0, ∃ p : Polynomial ℝ, ∀ x ∈ K, |p.eval x - g x| < ε := by
      have := @exists_polynomial_near_of_continuousOn;
      obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, K ⊆ Set.Icc a b := by
        exact ⟨ hK.bddBelow.some, hK.bddAbove.some, fun x hx => ⟨ hK.bddBelow.choose_spec hx, hK.bddAbove.choose_spec hx ⟩ ⟩;
      -- Extend $g$ to a continuous function on $[a, b]$.
      obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) ∧ ∀ x ∈ K, f x = g x := by
        have := @ContinuousMap.exists_restrict_eq;
        specialize this ( show IsClosed K from hK.isClosed ) ( ContinuousMap.mk ( fun x => g x ) <| by exact continuousOn_iff_continuous_restrict.mp hg );
        exact ⟨ _, this.choose.continuous.continuousOn, fun x hx => by simpa using congr_arg ( fun f => f ⟨ x, hx ⟩ ) this.choose_spec ⟩;
      exact fun ε εpos => by rcases this a b f hf.1 ε εpos with ⟨ p, hp ⟩ ; exact ⟨ p, fun x hx => by simpa only [ hf.2 x hx ] using hp x ( hab hx ) ⟩ ;
    exact ⟨ fun n => Classical.choose ( h_stone_weierstrass ( 1 / ( n + 1 ) ) ( by positivity ) ), fun n x hx => le_of_lt ( Classical.choose_spec ( h_stone_weierstrass ( 1 / ( n + 1 ) ) ( by positivity ) ) x hx ) ⟩;
  -- The sequence `A ↦ A.cfc (p_n)` converges uniformly to `A ↦ A.cfc g` on `{A | spectrum A ⊆ K}`.
  have h_uniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : HermitianMat d ℂ, spectrum ℝ A.mat ⊆ K → ‖A.cfc (fun x => (p_n n).eval x) - A.cfc g‖ < ε := by
    -- By the properties of the functional calculus, we have `‖A.cfc p_n - A.cfc g‖ ≤ sqrt(d) * ‖p_n - g‖_{∞, K}`.
    have h_uniform_bound : ∀ n, ∀ A : HermitianMat d ℂ, spectrum ℝ A.mat ⊆ K → ‖A.cfc (fun x => (p_n n).eval x) - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * (1 / (n + 1)) := by
      intro n A hA
      have h_uniform_bound : ‖A.cfc (fun x => (p_n n).eval x) - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ⨆ x ∈ spectrum ℝ A.mat, |(p_n n).eval x - g x| := by
        exact norm_cfc_sub_cfc_le_sqrt_card;
      refine' le_trans h_uniform_bound ( mul_le_mul_of_nonneg_left _ ( Real.sqrt_nonneg _ ) );
      refine' ciSup_le fun x => _;
      field_simp;
      by_cases hx : x ∈ spectrum ℝ A.mat <;> simp_all
      exact le_trans ( mul_le_mul_of_nonneg_right ( hp_n n x ( hA hx ) ) ( by positivity ) ) ( by nlinarith [ mul_inv_cancel₀ ( by positivity : ( n : ℝ ) + 1 ≠ 0 ) ] );
    exact fun ε εpos => ⟨ Nat.ceil ( ε⁻¹ * Real.sqrt ( Fintype.card d ) ), fun n hn A hA => lt_of_le_of_lt ( h_uniform_bound n A hA ) ( by rw [ mul_one_div, div_lt_iff₀ ] <;> nlinarith [ Nat.ceil_le.mp hn, inv_pos.mpr εpos, mul_inv_cancel₀ εpos.ne', Real.sqrt_nonneg ( Fintype.card d ), Real.sq_sqrt ( Nat.cast_nonneg ( Fintype.card d ) ) ] ) ⟩;
  -- The uniform limit of continuous functions is continuous.
  have h_cont : ContinuousOn (fun A : HermitianMat d ℂ => A.cfc g) {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ K} := by
    have h_seq_cont : ∀ n, ContinuousOn (fun A : HermitianMat d ℂ => A.cfc (fun x => (p_n n).eval x)) {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ K} := by
      fun_prop
    refine' Metric.continuousOn_iff.mpr _;
    intro A hA ε εpos
    obtain ⟨N, hN⟩ := h_uniform (ε / 3) (by linarith)
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ > 0, ∀ a ∈ {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ K}, dist a A < δ → ‖a.cfc (fun x => (p_n N).eval x) - A.cfc (fun x => (p_n N).eval x)‖ < ε / 3 := by
      have := Metric.continuousOn_iff.mp ( h_seq_cont N ) A hA ( ε / 3 ) ( by linarith );
      exact ⟨ this.choose, this.choose_spec.1, fun a ha ha' => by simpa only [ dist_eq_norm ] using this.choose_spec.2 a ha ha' ⟩;
    refine' ⟨ δ, δpos, fun a ha ha' => _ ⟩;
    have := hN N le_rfl a ha;
    have := hN N le_rfl A hA;
    rw [ dist_eq_norm ];
    rw [ show a.cfc g - A.cfc g = ( a.cfc g - a.cfc ( fun x => Polynomial.eval x ( p_n N ) ) ) + ( a.cfc ( fun x => Polynomial.eval x ( p_n N ) ) - A.cfc ( fun x => Polynomial.eval x ( p_n N ) ) ) + ( A.cfc ( fun x => Polynomial.eval x ( p_n N ) ) - A.cfc g ) by abel1 ];
    exact lt_of_le_of_lt ( norm_add₃_le .. ) ( by linarith [ norm_sub_rev ( a.cfc g ) ( a.cfc fun x => Polynomial.eval x ( p_n N ) ), norm_sub_rev ( A.cfc fun x => Polynomial.eval x ( p_n N ) ) ( A.cfc g ), hδ a ha ha' ] );
  contradiction

end joint_continuity

theorem continuous_cfc_joint {X d : Type*} [TopologicalSpace X] [Fintype d] [DecidableEq d]
  {f : X → ℝ → ℝ} {A : X → HermitianMat d ℂ} {S : Set X} {T : Set ℝ}
  (hT : IsCompact T)
  (hf : ContinuousOn (fun (p : X × ℝ) ↦ f p.1 p.2) (S ×ˢ T))
  (hA₁ : ∀ x ∈ S, spectrum ℝ (A x).mat ⊆ T)
  (hA₂ : ContinuousOn (fun x ↦ A x) S) :
    ContinuousOn (fun x ↦ (A x).cfc (f x)) S := by
  intro x x_in_S
  have h_eps_delta : ContinuousWithinAt (fun y => (A y).cfc (f x)) S x := by
    refine ContinuousOn.continuousWithinAt ?_ x_in_S
    exact (continuousOn_cfc_of_compact hT (hf.uncurry_left x x_in_S)).comp hA₂ hA₁
  rw [ ContinuousWithinAt ] at *;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε ε_pos
  obtain ⟨U, hU₁, hU₂⟩ : ∃ U ∈ nhds x, ∀ y ∈ U ∩ S, ‖(A y).cfc (f y) - (A y).cfc (f x)‖ ≤ Real.sqrt (Fintype.card d) * (ε / (2 * Real.sqrt (Fintype.card d) + 1)) := by
    have h_eps_delta₁ : ∀ ε > 0, ∃ U ∈ nhds x, ∀ y ∈ U ∩ S, ‖(A y).cfc (f y) - (A y).cfc (f x)‖ ≤ Real.sqrt (Fintype.card d) * ε := by
      intro ε ε_pos
      obtain ⟨U, hU₁, hU₂⟩ := dist_lt_of_continuous' (f := f) hT hf x_in_S ε_pos
      use U, hU₁
      intro y hy
      apply norm_cfc_sub_le_of_sup_le (hA₁ y hy.right) ε_pos.le
      intro t ht
      exact le_of_lt (hU₂ y hy t ht)
    exact h_eps_delta₁ _ (by positivity)
  filter_upwards [ h_eps_delta ( ε / 2 ) ( half_pos ε_pos ), self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hU₁ ] with y hy₁ hy₂ hy₃
  apply lt_of_le_of_lt (dist_triangle _ ((A y).cfc (f x)) _)
  nlinarith [hU₂ y ⟨ hy₃, hy₂ ⟩,
    Real.sqrt_nonneg ( Fintype.card d : ℝ ),
    mul_div_cancel₀ ε ( show ( 2 * Real.sqrt ( Fintype.card d : ℝ ) + 1 ) ≠ 0 by positivity ),
    norm_nonneg ( ( A y ).cfc ( f y ) - ( A y ).cfc ( f x ) ),
    norm_nonneg ( ( A y ).cfc ( f x ) - ( A x ).cfc ( f x ) ),
    dist_eq_norm ( ( A y ).cfc ( f y ) ) ( ( A y ).cfc ( f x ) ),
    dist_eq_norm ( ( A y ).cfc ( f x ) ) ( ( A x ).cfc ( f x ) )]

/-- Specialization of `continuousOn_cfc_fun` for nonsingular matrices. -/
@[fun_prop]
theorem continuousOn_cfc_fun_nonsingular {f : X → ℝ → ℝ} {S : Set X}
  (hf : ∀ i ≠ 0, ContinuousOn (f · i) S) [NonSingular A] :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  apply continuousOn_cfc_fun (T := {0}ᶜ)
  · exact hf
  · grind [nonSingular_zero_notMem_spectrum]

/-- Specialization of `continuousOn_cfc_fun` for positive semidefinite matrices. -/
@[fun_prop]
theorem continuousOn_cfc_fun_nonneg {f : X → ℝ → ℝ} {S : Set X}
  (hf : ∀ i ≥ 0, ContinuousOn (f · i) S) (hA : 0 ≤ A) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  apply continuousOn_cfc_fun (T := Set.Ici 0)
  · exact hf
  · rw [zero_le_iff] at hA
    exact hA.pos_of_mem_spectrum

open ComplexOrder in
/-- Specialization of `continuousOn_cfc_fun` for positive definite matrices. -/
@[fun_prop]
theorem continuousOn_cfc_fun_posDef {f : X → ℝ → ℝ} {S : Set X}
  (hf : ∀ i > 0, ContinuousOn (f · i) S) (hA : A.mat.PosDef) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  apply continuousOn_cfc_fun (T := Set.Ioi 0)
  · exact hf
  · exact Matrix.PosDef.spectrum_subset_Ioi hA

variable {A B : HermitianMat d 𝕜} (f : ℝ → ℝ)

/--
The inverse of the CFC is the CFC of the inverse function.
-/
lemma inv_cfc_eq_cfc_inv (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0) :
    (A.cfc f)⁻¹ = A.cfc (fun u ↦ (f u)⁻¹) := by
  suffices (A.cfc f).mat⁻¹ = (A.cfc (fun u ↦ 1 / f u)).mat by
    ext1
    simpa using this
  have h_def : (A.cfc f).mat = ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj A f;
  have h_subst : (A.cfc (fun u ↦ 1 / f u)).mat = ∑ i, (1 / f (A.H.eigenvalues i)) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj A fun u ↦ 1 / f u;
  have h_inv : (A.cfc f).mat * (A.cfc (fun u ↦ 1 / f u)).mat = 1 := by
    -- Since the eigenvectorUnitary is unitary, we have that the product of the projections is the identity matrix.
    have h_unitary : A.H.eigenvectorUnitary.val * A.H.eigenvectorUnitary.val.conjTranspose = 1 := by
      simp [ Matrix.IsHermitian.eigenvectorUnitary ];
    have h_inv : ∀ i j, (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) * (A.H.eigenvectorUnitary.val * (Matrix.single j j 1) * A.H.eigenvectorUnitary.val.conjTranspose) = if i = j then A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose else 0 := by
      simp [ ← Matrix.mul_assoc ];
      intro i j; split_ifs <;> simp_all [ Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp h_unitary ] ;
    simp_all [ Finset.sum_mul, Finset.mul_sum ];
    have h_sum : ∑ i, (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) = A.H.eigenvectorUnitary.val * (∑ i, Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose := by
      simp [ Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc ];
    simp_all [ Matrix.single ];
    convert h_unitary using 2;
    ext i j; simp [ Matrix.mul_apply]
    simp [ Matrix.sum_apply, Finset.filter_eq', Finset.filter_and ];
    rw [ Finset.sum_eq_single j ] <;> aesop;
  rw [ Matrix.inv_eq_right_inv h_inv ];

theorem cfc_inv [NonSingular A] : A.cfc (fun u ↦ u⁻¹) = A⁻¹ := by
  simpa using (inv_cfc_eq_cfc_inv id nonSingular_eigenvalue_ne_zero).symm

section integral

open MeasureTheory
open scoped Matrix.Norms.Frobenius

omit [DecidableEq d] in
/--
The integral of a Hermitian matrix function commutes with `toMat`.
-/
lemma integral_toMat (A : ℝ → HermitianMat d 𝕜) (T₁ T₂ : ℝ) {μ : Measure ℝ}
  (hA : IntervalIntegrable A μ T₁ T₂) :
    (∫ t in T₁..T₂, A t ∂μ).mat = ∫ t in T₁..T₂, (A t).mat ∂μ := by
  exact ((matₗ (R := ℝ)).intervalIntegral_comp_comm hA).symm

/--
A sum of scaled constant matrices is integrable if the scalar functions are integrable.
-/
lemma intervalIntegrable_sum_smul_const (T₁ T₂ : ℝ) {μ : Measure ℝ} (g : ℝ → d → ℝ)
    (P : d → Matrix d d 𝕜) (hg : ∀ i, IntervalIntegrable (fun t ↦ g t i) μ T₁ T₂) :
    IntervalIntegrable (fun t ↦ ∑ i, g t i • P i) μ T₁ T₂ := by
  simp_all [intervalIntegrable_iff]
  exact integrable_finset_sum _ fun i _ ↦ Integrable.smul_const (hg i) _

/--
A function to Hermitian matrices is integrable iff its matrix values are integrable.
-/
lemma intervalIntegrable_toMat_iff (A : ℝ → HermitianMat d 𝕜) (T₁ T₂ : ℝ) {μ : Measure ℝ} :
    IntervalIntegrable (fun t ↦ (A t).mat) μ T₁ T₂ ↔ IntervalIntegrable A μ T₁ T₂ := by
  --TODO Cleanup
  simp [ intervalIntegrable_iff ];
  constructor <;> intro h;
  · -- Since `toMat` is a linear isometry, the integrability of `A.toMat` implies the integrability of `A`.
    have h_toMat_integrable : IntegrableOn (fun t ↦ (A t).mat) (Set.uIoc T₁ T₂) μ → IntegrableOn A (Set.uIoc T₁ T₂) μ := by
      intro h_toMat_integrable
      have h_toMat_linear : ∃ (L : HermitianMat d 𝕜 →ₗ[ℝ] Matrix d d 𝕜), ∀ x, L x = x.mat := by
        refine' ⟨ _, _ ⟩;
        refine' { .. };
        exacts [ fun x ↦ x.mat, fun x y ↦ rfl, fun m x ↦ rfl, fun x ↦ rfl ];
      obtain ⟨L, hL⟩ := h_toMat_linear;
      have h_toMat_linear : IntegrableOn (fun t ↦ L (A t)) (Set.uIoc T₁ T₂) μ → IntegrableOn A (Set.uIoc T₁ T₂) μ := by
        intro h_toMat_integrable
        have h_toMat_linear : ∃ (L_inv : Matrix d d 𝕜 →ₗ[ℝ] HermitianMat d 𝕜), ∀ x, L_inv (L x) = x := by
          have h_toMat_linear : Function.Injective L := by
            intro x y hxy;
            simp_all only [HermitianMat.ext_iff]
          have h_toMat_linear : ∃ (L_inv : Matrix d d 𝕜 →ₗ[ℝ] HermitianMat d 𝕜), L_inv.comp L = LinearMap.id := by
            exact IsSemisimpleModule.extension_property L h_toMat_linear LinearMap.id;
          exact ⟨ h_toMat_linear.choose, fun x ↦ by simpa using LinearMap.congr_fun h_toMat_linear.choose_spec x ⟩;
        obtain ⟨ L_inv, hL_inv ⟩ := h_toMat_linear;
        have h_toMat_linear : IntegrableOn (fun t ↦ L_inv (L (A t))) (Set.uIoc T₁ T₂) μ := by
          exact ContinuousLinearMap.integrable_comp ( L_inv.toContinuousLinearMap ) h_toMat_integrable;
        aesop;
      aesop;
    exact h_toMat_integrable h;
  · apply h.norm.mono'
    · have := h.aestronglyMeasurable;
      fun_prop
    · filter_upwards with t using le_rfl

/--
The CFC of an integrable function family is integrable.
-/
lemma integrable_cfc (T₁ T₂ : ℝ) (f : ℝ → ℝ → ℝ) {μ : Measure ℝ}
    (hf : ∀ i, IntervalIntegrable (fun t ↦ f t (A.H.eigenvalues i)) μ T₁ T₂) :
    IntervalIntegrable (fun t ↦ A.cfc (f t)) μ T₁ T₂ := by
  have h_expand : ∀ t, (A.cfc (f t)).mat = ∑ i, f t (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact fun t ↦ cfc_toMat_eq_sum_smul_proj A (f t);
  rw [ ← intervalIntegrable_toMat_iff ];
  rw [ funext h_expand ];
  apply intervalIntegrable_sum_smul_const
  exact hf

/--
The integral of the CFC is the CFC of the integral.
-/
lemma integral_cfc_eq_cfc_integral (T₁ T₂ : ℝ) {μ : Measure ℝ} (f : ℝ → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (fun t ↦ f t (A.H.eigenvalues i)) μ T₁ T₂) :
    ∫ t in T₁..T₂, A.cfc (f t) ∂μ = A.cfc (fun u ↦ ∫ t in T₁..T₂, f t u ∂μ) := by
  ext1
  rw [ integral_toMat ];
  · rw [ intervalIntegral.integral_congr fun t ht ↦ HermitianMat.cfc_toMat_eq_sum_smul_proj A ( f t ), intervalIntegral.integral_finset_sum ];
    · rw [ Finset.sum_congr rfl fun i _ ↦ intervalIntegral.integral_smul_const _ _ ];
      exact Eq.symm (cfc_toMat_eq_sum_smul_proj A fun u ↦ ∫ (t : ℝ) in T₁..T₂, f t u ∂μ);
    · simp_all [ intervalIntegrable_iff ];
      exact fun i ↦ ( hf i ).smul_const _
  · exact integrable_cfc T₁ T₂ f hf

end integral

theorem cfc_pos_of_pos {A : HermitianMat d 𝕜} {f : ℝ → ℝ} (hA : 0 < A)
    (hf : ∀ i > 0, 0 < f i) (hf₂ : 0 ≤ f 0) : 0 < A.cfc f := by
  have h_pos := (posSemidef_iff_spectrum_nonneg A).mp hA.le
  have h_f_pos : ∃ x ∈ spectrum ℝ (A.cfc f).mat, x ≠ 0 := by
    obtain ⟨ x, hx₁, hx₂ ⟩ := ne_zero_iff_ne_zero_spectrum A |>.1 hA.ne'
    exact ⟨ f x, by simpa using HermitianMat.spectrum_cfc_eq_image A f ▸ Set.mem_image_of_mem f hx₁, by cases lt_or_gt_of_ne hx₂ <;> linarith [ hf x ( lt_of_le_of_ne ( h_pos x hx₁ ) ( Ne.symm hx₂ ) ) ] ⟩;
  have h_f_nonneg : 0 ≤ A.cfc f := by
    rw [HermitianMat.posSemidef_iff_spectrum_nonneg];
    rw [ HermitianMat.spectrum_cfc_eq_image ];
    rintro _ ⟨ x, hx, rfl ⟩ ; exact if hx0 : x = 0 then by simpa [ hx0 ] using hf₂ else hf x ( lt_of_le_of_ne ( h_pos x hx ) ( Ne.symm hx0 ) ) |> le_of_lt;
  have h_f_nonzero : A.cfc f ≠ 0 := by
    contrapose! h_f_pos;
    simp [h_f_pos, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, Algebra.algebraMap_eq_smul_one]
  exact lt_of_le_of_ne h_f_nonneg h_f_nonzero.symm

/-- If two matrices A and B commute, then they is a common matrix with which they are both CFCs of.
This is a variant of the common theorem that "commuting matrices can be simultaneously diagonalized." -/
theorem _root_.Commute.exists_HermitianMat_cfc (hAB : Commute A.mat B.mat) :
    ∃ C : HermitianMat d 𝕜, (∃ f : ℝ → ℝ, A = C.cfc f) ∧ (∃ g : ℝ → ℝ, B = C.cfc g) := by
  obtain ⟨C, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := hAB.exists_cfc A.H B.H
  by_cases hC : C.IsHermitian
  · use ⟨C, hC⟩
    constructor
    · exact ⟨g₁, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨g₂, by simp [HermitianMat.ext_iff, hg₂]⟩
  · change ¬(IsSelfAdjoint C) at hC
    rw [cfc_apply_of_not_predicate C hC] at hg₁ hg₂
    use 0
    constructor
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₂]⟩

open ComplexOrder in
theorem cfc_le_cfc_of_PosDef (hfg : ∀ i, 0 < i → f i ≤ g i) (hA : A.mat.PosDef) :
    A.cfc f ≤ A.cfc g := by
  rw [← sub_nonneg, ← HermitianMat.cfc_sub, cfc_nonneg_iff]
  intro i
  rw [Pi.sub_apply, sub_nonneg]
  rw [A.H.posDef_iff_eigenvalues_pos] at hA
  apply hfg
  apply hA

open ComplexOrder in
variable {f} in
/- TODO: Write a version of this that holds more broadly for some sets. Esp closed intervals of reals,
which correspond nicely to closed intervals of matrices. Write the specialization to Set.univ (Monotone
instead of MonotoneOn). Also a version that works for StrictMonoOn. -/
theorem cfc_le_cfc_of_commute_monoOn (hf : MonotoneOn f (Set.Ioi 0))
  (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, cfc_nonneg_iff] at hAB₂ ⊢
  intro i
  simp only [Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  · rw [cfc_posDef] at hA
    exact hA i
  · rw [cfc_posDef] at hB
    exact hB i
  · simpa using hAB₂ i

/-- TODO: See above -/
theorem cfc_le_cfc_of_commute (hf : Monotone f) (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  -- Need to show that g₁ ≤ g₂ on spectrum ℝ C
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, cfc_nonneg_iff] at hAB₂ ⊢
  intro i
  simp only [Pi.sub_apply, Function.comp_apply, sub_nonneg]
  apply hf
  simpa using hAB₂ i

--This is the more general version that requires operator concave functions but doesn't require the inputs
-- to commute. Requires the correct statement of operator convexity though, which we don't have right now.
open ComplexOrder in
proof_wanted cfc_monoOn_pos_of_monoOn_posDef {d : Type*} [Fintype d] [DecidableEq d]
  {f : ℝ → ℝ} (hf_is_operator_convex : False) :
    MonotoneOn (HermitianMat.cfc · f) { A : HermitianMat d ℂ | A.mat.PosDef }

section uncategorized_cleanup

open ComplexOrder in
theorem inv_ge_one_of_le_one (hA : A.mat.PosDef) (h : A ≤ 1) : 1 ≤ A⁻¹ := by
  --TODO Cleanup
  have := nonSingular_of_posDef hA
  have h_inv_ge_one : ∀ i, 1 ≤ 1 / A.H.eigenvalues i := by
    intro i
    have h_eigenvalue : 0 < A.H.eigenvalues i := by
      exact hA.eigenvalues_pos i
    have h_eigenvalue_le_one : A.H.eigenvalues i ≤ 1 := by
      have h_eigenvalue_le_one : ∀ x : d → 𝕜, x ≠ 0 → (star x ⬝ᵥ A.mat.mulVec x) / (star x ⬝ᵥ x) ≤ 1 := by
        intro x hx_nonzero
        have h_eigenvalue_le_one : (star x ⬝ᵥ A.mat.mulVec x) ≤ (star x ⬝ᵥ x) := by
          have h_eigenvalue_le_one : ∀ x : d → 𝕜, x ≠ 0 → (star x ⬝ᵥ A.mat.mulVec x) ≤ (star x ⬝ᵥ x) := by
            intro x hx_nonzero
            have h_eigenvalue_le_one : (star x ⬝ᵥ (1 - A.mat).mulVec x) ≥ 0 := by
              exact h.2 x
            simp_all +decide [ Matrix.sub_mulVec, dotProduct_sub ];
          exact h_eigenvalue_le_one x hx_nonzero
        generalize_proofs at *;
        convert div_le_one_of_le₀ h_eigenvalue_le_one _ using 1
        generalize_proofs at *;
        · exact PosMulReflectLT.toMulPosReflectLT;
        · exact dotProduct_star_self_nonneg x
      generalize_proofs at *;
      convert h_eigenvalue_le_one ( A.H.eigenvectorBasis i ) ( by intro h; simpa [ h ] using A.H.eigenvectorBasis.orthonormal.1 i ) using 1 ; simp [ Matrix.mulVec, dotProduct ];
      rw [ show ( ∑ x, ( starRingEnd 𝕜 ) ( A.H.eigenvectorBasis i x ) * ∑ x_1, A x x_1 * A.H.eigenvectorBasis i x_1 ) = ( A.H.eigenvalues i ) * ( ∑ x, ( starRingEnd 𝕜 ) ( A.H.eigenvectorBasis i x ) * A.H.eigenvectorBasis i x ) from ?_ ];
      · rw [ mul_div_cancel_right₀ ];
        · norm_cast;
        · have := A.H.eigenvectorBasis.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
          specialize this i i ; simp_all +decide [ Inner.inner ];
          simp_all [ mul_comm ];
      · have := A.H.mulVec_eigenvectorBasis i; simp_all [ Matrix.mulVec, dotProduct ] ;
        replace this := congr_arg ( fun x => ∑ j, ( starRingEnd 𝕜 ) ( A.H.eigenvectorBasis i j ) * x j ) this ; simp_all [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ] ;
        norm_num [ Algebra.smul_def ]
    exact one_le_one_div h_eigenvalue h_eigenvalue_le_one;
  replace h_inv_ge_one : 0 ≤ A.cfc (fun x => x⁻¹ - 1) := by
    simpa only [cfc_nonneg_iff, ← one_div, sub_nonneg]
  convert add_le_add_right h_inv_ge_one 1 using 1;
  · norm_num;
  · rw [ ← cfc_inv, ← sub_eq_zero ];
    rw [ ← sub_sub, ← cfc_sub ];
    simp [ Pi.sub_def ]

end uncategorized_cleanup

lemma mulVec_eq_zero_iff_inner_eigenvector_zero
    (A : HermitianMat d ℂ) (x : EuclideanSpace ℂ d) :
    A.mat.mulVec x = 0 ↔ ∀ i, A.H.eigenvalues i ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
  constructor <;> intro h
  · simp only [ne_eq]
    intro i hi; have := A.2;
    simp_all only [val_eq_coe] ;
    have := Matrix.IsHermitian.mulVec_eigenvectorBasis A.2 i;
    replace this := congr_arg ( fun y => inner ℂ y x ) this
    simp only [val_eq_coe, CStarModule.inner_smul_left_real, Complex.real_smul] at this;
    rename_i this1
    simp only [selfAdjoint, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] at this1
    simp only [IsSelfAdjoint] at this1
    simp only [inner, Matrix.mulVec, dotProduct, mat_apply, PiLp.ofLp_apply, map_sum,
      map_mul] at this ⊢
    simp only [funext_iff, Pi.zero_apply, ← Matrix.ext_iff, Matrix.star_apply, mat_apply,
      RCLike.star_def] at this this1 h
    simp_all only [Matrix.mulVec, dotProduct, mat_apply, mul_comm, Finset.mul_sum, mul_left_comm];
    rw [ Finset.sum_comm ] at this
    simp_all only [← mul_assoc, ← Finset.sum_mul, zero_mul, Finset.sum_const_zero] ;
    rw [ eq_comm ] at this
    simp_all only [mul_assoc] ;
    rw [ ← Finset.sum_congr rfl fun _ _ => by rw [ mul_left_comm ] ] at this
    simp_all [← Finset.mul_sum]
  · ext i
    replace this := congr_arg ( fun m => m.mulVec x i ) A.H.spectral_theorem
    simp_all only [ne_eq, Matrix.mulVec, mat_apply, Complex.coe_algebraMap,
      Matrix.mul_assoc, Pi.zero_apply];
    simp_all only [dotProduct, Matrix.mul_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
      PiLp.ofLp_apply, Matrix.star_apply, RCLike.star_def];
    simp_all only [Matrix.diagonal, Function.comp_apply, Matrix.of_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, ↓reduceIte, mul_left_comm, Finset.sum_mul, mul_assoc];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_eq_zero fun j hj => _;
    by_cases h2 : A.H.eigenvalues j = 0
    · simp_all only [mul_comm, mul_left_comm, Finset.mem_univ, Complex.ofReal_zero, zero_mul,
        mul_zero, Finset.sum_const_zero];
    simp_all only [mul_comm, mul_left_comm, Finset.mem_univ];
    convert congr_arg (fun y => A.H.eigenvalues j * (A.H.eigenvectorBasis j i) * y) (h j h2) using 1
    · simp [mul_comm, mul_left_comm, Finset.mul_sum, inner]
    · ring

open InnerProductSpace in
lemma cfc_mulVec_expansion (A : HermitianMat d ℂ) (f : ℝ → ℝ) (x : EuclideanSpace ℂ d) :
    (A.cfc f).mat.mulVec x = ∑ i, (f (A.H.eigenvalues i) : ℂ) • inner ℂ (A.H.eigenvectorBasis i) x • A.H.eigenvectorBasis i := by
  have h_apply : ∀ i,
     (Matrix.mulVec (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) x) = (⟪(A.H.eigenvectorBasis i), x⟫_ℂ) • (A.H.eigenvectorBasis i) := by
    intro i
    have h_apply : (Matrix.mulVec (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) x) = (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose).mulVec x := by
      rfl;
    ext j; simp [ Matrix.mulVec, dotProduct, inner ]
    ring_nf
    simp [ Matrix.mul_apply, Matrix.single, Finset.sum_mul _ _ _ ]
    ring_nf
    rw [ Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_eq_single i ( by aesop ) ( by aesop ) ]
    simp [ mul_comm, mul_left_comm ]
  have h_apply : (A.cfc f).mat = ∑ i, (f (A.H.eigenvalues i) : ℂ) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj A f;
  simp only [h_apply, Complex.coe_smul];
  simp only [mul_assoc, ← ‹∀ i, _›];
  ext i; simp only [Matrix.mulVec, dotProduct] ;
  simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, Finset.sum_mul];
  rw [ Finset.sum_apply ];
  rw [ Finset.sum_comm ];
  simp only [mul_assoc, PiLp.smul_apply, Matrix.mulVec, dotProduct, Complex.real_smul,
    Finset.mul_sum]

section ker_cfc

variable {A : HermitianMat d ℂ} {f : ℝ → ℝ} {s : Set ℝ}

lemma ker_cfc_le_ker_on_set
    (hs : spectrum ℝ A.mat ⊆ s)
    (h : ∀ i ∈ s, f i = 0 → i = 0) :
    (A.cfc f).ker ≤ A.ker := by
  intro x hx
  have h_f_nonzero : ∀ i, A.H.eigenvalues i ≠ 0 → f (A.H.eigenvalues i) ≠ 0 := by
    refine fun i hi => fun hi' => hi (h _ ?_ hi')
    rw [A.H.spectrum_real_eq_range_eigenvalues] at hs
    grind only [= Set.mem_range, = Set.subset_def]
  apply (A.mulVec_eq_zero_iff_inner_eigenvector_zero x).mpr
  intro i hi
  have h_coeff : (f (A.H.eigenvalues i) : ℂ) • inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
    have h_coeff : ∑ j, (f (A.H.eigenvalues j) : ℂ) • inner ℂ (A.H.eigenvectorBasis j) x • A.H.eigenvectorBasis j = 0 := by
      convert congr_arg ( fun y => y ) ( show ( A.cfc f ).mat.mulVec x = 0 from by simpa [ Matrix.mulVec ] using hx ) using 1;
      convert A.cfc_mulVec_expansion f x |> Eq.symm using 1;
    apply_fun (fun y => inner ℂ (A.H.eigenvectorBasis i) y) at h_coeff;
    simp_all [ orthonormal_iff_ite.mp ( A.H.eigenvectorBasis.orthonormal ) ];
  exact smul_eq_zero.mp h_coeff |> Or.resolve_left <| mod_cast h_f_nonzero i hi

lemma ker_cfc_le_ker (h : ∀ i, f i = 0 → i = 0) :
    (A.cfc f).ker ≤ A.ker := by
  exact ker_cfc_le_ker_on_set (Set.subset_univ _) (by simpa using h)

lemma ker_cfc_le_ker_nonneg (hA : 0 ≤ A) (h : ∀ i ≥ 0, f i = 0 → i = 0) :
    (A.cfc f).ker ≤ A.ker := by
  rw [posSemidef_iff_spectrum_Ici] at hA
  exact ker_cfc_le_ker_on_set hA h

lemma ker_le_ker_cfc_on_set (hs : spectrum ℝ A.mat ⊆ s) (h : ∀ i ∈ s, i = 0 → f i = 0) :
    A.ker ≤ (A.cfc f).ker := by
  intro x hx;
  have h_inner_zero : ∀ i, f (A.H.eigenvalues i) ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
    intro i hi
    have h_inner_zero : A.H.eigenvalues i ≠ 0 := by
      refine fun hi' => hi <| h _ ?_ hi'
      rw [A.H.spectrum_real_eq_range_eigenvalues] at hs
      grind only [= Set.mem_range, = Set.subset_def]
    exact HermitianMat.mulVec_eq_zero_iff_inner_eigenvector_zero A x |>.1 hx i h_inner_zero;
  have h_inner_zero : (A.cfc f).mat.mulVec x = 0 := by
    rw [HermitianMat.cfc_mulVec_expansion];
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : f ( A.H.eigenvalues i ) = 0
    · simp_all only [ne_eq, Finset.mem_univ, Complex.coe_smul, smul_eq_zero, true_or]
    · simp_all only [ne_eq, Finset.mem_univ, not_false_eq_true, zero_smul, smul_zero]
  exact h_inner_zero

lemma ker_le_ker_cfc (h : ∀ i, i = 0 → f i = 0) :
    A.ker ≤ (A.cfc f).ker := by
  exact ker_le_ker_cfc_on_set (Set.subset_univ _) (by simpa using h)

lemma ker_le_ker_cfc_nonneg (hA : 0 ≤ A) (h : ∀ i ≥ 0, i = 0 → f i = 0) :
    A.ker ≤ (A.cfc f).ker := by
  rw [posSemidef_iff_spectrum_Ici] at hA
  exact ker_le_ker_cfc_on_set hA h

theorem ker_cfc_eq_ker (h : ∀ i, f i = 0 ↔ i = 0) :
    (A.cfc f).ker = A.ker := by
  refine le_antisymm (ker_cfc_le_ker ?_) (ker_le_ker_cfc ?_)
  <;> grind only

theorem ker_cfc_eq_ker_nonneg (hA : 0 ≤ A) (h : ∀ i ≥ 0, f i = 0 ↔ i = 0) :
    (A.cfc f).ker = A.ker := by
  refine le_antisymm (ker_cfc_le_ker_nonneg hA ?_) (ker_le_ker_cfc_nonneg hA ?_)
  <;> grind only

end ker_cfc
end CFC
