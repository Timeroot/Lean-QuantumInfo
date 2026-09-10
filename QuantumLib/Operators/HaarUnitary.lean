/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazumi Kasaura, Hayata Yamasaki
-/

import QuantumLib.Channels.Superoperator
import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LiebAndoTrace
import QuantumLib.ForMathlib.TensorCFC
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Haar measure on the unitary group, and the twirl

The normalized (probability) Haar measure on the unitary group of a finite-dimensional Hilbert
space, the twirl identity it satisfies, and Jensen-type inequalities for jointly convex and
concave operator functions under Haar integration.

These are the measure-theoretic ingredients that carry monotonicity of the sandwiched Rényi
relative entropy (Theorem 1 of Frank–Lieb, arXiv:1306.5358) back to the joint convexity and
concavity of the sandwiched quasi-relative entropy (Proposition 3 of the same paper).

## Convention

We write `TrLeft` for `QuantumChannel.TrLeft`, which traces out the **first** tensor factor:
  `TrLeft : L(ℋ₁ ⊗ ℋ₂) → L ℋ₂`.
When the first factor is the "environment" ℋ_env and the second is the main system ℋ,
`TrLeft` computes the partial trace over the environment. This matches the Stinespring
convention `E(γ) = TrLeft(U (τ ⊗ γ) U*)` where τ is the environment state on ℋ₁ and
γ is the input state on ℋ₂.
-/

open QuantumState QuantumChannel TensorCFC
open MeasureTheory MeasureTheory.Measure
open GeneralizedPerspectiveFunction
open scoped ComplexOrder TensorProduct

namespace HaarUnitary

universe u

/-! ## Section 1: Compactness of the unitary group and Haar measure -/

section CompactHaar

variable {ℋ : Type u} [Qudit ℋ]

/-- Operators carry the Borel σ-algebra of their norm topology, so that operator-valued
functions on the unitary group can be integrated. -/
noncomputable instance instMeasurableSpaceLM : MeasurableSpace (L ℋ) := borel (L ℋ)

/-- That σ-algebra is the Borel one by definition. -/
instance instBorelSpaceLM : BorelSpace (L ℋ) := ⟨rfl⟩

/-- Every unitary operator on a finite-dimensional Hilbert space has operator norm ≤ 1. -/
lemma unitaryNormBound [Nontrivial ℋ] (U : unitary (L ℋ)) : ‖(U : L ℋ)‖ ≤ 1 := by
  rw [CStarRing.norm_coe_unitary]

/-- The unitary group on a finite-dimensional Hilbert space is bounded. -/
lemma unitary_isBounded [Nontrivial ℋ] : Bornology.IsBounded (unitary (L ℋ) : Set (L ℋ)) := by
  rw [Metric.isBounded_iff_subset_ball 0]
  exact ⟨2, fun x hx => by
    simp only [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (unitaryNormBound ⟨x, hx⟩) one_lt_two⟩

/-- The unitary group on a finite-dimensional Hilbert space is compact
    (closed + bounded in a finite-dimensional normed space). -/
instance compactSpace_unitary [Nontrivial ℋ] : CompactSpace (unitary (L ℋ)) := by
  have : ProperSpace (L ℋ) := FiniteDimensional.proper ℂ (L ℋ)
  exact isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_unitary unitary_isBounded)

/-- The unitary group is locally compact, being compact; this is what `haarMeasure` asks for. -/
instance locallyCompactSpace_unitary [Nontrivial ℋ] : LocallyCompactSpace (unitary (L ℋ)) := by
  have : ProperSpace (unitary (L ℋ)) := proper_of_compact
  exact locallyCompact_of_proper

/-- The whole unitary group, as the positive compact set that `haarMeasure` normalises against. -/
private noncomputable def unitaryPC (ℋ : Type u) [Qudit ℋ] [Nontrivial ℋ] :
    TopologicalSpace.PositiveCompacts (unitary (L ℋ)) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by rw [interior_univ]; exact Set.univ_nonempty⟩

/-- The normalized (probability) Haar measure on the unitary group of `L ℋ`.
    Normalized so that `haarUnitary ℋ Set.univ = 1`, making it a probability measure. -/
noncomputable def haarUnitary (ℋ : Type u) [Qudit ℋ] [Nontrivial ℋ] :
    Measure (unitary (L ℋ)) :=
  haarMeasure (unitaryPC ℋ)

/-- `haarUnitary` is a Haar measure, hence left invariant. -/
instance haarUnitary_isHaarMeasure [Nontrivial ℋ] :
    IsHaarMeasure (haarUnitary ℋ) := by
  unfold haarUnitary
  infer_instance

/-- `haarUnitary` is a probability measure on a compact group. -/
instance haarUnitary_isProbabilityMeasure [Nontrivial ℋ] :
    IsProbabilityMeasure (haarUnitary ℋ) :=
  ⟨by change haarMeasure (unitaryPC ℋ) Set.univ = 1
      have : haarMeasure (unitaryPC ℋ) (unitaryPC ℋ : Set _) = 1 := haarMeasure_self
      simpa [unitaryPC] using this⟩

end CompactHaar

/-! ## Section 2: Measurability and integrability of conjugation -/

section Measurability

variable {ℋ : Type u} [Qudit ℋ]

/-- Conjugation `u ↦ u X u†` is continuous on the unitary group. -/
lemma continuous_unitaryConj (X : L ℋ) :
    Continuous (fun u : unitary (L ℋ) => (u : L ℋ) * X * (star (u : L ℋ))) := by
  have hval : Continuous (fun u : unitary (L ℋ) => (u : L ℋ)) := continuous_subtype_val
  have hstar : Continuous (fun u : unitary (L ℋ) => star (u : L ℋ)) :=
    continuous_star.comp hval
  exact ((hval.mul continuous_const).mul hstar)

/-- Conjugation is integrable with respect to `haarUnitary`. -/
lemma integrable_unitaryConj [Nontrivial ℋ] (X : L ℋ) :
    Integrable (fun u : unitary (L ℋ) => (u : L ℋ) * X * (star (u : L ℋ)))
      (haarUnitary ℋ) :=
  (continuous_unitaryConj X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

end Measurability

/-! ## Section 3: Twirl (Schur averaging) identity

The core result is `twirl_eq_smul_one`: averaging unitary conjugation over the Haar measure
produces a scalar multiple of the identity. The averaged operator commutes with every unitary, by
left invariance of the Haar measure, and `scalar_of_commutes_unitaries` turns that into being a
scalar: reflections in unit vectors are unitary, and commuting with all of them makes every unit
vector an eigenvector, with one eigenvalue shared between them. The scalar is then read off from
the trace.

The Schur orthogonality relation and the tensor-product twirl identities are consequences.
-/

section Twirl

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- The rank-one projection P_v = |v⟩⟨v|. -/
private noncomputable def proj (v : ℋ) : L ℋ :=
  outerProduct v v

omit [Nontrivial ℋ] in
/-- `proj v` sends `w` to `⟪v, w⟫ • v`. -/
private lemma proj_apply (v w : ℋ) : proj v w = @inner ℂ ℋ _ v w • v := by
  simp [proj]

/-- The reflection R_v = 1 - 2|v⟩⟨v|. -/
private noncomputable def refl' (v : ℋ) : L ℋ :=
  (1 : L ℋ) - (2 : ℂ) • proj v

omit [Nontrivial ℋ] in
/-- `refl' v` sends `w` to `w - 2⟪v, w⟫ • v`. -/
private lemma refl'_apply (v w : ℋ) :
    refl' v w = w - (2 : ℂ) • @inner ℂ ℋ _ v w • v := by
  simp [refl', proj_apply, smul_smul]

omit [Nontrivial ℋ] in
/-- A rank-one projection is self-adjoint. -/
private lemma star_proj (v : ℋ) : star (proj v) = proj v := by
  rw [proj, ContinuousLinearMap.star_eq_adjoint, adjoint_outerProduct]

omit [Nontrivial ℋ] in
/-- A reflection in a unit vector is an involution. -/
private lemma refl'_sq (v : ℋ) (hv : ‖v‖ = 1) : refl' v * refl' v = 1 := by
  have hiv : @inner ℂ ℋ _ v v = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hv]
    simp
  ext w
  change refl' v (refl' v w) = w
  have h1 : refl' v w = w - (2 * @inner ℂ ℋ _ v w) • v := by
    rw [refl'_apply, smul_smul]
  have h2 : @inner ℂ ℋ _ v (refl' v w) = -@inner ℂ ℋ _ v w := by
    rw [h1, inner_sub_right, inner_smul_right, hiv]
    ring
  rw [refl'_apply, h2, smul_smul, h1]
  simp only [mul_neg, neg_smul, sub_neg_eq_add, sub_add_cancel]

omit [Nontrivial ℋ] in
/-- A reflection is self-adjoint. -/
private lemma refl'_star (v : ℋ) : star (refl' v) = refl' v := by
  simp [refl', star_sub, star_one, star_smul, star_proj]

omit [Nontrivial ℋ] in
/-- A reflection in a unit vector is unitary, being a self-adjoint involution. -/
private lemma refl'_unitary (v : ℋ) (hv : ‖v‖ = 1) : refl' v ∈ unitary (L ℋ) := by
  rw [Unitary.mem_iff]
  exact ⟨by rw [refl'_star, refl'_sq v hv], by rw [refl'_star, refl'_sq v hv]⟩

/-- An element of `L ℋ` that commutes with all unitaries is a scalar multiple
    of the identity. Uses reflection unitaries and the eigenvector argument. -/
lemma scalar_of_commutes_unitaries (M : L ℋ)
    (hM : ∀ V : unitary (L ℋ), (V : L ℋ) * M = M * (V : L ℋ)) :
    ∃ c : ℂ, M = c • (1 : L ℋ) := by
  -- Step 1: for unit v and any x, ⟨v, Mx⟩ v = ⟨v, x⟩ Mv (from reflection commutation)
  have proj_comm : ∀ (v : ℋ), ‖v‖ = 1 → ∀ (x : ℋ),
      @inner ℂ ℋ _ v (M x) • v = @inner ℂ ℋ _ v x • M v := by
    intro v hv x
    have h : refl' v (M x) = M (refl' v x) :=
      congr_fun (congr_arg DFunLike.coe (hM ⟨refl' v, refl'_unitary v hv⟩)) x
    rw [refl'_apply, refl'_apply, map_sub, map_smul, map_smul, smul_smul, smul_smul] at h
    have h' := congr_arg Neg.neg h
    simp only [neg_sub] at h'
    have hsub := sub_left_injective h'
    rw [mul_smul, mul_smul] at hsub
    exact smul_right_injective ℋ (two_ne_zero (α := ℂ)) hsub
  -- Step 2: for unit v, M v = ⟨v, Mv⟩ v
  have unit_eig : ∀ (v : ℋ), ‖v‖ = 1 → M v = @inner ℂ ℋ _ v (M v) • v := by
    intro v hv
    have h := proj_comm v hv v
    rw [show @inner ℂ ℋ _ v v = (1 : ℂ) from by
      rw [inner_self_eq_norm_sq_to_K, hv]; simp, one_smul] at h
    exact h.symm
  -- Step 3: the eigenvalue is constant across all unit vectors
  have eig_const : ∀ (v w : ℋ), ‖v‖ = 1 → ‖w‖ = 1 →
      @inner ℂ ℋ _ v (M v) = @inner ℂ ℋ _ w (M w) := by
    intro v w hv hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, norm_zero] at hw
      exact one_ne_zero hw.symm
    by_cases hvw : v + w = 0
    · have hwv : w = -v := eq_neg_of_add_eq_zero_right hvw
      rw [hwv, map_neg, inner_neg_left, inner_neg_right, neg_neg]
    · by_cases hli : LinearIndependent ℂ ![v, w]
      · have hvwn : ‖v + w‖ ≠ 0 := norm_ne_zero_iff.mpr hvw
        set u := ((↑‖v + w‖ : ℂ)⁻¹) • (v + w) with hu_def
        have hcinv : ((↑‖v + w‖ : ℂ)⁻¹) ≠ 0 :=
          inv_ne_zero (Complex.ofReal_ne_zero.mpr hvwn)
        have hu : ‖u‖ = 1 := by
          rw [hu_def, norm_smul, norm_inv, Complex.norm_real, norm_norm,
              inv_mul_cancel₀ hvwn]
        set lv := @inner ℂ ℋ _ v (M v)
        set lw := @inner ℂ ℋ _ w (M w)
        have hMu2 : M u = (↑‖v + w‖ : ℂ)⁻¹ • (lv • v + lw • w) := by
          conv_lhs => rw [hu_def, map_smul, map_add, unit_eig v hv, unit_eig w hw]
        have hMu1 : M u = @inner ℂ ℋ _ u (M u) • u := unit_eig u hu
        have h3 := hMu1.symm.trans hMu2
        rw [hu_def, smul_comm] at h3
        have key : @inner ℂ ℋ _ u (M u) • (v + w) = lv • v + lw • w :=
          smul_right_injective ℋ hcinv h3
        rw [smul_add] at key
        have hsub : (@inner ℂ ℋ _ u (M u) - lv) • v +
            (@inner ℂ ℋ _ u (M u) - lw) • w = 0 := by
          rw [sub_smul, sub_smul, sub_add_sub_comm, sub_eq_zero]
          exact key
        obtain ⟨h1, h2⟩ := hli.eq_zero_of_pair hsub
        exact (sub_eq_zero.mp h1).symm.trans (sub_eq_zero.mp h2)
      · simp only [linearIndependent_fin2, Matrix.cons_val_one,
            Matrix.cons_val_zero, not_and_or, not_forall, Classical.not_not] at hli
        rcases hli with hw0' | ⟨a, ha⟩
        · exact absurd hw0' hw0
        · set lv := @inner ℂ ℋ _ v (M v)
          set lw := @inner ℂ ℋ _ w (M w)
          have ha0 : a ≠ 0 := by
            intro h
            rw [h, zero_smul] at ha
            have hv0 : v ≠ 0 := by
              intro h
              rw [h, norm_zero] at hv
              exact one_ne_zero hv.symm
            exact hv0 ha.symm
          have h2 : M v = (a * lw) • w := by
            conv_lhs =>
              rw [← ha, map_smul, unit_eig w hw]
              rw [smul_smul]
          have h3 : lv • v = (a * lw) • w := (unit_eig v hv).symm.trans h2
          rw [show v = a • w from ha.symm, smul_smul] at h3
          have h4 : (lv * a - a * lw) • w = 0 := by
            rw [sub_smul, sub_eq_zero]
            exact h3
          have h5 : lv * a = a * lw := sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hw0)
          exact mul_left_cancel₀ ha0 (by rwa [mul_comm lv a] at h5)
  -- Step 4: define c and show M = c • 1
  obtain ⟨e, he⟩ : ∃ e : ℋ, ‖e‖ = 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : ℋ)
    exact ⟨(‖v‖⁻¹ : ℝ) • v, by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  refine ⟨@inner ℂ ℋ _ e (M e), ?_⟩
  ext x
  change M x = @inner ℂ ℋ _ e (M e) • ((1 : L ℋ) x)
  rw [show (1 : L ℋ) x = x from rfl]
  by_cases hx : x = 0
  · simp [hx]
  · set u := ((↑‖x‖ : ℂ)⁻¹) • x with hu_def
    have hcinv : ((↑‖x‖ : ℂ)⁻¹) ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx))
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, Complex.norm_real, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have hMu := unit_eig u hu
    rw [eig_const u e hu he] at hMu
    rw [hu_def, map_smul, smul_comm] at hMu
    exact smul_right_injective ℋ hcinv hMu

/-- **The twirl of an operator is a scalar.** Averaging `u X u†` over the Haar measure on the
unitary group gives `((dim ℋ)⁻¹ * Tr X) • 1`. -/
theorem twirl_eq_smul_one (X : L ℋ) :
    ∫ u : unitary (L ℋ), (u : L ℋ) * X * star (u : L ℋ) ∂(haarUnitary ℋ) =
    ((Module.finrank ℂ ℋ : ℂ)⁻¹ * Tr X) • (1 : L ℋ) := by
  set Φ := ∫ u : unitary (L ℋ), (u : L ℋ) * X * star (u : L ℋ) ∂(haarUnitary ℋ)
  -- Step 1: Φ commutes with all unitaries V (by Haar left-invariance)
  have hΦ_comm : ∀ V : unitary (L ℋ), (V : L ℋ) * Φ = Φ * (V : L ℋ) := by
    intro V
    suffices h_conj : (V : L ℋ) * Φ * star (V : L ℋ) = Φ by
      have hVV : star (↑V : L ℋ) * ↑V = 1 := (Unitary.mem_iff.mp V.property).1
      calc (↑V : L ℋ) * Φ
          = ↑V * Φ * 1 := (mul_one _).symm
        _ = ↑V * Φ * (star ↑V * ↑V) := by rw [hVV]
        _ = ↑V * Φ * star ↑V * ↑V := by rw [mul_assoc (↑V * Φ)]
        _ = Φ * ↑V := by rw [h_conj]
    let conjV : L ℋ →L[ℂ] L ℋ := ⟨{
      toFun := fun A => (V : L ℋ) * A * star (V : L ℋ)
      map_add' := fun A B => by rw [mul_add, add_mul]
      map_smul' := fun c A => by rw [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]
    }, (continuous_const.mul continuous_id).mul continuous_const⟩
    have h_pull := conjV.integral_comp_comm (integrable_unitaryConj X)
    have hfVu : ∀ u : unitary (L ℋ),
        conjV ((u : L ℋ) * X * star (u : L ℋ)) =
        ((V * u : unitary (L ℋ)) : L ℋ) * X * star ((V * u : unitary (L ℋ)) : L ℋ) := by
      intro u
      change (V : L ℋ) * ((u : L ℋ) * X * star (u : L ℋ)) * star (V : L ℋ) = _
      simp only [MulMemClass.coe_mul, star_mul, mul_assoc]
    simp_rw [hfVu] at h_pull
    have h_haar := integral_mul_left_eq_self (μ := haarUnitary ℋ)
      (fun u : unitary (L ℋ) => (u : L ℋ) * X * star (u : L ℋ)) V
    exact (h_pull.symm.trans h_haar)
  -- Step 2: Φ is scalar (from scalar_of_commutes_unitaries)
  obtain ⟨c, hc⟩ := scalar_of_commutes_unitaries Φ hΦ_comm
  -- Step 3: determine c from trace (Tr(Φ) = Tr(X) since trace is cyclic and Haar is prob.)
  have hc_val : c = (Module.finrank ℂ ℋ : ℂ)⁻¹ * Tr X := by
    have hd : (Module.finrank ℂ ℋ : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := ℋ)).ne'
    have h1 : Tr Φ = c * (Module.finrank ℂ ℋ : ℂ) := by
      rw [hc, map_smul, Tr_one, smul_eq_mul]
    have h2 : Tr Φ = Tr X := by
      let trCLM : L ℋ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap Tr
      have h_tr := trCLM.integral_comp_comm (integrable_unitaryConj X)
      have h_cycl : ∀ u : unitary (L ℋ),
          trCLM ((u : L ℋ) * X * star (u : L ℋ)) = Tr X := by
        intro u
        change Tr ((u : L ℋ) * X * star (u : L ℋ)) = _
        rw [Tr_mul_cycle,
            show star (↑u : L ℋ) * (↑u : L ℋ) = 1 from (Unitary.mem_iff.mp u.property).1,
            one_mul]
      simp_rw [h_cycl] at h_tr
      simp only [integral_const, probReal_univ, one_smul] at h_tr
      exact h_tr.symm
    have h := h1.symm.trans h2
    rw [← h, mul_comm c (Module.finrank ℂ ℋ : ℂ), ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  rw [hc, hc_val]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- **Schur orthogonality** for the fundamental representation of the unitary group. Writing
`u i j` for the matrix entry `⟪b i, u (b j)⟫` in an orthonormal basis `b`, the average of
`u i j * conj (u k l)` is `(dim ℋ)⁻¹` when `i = k` and `j = l`, and `0` otherwise. It comes from
`twirl_eq_smul_one` applied to `|b j⟩⟨b l|`, read off at the `(i, k)` entry. -/
theorem schur_orthogonality (b : OrthonormalBasis ι ℂ ℋ) (i j k l : ι) :
    ∫ u : unitary (L ℋ),
      @inner ℂ ℋ _ (b i) ((u : L ℋ) (b j)) *
      starRingEnd ℂ (@inner ℂ ℋ _ (b k) ((u : L ℋ) (b l)))
    ∂(haarUnitary ℋ) =
    if i = k ∧ j = l then (Fintype.card ι : ℂ)⁻¹ else 0 := by
  set X : L ℋ := outerProduct (b l) (b j) with hX
  have h_int : ∀ u : unitary (L ℋ),
      @inner ℂ ℋ _ (b i) ((u : L ℋ) (b j)) *
      starRingEnd ℂ (@inner ℂ ℋ _ (b k) ((u : L ℋ) (b l))) =
      @inner ℂ ℋ _ (b i) (((u : L ℋ) * X * star (u : L ℋ)) (b k)) := by
    intro u
    change _ = @inner ℂ ℋ _ (b i) ((↑u : L ℋ) (X ((star (↑u : L ℋ)) (b k))))
    have hXapp : X ((star (↑u : L ℋ)) (b k)) =
        @inner ℂ ℋ _ (b l) ((star (↑u : L ℋ)) (b k)) • b j := by
      rw [hX, outerProduct_apply]
    rw [hXapp, map_smul, inner_smul_right]
    suffices h : @inner ℂ ℋ _ (b l) ((star (↑u : L ℋ)) (b k)) =
        starRingEnd ℂ (@inner ℂ ℋ _ (b k) ((↑u : L ℋ) (b l))) by
          rw [h]
          ring
    rw [← inner_conj_symm]
    congr 1
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left (↑u : L ℋ) (b l) (b k)
  simp_rw [h_int]
  let lm : L ℋ →ₗ[ℂ] ℂ := ⟨⟨fun A => @inner ℂ ℋ _ (b i) (A (b k)),
    fun A B => by simp⟩, fun c A => by simp⟩
  let elem : L ℋ →L[ℂ] ℂ := ⟨lm, map_continuous lm⟩
  have h_eq : ∀ u : unitary (L ℋ),
      @inner ℂ ℋ _ (b i) (((u : L ℋ) * X * star (u : L ℋ)) (b k)) =
      elem ((u : L ℋ) * X * star (u : L ℋ)) := fun _ => rfl
  simp_rw [h_eq]
  rw [elem.integral_comp_comm (integrable_unitaryConj X), twirl_eq_smul_one X]
  change @inner ℂ ℋ _ (b i) (((Module.finrank ℂ ℋ : ℂ)⁻¹ * Tr X) • b k) =
    if i = k ∧ j = l then (Fintype.card ι : ℂ)⁻¹ else 0
  rw [inner_smul_right]
  have hTr : Tr X = @inner ℂ ℋ _ (b l) (b j) := by
    rw [hX, trace_outerProduct]
  rw [hTr, Module.finrank_eq_card_basis b.toBasis]
  have horth := orthonormal_iff_ite.mp b.orthonormal
  rw [horth l j, horth i k]
  simp only [show (l = j) = (j = l) from propext eq_comm]
  by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]

variable {ℋ₁ : Type u} {ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁] [Nontrivial ℋ₂]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- `f ⊗ 1` is the amplification `rTensorStarAlgHom f`. -/
private lemma mapL_one_eq_rTensorStarAlgHom (f : L ℋ₁) :
    TensorProduct.mapL f (1 : L ℋ₂) = (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f := by
  rw [map_eq_rTensor_mul_lTensor, map_one (lTensorStarAlgHom (ℋ₁ := ℋ₁)), mul_one]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- `1 ⊗ g` is the amplification `lTensorStarAlgHom g`. -/
private lemma one_mapL_eq_lTensorStarAlgHom (g : L ℋ₂) :
    TensorProduct.mapL (1 : L ℋ₁) g = (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g := by
  rw [map_eq_rTensor_mul_lTensor, map_one (rTensorStarAlgHom (ℋ₂ := ℋ₂)), one_mul]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Tensor-product conjugation `u ↦ (u ⊗ 1) X (u† ⊗ 1)` is continuous. -/
lemma continuous_unitaryConj_tensor (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Continuous (fun u : unitary (L ℋ₁) =>
      TensorProduct.mapL ((u : L ℋ₁)) (1 : L ℋ₂) * X *
      TensorProduct.mapL (star (u : L ℋ₁)) (1 : L ℋ₂)) := by
  simp_rw [mapL_one_eq_rTensorStarAlgHom]
  exact (((continuous_rTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).comp
    continuous_subtype_val).mul continuous_const).mul
    ((continuous_rTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).comp
      (continuous_star.comp continuous_subtype_val))

omit [Nontrivial ℋ₂] in
/-- Tensor-product conjugation is integrable against the Haar measure on the first factor. -/
lemma integrable_unitaryConj_tensor (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Integrable (fun u : unitary (L ℋ₁) =>
      TensorProduct.mapL ((u : L ℋ₁)) (1 : L ℋ₂) * X *
      TensorProduct.mapL (star (u : L ℋ₁)) (1 : L ℋ₂))
      (haarUnitary ℋ₁) :=
  (continuous_unitaryConj_tensor X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

omit [Nontrivial ℋ₂] in
/-- **Twirl over the first factor.** Averaging `(u ⊗ 1) X (u† ⊗ 1)` over the Haar measure on
`unitary (L ℋ₁)` leaves the first factor maximally mixed and the second factor traced out:
`∫ (u ⊗ 1) X (u† ⊗ 1) = ((dim ℋ₁)⁻¹ • 1) ⊗ TrLeft X`. It reduces, by linearity of the integral, to
`twirl_eq_smul_one` on the first factor. -/
theorem twirl_eq_partialTrace_smul_id (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ∫ u : unitary (L ℋ₁),
      TensorProduct.mapL ((u : L ℋ₁)) (1 : L ℋ₂) * X *
      TensorProduct.mapL (star (u : L ℋ₁)) (1 : L ℋ₂)
    ∂(haarUnitary ℋ₁) =
    TensorProduct.mapL ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : L ℋ₁)) (TrLeft X) := by
  suffices h : ∀ Y : L ℋ₁ ⊗[ℂ] L ℋ₂,
      ∫ u : unitary (L ℋ₁),
        TensorProduct.mapL ((u : L ℋ₁)) (1 : L ℋ₂) *
        opTensorEquiv.symm Y *
        TensorProduct.mapL (star (u : L ℋ₁)) (1 : L ℋ₂)
      ∂(haarUnitary ℋ₁) =
      TensorProduct.mapL ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : L ℋ₁))
        (TrLeft (opTensorEquiv.symm Y)) by
    have := h (opTensorEquiv X)
    simp only [LinearEquiv.symm_apply_apply] at this
    exact this
  intro Y
  induction Y using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, mul_zero, zero_mul, integral_zero, TensorProduct.mapL_zero_right]
  | tmul A B =>
    rw [TrLeft_opTensorEquiv_symm_tmul, opTensorEquiv_symm_tmul]
    have h_simp : ∀ u : unitary (L ℋ₁),
        TensorProduct.mapL ((u : L ℋ₁)) (1 : L ℋ₂) *
        TensorProduct.mapL A B *
        TensorProduct.mapL (star (u : L ℋ₁)) (1 : L ℋ₂) =
        TensorProduct.mapL ((u : L ℋ₁) * A * star (u : L ℋ₁)) B := fun u => by
      rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, one_mul, mul_one]
    simp_rw [h_simp]
    -- Goal: ∫ mapL (u*A*star u) B du = mapL (dim⁻¹ • 1) (Tr A • B)
    let mapB_lm : L ℋ₁ →ₗ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) :=
      { toFun := fun f => TensorProduct.mapL f B
        map_add' := fun f g => TensorProduct.mapL_add_left f g B
        map_smul' := fun c f => by
          simp only [RingHom.id_apply]
          exact TensorProduct.mapL_smul_left c f B }
    let mapB : L ℋ₁ →L[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) := ⟨mapB_lm, map_continuous mapB_lm⟩
    calc ∫ u : unitary (L ℋ₁),
            TensorProduct.mapL ((u : L ℋ₁) * A * star (u : L ℋ₁)) B
            ∂(haarUnitary ℋ₁)
        = mapB (∫ u : unitary (L ℋ₁),
            (u : L ℋ₁) * A * star (u : L ℋ₁) ∂(haarUnitary ℋ₁)) :=
          mapB.integral_comp_comm (integrable_unitaryConj A)
      _ = TensorProduct.mapL ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : L ℋ₁)) (Tr A • B) := by
          rw [twirl_eq_smul_one A]
          change TensorProduct.mapL
            (((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ * Tr A) • (1 : L ℋ₁)) B = _
          rw [TensorProduct.mapL_smul_left, TensorProduct.mapL_smul_left,
            TensorProduct.mapL_smul_right, smul_smul]
  | add Y₁ Y₂ hY₁ hY₂ =>
    rw [show (opTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm (Y₁ + Y₂) =
        opTensorEquiv.symm Y₁ + opTensorEquiv.symm Y₂ from map_add _ _ _]
    simp only [mul_add, add_mul]
    rw [integral_add
      (integrable_unitaryConj_tensor (opTensorEquiv.symm Y₁))
      (integrable_unitaryConj_tensor (opTensorEquiv.symm Y₂)),
      show TrLeft (opTensorEquiv.symm Y₁ + opTensorEquiv.symm Y₂) =
        TrLeft (opTensorEquiv.symm Y₁) + TrLeft (opTensorEquiv.symm Y₂) from map_add _ _ _,
      TensorProduct.mapL_add_right]
    exact congr_arg₂ (· + ·) hY₁ hY₂

/-! ### Right-factor twirl (mirror of `twirl_eq_partialTrace_smul_id`) -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Tensor-product conjugation on the right factor is continuous. -/
lemma continuous_unitaryConj_tensor_right (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Continuous (fun u : unitary (L ℋ₂) =>
      TensorProduct.mapL (1 : L ℋ₁) ((u : L ℋ₂)) * X *
      TensorProduct.mapL (1 : L ℋ₁) (star (u : L ℋ₂))) := by
  simp_rw [one_mapL_eq_lTensorStarAlgHom]
  exact (((continuous_lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).comp
    continuous_subtype_val).mul continuous_const).mul
    ((continuous_lTensorStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).comp
      (continuous_star.comp continuous_subtype_val))

omit [Nontrivial ℋ₁] in
/-- Tensor-product conjugation on the right factor is integrable. -/
lemma integrable_unitaryConj_tensor_right (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Integrable (fun u : unitary (L ℋ₂) =>
      TensorProduct.mapL (1 : L ℋ₁) ((u : L ℋ₂)) * X *
      TensorProduct.mapL (1 : L ℋ₁) (star (u : L ℋ₂)))
      (haarUnitary ℋ₂) :=
  (continuous_unitaryConj_tensor_right X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

omit [Nontrivial ℋ₁] in
/-- **Twirl over the second factor**, the mirror of `twirl_eq_partialTrace_smul_id`:
`∫ (1 ⊗ u) X (1 ⊗ u†) = TrRight X ⊗ ((dim ℋ₂)⁻¹ • 1)`, over the Haar measure on
`unitary (L ℋ₂)`. -/
theorem twirl_eq_partialTrace_right_smul_id (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ∫ u : unitary (L ℋ₂),
      TensorProduct.mapL (1 : L ℋ₁) ((u : L ℋ₂)) * X *
      TensorProduct.mapL (1 : L ℋ₁) (star (u : L ℋ₂))
    ∂(haarUnitary ℋ₂) =
    TensorProduct.mapL (TrRight X) ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : L ℋ₂)) := by
  suffices h : ∀ Y : L ℋ₁ ⊗[ℂ] L ℋ₂,
      ∫ u : unitary (L ℋ₂),
        TensorProduct.mapL (1 : L ℋ₁) ((u : L ℋ₂)) *
        opTensorEquiv.symm Y *
        TensorProduct.mapL (1 : L ℋ₁) (star (u : L ℋ₂))
      ∂(haarUnitary ℋ₂) =
      TensorProduct.mapL (TrRight (opTensorEquiv.symm Y))
        ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : L ℋ₂)) by
    have := h (opTensorEquiv X)
    simp only [LinearEquiv.symm_apply_apply] at this
    exact this
  intro Y
  induction Y using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, mul_zero, zero_mul, integral_zero, TensorProduct.mapL_zero_left]
  | tmul A B =>
    rw [TrRight_opTensorEquiv_symm_tmul, opTensorEquiv_symm_tmul]
    have h_simp : ∀ u : unitary (L ℋ₂),
        TensorProduct.mapL (1 : L ℋ₁) ((u : L ℋ₂)) *
        TensorProduct.mapL A B *
        TensorProduct.mapL (1 : L ℋ₁) (star (u : L ℋ₂)) =
        TensorProduct.mapL A ((u : L ℋ₂) * B * star (u : L ℋ₂)) := fun u => by
      rw [← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, one_mul, mul_one]
    simp_rw [h_simp]
    -- Goal: ∫ mapL A (u*B*star u) du = mapL (Tr B • A) (dim⁻¹ • 1)
    let mapA_lm : L ℋ₂ →ₗ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) :=
      { toFun := fun g => TensorProduct.mapL A g
        map_add' := fun g h => TensorProduct.mapL_add_right A g h
        map_smul' := fun c g => by
          simp only [RingHom.id_apply]
          exact TensorProduct.mapL_smul_right c A g }
    let mapA : L ℋ₂ →L[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) := ⟨mapA_lm, map_continuous mapA_lm⟩
    calc ∫ u : unitary (L ℋ₂),
            TensorProduct.mapL A ((u : L ℋ₂) * B * star (u : L ℋ₂))
            ∂(haarUnitary ℋ₂)
        = mapA (∫ u : unitary (L ℋ₂),
            (u : L ℋ₂) * B * star (u : L ℋ₂) ∂(haarUnitary ℋ₂)) :=
          mapA.integral_comp_comm (integrable_unitaryConj B)
      _ = TensorProduct.mapL (Tr B • A) ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : L ℋ₂)) := by
          rw [twirl_eq_smul_one B]
          change TensorProduct.mapL A
            (((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ * Tr B) • (1 : L ℋ₂)) = _
          rw [TensorProduct.mapL_smul_right, TensorProduct.mapL_smul_right,
            TensorProduct.mapL_smul_left, smul_smul]
  | add Y₁ Y₂ hY₁ hY₂ =>
    rw [show (opTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm (Y₁ + Y₂) =
        opTensorEquiv.symm Y₁ + opTensorEquiv.symm Y₂ from map_add _ _ _]
    simp only [mul_add, add_mul]
    rw [integral_add
      (integrable_unitaryConj_tensor_right (opTensorEquiv.symm Y₁))
      (integrable_unitaryConj_tensor_right (opTensorEquiv.symm Y₂)),
      show TrRight (opTensorEquiv.symm Y₁ + opTensorEquiv.symm Y₂) =
        TrRight (opTensorEquiv.symm Y₁) + TrRight (opTensorEquiv.symm Y₂) from map_add _ _ _,
      TensorProduct.mapL_add_left]
    exact congr_arg₂ (· + ·) hY₁ hY₂

end Twirl

/-! ## Section 4: Jensen inequality for jointly convex/concave operator functions -/

section Jensen

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

omit [Nontrivial ℋ] in
/-- **Jensen's inequality for jointly convex functions under probability measure**.
    If f : L ℋ → L ℋ → ℝ is jointly convex on S × T, continuous on S × T, and
    g₁(u) ∈ S, g₂(u) ∈ T for μ-a.e. u (where μ is a probability measure), then
    f(∫ g₁ dμ, ∫ g₂ dμ) ≤ ∫ f(g₁(u), g₂(u)) dμ. -/
theorem jointly_convex_integral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S T : Set (L ℋ)} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    {f : L ℋ → L ℋ → ℝ}
    (hf_conv : JointlyConvexOn S T f)
    (hf_cont : ContinuousOn (Function.uncurry f) (S ×ˢ T))
    {g₁ g₂ : α → L ℋ}
    (hg₁ : ∀ᵐ x ∂μ, g₁ x ∈ S)
    (hg₂ : ∀ᵐ x ∂μ, g₂ x ∈ T)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hfg_int : Integrable (fun x => f (g₁ x) (g₂ x)) μ)
    (_hmem₁ : ∫ x, g₁ x ∂μ ∈ S) (_hmem₂ : ∫ x, g₂ x ∂μ ∈ T) :
    f (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) ≤ ∫ x, f (g₁ x) (g₂ x) ∂μ := by
  have hF : ConvexOn ℝ (S ×ˢ T) (Function.uncurry f) := by
    constructor
    · exact hS.prod hT
    · rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ c d hc hd hcd
      change f (c • a₁ + d • a₂) (c • b₁ + d • b₂) ≤ c • f a₁ b₁ + d • f a₂ b₂
      have : c = 1 - d := by linarith
      rw [this]
      exact hf_conv ha₁ ha₂ hb₁ hb₂ hd (by linarith)
  have key := hF.map_integral_le hf_cont (hSc.prod hTc)
    (hg₁.mp (hg₂.mono fun x h₂ h₁ => ⟨h₁, h₂⟩))
    (hg₁_int.prodMk hg₂_int) hfg_int
  simp only [Function.uncurry_apply_pair, integral_pair hg₁_int hg₂_int] at key
  exact key

omit [Nontrivial ℋ] in
/-- **Jensen's inequality for jointly concave functions under probability measure**.
    If f : L ℋ → L ℋ → ℝ is jointly concave on S × T, then
    ∫ f(g₁(u), g₂(u)) dμ ≤ f(∫ g₁ dμ, ∫ g₂ dμ). -/
theorem jointly_concave_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S T : Set (L ℋ)} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    {f : L ℋ → L ℋ → ℝ}
    (hf_conc : JointlyConcaveOn S T f)
    (hf_cont : ContinuousOn (Function.uncurry f) (S ×ˢ T))
    {g₁ g₂ : α → L ℋ}
    (hg₁ : ∀ᵐ x ∂μ, g₁ x ∈ S)
    (hg₂ : ∀ᵐ x ∂μ, g₂ x ∈ T)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hfg_int : Integrable (fun x => f (g₁ x) (g₂ x)) μ)
    (_hmem₁ : ∫ x, g₁ x ∂μ ∈ S) (_hmem₂ : ∫ x, g₂ x ∂μ ∈ T) :
    (∫ x, f (g₁ x) (g₂ x) ∂μ) ≤ f (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) := by
  have hF : ConcaveOn ℝ (S ×ˢ T) (Function.uncurry f) := by
    constructor
    · exact hS.prod hT
    · rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ c d hc hd hcd
      change c • f a₁ b₁ + d • f a₂ b₂ ≤ f (c • a₁ + d • a₂) (c • b₁ + d • b₂)
      have : c = 1 - d := by linarith
      rw [this]
      exact hf_conc ha₁ ha₂ hb₁ hb₂ hd (by linarith)
  have key := hF.le_map_integral hf_cont (hSc.prod hTc)
    (hg₁.mp (hg₂.mono fun x h₂ h₁ => ⟨h₁, h₂⟩))
    (hg₁_int.prodMk hg₂_int) hfg_int
  simp only [Function.uncurry_apply_pair, integral_pair hg₁_int hg₂_int] at key
  exact key

end Jensen

/-! ## Section 5: Stinespring–Haar identity (Equation (1) of Frank–Lieb) -/

section StinespringHaar

variable {ℋ₁ : Type u} {ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁]

/-- **Stinespring–Haar identity**, equation (1) of arXiv:1306.5358. For a channel given by the
Stinespring dilation `E γ = TrLeft (U (τ ⊗ γ) U†)`, with `ℋ₁` the environment and `ℋ₂` the system,
`((dim ℋ₁)⁻¹ • 1) ⊗ E γ = ∫ (u ⊗ 1) U (τ ⊗ γ) U† (u† ⊗ 1)`, the integral being over the Haar
measure on the unitaries of the environment. -/
theorem stinespring_haar_eq
    (U : unitary (L (ℋ₁ ⊗[ℂ] ℋ₂))) (τ : L ℋ₁) (γ : L ℋ₂) :
    TensorProduct.mapL ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : L ℋ₁))
      (TrLeft
        ((U : L (ℋ₁ ⊗[ℂ] ℋ₂)) *
         TensorProduct.mapL τ γ *
         star (U : L (ℋ₁ ⊗[ℂ] ℋ₂)))) =
    ∫ u : unitary (L ℋ₁),
      TensorProduct.mapL ((u : L ℋ₁)) (1 : L ℋ₂) *
        ((U : L (ℋ₁ ⊗[ℂ] ℋ₂)) *
         TensorProduct.mapL τ γ *
         star (U : L (ℋ₁ ⊗[ℂ] ℋ₂))) *
      TensorProduct.mapL (star (u : L ℋ₁)) (1 : L ℋ₂)
    ∂(haarUnitary ℋ₁) :=
  (twirl_eq_partialTrace_smul_id
    ((U : L (ℋ₁ ⊗[ℂ] ℋ₂)) * TensorProduct.mapL τ γ *
     star (U : L (ℋ₁ ⊗[ℂ] ℋ₂)))).symm

end StinespringHaar

end HaarUnitary
