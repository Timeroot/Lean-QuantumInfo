/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.ForMathlib.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Sequences

/-!
# Cartan's closed subgroup theorem

A subgroup `H` of the multiplicative group of a finite-dimensional real normed algebra `𝔸` that is
closed as a subset of `𝔸` is a Lie subgroup: its **Lie algebra**

`expTangent H = {A | ∀ t : ℝ, exp (t • A) ∈ H}`

is an `ℝ`-submodule of `𝔸` (`IsMulSubgroup.lieAlgebra`), and near `1` the group is exactly the
exponential image of that submodule (`IsMulSubgroup.exists_exp_eq_of_mem_ball`).

`expTangent H` is closed under scalar multiples by definition; it is closed under addition by the
Lie product formula, `exp (A + B) = lim (exp (A/n) · exp (B/n))ⁿ`, together with closedness of `H`.
That it exhausts a neighbourhood of `1` is the substance of the theorem: writing
`𝔸 = 𝔥 ⊕ 𝔪` with `𝔥 = expTangent H`, the map `(X, Y) ↦ exp X · exp Y` is a local diffeomorphism at
`0`, so a sequence in `H` approaching `1` with nonzero `𝔪`-component would produce a nonzero
`Z ∈ 𝔪` with `exp (t • Z) ∈ H` for all `t`, i.e. `Z ∈ 𝔥 ⊓ 𝔪 = ⊥`. The elements `exp (t • Z)` are
obtained as limits of powers `exp (Yⱼ) ^ ⌊t / ‖Yⱼ‖⌋`, and `Z` as a limit of `Yⱼ / ‖Yⱼ‖` on the unit
sphere of `𝔪`, which is compact.

For a compact group this globalises: `IsMulSubgroup.exists_finset_mul_exp` covers `H` by finitely
many left translates `f · exp (expTangent H)`, one for each connected component.

## Main results

* `IsMulSubgroup.lieAlgebra` — the Lie algebra of a closed subgroup;
* `IsMulSubgroup.exists_exp_eq_of_mem_ball` — Cartan's theorem, local form;
* `IsMulSubgroup.exists_finset_mul_exp` — Cartan's theorem for a compact group, global form.
-/

open Filter Metric NormedSpace Set
open scoped Topology

section Subgroup

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- A subset of a monoid that contains `1`, is closed under multiplication, and in which every
element has a two-sided inverse. For a normed algebra this is the right notion for Cartan's
theorem: the closedness hypothesis is closedness in the algebra, not in its group of units. -/
structure IsMulSubgroup (H : Set 𝔸) : Prop where
  /-- The identity belongs to `H`. -/
  one_mem : (1 : 𝔸) ∈ H
  /-- `H` is closed under multiplication. -/
  mul_mem : ∀ ⦃a b : 𝔸⦄, a ∈ H → b ∈ H → a * b ∈ H
  /-- Every element of `H` has a two-sided inverse in `H`. -/
  exists_inv : ∀ a ∈ H, ∃ b ∈ H, b * a = 1 ∧ a * b = 1

namespace IsMulSubgroup

variable {H : Set 𝔸}

theorem pow_mem (hH : IsMulSubgroup H) {a : 𝔸} (ha : a ∈ H) : ∀ n : ℕ, a ^ n ∈ H
  | 0 => by simpa using hH.one_mem
  | (n + 1) => by
      rw [pow_succ]
      exact hH.mul_mem (hH.pow_mem ha n) ha

/-- A right inverse of an element of `H` again lies in `H`, being its inverse in `H`. -/
theorem mem_of_mul_eq_one (hH : IsMulSubgroup H) {a b : 𝔸} (ha : a ∈ H) (h1 : a * b = 1) :
    b ∈ H := by
  obtain ⟨c, hc, hca, -⟩ := hH.exists_inv a ha
  have hbc : b = c := by
    calc b = 1 * b := (one_mul b).symm
      _ = c * a * b := by rw [hca]
      _ = c * (a * b) := mul_assoc _ _ _
      _ = c := by rw [h1, mul_one]
  rwa [hbc]

end IsMulSubgroup

end Subgroup

section Tangent

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The **Lie algebra** of a subset `H` of a normed algebra: those `A` all of whose one-parameter
exponentials `exp (t • A)` lie in `H`. -/
def expTangent (H : Set 𝔸) : Set 𝔸 := {A | ∀ t : ℝ, exp (t • A) ∈ H}

theorem mem_expTangent_iff {H : Set 𝔸} {A : 𝔸} :
    A ∈ expTangent H ↔ ∀ t : ℝ, exp (t • A) ∈ H := Iff.rfl

theorem exp_mem_of_mem_expTangent {H : Set 𝔸} {A : 𝔸} (hA : A ∈ expTangent H) : exp A ∈ H := by
  simpa using hA 1

namespace IsMulSubgroup

variable {H : Set 𝔸}

theorem zero_mem_expTangent (hH : IsMulSubgroup H) : (0 : 𝔸) ∈ expTangent H := by
  intro t
  simpa using hH.one_mem

theorem smul_mem_expTangent {A : 𝔸} (hA : A ∈ expTangent H) (r : ℝ) : r • A ∈ expTangent H := by
  intro t
  rw [smul_smul]
  exact hA _

end IsMulSubgroup

end Tangent

section Cartan

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸]
  [FiniteDimensional ℝ 𝔸]

namespace IsMulSubgroup

variable {H : Set 𝔸}

/-- The Lie algebra of a closed subgroup is closed under addition: `exp (A + B)` is the limit of
the products `(exp (A/n) · exp (B/n))ⁿ`, all of which lie in `H`. -/
theorem add_mem_expTangent (hH : IsMulSubgroup H) (hcl : IsClosed H) {A B : 𝔸}
    (hA : A ∈ expTangent H) (hB : B ∈ expTangent H) : A + B ∈ expTangent H := by
  intro t
  have hlim := tendsto_exp_smul_mul_exp_smul_pow (t • A) (t • B)
  have hmem : ∀ n : ℕ, (exp ((n : ℝ)⁻¹ • (t • A)) * exp ((n : ℝ)⁻¹ • (t • B))) ^ n ∈ H := by
    intro n
    refine hH.pow_mem (hH.mul_mem ?_ ?_) n
    · rw [smul_smul]
      exact hA _
    · rw [smul_smul]
      exact hB _
  have : exp (t • A + t • B) ∈ H :=
    hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  rwa [← smul_add] at this

/-- The Lie algebra of a closed subgroup of the multiplicative group of a
finite-dimensional normed algebra. -/
def lieAlgebra (hH : IsMulSubgroup H) (hcl : IsClosed H) : Submodule ℝ 𝔸 where
  carrier := expTangent H
  add_mem' := hH.add_mem_expTangent hcl
  zero_mem' := hH.zero_mem_expTangent
  smul_mem' r _ hA := smul_mem_expTangent hA r

@[simp]
theorem mem_lieAlgebra (hH : IsMulSubgroup H) (hcl : IsClosed H) {A : 𝔸} :
    A ∈ hH.lieAlgebra hcl ↔ A ∈ expTangent H := Iff.rfl


/-- **Cartan's closed subgroup theorem**, local form: near `1`, a closed subgroup of the
multiplicative group of a finite-dimensional normed algebra consists exactly of the
exponentials of elements of its Lie algebra. -/
theorem exists_exp_eq_of_mem_ball (hH : IsMulSubgroup H) (hcl : IsClosed H) :
    ∃ ε > 0, ∀ h ∈ H, ‖h - 1‖ < ε → ∃ A ∈ expTangent H, exp A = h := by
  classical
  set 𝔥 : Submodule ℝ 𝔸 := hH.lieAlgebra hcl with h𝔥def
  obtain ⟨𝔪, hcompl⟩ := 𝔥.exists_isCompl
  set L : (↥𝔥 × ↥𝔪) ≃L[ℝ] 𝔸 :=
    (Submodule.prodEquivOfIsCompl 𝔥 𝔪 hcompl).toContinuousLinearEquiv with hLdef
  have hLapply : ∀ p : ↥𝔥 × ↥𝔪, L p = (p.1 : 𝔸) + (p.2 : 𝔸) := fun _ => rfl
  set φ : ↥𝔥 × ↥𝔪 → 𝔸 := fun p => exp ((p.1 : 𝔸)) * exp ((p.2 : 𝔸)) with hφdef
  have hφ0 : φ 0 = 1 := by simp [hφdef]
  have hφ : HasStrictFDerivAt φ (L : (↥𝔥 × ↥𝔪) →L[ℝ] 𝔸) 0 := by
    have hc1 : HasStrictFDerivAt (fun p : ↥𝔥 × ↥𝔪 => ((p.1 : 𝔸)))
        (𝔥.subtypeL.comp (ContinuousLinearMap.fst ℝ ↥𝔥 ↥𝔪)) 0 :=
      (𝔥.subtypeL.comp (ContinuousLinearMap.fst ℝ ↥𝔥 ↥𝔪)).hasStrictFDerivAt
    have hc2 : HasStrictFDerivAt (fun p : ↥𝔥 × ↥𝔪 => ((p.2 : 𝔸)))
        (𝔪.subtypeL.comp (ContinuousLinearMap.snd ℝ ↥𝔥 ↥𝔪)) 0 :=
      (𝔪.subtypeL.comp (ContinuousLinearMap.snd ℝ ↥𝔥 ↥𝔪)).hasStrictFDerivAt
    have he1 : HasStrictFDerivAt (fun p : ↥𝔥 × ↥𝔪 => exp ((p.1 : 𝔸)))
        ((1 : 𝔸 →L[ℝ] 𝔸).comp (𝔥.subtypeL.comp (ContinuousLinearMap.fst ℝ ↥𝔥 ↥𝔪))) 0 := by
      refine HasStrictFDerivAt.comp (0 : ↥𝔥 × ↥𝔪) ?_ hc1
      simpa using hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)
    have he2 : HasStrictFDerivAt (fun p : ↥𝔥 × ↥𝔪 => exp ((p.2 : 𝔸)))
        ((1 : 𝔸 →L[ℝ] 𝔸).comp (𝔪.subtypeL.comp (ContinuousLinearMap.snd ℝ ↥𝔥 ↥𝔪))) 0 := by
      refine HasStrictFDerivAt.comp (0 : ↥𝔥 × ↥𝔪) ?_ hc2
      simpa using hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)
    refine (he1.fun_mul' he2).congr_fderiv ?_
    ext p
    · simp [hLapply]
    · simp [hLapply]
  obtain ⟨ψ, hψ1, hψtend, hright⟩ : ∃ ψ : 𝔸 → ↥𝔥 × ↥𝔪, ψ 1 = 0 ∧
      Tendsto ψ (𝓝 (1 : 𝔸)) (𝓝 0) ∧ ∀ᶠ y in 𝓝 (1 : 𝔸), φ (ψ y) = y := by
    refine ⟨hφ.localInverse φ L 0, ?_, ?_, ?_⟩
    · have h := hφ.localInverse_apply_image
      rwa [hφ0] at h
    · have h := hφ.localInverse_tendsto
      rwa [hφ0] at h
    · have h := hφ.eventually_right_inverse
      rwa [hφ0] at h
  have key : ∀ᶠ y in 𝓝 (1 : 𝔸), y ∈ H → ((ψ y).2 : 𝔸) = 0 := by
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    obtain ⟨u, hu, hu'⟩ := exists_seq_forall_of_frequently (hcon.and_eventually hright)
    have huH : ∀ n, u n ∈ H := fun n => ((Classical.not_imp.mp (hu' n).1)).1
    have huY : ∀ n, ((ψ (u n)).2 : 𝔸) ≠ 0 := fun n => ((Classical.not_imp.mp (hu' n).1)).2
    have huφ : ∀ n, φ (ψ (u n)) = u n := fun n => (hu' n).2
    have hexpY : ∀ n, exp ((ψ (u n)).2 : 𝔸) ∈ H := by
      intro n
      have hX : exp ((ψ (u n)).1 : 𝔸) ∈ H := exp_mem_of_mem_expTangent (ψ (u n)).1.2
      obtain ⟨b, hbH, hb1, hb2⟩ := hH.exists_inv _ hX
      have hb : b * φ (ψ (u n)) = exp ((ψ (u n)).2 : 𝔸) := by
        simp only [hφdef, ← mul_assoc, hb1, one_mul]
      rw [huφ n] at hb
      rw [← hb]
      exact hH.mul_mem hbH (huH n)
    set Y : ℕ → ↥𝔪 := fun n => (ψ (u n)).2 with hYdef
    have hY0 : ∀ n, Y n ≠ 0 := by
      intro n hn
      exact huY n (by simpa using congrArg (fun x : ↥𝔪 => (x : 𝔸)) hn)
    have hYtend : Tendsto Y atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ψ (u n)) atTop (𝓝 0) := hψtend.comp hu
      exact ((continuous_snd.tendsto (0 : ↥𝔥 × ↥𝔪)).comp h1 :
        Tendsto (fun n => (ψ (u n)).2) atTop (𝓝 (0 : ↥𝔪)))
    set c : ℕ → ℝ := fun n => ‖Y n‖ with hcdef
    have hcpos : ∀ n, 0 < c n := fun n => norm_pos_iff.mpr (hY0 n)
    have hctend : Tendsto c atTop (𝓝 0) := by
      simpa [hcdef] using hYtend.norm
    set Z : ℕ → ↥𝔪 := fun n => (c n)⁻¹ • Y n with hZdef
    have hZnorm : ∀ n, ‖Z n‖ = 1 := by
      intro n
      rw [hZdef]
      simp only [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hcpos n)]
      exact inv_mul_cancel₀ (hcpos n).ne'
    obtain ⟨Z₀, hZ₀mem, σ, hσ, hZσ⟩ :=
      (isCompact_sphere (0 : ↥𝔪) 1).tendsto_subseq (x := Z) (fun n => by
        simpa [Metric.mem_sphere, dist_zero_right] using hZnorm n)
    have hZ₀norm : ‖Z₀‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using hZ₀mem
    have hvec : Tendsto (fun j => ((Z (σ j) : 𝔸))) atTop (𝓝 (Z₀ : 𝔸)) :=
      (continuous_subtype_val.tendsto _).comp hZσ
    have hcσ : Tendsto (fun j => c (σ j)) atTop (𝓝 0) := hctend.comp hσ.tendsto_atTop
    have hnonneg : ∀ t : ℝ, 0 ≤ t → exp (t • (Z₀ : 𝔸)) ∈ H := by
      intro t ht
      set m : ℕ → ℕ := fun j => ⌊t / c (σ j)⌋₊ with hmdef
      have hterm : ∀ j, exp (((m j : ℝ) * c (σ j)) • (Z (σ j) : 𝔸)) ∈ H := by
        intro j
        have h1 : ((m j : ℝ) * c (σ j)) • (Z (σ j) : 𝔸) = (m j) • ((Y (σ j) : 𝔸)) := by
          rw [hZdef]
          push_cast
          rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hcpos (σ j)).ne', mul_one,
            Nat.cast_smul_eq_nsmul]
        rw [h1, exp_nsmul']
        exact hH.pow_mem (hexpY (σ j)) _
      have hscal : Tendsto (fun j => (m j : ℝ) * c (σ j)) atTop (𝓝 t) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le
          (g := fun j => t - c (σ j)) (h := fun _ : ℕ => t) ?_ tendsto_const_nhds ?_ ?_
        · simpa using tendsto_const_nhds.sub hcσ
        · intro j
          have hc0 := hcpos (σ j)
          have := Nat.lt_floor_add_one (t / c (σ j))
          rw [hmdef]
          nlinarith [(div_lt_iff₀ hc0).mp (by linarith [this] : t / c (σ j) < (m j : ℝ) + 1)]
        · intro j
          have hc0 := hcpos (σ j)
          have hfl : ((m j : ℝ)) ≤ t / c (σ j) :=
            Nat.floor_le (by positivity)
          calc (m j : ℝ) * c (σ j) ≤ (t / c (σ j)) * c (σ j) := by gcongr
            _ = t := div_mul_cancel₀ t hc0.ne'
      have hlim := (exp_continuous'.tendsto ((t : ℝ) • (Z₀ : 𝔸))).comp (hscal.smul hvec)
      exact hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall hterm)
    have hZ₀tangent : (Z₀ : 𝔸) ∈ expTangent H := by
      intro t
      rcases le_or_gt 0 t with h | h
      · exact hnonneg t h
      · have hcomm : Commute ((-t) • (Z₀ : 𝔸)) (t • (Z₀ : 𝔸)) :=
          ((Commute.refl (Z₀ : 𝔸)).smul_left _).smul_right _
        have h1 : exp ((-t) • (Z₀ : 𝔸)) * exp (t • (Z₀ : 𝔸)) = 1 := by
          rw [← exp_add_of_commute' hcomm, ← add_smul]
          simp
        exact hH.mem_of_mul_eq_one (hnonneg (-t) (by linarith)) h1
    have hzero : (Z₀ : 𝔸) = 0 := by
      have hmem : (Z₀ : 𝔸) ∈ 𝔥 ⊓ 𝔪 := ⟨hZ₀tangent, Z₀.2⟩
      rw [hcompl.inf_eq_bot] at hmem
      simpa using hmem
    rw [show ‖Z₀‖ = ‖(Z₀ : 𝔸)‖ from rfl, hzero, norm_zero] at hZ₀norm
    exact zero_ne_one hZ₀norm
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (key.and hright)
  refine ⟨ε, hε, fun h hhH hnorm => ?_⟩
  obtain ⟨hz, hinv⟩ := hball (by rwa [dist_eq_norm] : dist h 1 < ε)
  refine ⟨((ψ h).1 : 𝔸), (ψ h).1.2, ?_⟩
  have hsplit : φ (ψ h) = exp ((ψ h).1 : 𝔸) := by simp [hφdef, hz hhH]
  rw [← hsplit]
  exact hinv


/-- **Cartan's closed subgroup theorem**, global form for a compact group: a compact subgroup of
the multiplicative group of a finite-dimensional normed algebra is covered by finitely many left
translates of the exponential image of its Lie algebra. -/
theorem exists_finset_mul_exp (hH : IsMulSubgroup H) (hcpt : IsCompact H) :
    ∃ F : Finset 𝔸, ↑F ⊆ H ∧ ∀ h ∈ H, ∃ f ∈ F, ∃ A ∈ expTangent H, h = f * exp A := by
  classical
  obtain ⟨ε, hε, hloc⟩ := hH.exists_exp_eq_of_mem_ball hcpt.isClosed
  choose! g hgH hgl hgr using hH.exists_inv
  set δ : 𝔸 → ℝ := fun f => ε / (1 + ‖g f‖) with hδ
  have hδpos : ∀ f, 0 < δ f := fun f => div_pos hε (by positivity)
  obtain ⟨F₀, hF₀H, hF₀fin, hcover⟩ :=
    hcpt.elim_finite_subcover_image (b := H) (c := fun f => Metric.ball f (δ f))
      (fun f _ => Metric.isOpen_ball)
      (fun x hx => Set.mem_biUnion hx (Metric.mem_ball_self (hδpos x)))
  refine ⟨hF₀fin.toFinset, by simpa using hF₀H, fun h hh => ?_⟩
  obtain ⟨f, hf, hball⟩ := Set.mem_iUnion₂.mp (hcover hh)
  have hfH : f ∈ H := hF₀H hf
  have hnorm : ‖h - f‖ < δ f := by rwa [Metric.mem_ball, dist_eq_norm] at hball
  have hkey : ‖g f * h - 1‖ < ε := by
    have h1 : g f * h - 1 = g f * (h - f) := by rw [mul_sub, hgl f hfH]
    have h2 : ‖g f‖ * ‖h - f‖ ≤ (1 + ‖g f‖) * ‖h - f‖ := by
      nlinarith [norm_nonneg (h - f), norm_nonneg (g f)]
    have h3 : (1 + ‖g f‖) * ‖h - f‖ < (1 + ‖g f‖) * δ f :=
      mul_lt_mul_of_pos_left hnorm (by positivity)
    have h4 : (1 + ‖g f‖) * δ f = ε := by
      rw [hδ]
      field_simp
    calc ‖g f * h - 1‖ = ‖g f * (h - f)‖ := by rw [h1]
      _ ≤ ‖g f‖ * ‖h - f‖ := norm_mul_le _ _
      _ ≤ (1 + ‖g f‖) * ‖h - f‖ := h2
      _ < (1 + ‖g f‖) * δ f := h3
      _ = ε := h4
  obtain ⟨A, hA, hexp⟩ := hloc (g f * h) (hH.mul_mem (hgH f hfH) hh) hkey
  refine ⟨f, by simpa using hf, A, hA, ?_⟩
  rw [hexp, ← mul_assoc, hgr f hfH, one_mul]

end IsMulSubgroup

end Cartan
