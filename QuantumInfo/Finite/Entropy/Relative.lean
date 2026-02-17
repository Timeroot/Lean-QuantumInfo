/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}

open scoped InnerProductSpace RealInnerProductSpace

/-!
To do relative entropies, we start with the _sandwiched Renyi Relative Entropy_ which is a nice general form.
Then instead of proving many theorems (like DPI, relabelling, additivity, etc.) several times, we just prove
it for this one quantity, then it follows for other quantities (like the relative entropy) as a special case.
-/

theorem inner_log_sub_log_nonneg (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  sorry

theorem sandwichedRelRentropy_nonneg_α_gt_1 {α : ℝ} (ρ σ : MState d)
  (h : σ.M.ker ≤ ρ.M.ker) (hα : α > 1) :
    0 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  sorry

theorem sandwichedRelRentropy_nonneg (α : ℝ) (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫
      else ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  split_ifs
  · exact inner_log_sub_log_nonneg ρ σ h
  by_cases hα : α > 1
  · exact sandwichedRelRentropy_nonneg_α_gt_1 ρ σ h hα
  · sorry

/-- The Sandwiched Renyi Relative Entropy, defined with ln (nits). Note that at `α = 1` this definition
  switch to the standard Relative Entropy, for continuity. -/
def SandwichedRelRentropy (α : ℝ) (ρ σ : MState d) : ENNReal :=
  open Classical in
  if h : σ.M.ker ≤ ρ.M.ker
  then (.ofNNReal ⟨if α = 1 then
      ⟪ρ.M, ρ.M.log - σ.M.log⟫
    else
      ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1),
    sandwichedRelRentropy_nonneg α ρ σ h⟩)
  else ⊤

notation "D̃_" α "(" ρ "‖" σ ")" => SandwichedRelRentropy α ρ σ

/-- The Sandwiched Renyi Relative entropy is additive when the inputs are product states -/
@[simp]
theorem sandwichedRelRentropy_additive (α) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  dsimp [SandwichedRelRentropy]
  sorry
  -- split_ifs
  -- · sorry
  -- · sorry
  -- · sorry
  /-
  handle the kernels of tensor products
  log of ⊗ is (log A ⊗ I) + (I ⊗ log B)
  rinner distributes over sub and add
  rinner of ⊗ is mul of rinner
  -/

@[simp]
theorem sandwichedRelRentropy_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    D̃_ α(ρ.relabel e‖σ.relabel e) = D̃_ α(ρ‖σ) := by
  simp only [SandwichedRelRentropy, MState.relabel_M]
  rw! [HermitianMat.ker_reindex_le_iff] --Why doesn't this `simp`? Because it's an if condition, I'm guessing
  simp [HermitianMat.conj_submatrix]

@[simp]
theorem sandwichedRelRentropy_self (hα : 0 < α) (ρ : MState d) :
  --Technically this holds for all α except for `-1` and `0`. But those are stupid.
  --TODO: Maybe SandwichedRelRentropy should actually be defined differently for α = 0?
    D̃_ α(ρ‖ρ) = 0 := by
  simp? [SandwichedRelRentropy, NNReal.eq_iff] says
    simp only [SandwichedRelRentropy, le_refl, ↓reduceDIte, sub_self, HermitianMat.inner_zero_right,
    ENNReal.coe_eq_zero, NNReal.eq_iff, NNReal.coe_mk, NNReal.coe_zero, ite_eq_left_iff,
    div_eq_zero_iff, Real.log_eq_zero]
  intro hα
  left; right; left
  rw [HermitianMat.pow_eq_cfc, HermitianMat.pow_eq_cfc]
  nth_rw 2 [← HermitianMat.cfc_id ρ.M]
  rw [HermitianMat.cfc_conj, ← HermitianMat.cfc_comp]
  conv =>
    enter [1, 1]
    equals ρ.M.cfc id =>
      apply HermitianMat.cfc_congr_of_zero_le ρ.zero_le
      intro i (hi : 0 ≤ i)
      simp
      rw [← Real.rpow_mul_natCast hi, ← Real.rpow_one_add' hi]
      · rw [← Real.rpow_mul hi]
        field_simp
        ring_nf
        exact Real.rpow_one i
      · field_simp; ring_nf; positivity
  simp

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem sandwichedRelEntropy_ne_top {ρ σ : MState d} [σ.M.NonSingular] : D̃_ α(ρ‖σ) ≠ ⊤ := by
  simp [SandwichedRelRentropy, HermitianMat.nonSingular_ker_bot]

@[fun_prop]
lemma continuousOn_exponent : ContinuousOn (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 1) := by
  fun_prop (disch := intros; linarith [Set.mem_Ioi.mp ‹_›])

omit [Fintype d₂] [DecidableEq d] [DecidableEq d₂] in
@[fun_prop]
lemma continuous_conj (ρ : HermitianMat d 𝕜) : Continuous (ρ.conj (m := d₂) ·) := by
  simp only [HermitianMat.conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  fun_prop

@[fun_prop]
lemma Complex.continuousOn_cpow_const_Ioi (z : ℂ) :
    ContinuousOn (fun r : ℝ => z ^ (r : ℂ)) (Set.Ioi 0) := by
  apply ContinuousOn.const_cpow (f := Complex.ofReal)
  · fun_prop
  · grind [ofReal_ne_zero]

omit [Fintype d] [DecidableEq d] in
lemma HermitianMat.continuousOn_iff_coe {X : Type*} [TopologicalSpace X] {s : Set X}
    (f : X → HermitianMat d 𝕜) :
    ContinuousOn f s ↔ ContinuousOn (fun x => (f x).mat) s := by
  apply Iff.intro;
  · intro hf
    apply ContinuousOn.comp continuous_subtype_val.continuousOn hf
    exact Set.mapsTo_iff_image_subset.mpr fun _ a => a
  · intro h;
    rw [continuousOn_iff_continuous_restrict] at *
    apply Continuous.subtype_mk h

/--
If a parameter-dependent function `f x` is continuous in `x` when evaluated at
the eigenvalues of `A`, then `A.cfc (f x)` is continuous in `x`.
-/
lemma HermitianMat.continuousOn_cfc_param {X : Type*} [TopologicalSpace X] {S : Set X}
    (A : HermitianMat d 𝕜) {f : X → ℝ → ℝ}
    (hf : ∀ i, ContinuousOn (fun x => f x (A.H.eigenvalues i)) S) :
    ContinuousOn (fun x => A.cfc (f x)) S := by
  simp_rw [continuousOn_iff_coe, cfc_toMat_eq_sum_smul_proj A]
  fun_prop

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x < 0.
-/
lemma HermitianMat.continuousOn_rpow_neg (A : HermitianMat d ℂ) :
    ContinuousOn (fun x : ℝ => A ^ x) (Set.Iio 0) := by
  apply A.continuousOn_cfc_param
  intro i x hx
  exact (Real.continuousAt_const_rpow' hx.ne).continuousWithinAt

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x < 0.
-/
lemma HermitianMat.continuousOn_rpow_pos (A : HermitianMat d 𝕜) :
    ContinuousOn (fun x : ℝ => A ^ x) (Set.Ioi 0) := by
  apply A.continuousOn_cfc_param
  intro i x hx
  exact (Real.continuousAt_const_rpow' hx.ne').continuousWithinAt

/--
The function α ↦ (1 - α) / (2 * α) maps the interval (1, ∞) to (-∞, 0).
-/
lemma maps_to_Iio_of_Ioi_1 : Set.MapsTo (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 1) (Set.Iio 0) := by
  intro x hx
  rw [Set.mem_Ioi] at hx
  rw [Set.mem_Iio]
  have h1 : 1 - x < 0 := by linarith
  have h2 : 0 < 2 * x := by linarith
  exact div_neg_of_neg_of_pos h1 h2

@[fun_prop]
theorem sandwichedRelRentropy.continuousOn (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 0) := by
  --If this turns out too hard, we just need `ContinousAt f 1`.
  --If that's still too hard, we really _just_ need that `(𝓝[≠] 1).tendsto (f 1)`.
  sorry

/-- The Data Processing Inequality for the Sandwiched Renyi relative entropy.
Proved in `https://arxiv.org/pdf/1306.5920`. Seems kind of involved. -/
theorem sandwichedRenyiEntropy_DPI (hα : 1 ≤ α) (ρ σ : MState d) (Φ : CPTPMap d d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  --If we want, we can prove this just for 1 < α, and then use continuity (above) to take the limit as
  -- α → 1.
  sorry

/-- The quantum relative entropy `𝐃(ρ‖σ) := Tr[ρ (log ρ - log σ)]`. -/
def qRelativeEnt (ρ σ : MState d) : ENNReal :=
  D̃_1(ρ‖σ)

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simp [qRelativeEnt, SandwichedRelRentropy, h, EReal.coe_nnreal_eq_coe_real]

open Classical in
theorem qRelativeEnt_eq_neg_Sᵥₙ_add (ρ σ : MState d) :
    (qRelativeEnt ρ σ).toEReal = -(Sᵥₙ ρ : EReal) +
      if σ.M.ker ≤ ρ.M.ker then (-⟪ρ.M, σ.M.log⟫ : EReal) else (⊤ : EReal) := by
  by_cases h : σ.M.ker ≤ ρ.M.ker
  · simp [h, Sᵥₙ_eq_neg_trace_log, qRelativeEnt_ker, inner_sub_right]
    rw [real_inner_comm, sub_eq_add_neg]
  · simp [h]
    exact dif_neg h

/-- The quantum relative entropy is unchanged by `MState.relabel` -/
@[simp]
theorem qRelativeEnt_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    𝐃(ρ.relabel e‖σ.relabel e) = 𝐃(ρ‖σ) := by
  simp [qRelativeEnt]

/-- "Formula for conversion from operator inequality to quantum relative entropy",
-- Proposition S17 of https://arxiv.org/pdf/2401.01926v2 -/
theorem qRelativeEnt_op_le {ρ σ : MState d} (hpos : 0 < α) (h : ρ.M ≤ α • σ.M) :
    𝐃(ρ‖σ) ≤ ENNReal.ofReal (Real.log α) := by
  sorry

@[simp]
theorem sandwichedRelRentropy_of_unique [Unique d] (ρ σ : MState d) :
    D̃_α(ρ‖σ) = 0 := by
  rcases Subsingleton.allEq ρ default
  rcases Subsingleton.allEq σ default
  simp [SandwichedRelRentropy]

@[simp]
theorem qRelEntropy_of_unique [Unique d] (ρ σ : MState d) :
    𝐃(ρ‖σ) = 0 := by
  exact sandwichedRelRentropy_of_unique ρ σ

theorem sandwichedRelRentropy_heq_congr
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  --Why does this thm need to exist? Why not just `subst d₁` and `simp [heq_eq_eq]`? Well, even though d₁
  --and d₂ are equal, we then end up with two distinct instances of `Fintype d₁` and `DecidableEq d₁`,
  --and ρ₁ and ρ₂ refer to them each and so have different types. And then we'd need to `subst` those away
  --too. This is kind of tedious, so it's better to just have this theorem around.
  rw [heq_iff_exists_eq_cast] at hρ hσ
  obtain ⟨_, rfl⟩ := hρ
  obtain ⟨_, rfl⟩ := hσ
  simp [← MState.relabel_cast _ hd]

@[gcongr]
theorem sandwichedRelRentropy_congr {α : ℝ}
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂)
        (hρ : ρ₁ = ρ₂.relabel (Equiv.cast hd)) (hσ : σ₁ = σ₂.relabel (Equiv.cast hd)) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  subst ρ₁ σ₁
  simp

@[gcongr]
theorem qRelEntropy_heq_congr {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    𝐃(ρ₁‖σ₁) = 𝐃(ρ₂‖σ₂) := by
  exact sandwichedRelRentropy_heq_congr hd hρ hσ

/-- Quantum relative entropy when σ has full rank -/
theorem qRelativeEnt_rank {ρ σ : MState d} [σ.M.NonSingular] :
    (𝐃(ρ‖σ) : EReal) = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  apply qRelativeEnt_ker
  simp [HermitianMat.nonSingular_ker_bot]

/-- The quantum relative entropy is additive when the inputs are product states -/
@[simp]
theorem qRelativeEnt_additive (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    𝐃(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂) := by
  simp [qRelativeEnt]

--BACKPORT
private theorem lowerSemicontinuous_iff {α : Type u_1} {β : Type u_2} [TopologicalSpace α] [Preorder β] {f : α → β} :
    LowerSemicontinuous f ↔ ∀ (x : α), LowerSemicontinuousAt f x := by
  rfl

lemma lowerSemicontinuous_inner (ρ x : MState d) (hx : x.M.ker ≤ ρ.M.ker):
    LowerSemicontinuousAt (fun x ↦ ⟪ρ.M, x.M.log⟫) x := by
  sorry

open Classical in
theorem qRelativeEnt_lowerSemicontinuous_2 (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) (y : ENNReal) (hy : y < ⊤) :
    ∀ᶠ (x' : MState d) in nhds x,
      y < (if x'.M.ker ≤ ρ.M.ker then ⟪ρ.M, ρ.M.log - x'.M.log⟫ else ⊤ : EReal) := by
  sorry

/-- Relative entropy is lower semicontinuous (in each argument, actually, but we only need in the
latter here). Will need the fact that all the cfc / eigenvalue stuff is continuous, plus
carefully handling what happens with the kernel subspace, which will make this a pain. -/
@[fun_prop]
theorem qRelativeEnt.lowerSemicontinuous (ρ : MState d) : LowerSemicontinuous fun σ => 𝐃(ρ‖σ) := by
  simp_rw [qRelativeEnt, SandwichedRelRentropy, if_true, lowerSemicontinuous_iff]
  intro x
  by_cases hx : x.M.ker ≤ ρ.M.ker
  · have h₂ := lowerSemicontinuous_inner ρ x hx
    sorry
  · intro y hy
    simp only [hx, ↓reduceDIte] at hy ⊢
    have h₂ := qRelativeEnt_lowerSemicontinuous_2 ρ x hx y hy
    sorry

/-- Joint convexity of Quantum relative entropy. We can't state this with `ConvexOn` because that requires
an `AddCommMonoid`, which `MState`s are not. Instead we state it with `Mixable`.

TODO:
 * Add the `Mixable` instance that infers from the `Coe` so that the right hand side can be written as
`p [𝐃(ρ₁‖σ₁) ↔ 𝐃(ρ₂‖σ₂)]`
 * Define (joint) convexity as its own thing - a `ConvexOn` for `Mixable` types.
 * Maybe, more broadly, find a way to make `ConvexOn` work with the subset of `Matrix` that corresponds to `MState`.
-/
theorem qRelativeEnt_joint_convexity :
  ∀ (ρ₁ ρ₂ σ₁ σ₂ : MState d), ∀ (p : Prob),
    𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
  sorry

@[simp]
theorem qRelEntropy_self (ρ : MState d) : 𝐃(ρ‖ρ) = 0 := by
  simp [qRelativeEnt]

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem qRelativeEnt_ne_top {ρ σ : MState d} [σ.M.NonSingular] : 𝐃(ρ‖σ) ≠ ⊤ := by
  rw [qRelativeEnt]
  finiteness

/-- `I(A:B) = 𝐃(ρᴬᴮ‖ρᴬ ⊗ ρᴮ)` -/
theorem qMutualInfo_as_qRelativeEnt (ρ : MState (dA × dB)) :
    qMutualInfo ρ = (𝐃(ρ‖ρ.traceRight ⊗ᴹ ρ.traceLeft) : EReal) := by
  sorry

theorem qRelEntropy_le_add_of_le_smul (ρ : MState d) {σ₁ σ₂ : MState d} (hσ : σ₁.M ≤ α • σ₂.M) :
    𝐃(ρ‖σ₁) ≤ 𝐃(ρ‖σ₂) + ENNReal.ofReal (Real.log α)
    := by
  sorry
