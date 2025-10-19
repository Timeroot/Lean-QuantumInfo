/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.SionMinimax

--minimize these imports?
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.StrongTopology
import Mathlib.Topology.Algebra.Module.FiniteDimension

--TODO go elsewhere
attribute [fun_prop] LowerSemicontinuous UpperSemicontinuous
attribute [fun_prop] LowerSemicontinuousOn UpperSemicontinuousOn
attribute [fun_prop] LowerSemicontinuous.lowerSemicontinuousOn
attribute [fun_prop] UpperSemicontinuous.upperSemicontinuousOn
attribute [fun_prop] Continuous.lowerSemicontinuous Continuous.upperSemicontinuous

attribute [fun_prop] QuasilinearOn QuasiconvexOn QuasiconcaveOn

attribute [fun_prop] QuasiconvexOn.sup
attribute [fun_prop] QuasiconcaveOn.inf
attribute [fun_prop] QuasiconcaveOn.inf

attribute [fun_prop] ConvexOn ConcaveOn

attribute [fun_prop] ConvexOn.quasiconvexOn ConcaveOn.quasiconcaveOn
attribute [fun_prop] LinearMap.convexOn LinearMap.concaveOn

theorem _root_.IsCompact.exists_isMinOn_lowerSemicontinuousOn {α β : Type*}
  [LinearOrder α] [TopologicalSpace α] [TopologicalSpace β] [ClosedIicTopology α]
  {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : LowerSemicontinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x := by
  --Thanks Aristotle
  -- By the Extreme Value Theorem for lower semicontinuous functions on compact sets, there exists x in s such that f(x) is the minimum value of f on s.
  have h_extreme : ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y := by
    by_contra! h;
    choose! g hg using h;
    -- For each $x \in s$, since $f$ is lower semicontinuous at $x$, there exists a neighborhood $U_x$ of $x$ such that $f(y) > f(g(x))$ for all $y \in U_x \cap s$.
    have h_neighborhood : ∀ x ∈ s, ∃ U : Set β, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ s, f y > f (g x) := by
      intro x hx;
      have := hf x hx;
      rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp ( this ( f ( g x ) ) ( hg x hx |>.2 ) ) with ⟨ U, hU, hU' ⟩;
      exact ⟨ interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hU, fun y hy => hU' ⟨ interior_subset hy.1, hy.2 ⟩ ⟩;
    choose! U hU using h_neighborhood;
    -- Since $s$ is compact, the open cover $\{U_x \cap s \mid x \in s\}$ has a finite subcover.
    obtain ⟨t, ht⟩ : ∃ t : Finset β, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x ∩ s := by
      -- Since $s$ is compact, the open cover $\{U_x \mid x \in s\}$ has a finite subcover.
      obtain ⟨t, ht⟩ : ∃ t : Finset β, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x := by
        exact hs.elim_nhds_subcover U fun x hx => IsOpen.mem_nhds ( hU x hx |>.1 ) ( hU x hx |>.2.1 );
      exact ⟨ t, ht.1, fun x hx => by rcases Set.mem_iUnion₂.1 ( ht.2 hx ) with ⟨ y, hy, hy' ⟩ ; exact Set.mem_iUnion₂.2 ⟨ y, hy, ⟨ hy', hx ⟩ ⟩ ⟩;
    -- Since $t$ is finite, there exists $x \in t$ such that $f(g(x))$ is minimal.
    obtain ⟨x, hx⟩ : ∃ x ∈ t, ∀ y ∈ t, f (g x) ≤ f (g y) := by
      apply_rules [ Finset.exists_min_image ];
      -- Since $s$ is nonempty, there exists some $y \in s$.
      obtain ⟨y, hy⟩ : ∃ y, y ∈ s := ne_s;
      exact Exists.elim ( Set.mem_iUnion₂.1 ( ht.2 hy ) ) fun x hx => ⟨ x, hx.1 ⟩;
    obtain ⟨ y, hy ⟩ := ht.2 ( hg x ( ht.1 x hx.1 ) |>.1 );
    simp_all only [Set.mem_inter_iff, and_self, and_true, gt_iff_lt, and_imp, Set.mem_range]
    obtain ⟨left, right⟩ := ht
    obtain ⟨left_1, right_1⟩ := hx
    obtain ⟨⟨w, rfl⟩, right_2⟩ := hy
    simp_all only [Set.mem_iUnion, Set.mem_inter_iff, and_true, exists_prop]
    obtain ⟨left_2, right_2⟩ := right_2
    exact lt_irrefl _ ( lt_of_le_of_lt ( right_1 _ left_2 ) ( hU _ ( left _ left_2 ) |>.2.2 _ right_2 ( hg _ ( left _ left_1 ) ) ) );
  -- By definition of IsMinOn, we need to show that for all y in s, f(x) ≤ f(y). This is exactly what h_extreme provides.
  obtain ⟨x, hx_s, hx_min⟩ := h_extreme;
  use x, hx_s;
  exact hx_min

@[fun_prop]
theorem LinearMap.quasilinearOn {E β 𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [PartialOrder β] [AddCommMonoid β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) :
    QuasilinearOn 𝕜 s f := by
  constructor
  · apply ConvexOn.quasiconvexOn
    apply LinearMap.convexOn
    assumption --why doesn't fun_prop find this assumption? TODO learn
  · apply ConcaveOn.quasiconcaveOn
    apply LinearMap.concaveOn
    assumption --why doesn't fun_prop find this assumption? TODO

@[fun_prop]
theorem LinearMap.quasiconvexOn {E β 𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [PartialOrder β] [AddCommMonoid β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) :
    QuasiconvexOn 𝕜 s f :=
  (f.quasilinearOn hs).left

@[fun_prop]
theorem LinearMap.quasiconcaveOn {E β 𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [PartialOrder β] [AddCommMonoid β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) :
    QuasiconcaveOn 𝕜 s f :=
  (f.quasilinearOn hs).right

--??
theorem continuous_stupid.{u_2, u_1} {M : Type u_1} [inst : NormedAddCommGroup M] [inst_1 : Module ℝ M]
  [inst_3 : ContinuousSMul ℝ M] {N : Type u_2} [inst_4 : NormedAddCommGroup N]
  [inst_5 : Module ℝ N]
  [FiniteDimensional ℝ M]
  (f : N →L[ℝ] M →L[ℝ] ℝ) :
    Continuous fun (x : N × M) ↦ (f x.1) x.2 :=
  have h_eval : Continuous (fun p : (M →L[ℝ] ℝ) × M ↦ p.1 p.2) := by
    have h_sum : Continuous (fun p : (M →L[ℝ] ℝ) × M ↦
        ∑ i, p.1 (Module.finBasis ℝ M i) * ((Module.finBasis ℝ M).repr p.2) i) := by
      refine continuous_finset_sum _ fun i _ ↦ .mul (by fun_prop) ?_;
      · exact ((Module.finBasis ℝ M).coord i).continuous_of_finiteDimensional.comp continuous_snd;
    convert h_sum with x
    rw [ ← (Module.finBasis ℝ M).sum_repr x.2, map_sum]
    simp [mul_comm]
  h_eval.comp <| .prodMk (f.continuous.comp continuous_fst) continuous_snd

/-- The minimax theorem, at the level of generality we need. For convex, compact, nonempty sets `S`
and `T`in a real topological vector space `M`, and a bilinear function `f` on M, we can exchange
the order of minimizing and maximizing. -/
theorem minimax
  {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  {N : Type*} [NormedAddCommGroup N] [Module ℝ N] [ContinuousAdd N] [ContinuousSMul ℝ N]
  (f : N →L[ℝ] M →L[ℝ] ℝ)
  (S : Set M) (T : Set N) (hS₁ : IsCompact S) (hT₁ : IsCompact T)
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)
    : ⨅ x : T, ⨆ y : S, f x y = ⨆ y : S, ⨅ x : T, f x y := by
  have := sion_minimax (f := (f · ·)) (S := T) (T := S) ?_ hT₁ hT₃ hS₃ ?_ ?_ ?_ hS₂ hT₂ ?_ ?_
  · exact this
  · intro y t
    --Why doesn't fun_prop find this, even though this theorem is marked fun_prop? TODO
    apply LowerSemicontinuous.lowerSemicontinuousOn
    fun_prop
  · intro y t
    --Why doesn't fun_prop find this, even though this theorem is marked fun_prop? TODO
    apply UpperSemicontinuous.upperSemicontinuousOn
    fun_prop
  · intro y hy
    exact LinearMap.quasiconvexOn (f := LinearMap.flip {
        toFun := fun x ↦ (f x).toLinearMap, map_add' := by simp, map_smul' := by simp} y) hT₂
  · intro x hx
    apply LinearMap.quasiconcaveOn _ hS₂
  · rw [← Set.image_prod]
    apply (hT₁.prod hS₁).bddAbove_image
    apply Continuous.continuousOn
    apply continuous_stupid
  · rw [← Set.image_prod]
    apply (hT₁.prod hS₁).bddBelow_image
    apply Continuous.continuousOn
    apply continuous_stupid

/-- **Von-Neumann's Minimax Theorem**, specialized to bilinear forms. -/
theorem LinearMap.BilinForm.minimax
  {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  (f : LinearMap.BilinForm ℝ M)
  (S : Set M) (T : Set M) (hS₁ : IsCompact S) (hT₁ : IsCompact T)
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)
    : ⨅ x : T, ⨆ y : S, f x y = ⨆ y : S, ⨅ x : T, f x y :=
  _root_.minimax (LinearMap.toContinuousLinearMap {
    toFun := fun x ↦ (f x).toContinuousLinearMap, map_add' := by simp, map_smul' := by simp})
    S T hS₁ hT₁ hS₂ hT₂ hS₃ hT₃

/-- Convenience form of `LinearMap.BilinForm.minimax` with the order inf/sup arguments supplied to f flipped. -/
theorem LinearMap.BilinForm.minimax'
  {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  (f : LinearMap.BilinForm ℝ M)
  (S : Set M) (T : Set M) (hS₁ : IsCompact S) (hT₁ : IsCompact T)
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)
    : ⨆ x : S, ⨅ y : T, f x y = ⨅ y : T, ⨆ x : S, f x y := by
  symm; exact minimax f.flip S T hS₁ hT₁ hS₂ hT₂ hS₃ hT₃
