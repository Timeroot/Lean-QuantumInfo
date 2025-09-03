import HarmonicLean

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

/-- The max-min theorem. A version of `iSup_iInf_le_iInf_iSup` for conditionally complete lattices. -/
theorem ciSup_ciInf_le_ciInf_ciSup {ι ι' α : Type*} [ConditionallyCompleteLattice α ] [Nonempty ι]
  (f : ι → ι' → α) (Ha : ∀ j, BddAbove (Set.range (f · j))) (Hb : ∀ i, BddBelow (Set.range (f i))) :
    ⨆ i, ⨅ j, f i j ≤ ⨅ j, ⨆ i, f i j :=
  ciSup_le fun i ↦ ciInf_mono (Hb i) fun j ↦ le_ciSup (Ha j) i

theorem lt_ciInf_iff {α : Type*} {ι : Sort*} [Nonempty ι] [ConditionallyCompleteLattice α] {f : ι → α} {a : α}
    (hf : BddBelow (Set.range f)) :
    a < iInf f ↔ ∃ b, a < b ∧ ∀ (i : ι), b ≤ f i := by
  apply Iff.intro;
  · intro a_1
    exact ⟨ iInf f, a_1, fun i => ciInf_le hf i ⟩;
  · intro h
    obtain ⟨b, hb₁, hb₂⟩ := h
    have h_inf : b ≤ iInf f := by
      exact le_ciInf hb₂;
    exact lt_of_lt_of_le hb₁ h_inf

/-- The minimax theorem. For convex, compact, nonempty sets `S` and `T` in a pair of real
topological vector spaces `M` and `N`, and a bilinear function `f` on `M` and `N`, we can exchange
the order of minimizing and maximizing. -/
theorem bilin_minimax
  {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  {N : Type*} [NormedAddCommGroup N] [Module ℝ N] [ContinuousAdd N] [ContinuousSMul ℝ N] [FiniteDimensional ℝ N]
  (f : M →ₗ[ℝ] N →ₗ[ℝ] ℝ) (S : Set M) (T : Set N) (hS₁ : IsCompact S) (hT₁ : IsCompact T)
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)
    : ⨆ x : S, ⨅ y : T, f x y = ⨅ y : T, ⨆ x : S, f x y := by
  have := hS₃.coe_sort
  have := hT₃.coe_sort
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS₁
  have : CompactSpace T := isCompact_iff_compactSpace.mp hT₁
  apply le_antisymm
  · --The easy direction, also called the "min-max theorem".
    apply ciSup_ciInf_le_ciInf_ciSup
    · intro
      rw [← Set.image_univ]
      apply IsCompact.bddAbove_image CompactSpace.isCompact_univ
      simp_rw [← LinearMap.flip_apply (f)]
      fun_prop
    · intro
      rw [← Set.image_univ]
      apply IsCompact.bddBelow_image CompactSpace.isCompact_univ
      fun_prop
  sorry

--Currently in Mathlib, backporting this proof
theorem lowerSemicontinuousOn_iff_isClosed_epigraph
  {α γ : Type*} [TopologicalSpace α] [LinearOrder γ] [TopologicalSpace γ] [ClosedIciTopology γ]
  {f : α → γ} {s : Set α} (hs : IsClosed s) :
    LowerSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  simp_rw [LowerSemicontinuousOn, LowerSemicontinuousWithinAt, eventually_nhdsWithin_iff,
    ← isOpen_compl_iff, Set.compl_setOf, isOpen_iff_eventually, Set.mem_setOf, not_and, not_le]
  constructor
  · intro hf ⟨x, y⟩ h
    by_cases hx : x ∈ s
    · have ⟨y', hy', z, hz, h₁⟩ := (h hx).exists_disjoint_Iio_Ioi
      filter_upwards [(hf x hx z hz).prodMk_nhds (eventually_lt_nhds hy')]
        with _ ⟨h₂, h₃⟩ h₄ using h₁ _ h₃ _ <| h₂ h₄
    · filter_upwards [(continuous_fst.tendsto _).eventually (hs.isOpen_compl.eventually_mem hx)]
        with _ h₁ h₂ using (h₁ h₂).elim
  · intro hf x _ y hy
    exact ((Continuous.prodMk_left y).tendsto x).eventually (hf (x, y) (fun _ => hy))

theorem QuasiconvexOn.subset
  {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [LE β] [SMul 𝕜 E]
  {s : Set E} {f : E → β} (h : QuasiconvexOn 𝕜 s f) {t : Set E} (hts : t ⊆ s) (ht : Convex 𝕜 t) :
    QuasiconvexOn 𝕜 t f := by
  intro b
  convert ht.inter (h b) using 1
  simp +contextual [Set.ext_iff, @hts _]

theorem QuasiconvexOn.mem_segment_le_max
  {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SemilatticeSup β] [SMul 𝕜 E]
  {s : Set E} {f : E → β} (h : QuasiconvexOn 𝕜 s f)
  {x y z : E} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ segment 𝕜 x y):
    f z ≤ f x ⊔ f y :=
  ((h (f x ⊔ f y)).segment_subset (by simpa) (by simpa) hz).right

theorem QuasiconcaveOn.min_le_mem_segment
  {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SemilatticeInf β] [SMul 𝕜 E]
  {s : Set E} {f : E → β} (h : QuasiconcaveOn 𝕜 s f)
  {x y z : E} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ segment 𝕜 x y):
    f x ⊓ f y ≤ f z :=
  ((h (f x ⊓ f y)).segment_subset (by simpa) (by simpa) hz).right

theorem LowerSemicontinuousOn.bddBelow {α : Type*} [TopologicalSpace α] {S : Set α} {g : α → ℝ}
    (hg : LowerSemicontinuousOn g S) (hS : IsCompact S) : BddBelow (g '' S) := by
  rcases S.eq_empty_or_nonempty with rfl | hS₂
  · simp
  have h_neighborhood : ∀ x ∈ S, ∃ U ∈ nhds x, ∀ y ∈ U ∩ S, g y > g x - 1 := by
    -- By definition of lower semicontinuity, for each x ∈ S, there exists a neighborhood U_x such that g(y) > g(x) - 1 for all y ∈ U_x ∩ S.
    intros x hx
    specialize hg x hx (g x - 1) (sub_one_lt (g x))
    rw [eventually_nhdsWithin_iff] at hg
    simp only [Set.mem_inter_iff, gt_iff_lt, and_imp]
    exact ⟨_, hg, fun y hy hyS ↦ hy hyS⟩
  choose! U hU using h_neighborhood
  -- By the finite subcover property, there exists a finite subset t ⊆ S$ such that S ⊆ ⋃_{x ∈ t} U_x$.
  obtain ⟨t, ht⟩ : ∃ t, (∀ x ∈ t, x ∈ S) ∧ S ⊆ ⋃ x ∈ t, U x :=
    hS.elim_nhds_subcover U fun x hx ↦ hU x hx |>.1;
  -- Let $m$ be the minimum value of $g$ on the finite set $t$.
  obtain ⟨m, hm⟩ : ∃ m, ∀ x ∈ t, g x ≥ m := by
    use Finset.min' (t.image g) ?_
    · exact fun x hx ↦ Finset.min'_le _ _ (t.mem_image_of_mem g hx)
    refine ⟨_, Finset.mem_image_of_mem g <| Classical.choose_spec <| Finset.nonempty_of_ne_empty ?_⟩
    rintro rfl
    simpa using ht.2 hS₂.some_mem
  use m - 1
  refine Set.forall_mem_image.mpr fun x hx ↦ ?_
  rcases Set.mem_iUnion₂.mp (ht.2 hx) with ⟨y, hy, hy'⟩
  linarith [hm y hy, hU y (ht.1 y hy) |>.2 x ⟨hy', hx⟩]

theorem LowerSemicontinuousOn.max {α : Type*} [TopologicalSpace α] {S : Set α} {f g : α → ℝ}
    (hf : LowerSemicontinuousOn f S) (hg : LowerSemicontinuousOn g S) :
    LowerSemicontinuousOn (fun x ↦ max (f x) (g x)) S := by
  convert lowerSemicontinuousOn_ciSup (s := S) (f := fun (i : Bool) x' ↦ if i then f x' else g x') ?_ ?_
  · rw [ciSup_eq_of_forall_le_of_forall_lt_exists_gt] <;> aesop
  · simp
  · simp [hf, hg]

variable {α : Type*} [TopologicalSpace α] {β : Type*} [Preorder β] {f g : α → β} {x : α}
  {s t : Set α} {y z : β} {γ : Type*} [LinearOrder γ]

theorem lowerSemicontinuousOn_iff_isClosed_preimage {f : α → γ} [IsClosed s] :
    LowerSemicontinuousOn f s ↔ ∀ y, IsClosed (s ∩ f ⁻¹' Set.Iic y) := by
  constructor
  · intro a y
    refine' isClosed_of_closure_subset fun x hx => _;
    rw [ mem_closure_iff ] at hx;
    contrapose! hx;
    cases' em ( x ∈ s ) with hx' hx';
    · simp only [Set.mem_inter_iff, hx', Set.mem_preimage, Set.mem_Iic, true_and, not_le] at hx
      have := a x hx';
      rcases mem_nhdsWithin.1 ( this y hx ) with ⟨ o, ho, h ⟩;
      exact ⟨ o, ho, h.1, Set.eq_empty_iff_forall_not_mem.2 fun z hz => h.2 ⟨ hz.1, hz.2.1 ⟩ |> not_le_of_gt <| Set.mem_Iic.1 hz.2.2 ⟩;
    · exact ⟨ sᶜ, IsClosed.isOpen_compl, hx', by aesop ⟩;
  · intro a x hx y hy
    have hx_not_in : x ∉ s ∩ f ⁻¹' Set.Iic y := by
      simp [hy]
    rw [ eventually_nhdsWithin_iff ]
    filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.2 ( a y ) ) hx_not_in ] with z hz hzs
    exact lt_of_not_ge fun h => hz ⟨hzs, h⟩

theorem segment.isConnected {E : Type u_1} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] (a b : E) :
    IsConnected (segment ℝ a b) := by
  sorry --The below proof works in latest mathlib
  -- rw [← Path.range_segment a b]
  -- exact isConnected_range (Path.segment a b).continuous

section extracted

variable {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  {N : Type*} [NormedAddCommGroup N] [Module ℝ N] [ContinuousAdd N] [ContinuousSMul ℝ N] [FiniteDimensional ℝ N]
  (f : M → N → ℝ) (S : Set M) (T : Set N)
  (hfc₂ : ∀ y, y ∈ T → LowerSemicontinuousOn (f · y) S)
  (hfq₂ : ∀ y, y ∈ T → QuasiconvexOn ℝ S (f · y))
  (hS₁ : IsCompact S) (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)

end extracted

section sion_minimax
--Following https://projecteuclid.org/journals/kodai-mathematical-journal/volume-11/issue-1/Elementary-proof-for-Sions-minimax-theorem/10.2996/kmj/1138038812.pdf

variable  {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  {N : Type*} [NormedAddCommGroup N] [Module ℝ N] [ContinuousAdd N] [ContinuousSMul ℝ N] [FiniteDimensional ℝ N]
  (f : M → N → ℝ) (S : Set M) (T : Set N)
  (hfc₁ : ∀ x, x ∈ S → UpperSemicontinuousOn (f x) T)
  (hfq₁ : ∀ x, x ∈ S → QuasiconcaveOn ℝ T (f x))
  (hfc₂ : ∀ y, y ∈ T → LowerSemicontinuousOn (f · y) S)
  (hfq₂ : ∀ y, y ∈ T → QuasiconvexOn ℝ S (f · y))
  (hS₁ : IsCompact S)
  -- (hT₁ : IsCompact T) -- --In principle we don't need hT₁.
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃ in
private lemma sion_exists_min_2 (y₁ y₂ : N) (hy₁ : y₁ ∈ T) (hy₂ : y₂ ∈ T)
    (a : ℝ) (ha : a < ⨅ x : S, (max (f x y₁) (f x y₂)))
    : ∃ y₀ : N, y₀ ∈ T ∧ a < ⨅ x : S, f x y₀ := by
  by_contra! hc
  have _ := isCompact_iff_compactSpace.mp hS₁
  have _ := hS₁.isClosed
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_between ha
  let C : N → Set M := fun z ↦ { x ∈ S | f x z ≤ a }
  let C' : N → Set M := fun z ↦ { x ∈ S | f x z ≤ β }
  let A := C' y₁
  let B := C' y₂
  have hC_subset_C' (z) : C z ⊆ C' z :=
    fun x hx ↦ ⟨hx.1, hx.2.trans hβ₁.le⟩
  have hC_nonempty (z) (hz : z ∈ segment ℝ y₁ y₂) : (C z).Nonempty := by
    sorry
  have hC_closed (z) (hz : z ∈ segment ℝ y₁ y₂) : IsClosed (C z) := by
    specialize hfc₂ z (hT₂.segment_subset hy₁ hy₂ hz)
    rw [lowerSemicontinuousOn_iff_isClosed_preimage] at hfc₂
    exact hfc₂ a
  have hC'_nonempty (z) (hz : z ∈ segment ℝ y₁ y₂) : (C' z).Nonempty :=
    (hC_nonempty z hz).mono (hC_subset_C' z)
  have hC'_closed (z) (hz : z ∈ segment ℝ y₁ y₂) : IsClosed (C' z) := by
    specialize hfc₂ z (hT₂.segment_subset hy₁ hy₂ hz)
    rw [lowerSemicontinuousOn_iff_isClosed_preimage] at hfc₂
    exact hfc₂ β
  have hA_nonempty : A.Nonempty := hC'_nonempty y₁ (left_mem_segment ℝ y₁ y₂)
  have hA_closed : IsClosed A := hC'_closed y₁ (left_mem_segment ℝ y₁ y₂)
  have hB_nonempty : B.Nonempty := hC'_nonempty y₂ (right_mem_segment ℝ y₁ y₂)
  have hB_closed : IsClosed B := hC'_closed y₂ (right_mem_segment ℝ y₁ y₂)
  have hAB : A ∩ B = ∅ := by
    simp [A, B, C', Set.ext_iff]
    intro x hx hβy₁ _
    by_contra! hβy₂
    have hβ := max_le hβy₁ hβy₂
    revert hβ
    rw [imp_false, not_le]
    refine lt_of_lt_of_le hβ₂ ?_
    have h := ((hfc₂ y₁ hy₁).max (hfc₂ y₂ hy₂)).bddBelow hS₁
    rw [Set.image_eq_range] at h
    exact ciInf_le h ⟨x, hx⟩
  have hfxz (x) (hx : x ∈ S) (z) (hz : z ∈ segment ℝ y₁ y₂) : min (f x y₁) (f x y₂) ≤ f x z :=
    (hfq₁ x hx).min_le_mem_segment hy₁ hy₂ hz
  have hC'zAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C' z ⊆ A ∪ B := by
    intro t
    simp only [A, B, C', Set.mem_setOf_eq, Set.mem_union, and_imp]
    intro ht hftz
    replace hfxz := (hfxz t ht z hz).trans hftz
    simp only [ht, true_and]
    exact inf_le_iff.mp hfxz
  have hC'z (z) (hz : z ∈ segment ℝ y₁ y₂) : Convex ℝ (C' z) :=
    hfq₂ z (hT₂.segment_subset hy₁ hy₂ hz) β
  have hCzAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C z ⊆ A ∨ C z ⊆ B := by
    sorry
  let I : Set N := { z | z ∈ segment ℝ y₁ y₂ ∧ C z ⊆ A}
  let J : Set N := { z | z ∈ segment ℝ y₁ y₂ ∧ C z ⊆ B}
  have hIJ : I ∩ J = ∅ := by
    simp [I, J, Set.ext_iff]
    intro z hz hCzA _ hCzB
    specialize hCzA (hC_nonempty z hz).some_mem
    specialize hCzB (hC_nonempty z hz).some_mem
    rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left] at hAB
    tauto
  have hIJ₂ : I ∪ J = segment ℝ y₁ y₂ := by
    simp [I, J, Set.ext_iff]
    intro z
    specialize hCzAB z
    tauto
  have hI : IsClosed I := by
    sorry
  have hJ : IsClosed J := by
    sorry
  have hConnected := segment.isConnected y₁ y₂
  rw [IsConnected, isPreconnected_iff_subset_of_fully_disjoint_closed (by sorry)] at hConnected
  replace hConnected := hConnected.right I J
  simp [hIJ, ← hIJ₂, Set.disjoint_iff_inter_eq_empty] at hConnected
  replace hConnected := hConnected hI hJ
  sorry

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃ in
private lemma sion_exists_min_fin (ys : Finset N) (hys_n : ys.Nonempty) (hys : (ys : Set N) ⊆ T)
    (a : ℝ) (ha : a < ⨅ x : S, ⨆ yi : ys, f x yi)
    : ∃ y₀ : N, y₀ ∈ T ∧ a < ⨅ x : S, f x y₀ := by
  induction hys_n using Finset.Nonempty.cons_induction generalizing S
  case singleton x =>
    simp at ha hys
    use x
  case cons yₙ t hxt htn ih =>
    classical rw [Finset.cons_eq_insert] at hys ha
    simp [Set.insert_subset_iff] at hys
    rcases hys with ⟨hyₙ, ht⟩
    let S' := {z : M | z ∈ S ∧ f z yₙ ≤ a}
    have hS'_sub : S' ⊆ S := Set.sep_subset ..
    rcases S'.eq_empty_or_nonempty with hS'_e | hS'_n
    · simp [S'] at hS'_e
      use yₙ, hyₙ
      --should be immediate from hS'_e
      sorry

    -- have _ := hS₃.coe_sort
    -- rw [lt_ciInf_iff ?_] at ha; swap
    -- · sorry
    -- rcases ha with ⟨b, hab, hb⟩
    -- have ha := fun i ↦ lt_of_lt_of_le hab (hb i)
    -- clear b hab hb

    have hS'₁ : IsCompact S' := by
      apply hS₁.of_isClosed_subset ?_ hS'_sub
      specialize hfc₂ yₙ
      rw [lowerSemicontinuousOn_iff_isClosed_epigraph hS₁.isClosed] at hfc₂
      have ha_closed : IsClosed {p : M × ℝ | p.2 = a} := by
        convert isClosed_univ.prod (isClosed_singleton (x := a))
        simp [Set.ext_iff]
      suffices Continuous (fun (z : M) ↦ (z, a) : M → M × ℝ) by
        convert ((hfc₂ sorry).inter ha_closed).preimage this
        simp [S']
      fun_prop
    have hS'₂ : Convex ℝ S' := hfq₂ _ hyₙ _
    specialize ih S' (fun y ↦ (hfc₂ y sorry).mono hS'_sub) (fun y ↦ (hfq₂ y).subset hS'_sub hS'₂)
      hS'₁ hS'₂ hS'_n ht ?_
    · sorry
    obtain ⟨y₀', hy₀'_mem, hy₀'⟩ := ih
    apply sion_exists_min_2 f S T hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃
      y₀' yₙ hy₀'_mem hyₙ a
    sorry


include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃ in
theorem sion_minimax
    : ⨅ x : S, ⨆ y : T, f x y = ⨆ y : T, ⨅ x : S, f x y := by
  sorry
