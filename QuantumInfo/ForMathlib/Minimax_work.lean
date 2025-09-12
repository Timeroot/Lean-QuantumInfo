import Mathlib

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
      exact ⟨ o, ho, h.1, Set.eq_empty_iff_forall_notMem.2 fun z hz => h.2 ⟨ hz.1, hz.2.1 ⟩ |> not_le_of_gt <| Set.mem_Iic.1 hz.2.2 ⟩;
    · exact ⟨ sᶜ, IsClosed.isOpen_compl, hx', by aesop ⟩;
  · intro a x hx y hy
    have hx_not_in : x ∉ s ∩ f ⁻¹' Set.Iic y := by
      simp [hy]
    rw [ eventually_nhdsWithin_iff ]
    filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.2 ( a y ) ) hx_not_in ] with z hz hzs
    exact lt_of_not_ge fun h => hz ⟨hzs, h⟩

theorem segment.isConnected {E : Type u_1} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] (a b : E) :
    IsConnected (segment ℝ a b) := by
  rw [← Path.range_segment a b]
  exact isConnected_range (Path.segment a b).continuous

theorem IsPreconnected.subset_or_of_closed_inter_empty {M : Type*} [TopologicalSpace M] {A B C: Set M}
  [hA : IsClosed A] [hB : IsClosed B] (hAB : A ∩ B = ∅) (hABC : C ⊆ A ∪ B) (hC : IsPreconnected C) : C ⊆ A ∨ C ⊆ B := by
  open Set in
  rw [IsPreconnected] at hC
  contrapose! hC
  refine ⟨Bᶜ, Aᶜ, hB.isOpen_compl, hA.isOpen_compl, ?_, C.not_subset.mp hC.2, C.not_subset.mp hC.1, ?_⟩
  · simp only [Set.ext_iff, mem_inter_iff, mem_empty_iff_false, subset_def, mem_union, mem_compl_iff] at *
    grind only
  · simpa [Set.ext_iff] using fun _ ↦ (hABC · |> Or.resolve_right <| ·)

section extracted

variable {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  {N : Type*} [NormedAddCommGroup N] [Module ℝ N] [ContinuousAdd N] [ContinuousSMul ℝ N] [FiniteDimensional ℝ N]
  (f : M → N → ℝ) (S : Set M) (T : Set N)
  (hfc₁ : ∀ x, x ∈ S → UpperSemicontinuousOn (f x) T)
  (hfq₁ : ∀ x, x ∈ S → QuasiconcaveOn ℝ T (f x))
  (hfc₂ : ∀ y, y ∈ T → LowerSemicontinuousOn (f · y) S)
  (hfq₂ : ∀ y, y ∈ T → QuasiconvexOn ℝ S (f · y))
  (hS₁ : IsCompact S) (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃ in
theorem sion_exists_min_2.extracted_1_4 (y₁ y₂ : N)
  (hy₁ : y₁ ∈ T) (hy₂ : y₂ ∈ T) (a : ℝ) (x : CompactSpace ↑S) (x_1 : IsClosed S) (β : ℝ) (hβ₁ : a < β)
  (hβ₂ : β < ⨅ x, max (f (↑x) y₁) (f (↑x) y₂)) :
  let C := fun z => {x | x ∈ S ∧ f x z ≤ a};
  let C' := fun z => {x | x ∈ S ∧ f x z ≤ β};
  let A := C' y₁;
  (∀ (z : N), C z ⊆ C' z) → (∀ z ∈ segment ℝ y₁ y₂, (C z).Nonempty) →
  (∀ z ∈ segment ℝ y₁ y₂, IsClosed (C z)) → (∀ z ∈ segment ℝ y₁ y₂, (C' z).Nonempty) →
  (∀ z ∈ segment ℝ y₁ y₂, IsClosed (C' z)) → A.Nonempty → IsClosed A →
  (∀ x ∈ S, ∀ z ∈ segment ℝ y₁ y₂, min (f x y₁) (f x y₂) ≤ f x z) →
  (∀ z ∈ segment ℝ y₁ y₂, Convex ℝ (C' z)) → let I := {z | z ∈ segment ℝ y₁ y₂ ∧ C z ⊆ A};
    IsClosed I := by
  sorry

end extracted

section sion_minimax
--Following https://projecteuclid.org/journals/kodai-mathematical-journal/volume-11/issue-1/Elementary-proof-for-Sions-minimax-theorem/10.2996/kmj/1138038812.pdf

variable  {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  {N : Type*} [NormedAddCommGroup N] [Module ℝ N] [ContinuousAdd N] [ContinuousSMul ℝ N] [FiniteDimensional ℝ N]
  {f : M → N → ℝ} {S : Set M} {T : Set N}
  (hfc₁ : ∀ x, x ∈ S → UpperSemicontinuousOn (f x) T)
  (hfq₁ : ∀ x, x ∈ S → QuasiconcaveOn ℝ T (f x))
  (hfc₂ : ∀ y, y ∈ T → LowerSemicontinuousOn (f · y) S)
  (hfq₂ : ∀ y, y ∈ T → QuasiconvexOn ℝ S (f · y))
  (hS₁ : IsCompact S)
  -- (hT₁ : IsCompact T) -- --In principle we don't need hT₁.
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)

set_option linter.unusedSectionVars false in
include hfc₂ hS₁ hS₃ in
private theorem sion_exists_min_lowerSemi (a : ℝ) (hc : ∀ y₀ ∈ T, ⨅ (x : S), f (↑x) y₀ ≤ a) (z : N) (hzT : z ∈ T) :
    ∃ x ∈ S, f x z ≤ a := by
  let _ := hS₃.to_subtype
  contrapose! hc
  -- have hzT : z ∈ T := hT₂.segment_subset hy₁ hy₂ hz
  use z, hzT
  have h_lower_bound (x : S) : a < f x z := hc x x.2
  apply lt_of_le_of_ne
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact (h_lower_bound x).le
  intro h
  obtain ⟨x, hxz⟩ : ∃ x : S, f x z ≤ a := by
    obtain ⟨xn, hxn⟩ : ∃ xn : ℕ → S, Filter.atTop.Tendsto (fun n => f (xn n) z) (nhds a) := by
      have h_eps : ∀ ε > 0, ∃ x : S, f x z < a + ε := by
        intro ε εpos
        have hx : ⨅ x : S, f x z < a + ε := by linarith
        simpa using exists_lt_of_csInf_lt (Set.range_nonempty _) hx
      choose! xn hxn using h_eps
      use fun n ↦ xn (1 / (n + 1))
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ ↦ abs_nonneg _) (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [h_lower_bound (xn (1 / (n + 1))), hxn (1 / (n + 1)) (by positivity)]
    obtain ⟨x, subseq, hsubseq₁, hsubseq₂⟩ : ∃ x : S, ∃ subseq : ℕ → ℕ,
        StrictMono subseq ∧ Filter.Tendsto (fun n => xn (subseq n)) Filter.atTop (nhds x) := by
      simpa using (isCompact_iff_isCompact_univ.mp hS₁).isSeqCompact (x := xn) fun _ ↦ trivial
    use x
    refine le_of_forall_pos_le_add fun ε εpos ↦ ?_
    rw [← tsub_le_iff_right]
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (hxn.comp hsubseq₁.tendsto_atTop)
    apply Filter.eventually_atTop.mpr
    rw [Metric.tendsto_atTop] at hsubseq₂
    have ⟨δ, δpos, H⟩ : ∃ δ > 0, ∀ y ∈ S, dist y x < δ → f y z > f x z - ε := by
      obtain ⟨δ, hδ⟩ := Metric.mem_nhdsWithin_iff.mp (((hfc₂ z hzT) x x.2) _ (sub_lt_self _ εpos))
      exact ⟨δ, hδ.1, fun y hy hyx => hδ.2 ⟨hyx, hy⟩⟩
    rcases hsubseq₂ δ δpos with ⟨N, hN⟩
    exact ⟨N, fun n hn ↦ (H _ (xn (subseq n)).coe_prop (hN _ hn)).le⟩
  specialize h_lower_bound x
  order

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
    simp only [Set.Nonempty, Set.mem_setOf_eq, C]
    exact sion_exists_min_lowerSemi hfc₂ hS₁ hS₃ a hc z (hT₂.segment_subset hy₁ hy₂ hz)
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
  have hC'zAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C' z ⊆ A ∪ B := by grind [inf_le_iff, le_trans]
  have hC'z (z) (hz : z ∈ segment ℝ y₁ y₂) : Convex ℝ (C' z) :=
    hfq₂ z (hT₂.segment_subset hy₁ hy₂ hz) β
  have hCzAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C z ⊆ A ∨ C z ⊆ B := by
    specialize hC_subset_C' z
    specialize hC'z z hz
    have hC' : IsPreconnected (C' z) :=
      ((hC'z).isConnected ((hC_nonempty z hz).mono hC_subset_C')).isPreconnected;
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hC'
    rcases hC' A B hA_closed hB_closed (hC'zAB z hz) (by simp [hAB]) with h | h
    · exact .inl (hC_subset_C'.trans h)
    · exact .inr (hC_subset_C'.trans h)
  let I : Set N := { z | z ∈ segment ℝ y₁ y₂ ∧ C z ⊆ A}
  let J : Set N := { z | z ∈ segment ℝ y₁ y₂ ∧ C z ⊆ B}
  have hI₁ : I.Nonempty := by
    use y₁
    simp [I, A, hC_subset_C', left_mem_segment]
  have hJ₁ : J.Nonempty := by
    use y₂
    simp [J, B, hC_subset_C', right_mem_segment]
  rw [Set.nonempty_iff_ne_empty] at hI₁ hJ₁
  have hIJ : I ∩ J = ∅ := by
    simp [I, J, Set.ext_iff]
    intro z hz hCzA _ hCzB
    specialize hCzA (hC_nonempty z hz).some_mem
    specialize hCzB (hC_nonempty z hz).some_mem
    rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left] at hAB
    tauto
  have hIJ₂ : I ∪ J = segment ℝ y₁ y₂ := by
    simp [I, J, Set.ext_iff]
    grind
  have hI : IsClosed I := by
    -- clear hIJ₂ hIJ J hCzAB hC'zAB hAB hB_nonempty hB_closed B hc ha
    -- extract_goal
    -- have cloL : IsClosed (segment ℝ y₁ y₂) := by
    --   rw [← closure_openSegment]
    --   exact isClosed_closure
    -- have cloR : IsClosed {z | C z ⊆ A} := by
    --   simp +contextual only [Set.setOf_subset_setOf, true_and, and_imp, C, A, C']
    --   sorry
    -- exact cloL.inter cloR
    sorry
  have hJ : IsClosed J := by
    -- have cloL : IsClosed (segment ℝ y₁ y₂) := by
    --   rw [← closure_openSegment]
    --   exact isClosed_closure
    -- have cloR : IsClosed {z | C z ⊆ B} := by
    --   simp +contextual only [Set.setOf_subset_setOf, true_and, and_imp, C, B, C']
      -- sorry
    -- exact cloL.inter cloR
    sorry
  have hConnected := segment.isConnected y₁ y₂
  rw [IsConnected, isPreconnected_iff_subset_of_fully_disjoint_closed ?_] at hConnected; swap
  · rw [← closure_openSegment]
    exact isClosed_closure
  replace hConnected := hConnected.right I J
  simp [hIJ, ← hIJ₂, Set.disjoint_iff_inter_eq_empty] at hConnected
  obtain hL | hR := hConnected hI hJ
  · rw [Set.inter_eq_self_of_subset_right hL] at hIJ
    exact hJ₁ hIJ
  · rw [Set.inter_eq_self_of_subset_left hR] at hIJ
    exact hI₁ hIJ

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
        convert ((hfc₂ hyₙ).inter ha_closed).preimage this
        simp [S']
      fun_prop
    have hS'₂ : Convex ℝ S' := hfq₂ _ hyₙ _
    specialize @ih S'
      (hfc₁ · <| hS'_sub ·) (hfq₁ · <| hS'_sub ·)
      (hfc₂ · · |>.mono hS'_sub) (hfq₂ · · |>.subset hS'_sub hS'₂)
      hS'₁ hS'₂ hS'_n ht ?_
    · sorry
    obtain ⟨y₀', hy₀'_mem, hy₀'⟩ := ih
    apply sion_exists_min_2 hfc₁ hfq₁ hfc₂ hfq₂
      hS₁ hS₂ hT₂ hS₃ hT₃ y₀' yₙ hy₀'_mem hyₙ a
    sorry


include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃ in
/-- **Sion's Minimax theorem**. Because of `ciSup` junk values when f isn't bounded,
we need to assume that it's bounded above on one of its arguments. -/
theorem sion_minimax (h_bdd : ∀ j : S, BddAbove (Set.range fun x : T ↦ f j x))
    : ⨅ x : S, ⨆ y : T, f x y = ⨆ y : T, ⨅ x : S, f x y := by
  have := hT₃.to_subtype
  have h_bdd_1 (i : T) : BddBelow (Set.range fun j : S ↦ f j i) := by
    convert (hfc₂ i i.2).bddBelow hS₁
    ext; simp
  have h_bdd_2 : BddAbove (Set.range fun y : T ↦ ⨅ x : S, f x y) := by
    sorry
  have h_bdd_3 : BddBelow (Set.range fun x : S ↦ ⨆ y : T, f x y) := by
    sorry
  apply le_antisymm; swap
  · exact ciSup_ciInf_le_ciInf_ciSup _ h_bdd h_bdd_1
  by_contra! h
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h; clear h
  revert ha₁
  rw [imp_false, not_lt]
  have := hS₁.elim_finite_subfamily_closed (fun (y : T) ↦ { x | x ∈ S ∧ f x y ≤ a}) ?_ ?_
  · rcases this with ⟨u, hu⟩
    have hu' : u.Nonempty := by
      by_contra hu'
      rw [Finset.not_nonempty_iff_eq_empty] at hu'
      simp [hu'] at hu
      simp [hu] at hS₃
    have h_fin := sion_exists_min_fin hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃
    specialize h_fin (u.map ⟨_, Subtype.val_injective⟩) (by simpa) (by simp) a ?_
    · contrapose! hu
      sorry
    rcases h_fin with ⟨y₀, hy₀T, hy₀⟩
    refine hy₀.le.trans ?_
    exact le_ciSup h_bdd_2 ⟨y₀, hy₀T⟩
  · intro i
    specialize hfc₂ i i.2
    dsimp
    have _ := hS₁.isClosed
    rw [lowerSemicontinuousOn_iff_isClosed_preimage] at hfc₂
    exact hfc₂ a
  · convert Set.inter_empty _
    by_contra hu
    simp? [Set.iInter_eq_empty_iff] says simp only [
      Set.iInter_coe_set, Set.iInter_eq_empty_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Classical.not_imp, not_and, not_le, not_forall, not_exists, not_lt] at hu
    have _ := hS₃.to_subtype
    rw [lt_ciInf_iff h_bdd_3] at ha₂
    rcases hu with ⟨x, hx⟩
    rcases ha₂ with ⟨b, hab, hb⟩
    specialize hx _ hT₃.some_mem
    rcases hx with ⟨hx, hb2⟩
    specialize hb ⟨x, hx⟩
    dsimp at hb
    sorry
