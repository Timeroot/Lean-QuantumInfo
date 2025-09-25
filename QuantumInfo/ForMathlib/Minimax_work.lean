import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Fintype.Order
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.SpecificLimits.Basic

@[simp]
theorem Set.image2_flip {α β γ : Type*} {f : α → β → γ} (s : Set α) (t : Set β) :
    image2 (flip f) t s = image2 f s t := by
  grind [image2, flip]

section ciSup

variable {ι α : Type*} [ConditionallyCompleteLattice α] {f g : ι → α} {a : α}

/-- The **max-min theorem**. A version of `iSup_iInf_le_iInf_iSup` for conditionally complete lattices. -/
theorem ciSup_ciInf_le_ciInf_ciSup {ι': Type*} [Nonempty ι]
  (f : ι → ι' → α) (Ha : ∀ j, BddAbove (Set.range (f · j))) (Hb : ∀ i, BddBelow (Set.range (f i))) :
    ⨆ i, ⨅ j, f i j ≤ ⨅ j, ⨆ i, f i j :=
  ciSup_le fun i ↦ ciInf_mono (Hb i) fun j ↦ le_ciSup (Ha j) i

theorem lt_ciInf_iff {α : Type*} {ι : Sort*} [Nonempty ι] [ConditionallyCompleteLattice α] {f : ι → α} {a : α}
    (hf : BddBelow (Set.range f)) :
    a < iInf f ↔ ∃ b, a < b ∧ ∀ (i : ι), b ≤ f i :=
  ⟨(⟨iInf f, ·, (ciInf_le hf ·)⟩), fun ⟨_, hb₁, hb₂⟩ ↦ lt_of_lt_of_le hb₁ (le_ciInf hb₂)⟩

theorem BddAbove.range_max (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) :
    BddAbove (Set.range (max f g)) := by
  rcases hf with ⟨a, ha⟩
  rcases hg with ⟨b, hb⟩
  use a ⊔ b
  simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, Pi.sup_apply] at ha hb ⊢
  intro i
  specialize ha i
  specialize hb i
  order

theorem BddBelow.range_min (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g)) :
    BddBelow (Set.range (min f g)) :=
  BddAbove.range_max (α := αᵒᵈ) hf hg

variable [Nonempty ι]

theorem ciSup_sup_eq (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (ciSup_le fun _ => sup_le_sup (le_ciSup hf _) <| le_ciSup hg _)
    (sup_le (ciSup_mono (hf.range_max hg) fun _ => le_sup_left) <| ciSup_mono (hf.range_max hg) fun _ => le_sup_right)

theorem ciInf_inf_eq (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g)) : ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ ⨅ x, g x :=
  ciSup_sup_eq (α := αᵒᵈ) hf hg

theorem sup_ciSup (hf : BddAbove (Set.range f)) : a ⊔ ⨆ x, f x = ⨆ x, a ⊔ f x := by
  rw [ciSup_sup_eq (by simp) hf, ciSup_const]

theorem inf_ciInf (hf : BddBelow (Set.range f)) : a ⊓ ⨅ x, f x = ⨅ x, a ⊓ f x :=
  sup_ciSup (α := αᵒᵈ) hf

theorem ciInf_sup_ciInf_le (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g)) :
    (⨅ i, f i) ⊔ ⨅ i, g i ≤ ⨅ i, f i ⊔ g i :=
  le_ciInf (fun i ↦ sup_le_sup (ciInf_le hf i) (ciInf_le hg i))

theorem le_ciSup_inf_ciSup (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) :
    ⨆ (i : ι), f i ⊓ g i ≤ (⨆ (i : ι), f i) ⊓ ⨆ (i : ι), g i :=
  ciInf_sup_ciInf_le (α := αᵒᵈ) hf hg

omit [Nonempty ι] in
theorem ciInf_eq_min_cInf_inter_diff (S T : Set ι)
  [Nonempty (S ∩ T : Set ι)] [Nonempty (S \ T : Set ι)] (hf : BddBelow (f '' S)) :
    ⨅ i : S, f i = (⨅ i : (S ∩ T : Set ι), f i) ⊓ ⨅ i : (S \ T : Set ι), f i := by
  refine' le_antisymm _ _;
  · rw [le_inf_iff]
    apply And.intro
    · apply_rules [ ciInf_le, le_ciInf ];
      simp only [Subtype.forall, Set.mem_inter_iff, and_imp]
      exact fun a ha hb => ciInf_le ( show BddBelow ( Set.range fun i : S => f i ) by simpa [ Set.range ] using hf ) ⟨ a, ha ⟩;
    · apply_rules [ ciInf_le, le_ciInf ];
      simp only [Subtype.forall, Set.mem_diff, and_imp]
      exact fun a ha hb => ciInf_le ( show BddBelow ( Set.range fun i : S => f i ) by simpa [ Set.range ] using hf ) ⟨ a, ha ⟩;
  · have _ : Nonempty S := .map (fun (x : (S ∩ T : Set _)) ↦ ⟨x, x.2.1⟩) ‹_›
    apply le_csInf (Set.range_nonempty _)
    rintro i ⟨b, rfl⟩
    by_cases hiT : b.1 ∈ T
    · refine' le_trans ( inf_le_left ) _;
      refine' csInf_le _ _;
      · exact ⟨ hf.choose, Set.forall_mem_range.2 fun i => hf.choose_spec ⟨ i, i.2.1, rfl ⟩ ⟩;
      · aesop
    · refine' le_trans ( inf_le_right ) _;
      refine' csInf_le _ _
      · exact ⟨ hf.choose, Set.forall_mem_range.2 fun x => hf.choose_spec ⟨ x, by aesop ⟩ ⟩
      · aesop

end ciSup

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
    rcases em ( x ∈ s ) with hx' | hx'
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

theorem BddAbove.range_inf_of_image2 {M N α : Type*} {f : M → N → α} [ConditionallyCompleteLinearOrder α]
  {S : Set M} {T : Set N} (h_bddA : BddAbove (Set.image2 f S T)) (h_bddB : BddBelow (Set.image2 f S T)) :
    BddAbove (Set.range fun y : T ↦ ⨅ x : S, f x y) := by
  rcases isEmpty_or_nonempty T with hT | hT
  · aesop
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [Set.range, iInf]
  rw [← Set.nonempty_coe_sort, nonempty_subtype] at hS
  rcases hS with ⟨x, hx⟩
  choose z hz using h_bddA
  choose w hw using h_bddB
  have h_inf_le_M : ∀ y ∈ T, ⨅ x : S, f x y ≤ z := by
    intro y hy
    apply (ciInf_le ⟨_, Set.forall_mem_range.2 (hw <| Set.mem_image2_of_mem ·.2 hy)⟩ ⟨x, hx⟩).trans
    exact hz (Set.mem_image2_of_mem hx hy)
  exact ⟨_, Set.forall_mem_range.2 (h_inf_le_M _ ·.2)⟩

theorem BddBelow.range_sup_of_image2 {M N α : Type*} {f : M → N → α} [ConditionallyCompleteLinearOrder α]
  {S : Set M} {T : Set N} (h_bddA : BddAbove (Set.image2 f S T)) (h_bddB : BddBelow (Set.image2 f S T)) :
      BddBelow (Set.range fun y : T ↦ ⨆ x : S, f x y) :=
  BddAbove.range_inf_of_image2 (α := αᵒᵈ) h_bddB h_bddA

theorem ciInf_le_ciInf_of_subset {α β : Type*} [ConditionallyCompleteLattice α]
  {f : β → α} {s t : Set β} (hs : s.Nonempty) (hf : BddBelow (f '' t)) (hst : s ⊆ t) :
    ⨅ x : t, f x ≤ ⨅ x : s, f x := by
  have h_lower_bound : ∀ y ∈ s, ⨅ x : t, f x ≤ f y := by
    intro y hy
    obtain ⟨w_1, ⟨left_1, right_1⟩⟩ : f y ∈ f '' t := by
      use y, hst hy
    exact le_trans ( ciInf_le (by simpa [ Set.range ] using hf ) ⟨ w_1, left_1 ⟩ ) ( by simp[right_1] );
  apply le_csInf
  · exact ⟨_, ⟨⟨_, hs.choose_spec⟩, rfl⟩⟩;
  · aesop

theorem LowerSemicontinuousOn.dite_top {α β : Type*} [TopologicalSpace α] [Preorder β] [OrderTop β]
  {s : Set α} (p : α → Prop) [DecidablePred p] {f : (a : α) → p a → β}
  (hf : LowerSemicontinuousOn (fun x : Subtype p ↦ f x.val x.prop) {x | x.val ∈ s})
  (h_relatively_closed : ∃ U : Set α, IsClosed U ∧ s ∩ U = s ∩ setOf p) :
    LowerSemicontinuousOn (fun x ↦ dite (p x) (f x) (fun _ ↦ ⊤)) s := by
  rcases h_relatively_closed with ⟨u, ⟨hu, hsu⟩⟩
  simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_right_iff] at hsu
  intro x hx y hy
  dsimp at hy
  split_ifs at hy with h
  · specialize hf ⟨x, h⟩ hx y hy
    rw [ eventually_nhdsWithin_iff ] at hf ⊢
    rw [ nhds_subtype_eq_comap, Filter.eventually_comap ] at hf;
    filter_upwards [hf]
    simp only [Subtype.forall]
    grind [lt_top_of_lt]
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hu.isOpen_compl.mem_nhds (show x ∉ u by grind))]
    intros
    simp_all only [Set.mem_compl_iff, ↓reduceDIte]

theorem LowerSemicontinuousOn.comp_continuousOn {α β γ : Type*}
  [TopologicalSpace α] [TopologicalSpace β] [Preorder γ] {f : α → β} {s : Set α} {g : β → γ} {t : Set β}
  (hg : LowerSemicontinuousOn g t) (hf : ContinuousOn f s) (h : Set.MapsTo f s t) :
    LowerSemicontinuousOn (g ∘ f) s := by
  intro x hx y hy
  have h_neighborhood : ∃ U ∈ nhds (f x), ∀ z ∈ U ∩ t, y < g z := by
    have := hg ( f x ) ( h hx ) y hy
    simp_all only [Function.comp_apply, Set.mem_inter_iff, and_imp]
    rw [ eventually_nhdsWithin_iff ] at this
    aesop
  obtain ⟨U, hU_nhds, hU⟩ : ∃ U ∈ nhds (f x), ∀ z ∈ U ∩ t, y < g z := h_neighborhood
  have h_final : ∀ᶠ x' in nhdsWithin x s, f x' ∈ U ∧ f x' ∈ t := by
    filter_upwards [ hf x hx hU_nhds, self_mem_nhdsWithin ] with x' hx' hx'' using ⟨ hx', h hx'' ⟩;
  exact h_final.mono fun x' hx' => hU _ hx'

theorem UpperSemicontinuousOn.comp_continuousOn {α β γ : Type*}
  [TopologicalSpace α] [TopologicalSpace β] [Preorder γ] {f : α → β} {s : Set α} {g : β → γ} {t : Set β}
  (hg : UpperSemicontinuousOn g t) (hf : ContinuousOn f s) (h : Set.MapsTo f s t) :
    UpperSemicontinuousOn (g ∘ f) s :=
  LowerSemicontinuousOn.comp_continuousOn (γ := γᵒᵈ) hg hf h

theorem LowerSemicontinuousOn.ite_top {α β : Type*} [TopologicalSpace α] [Preorder β] [OrderTop β]
  {s : Set α} (p : α → Prop) [DecidablePred p] {f : (a : α) → β} (hf : LowerSemicontinuousOn f (s ∩ setOf p))
  (h_relatively_closed : ∃ U : Set α, IsClosed U ∧ s ∩ U = s ∩ setOf p) :
    LowerSemicontinuousOn (fun x ↦ ite (p x) (f x) ⊤) s :=
  dite_top p (hf.comp_continuousOn (by fun_prop) (by intro; simp)) h_relatively_closed

theorem LeftOrdContinuous.comp_lowerSemicontinuousOn_strong_assumptions {α γ δ : Type*}
  [TopologicalSpace α] [LinearOrder γ] [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
  [TopologicalSpace γ] [OrderTopology γ] [DenselyOrdered γ] [DenselyOrdered δ]
  {s : Set α} {g : γ → δ} {f : α → γ} (hg : LeftOrdContinuous g) (hf : LowerSemicontinuousOn f s) (hg2 : Monotone g) :
    LowerSemicontinuousOn (g ∘ f) s := by
  intros x hx y hy
  have hU : ∃ U ∈ nhds x, ∀ z ∈ U ∩ s, g (f z) > y := by
    simp_all only [Set.mem_inter_iff, gt_iff_lt, and_imp]
    obtain ⟨z, hz1, hz2⟩ : ∃ z, y < g z ∧ z < f x := by
      obtain ⟨z, hz⟩ : ∃ z, z < f x ∧ y < g z := by
        by_contra h_contra
        simp only [not_exists, not_and, not_lt] at h_contra
        have h_exists_z : ∃ z, z < f x ∧ g z > y := by
          have h_lub : IsLUB (Set.Iio (f x)) (f x) := by
            exact isLUB_Iio
          have := hg h_lub;
          have := this.exists_between hy
          simp_all only [Set.mem_image, Set.mem_Iio, exists_exists_and_eq_and, gt_iff_lt]
          grind
        exact h_exists_z.choose_spec.2.not_ge ( h_contra _ h_exists_z.choose_spec.1 );
      aesop
    specialize hf x hx z hz2
    rw [ eventually_nhdsWithin_iff ] at hf
    exact ⟨_, hf, fun _ hx hx' ↦ hz1.trans_le (hg2 (hx hx').le)⟩
  simp only [Set.mem_inter_iff, and_imp] at hU
  obtain ⟨w, ⟨left, right⟩⟩ := hU
  exact Filter.eventually_inf_principal.2 (Filter.mem_of_superset left right)

theorem UpperSemicontinuousOn.frequently_lt_of_tendsto {α β γ : Type*} [TopologicalSpace β] [Preorder γ]
  {f : β → γ} {T : Set β} (hf : UpperSemicontinuousOn f T) {c : γ} {zs : α → β} {z : β}
  {l : Filter α} [l.NeBot] (hzs : l.Tendsto zs (nhds z)) (hx₂ : f z < c) (hzI : ∀ a, zs a ∈ T) (hzT : z ∈ T) :
    ∀ᶠ a in l, f (zs a) < c := by
  have h : ∀ᶠ n in l, zs n ∈ {y ∈ T | f y < c} := by
    filter_upwards [hzs.eventually (eventually_nhdsWithin_iff.mp ((hf z hzT) c hx₂))] with n hn
      using ⟨hzI n, hn (hzI n)⟩
  simp_all

theorem Finset.ciInf_insert {α β : Type*} [DecidableEq α] [ConditionallyCompleteLattice β]
  (t : Finset α) (ht : t.Nonempty) (x : α) (f : α → β) :
    ⨅ (a : (insert x t : _)), f a = f x ⊓ ⨅ (a : t), f a := by
  apply le_antisymm
  · apply le_inf
    · apply csInf_le <;> aesop
    apply le_csInf
    · exact ⟨_, ⟨⟨ht.choose, ht.choose_spec ⟩, rfl⟩⟩
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    exact csInf_le (Finite.bddBelow_range _) ⟨⟨a, Finset.mem_insert_of_mem ha⟩, rfl⟩
  · apply le_csInf
    · exact ⟨_, ⟨⟨x, Finset.mem_insert_self _ _⟩, rfl⟩⟩
    simp only [Set.mem_range, Subtype.exists, mem_insert, exists_prop, exists_eq_or_imp]
    rintro b (rfl | ⟨_, ⟨_, rfl⟩⟩)
    · exact inf_le_left
    apply inf_le_right.trans
    apply csInf_le (Set.finite_range _).bddBelow
    aesop

theorem Finset.ciSup_insert {α β : Type*} [DecidableEq α] [ConditionallyCompleteLattice β]
  (t : Finset α) (ht : t.Nonempty) (x : α) (f : α → β) :
    ⨆ (a : (insert x t : _)), f a = f x ⊔ ⨆ (a : t), f a :=
  t.ciInf_insert (β := βᵒᵈ) ht x f

section sion_minimax
/-!
Following https://projecteuclid.org/journals/kodai-mathematical-journal/volume-11/issue-1/Elementary-proof-for-Sions-minimax-theorem/10.2996/kmj/1138038812.full, with some corrections. There are two errors in Lemma 2 and the main theorem: an incorrect step that
`(∀ x, a < f x) → (a < ⨅ x, f x)`. This is repaired by taking an extra `exists_between` to get `a < b < ⨅ ...`, concluding that
`(∀ x, b < f x) → (b ≤ ⨅ x, f x)` and so `(a < ⨅ x, f x)`.
-/

variable  {M : Type*} [NormedAddCommGroup M]
  {N : Type*}
  {f : M → N → ℝ} {S : Set M} {T : Set N}
  (hfc₂ : ∀ y, y ∈ T → LowerSemicontinuousOn (f · y) S)
  (hS₁ : IsCompact S) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)

include hfc₂ hS₁ hS₃ in
private theorem sion_exists_min_lowerSemi (a : ℝ) (hc : ∀ y₀ : T, ⨅ (x : S), f (↑x) y₀ ≤ a) (z : N) (hzT : z ∈ T) :
    ∃ x ∈ S, f x z ≤ a := by
  let _ := hS₃.to_subtype
  contrapose! hc
  use ⟨z, hzT⟩
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

variable [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M]
variable [NormedAddCommGroup N] [Module ℝ N] [ContinuousAdd N] [ContinuousSMul ℝ N]
variable
  (hfc₁ : ∀ x, x ∈ S → UpperSemicontinuousOn (f x) T)
  (hfq₂ : ∀ y, y ∈ T → QuasiconvexOn ℝ S (f · y))
  (hfq₁ : ∀ x, x ∈ S → QuasiconcaveOn ℝ T (f x))
  (hT₂ : Convex ℝ T) (hS₂ : Convex ℝ S)

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hT₂ hS₃ in
private lemma sion_exists_min_2 (y₁ y₂ : N) (hy₁ : y₁ ∈ T) (hy₂ : y₂ ∈ T)
    (a : ℝ) (ha : a < ⨅ x : S, (max (f x y₁) (f x y₂)))
    : ∃ y₀ : T, a < ⨅ x : S, f x y₀ := by
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
  have hC'zAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C' z ⊆ A ∪ B := by
    --TODO: On newer Mathlib this is just `grind [inf_le_iff, le_trans]`
    intro; simp [C', A, B]; grind [inf_le_iff, le_trans]
  have hC'z (z) (hz : z ∈ segment ℝ y₁ y₂) : Convex ℝ (C' z) :=
    hfq₂ z (hT₂.segment_subset hy₁ hy₂ hz) β
  have hC'zAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C' z ⊆ A ∨ C' z ⊆ B := by
    specialize hC_subset_C' z
    specialize hC'z z hz
    have hC' : IsPreconnected (C' z) :=
      ((hC'z).isConnected ((hC_nonempty z hz).mono hC_subset_C')).isPreconnected
    rw [isPreconnected_iff_subset_of_disjoint_closed] at hC'
    exact hC' A B hA_closed hB_closed (hC'zAB z hz) (by simp [hAB])
  have hCzAB (z) (hz : z ∈ segment ℝ y₁ y₂) : C z ⊆ A ∨ C z ⊆ B := by
    specialize hC_subset_C' z
    rcases hC'zAB z hz with h | h
    · exact .inl (hC_subset_C'.trans h)
    · exact .inr (hC_subset_C'.trans h)
  have h_not_CzAB (z) (hz : z ∈ segment ℝ y₁ y₂) : ¬(C z ⊆ A ∧ C z ⊆ B) := by
    rintro ⟨h₁, h₂⟩
    specialize hC_nonempty z hz
    replace h₁ := Set.mem_of_mem_of_subset hC_nonempty.some_mem h₁
    replace h₂ := Set.mem_of_mem_of_subset hC_nonempty.some_mem h₂
    simpa [hAB] using Set.mem_inter h₁ h₂
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
    apply IsSeqClosed.isClosed
    intro zs z hzI hzs
    simp only [Set.mem_setOf_eq, I, C] at hzI
    replace ⟨hzI, hzI2⟩ := And.intro (hzI · |>.left) (hzI · |>.right)
    have hz_mem : z ∈ segment ℝ y₁ y₂ :=
      have cloL : IsClosed (segment ℝ y₁ y₂) := by
        rw [← closure_openSegment]
        exact isClosed_closure
      cloL.isSeqClosed hzI hzs
    let x := (hC_nonempty z hz_mem).some
    have hx : x ∈ C z := (hC_nonempty z hz_mem).some_mem
    suffices hn : ∃ n, x ∈ C' (zs n) by
      use hz_mem
      rcases hn with ⟨n, hn⟩
      have hCzn : C (zs n) ⊆ A := hzI2 n
      replace hCzn : C' (zs n) ⊆ A := by
        refine (hC'zAB (zs n) (hzI n)).resolve_right ?_
        intro hC'B
        exact (h_not_CzAB (zs n) (hzI n)) ⟨hCzn, (hC_subset_C' _).trans hC'B⟩
      have hxA : x ∈ A := Set.mem_of_mem_of_subset hn hCzn
      refine (hCzAB z hz_mem).resolve_right ?_
      intro hCB
      have hAC : A ∩ C z ⊆ A ∩ B := by apply Set.inter_subset_inter_right _ hCB
      rw [hAB, Set.subset_empty_iff, Set.ext_iff] at hAC
      revert hAC
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, imp_false, not_forall, not_not]
      exact ⟨x, hxA, hx⟩
    suffices hn : ∃ n, f x (zs n) < β by
      refine hn.imp fun n ↦ ?_
      simp +contextual [C', le_of_lt, hx.left]
    simp only [Set.mem_setOf_eq, C] at hx
    rcases hx with ⟨hx₁, hx₂⟩
    specialize hfc₁ x hx₁
    replace hx₂ := hx₂.trans_lt hβ₁
    replace hzI (n) := hT₂.segment_subset hy₁ hy₂ (hzI n)
    replace hz_mem := hT₂.segment_subset hy₁ hy₂ hz_mem
    exact (hfc₁.frequently_lt_of_tendsto hzs hx₂ hzI hz_mem).exists
  have hJ : IsClosed J := by
    apply IsSeqClosed.isClosed
    intro zs z hzI hzs
    simp only [Set.mem_setOf_eq, J, C] at hzI
    replace ⟨hzI, hzI2⟩ := And.intro (hzI · |>.left) (hzI · |>.right)
    have hz_mem : z ∈ segment ℝ y₁ y₂ :=
      have cloL : IsClosed (segment ℝ y₁ y₂) := by
        rw [← closure_openSegment]
        exact isClosed_closure
      cloL.isSeqClosed hzI hzs
    let x := (hC_nonempty z hz_mem).some
    have hx : x ∈ C z := (hC_nonempty z hz_mem).some_mem
    suffices hn : ∃ n, x ∈ C' (zs n) by
      use hz_mem
      rcases hn with ⟨n, hn⟩
      have hCzn : C (zs n) ⊆ B := hzI2 n
      replace hCzn : C' (zs n) ⊆ B := by
        refine (hC'zAB (zs n) (hzI n)).resolve_left ?_
        intro hC'B
        exact (h_not_CzAB (zs n) (hzI n)) ⟨(hC_subset_C' _).trans hC'B, hCzn⟩
      have hxA : x ∈ B := Set.mem_of_mem_of_subset hn hCzn
      refine (hCzAB z hz_mem).resolve_left ?_
      intro hCB
      have hAC : C z ∩ B ⊆ A ∩ B := by apply Set.inter_subset_inter_left _ hCB
      rw [hAB, Set.subset_empty_iff, Set.ext_iff] at hAC
      revert hAC
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, imp_false, not_forall, not_not]
      exact ⟨x, hx, hxA⟩
    suffices hn : ∃ n, f x (zs n) < β by
      refine hn.imp fun n ↦ ?_
      simp +contextual [C', le_of_lt, hx.left]
    simp only [Set.mem_setOf_eq, C] at hx
    rcases hx with ⟨hx₁, hx₂⟩
    specialize hfc₁ x hx₁
    replace hx₂ := hx₂.trans_lt hβ₁
    replace hzI (n) := hT₂.segment_subset hy₁ hy₂ (hzI n)
    replace hz_mem := hT₂.segment_subset hy₁ hy₂ hz_mem
    exact (hfc₁.frequently_lt_of_tendsto hzs hx₂ hzI hz_mem).exists
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

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ in
private lemma sion_exists_min_fin
  (h_bddA : BddAbove (Set.image2 f S T)) (h_bddB : BddBelow (Set.image2 f S T))
  (ys : Finset N) (hys_n : ys.Nonempty) (hys : (ys : Set N) ⊆ T)
  (a : ℝ) (ha : a < ⨅ x : S, ⨆ yi : ys, f x yi)
    : ∃ y₀ : T, a < ⨅ x : S, f x y₀ := by
  induction hys_n using Finset.Nonempty.cons_induction generalizing S
  case singleton x =>
    simp at ha hys
    use ⟨x, hys⟩
  case cons yₙ t hxt htn ih =>
    classical rw [Finset.cons_eq_insert] at hys ha
    simp [Set.insert_subset_iff] at hys
    rcases hys with ⟨hyₙ, ht⟩
    let _ := hS₃.to_subtype
    obtain ⟨b, hab, hb⟩ := exists_between ha
    let S' := {z : M | z ∈ S ∧ f z yₙ ≤ b}
    have hS'_sub : S' ⊆ S := Set.sep_subset ..
    rcases S'.eq_empty_or_nonempty with hS'_e | hS'_n
    · simp [S'] at hS'_e
      use ⟨yₙ, hyₙ⟩
      rw [lt_ciInf_iff]; swap
      · --BddBelow (Set.range fun x : S => f (↑x) yₙ)
        convert (hfc₂ yₙ hyₙ).bddBelow hS₁
        ext; simp
      use b, hab
      intro i
      exact (hS'_e i i.2).le
    let _ := hS'_n.to_subtype
    have hS'₁ : IsCompact S' := by
      apply hS₁.of_isClosed_subset ?_ hS'_sub
      specialize hfc₂ yₙ
      rw [lowerSemicontinuousOn_iff_isClosed_epigraph hS₁.isClosed] at hfc₂
      have ha_closed : IsClosed {p : M × ℝ | p.2 = b} := by
        convert isClosed_univ.prod (isClosed_singleton (x := b))
        simp [Set.ext_iff]
      suffices Continuous (fun (z : M) ↦ (z, b) : M → M × ℝ) by
        convert ((hfc₂ hyₙ).inter ha_closed).preimage this
        simp [S']
      fun_prop
    have hS'₂ : Convex ℝ S' := hfq₂ _ hyₙ _
    have ha' : a < ⨅ x : S', ⨆ yi : t, f x yi := by
      apply lt_of_lt_of_le hab (hb.le.trans ?_)
      classical
      trans (⨅ x : S', ⨆ yi : { x // x ∈ (Insert.insert yₙ t : Finset N)}, f ↑x ↑yi)
      · apply ciInf_le_ciInf_of_subset (f := fun x ↦ ⨆ yi : { x // x ∈ (Insert.insert yₙ t : Finset N)}, f ↑x ↑yi)
        · exact hS'_n
        · --BddBelow ((fun x => ⨆ yi, f x ↑yi) '' S)
          convert BddBelow.range_sup_of_image2 (T := S) (S := { x | x ∈ insert yₙ t }) (f := flip f)
            (by apply h_bddA.mono; simp [flip]; grind) (by apply h_bddB.mono; simp [flip]; grind)
          simp [Set.ext_iff, flip]
        · exact hS'_sub
      · gcongr with x
        · --BddBelow (Set.range fun x : S' => ⨆ yi, f ↑x ↑yi)
          exact BddBelow.range_sup_of_image2 (T := S') (S := { x | x ∈ insert yₙ t }) (f := flip f)
            (by apply h_bddA.mono; simp [flip]; grind) (by apply h_bddB.mono; simp [flip]; grind)
        rw [t.ciSup_insert htn]
        simp only [sup_le_iff, le_refl, and_true]
        conv at hb => enter [2, 1, x]; rw [t.ciSup_insert htn]
        contrapose! hb
        refine ciInf_le_of_le ?_ ⟨x.val, hS'_sub x.2⟩ ?_
        · --BddBelow (Set.range fun x => max (f (↑x) yₙ) (⨆ a, f ↑x ↑a))
          apply BddBelow.range_mono (h := fun x ↦ le_max_left _ _)
          convert (hfc₂ yₙ hyₙ).bddBelow hS₁
          ext; simp
        · have := x.2.2
          simp [this, hb.le.trans this]
    specialize @ih S'
      (hfc₂ · · |>.mono hS'_sub) hS'₁ hS'_n
      (hfc₁ · <| hS'_sub ·) (hfq₂ · · |>.subset hS'_sub hS'₂)
      (hfq₁ · <| hS'_sub ·) hS'₂
      (h_bddA.mono <| Set.image2_subset_right hS'_sub)
      (h_bddB.mono <| Set.image2_subset_right hS'_sub) ht ha'
    clear ha'
    obtain ⟨y₀', hy₀'⟩ := ih
    refine (sion_exists_min_2 hfc₂ hS₁ hS₃ hfc₁ hfq₂ hfq₁
      hT₂ y₀' yₙ y₀'.2 hyₙ a ?_)
    by_cases hS'eq : S' = S
    · rw [hS'eq] at hy₀'
      apply hy₀'.trans_le
      gcongr
      · --BddBelow (Set.range fun x : S => f (↑x) y₀')
        convert (hfc₂ y₀' y₀'.2).bddBelow hS₁
        ext; simp
      exact le_sup_left
    have hS_diff_ne : (S \ S').Nonempty :=
      Set.nonempty_of_ssubset (hS'_sub.ssubset_of_ne hS'eq)
    apply Set.Nonempty.to_subtype at hS_diff_ne

    have h_non_inter : Nonempty ↑(S ∩ S') := by
      rwa [Set.inter_eq_self_of_subset_right hS'_sub]
    rw [ciInf_eq_min_cInf_inter_diff (f := fun x ↦ max (f x y₀') (f x yₙ)) S S']; swap
    · --BddAbove ((fun x => max (f x y₀') (f x yₙ)) '' S)
      apply h_bddB.mono
      rintro _ ⟨x, hx, rfl⟩
      use x, hx
      -- TODO: On a newer mathlib this line is just `grind`
      rcases max_cases (f x ↑y₀') (f x yₙ) <;> grind
    clear h_non_inter
    rw [lt_inf_iff]
    constructor
    · rw [Set.inter_eq_self_of_subset_right hS'_sub]
      apply hy₀'.trans_le
      gcongr
      · --BddBelow (Set.range fun x : S' => f (↑x) y₀')
        apply h_bddB.mono
        rintro _ ⟨x, rfl⟩
        use x, hS'_sub x.2, y₀', y₀'.2
      exact le_sup_left
    · have hS'_compl : S \ S' = { z | z ∈ S ∧ b < f z yₙ } := by
        ext
        simp [S']
      rw [hS'_compl] at hS_diff_ne ⊢
      rw [Set.coe_setOf] at hS_diff_ne
      refine hab.trans_le ?_
      simp
      apply le_ciInf
      intro x
      have := x.2.2.le
      exact le_sup_of_le_right this

include hfc₁ hfq₁ hfc₂ hfq₂ hS₁ hS₂ hT₂ hS₃ hT₃ in
/-- **Sion's Minimax theorem**. Because of `ciSup` and `ciInf` junk values when f isn't
bounded, we need to assume that it's bounded above and below. -/
theorem sion_minimax
  (h_bddA : BddAbove (Set.image2 f S T))
  (h_bddB : BddBelow (Set.image2 f S T))
    : ⨅ x : S, ⨆ y : T, f x y = ⨆ y : T, ⨅ x : S, f x y := by
  have _ := hS₁.isClosed
  have _ := hS₃.to_subtype
  have _ := hT₃.to_subtype
  have h_bdd_0 (i : T) : BddBelow (Set.range fun j : S ↦ f j i) := by
    --This one actually doesn't require h_bddB, we can just prove it from compactness + semicontinuity
    convert (hfc₂ i i.2).bddBelow hS₁
    ext; simp
  have h_bdd_1 (j : S) : BddAbove (Set.range fun (x : T) => f j x) :=
    h_bddA.mono (T.range_restrict (f j) ▸ Set.image_subset_image2_right j.coe_prop)
  have h_bdd_2 : BddAbove (Set.range fun y : T ↦ ⨅ x : S, f x y) :=
    h_bddA.range_inf_of_image2 h_bddB
  have h_bdd_3 : BddBelow (Set.range fun x : S ↦ ⨆ y : T, f x y) :=
    BddBelow.range_sup_of_image2 (f := flip f) (by simpa) (by simpa)
  apply le_antisymm; swap
  · exact ciSup_ciInf_le_ciInf_ciSup _ h_bdd_1 h_bdd_0
  by_contra! h
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h; clear h
  obtain ⟨b, hb₁, hb₂⟩ := exists_between ha₂; clear ha₂
  revert ha₁
  rw [imp_false, not_lt]
  have := hS₁.elim_finite_subfamily_closed (fun (y : T) ↦ { x | x ∈ S ∧ f x y ≤ b}) ?_ ?_
  · rcases this with ⟨u, hu⟩
    have hu' : u.Nonempty := by
      grind [Finset.not_nonempty_iff_eq_empty, Set.iInter_univ,
        Set.inter_univ, Set.not_nonempty_empty]
    have hau : a < ⨅ x : S, ⨆ yi : u.map ⟨_, Subtype.val_injective⟩, f ↑x ↑yi := by
      simp +contextual only [Set.iInter_coe_set, Set.ext_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, true_and, not_forall,
        not_le] at hu
      rw [lt_ciInf_iff]; swap
      · --BddBelow (Set.range fun x => ⨆ yi : Finset.map ⋯, f ↑x ↑yi)
        exact BddBelow.range_sup_of_image2 (T := S) (S := u.map ⟨_, Subtype.val_injective⟩)
          (f := flip f) (by apply h_bddA.mono; simp [flip]; grind) (by apply h_bddB.mono; simp [flip]; grind)
      use b, hb₁
      intro i
      specialize hu i i.2
      rcases hu with ⟨c, hc₁, hc₂, hc₃⟩
      refine le_ciSup_of_le ?_ ⟨c, by simpa using ⟨hc₁, hc₂⟩⟩ hc₃.le
      --BddAbove (Set.range fun yi : Finset.map ⋯ => f ↑i ↑yi)
      apply h_bddA.mono
      simp [Set.range, Set.image2]; grind
    obtain ⟨y₀, hy₀⟩ := sion_exists_min_fin hfc₂ hS₁ hS₃ hfc₁ hfq₂ hfq₁ hT₂ hS₂
      h_bddA h_bddB (u.map ⟨_, Subtype.val_injective⟩) (by simpa) (by simp) a hau
    exact hy₀.le.trans (le_ciSup h_bdd_2 y₀)
  · intro i
    specialize hfc₂ i i.2
    rw [lowerSemicontinuousOn_iff_isClosed_preimage] at hfc₂
    exact hfc₂ b
  · convert Set.inter_empty _
    by_contra hu
    simp? [Set.iInter_eq_empty_iff] says simp only [
      Set.iInter_coe_set, Set.iInter_eq_empty_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Classical.not_imp, not_and, not_le, not_forall, not_exists, not_lt] at hu
    obtain ⟨x, hx⟩ := hu
    apply hb₂.not_ge
    apply (ciInf_le h_bdd_3 ⟨x, hx _ hT₃.some_mem |>.1⟩).trans _
    apply ciSup_le (hx _ ·.2 |>.2)
