import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Peel
import Mathlib.Topology.Compactness.PseudometrizableLindelof
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Nat

open scoped NNReal
open scoped ENNReal
open Topology

/-!
Several 'bespoke' facts about limsup and liminf on ENNReal / NNReal needed in SteinsLemma
-/

/-
There exists a strictly increasing sequence of indices $n_k$ such that $f(1/(k+1), n_k) \le y + 1/(k+1)$.
-/
lemma exists_strictMono_seq_le (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞) (hf : ∀ x > 0, Filter.atTop.liminf (f x) ≤ y) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k : ℕ, f ((k : ℝ≥0) + 1)⁻¹ (n k) ≤ (y : ℝ≥0∞) + ((k : ℝ≥0) + 1)⁻¹ := by
  -- Since the liminf is ≤ y, for any ε > 0 and index n, there frequently exists an m > n satisfying the bound.
  have h_freq (k n : ℕ) : ∃ m > n, f ((k + 1 : ℝ≥0)⁻¹) m ≤ y + (k + 1 : ℝ≥0)⁻¹ := by
    specialize hf ((k + 1 : ℝ≥0)⁻¹) (by positivity)
    rw [Filter.liminf_eq] at hf
    simp only [Filter.eventually_atTop, ge_iff_le, sSup_le_iff, Set.mem_setOf_eq, forall_exists_index] at hf
    contrapose! hf
    refine ⟨_, n + 1, fun m hm ↦ (hf m hm).le, ENNReal.lt_add_right (by norm_num) (by norm_num)⟩
  refine ⟨fun k ↦ k.recOn (Classical.choose (h_freq 0 0))
    (fun i ih ↦ Nat.find (h_freq (i + 1) ih)), ?_, ?_⟩
  · exact strictMono_nat_of_lt_succ fun k ↦ (Nat.find_spec (h_freq (k + 1) _)).1
  · rintro (_ | k)
    · exact (Classical.choose_spec (h_freq 0 _)).2
    · exact (Nat.find_spec (h_freq (k + 1) _)).2
/-
There exists a strictly increasing sequence M such that for all k, and all n ≥ M k, f (1/(k+1)) n is close to y.
-/
lemma exists_seq_bound (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞) (hf : ∀ x > 0, Filter.atTop.limsup (f x) ≤ y) :
    ∃ M : ℕ → ℕ, StrictMono M ∧ ∀ k, ∀ n ≥ M k, f ((k + 1 : ℝ≥0)⁻¹) n ≤ y + (k + 1 : ℝ≥0∞)⁻¹ := by
  have h_M (k : ℕ) : ∃ M_k, ∀ n ≥ M_k, f (k + 1)⁻¹ n ≤ y + (k + 1 : ℝ≥0∞)⁻¹ := by
    specialize hf (k + 1)⁻¹ (by positivity)
    contrapose! hf
    refine lt_of_lt_of_le (b := ?_) ?_ (le_csInf ⟨⊤, by simp⟩ ?_)
    · exact y + (k + 1 : ℝ≥0∞)⁻¹
    · exact ENNReal.lt_add_right (by norm_num) (by norm_num)
    · intro b hb
      simp only [Filter.eventually_map, Filter.eventually_atTop, Set.mem_setOf_eq] at hb
      obtain ⟨w, h⟩ := hb
      obtain ⟨_, hw_left, hw_right⟩ := hf w
      grw [hw_right]
      exact h _ hw_left
  choose M hM using h_M
  use Nat.rec (M 0) fun k ih ↦ M (k + 1) ⊔ (ih + 1)
  constructor
  · apply strictMono_nat_of_lt_succ
    exact fun _ ↦ lt_sup_of_lt_right (lt_add_one _)
  · intro k n hn
    apply hM
    grw [hn]
    cases k
    · rfl
    · apply le_max_left

/- (∀ x, x > 0 → liminf (n ↦ f x n) ≤ y) →
  ∃ g : ℕ → ℝ, (∀ x, g x > 0) ∧ (liminf g = 0) ∧ (liminf (n ↦ f (g n) n) ≤ y) -/
lemma exists_liminf_zero_of_forall_liminf_le (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞)
  (hf : ∀ x > 0, Filter.atTop.liminf (f x) ≤ y) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ Filter.atTop.Tendsto g (𝓝 0) ∧
      Filter.atTop.liminf (fun n ↦ f (g n) n) ≤ y := by
  conv at hf =>
    enter [x, h]
    exact propext (Filter.liminf_le_iff (by isBoundedDefault) (by isBoundedDefault))
  replace hf x hx z hz := Filter.exists_seq_forall_of_frequently (hf x hx z hz)
  choose! c hc hc₂ using hf
  classical
  by_contra h_contra;
  -- By definition of negation, if $\neg P$ holds, then $P$ does not hold.
  push_neg at h_contra;
  -- Apply `exists_strictMono_seq_le` to obtain a strictly increasing sequence `n_k` such that `f (1/(k+1)) (n_k) ≤ y + 1/(k+1)`.
  obtain ⟨n, hn_mono, hn_le⟩ : ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k : ℕ, f ((k : ℝ≥0) + 1)⁻¹ (n k) ≤ (y : ℝ≥0∞) + ((k : ℝ≥0) + 1)⁻¹ := by
    -- Apply `exists_strictMono_seq_le` to obtain a strictly increasing sequence `n_k` such that `f (1/(k+1)) (n_k) ≤ y + 1/(k+1)` for all `k`.
    apply exists_strictMono_seq_le y f; intro x hx_pos; (
    refine' le_of_forall_gt_imp_ge_of_dense fun z hz => _;
    refine' csSup_le _ _ <;> norm_num;
    · exact ⟨ 0, ⟨ 0, fun _ _ => zero_le _ ⟩ ⟩;
    · intro b n hn; specialize hc x hx_pos z hz; have := hc.eventually_gt_atTop n
      simp_all only [gt_iff_lt, Filter.eventually_atTop, ge_iff_le]
      obtain ⟨w, h⟩ := this
      exact le_trans ( hn _ ( le_of_lt ( h _ le_rfl ) ) ) ( le_of_lt ( hc₂ _ hx_pos _ hz _ ) ));
  -- Define $g(m) = 1/(k(m)+1)$ where $k(m)$ is the index such that $n_{k(m)} \leq m < n_{k(m)+1}$.
  set g : ℕ → ℝ≥0 := fun m => (Nat.findGreatest (fun k => m ≥ n k) m + 1 : ℝ≥0)⁻¹;
  have hg_pos : ∀ m, g m > 0 := by
    exact fun m => by positivity;;
  have hg_tendsto_zero : Filter.Tendsto g Filter.atTop (𝓝 0) := by
    -- Since $n$ is strictly monotone, $Nat.findGreatest (fun k => m ≥ n k) m$ tends to infinity as $m$ tends to infinity.
    have h_find_greatest_inf : Filter.Tendsto (fun m => Nat.findGreatest (fun k => m ≥ n k) m) Filter.atTop Filter.atTop := by
      refine' Filter.tendsto_atTop_atTop.mpr fun x => _;
      use n x; intro a ha
      refine' Nat.le_findGreatest _ ha
      simp_all only [gt_iff_lt, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false, not_false_eq_true,
        ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one, ge_iff_le, inv_pos, add_pos_iff,
        Nat.cast_pos, Nat.findGreatest_pos, zero_lt_one, or_true, implies_true, g]
      exact le_trans ( hn_mono.id_le _ ) ha;
    rw [ tendsto_order ] at *
    simp_all only [gt_iff_lt, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one, ge_iff_le, inv_pos, add_pos_iff,
      Nat.cast_pos, Nat.findGreatest_pos, zero_lt_one, or_true, implies_true, not_lt_zero', Filter.eventually_atTop,
      not_isEmpty_of_nonempty, IsEmpty.forall_iff, IsEmpty.exists_iff, true_and, g]
    intro a' a
    exact Filter.eventually_atTop.mp ( h_find_greatest_inf.eventually_gt_atTop ⌈ ( a' : ℝ≥0 ) ⁻¹⌉₊ ) |> fun ⟨ M, hM ⟩ ↦ ⟨ M, fun m hm ↦ by simpa using inv_lt_of_inv_lt₀ a <| by exact lt_of_lt_of_le ( Nat.lt_of_ceil_lt <| hM m hm ) <| mod_cast Nat.le_succ _ ⟩;
  have hg_le : ∀ k, f (g (n k)) (n k) ≤ (y : ℝ≥0∞) + ((k : ℝ≥0) + 1)⁻¹ := by
    intro k
    specialize hn_le k
    simp_all only [gt_iff_lt, ge_iff_le, inv_pos, add_pos_iff, Nat.cast_pos, Nat.findGreatest_pos, zero_lt_one,
      or_true, implies_true, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one, g]
    rw [ show Nat.findGreatest ( fun k_1 => n k_1 ≤ n k ) ( n k ) = k from _ ]
    simp_all only
    rw [ Nat.findGreatest_eq_iff ]
    simp_all only [ne_eq, le_refl, implies_true, not_le, true_and]
    apply And.intro
    · exact hn_mono.id_le _;
    · intro n_1 a a_1
      exact hn_mono a;
  have hg_liminf : Filter.liminf (fun n => f (g n) n) Filter.atTop ≤ y := by
    refine' csSup_le _ _ <;> norm_num;
    · exact ⟨ 0, ⟨ 0, fun _ _ => zero_le _ ⟩ ⟩;
    · intro b x hx; contrapose! hx
      simp_all only [gt_iff_lt, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false, not_false_eq_true,
        ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one, ge_iff_le, inv_pos, add_pos_iff,
        Nat.cast_pos, Nat.findGreatest_pos, zero_lt_one, or_true, implies_true, g]
      -- Choose $k$ such that $y + 1/(k+1) < b$.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, y + ((k : ℝ≥0) + 1)⁻¹ < b := by
        rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hx with ⟨z, hz⟩
        simp_all only [ENNReal.coe_lt_coe, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false,
          not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one]
        obtain ⟨left, right⟩ := hz
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt ( show 0 < ( z : ℝ ) - y from sub_pos.mpr <| mod_cast left )
        use k
        norm_num at *;
        refine' lt_of_le_of_lt _ right;
        convert add_le_add_left ( ENNReal.ofReal_le_ofReal hk.le ) ( y : ℝ≥0∞ ) using 1 ; norm_num [ ENNReal.ofReal ];
        · norm_num [ Real.toNNReal_inv ];
        · rw [ ENNReal.ofReal_sub ] <;> norm_num [ left.le ];
      refine' ⟨ n ( Max.max x k ), _, _ ⟩
      · simp_all only [ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false, not_false_eq_true, ENNReal.coe_inv,
          ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one]
        exact le_trans ( le_max_left _ _ ) ( hn_mono.id_le _ );
      · simp_all only [ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false, not_false_eq_true, ENNReal.coe_inv,
          ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one]
        refine' lt_of_le_of_lt ( hg_le _ ) _;
        refine' lt_of_le_of_lt _ hk
        gcongr
        exact le_sup_right
  exact h_contra g hg_pos hg_tendsto_zero |> not_lt_of_ge hg_liminf;

/- Version of `exists_liminf_zero_of_forall_liminf_le` that lets you also require `g`
to have an upper bound. -/
lemma exists_liminf_zero_of_forall_liminf_le_with_UB (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞)
  {z : ℝ≥0} (hz : 0 < z)
  (hf : ∀ x, x > 0 → Filter.atTop.liminf (f x) ≤ y) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ (∀ x, g x < z) ∧ (Filter.atTop.Tendsto g (𝓝 0)) ∧
      (Filter.atTop.liminf (fun n ↦ f (g n) n) ≤ y) := by
  obtain ⟨g, hg₀, hg₁, hg₂⟩ := exists_liminf_zero_of_forall_liminf_le y (fun x n => f x n) hf;
  refine ⟨fun n => min (g n) (z / 2), by bound, by bound, ?_, ?_⟩
  · convert hg₁.min tendsto_const_nhds using 2
    simp
  · beta_reduce
    rwa [Filter.liminf_congr]
    have h := hg₁.eventually (gt_mem_nhds <| half_pos hz)
    peel h with h
    rw [min_eq_left h.le]

/- (∀ x, x > 0 → liminf (n ↦ f x n) ≤ y) →
  ∃ g : ℕ → ℝ, (∀ x, g x > 0) ∧ (liminf g = 0) ∧ (liminf (n ↦ f (g n) n) ≤ y) -/
lemma exists_limsup_zero_of_forall_limsup_le (y : ℝ≥0) (f : ℝ≥0 → ℕ → ℝ≥0∞)
  (hf : ∀ x, x > 0 → Filter.atTop.limsup (f x) ≤ y) :
    ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ (Filter.atTop.Tendsto g (𝓝 0)) ∧
      (Filter.atTop.limsup (fun n ↦ f (g n) n) ≤ y) := by
    -- Let's choose a sequence M such that for all k, and all n ≥ M k, f (1/(k+1)) n is close to y.
  obtain ⟨M, hM⟩ : ∃ M : ℕ → ℕ, StrictMono M ∧ ∀ k, ∀ n ≥ M k, f ((k + 1 : ℝ≥0)⁻¹) n ≤ y + (k + 1 : ℝ≥0∞)⁻¹ := by
    -- Apply the hypothesis `exists_seq_bound` to obtain the sequence $M$.
    apply exists_seq_bound y f hf;
  use fun n => 1 / ( Nat.findGreatest ( fun k => M k ≤ n ) n + 1 );
  refine ⟨?_, ?_, ?_⟩
  · aesop;
  · -- We'll use that Nat.findGreatest (fun k => M k ≤ n) n tends to infinity as n tends to infinity.
    have h_find_greatest : Filter.Tendsto (fun n => Nat.findGreatest (fun k => M k ≤ n) n) Filter.atTop Filter.atTop := by
      refine' Filter.tendsto_atTop_atTop.mpr fun k => _;
      use M k; intro a ha; refine' Nat.le_findGreatest _ ha
      simp_all only [gt_iff_lt, ge_iff_le]
      obtain ⟨left, right⟩ := hM
      exact le_trans ( left.id_le _ ) ha;
    rw [ tendsto_order ]
    simp_all only [gt_iff_lt, ge_iff_le, not_lt_zero', one_div, Filter.eventually_atTop, not_isEmpty_of_nonempty,
      IsEmpty.forall_iff, IsEmpty.exists_iff, implies_true, true_and]
    intro a' a
    obtain ⟨left, right⟩ := hM
    have := h_find_greatest.eventually_gt_atTop ⌈a'⁻¹⌉₊
    simp_all only [Filter.eventually_atTop, ge_iff_le]
    obtain ⟨w, h⟩ := this
    exact ⟨ w, fun n hn => inv_lt_of_inv_lt₀ a <| by exact lt_of_lt_of_le ( Nat.lt_of_ceil_lt <| h n hn ) <| mod_cast Nat.le_succ _ ⟩;
  · -- For any ε > 0, choose K such that 1/(K+1) < ε. For n ≥ M K, we have g n = 1/(k+1) with k ≥ K. Also n ≥ M k (since k is the smallest such that n < M (k+1)). Thus f (g n) n ≤ y + 1/(k+1) < y + ε.
    have h_eps : ∀ ε > 0, ∃ N, ∀ n ≥ N, f (1 / (Nat.findGreatest (fun k => M k ≤ n) n + 1)) n ≤ y + ε := by
      intro ε hε_pos
      obtain ⟨K, hK⟩ : ∃ K : ℕ, (K + 1 : ℝ≥0∞)⁻¹ < ε := by
        rcases ENNReal.exists_inv_nat_lt hε_pos.ne' with ⟨ K, hK ⟩
        use K
        simp_all only [gt_iff_lt, ge_iff_le]
        obtain ⟨left, right⟩ := hM
        exact lt_of_le_of_lt ( by gcongr ; norm_num ) hK;
      use M K;
      intros n hn
      have h_k_ge_K : Nat.findGreatest (fun k => M k ≤ n) n ≥ K := by
        refine' Nat.le_findGreatest _ hn
        simp_all only [gt_iff_lt, ge_iff_le]
        obtain ⟨left, right⟩ := hM
        exact le_trans ( left.id_le _ ) hn;
      have := hM.2 ( Nat.findGreatest ( fun k => M k ≤ n ) n ) n ?_
      · simp_all only [gt_iff_lt, ge_iff_le, one_div]
        obtain ⟨left, right⟩ := hM
        exact le_trans this ( add_le_add_left ( le_trans ( by gcongr ) hK.le ) _ );
      · simp_all only [gt_iff_lt, ge_iff_le]
        obtain ⟨left, right⟩ := hM
        have := Nat.findGreatest_eq_iff.mp ( by aesop : Nat.findGreatest ( fun k => M k ≤ n ) n = Nat.findGreatest ( fun k => M k ≤ n ) n )
        by_cases h : Nat.findGreatest ( fun k => M k ≤ n ) n = 0
        · simp_all
        · simp_all
    refine' le_of_forall_pos_le_add fun ε hε => _;
    refine' csInf_le _ _
    · aesop
    · aesop

/-
If x_k tends to L and g(n) = x_k for n in [T_k, T_{k+1}) where T is strictly increasing, then g(n) tends to L.
-/
lemma tendsto_of_block_sequence {α : Type*} [TopologicalSpace α] {x : ℕ → α} {T : ℕ → ℕ}
    (hT : StrictMono T) {L : α} (hx : Filter.atTop.Tendsto x (𝓝 L)) (g : ℕ → α) (hg : ∀ k, ∀ n ∈ Set.Ico (T k) (T (k + 1)), g n = x k) :
      Filter.atTop.Tendsto g (𝓝 L) := by
  rw [Filter.tendsto_atTop'] at hx ⊢
  intro s hs
  -- Let `a` be the witness from the definition of `Tendsto`.
  rcases hx s hs with ⟨a, ha⟩
  use T a
  intros n hn
  -- Let `k` be such that `T k ≤ n < T (k + 1)`.
  obtain ⟨k, hk⟩ : ∃ k, T k ≤ n ∧ n < T (k + 1) := by
    -- Since $T$ is strictly increasing, the set $\{k \mid T k \leq n\}$ is finite and non-empty.
    have h_finite : Set.Finite {k | T k ≤ n} := by
      rw [Set.finite_iff_bddAbove]
      exact ⟨_, (hT.id_le · |>.trans)⟩
    use h_finite.toFinset.max' ⟨a, h_finite.mem_toFinset.mpr hn⟩
    constructor
    · exact h_finite.mem_toFinset.mp (Finset.max'_mem _ _)
    · rw [← not_le]
      intro h
      exact not_lt_of_ge (Finset.le_max' _ _ (h_finite.mem_toFinset.mpr h)) (Nat.lt_succ_self _)
  rw [hg k n hk]
  exact ha k (le_of_not_gt fun hk' ↦ by linarith [hT.monotone hk'])

/-
Given a lower bound sequence M and a property P that can always be satisfied eventually, there exists a strictly increasing sequence T bounded by M such that each interval [T_k, T_{k+1}) contains a witness for P.
-/
lemma exists_increasing_sequence_with_property (M : ℕ → ℕ) (P : ℕ → ℕ → Prop) (hP : ∀ k L, ∃ n ≥ L, P k n) :
    ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ k, T k ≥ M k) ∧ (∀ k, ∃ n ∈ Set.Ico (T k) (T (k + 1)), P k n) := by
  -- We construct $T_k$ by induction.
  have hT_ind : ∀ k : ℕ, ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ k, T k ≥ M k) ∧ (∀ k, ∃ n ∈ Set.Ico (T k) (T (k + 1)), P k n) ∧ T (k + 1) > T k := by
    intro k
    induction k
    · choose! n hn using hP;
      use fun k => Nat.recOn k ( M 0 ) fun k ih => Max.max ( ih + 1 ) ( Max.max ( M ( k + 1 ) ) ( n k ih + 1 ) )
      simp_all only [ge_iff_le, le_sup_iff, add_le_add_iff_right, or_true, sup_of_le_right, Set.mem_Ico, lt_sup_iff,
        Nat.rec_zero, zero_add]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact strictMono_nat_of_lt_succ fun k => by cases max_cases ( M ( k + 1 ) ) ( n k ( Nat.rec ( M 0 ) ( fun k ih => Max.max ( M ( k + 1 ) ) ( n k ih + 1 ) ) k ) + 1 ) <;> linarith [ hn k ( Nat.rec ( M 0 ) ( fun k ih => Max.max ( M ( k + 1 ) ) ( n k ih + 1 ) ) k ) ] ;
      · intro k
        induction k <;> aesop;
      · intro k
        exact ⟨ n k ( Nat.rec ( M 0 ) ( fun k ih => Max.max ( M ( k + 1 ) ) ( n k ih + 1 ) ) k ), ⟨ hn _ _ |>.1, Or.inr ( Nat.lt_succ_self _ ) ⟩, hn _ _ |>.2 ⟩;
      · exact Or.inr ( by linarith [ hn 0 ( M 0 ) ] );
    · rename_i ih
      obtain ⟨ T, hT₁, hT₂, hT₃, hT₄ ⟩ := ih
      use T
      aesop
  exact Exists.elim ( hT_ind 0 ) fun T hT => ⟨ T, hT.1, hT.2.1, hT.2.2.1 ⟩

/-
If g is a block sequence constructed from x and T, and each block contains a witness where f is bounded by y + 1/(k+1), then liminf f(g) <= y.
-/
lemma liminf_le_of_block_sequence_witnesses {α : Type*} (y : ℝ≥0) (f : α → ℕ → ℝ≥0∞)
    (T : ℕ → ℕ) (hT : StrictMono T) (x : ℕ → α) (g : ℕ → α)
    (hg : ∀ k, ∀ n ∈ Set.Ico (T k) (T (k + 1)), g n = x k)
    (hwit : ∀ k, ∃ n ∈ Set.Ico (T k) (T (k + 1)), f (x k) n ≤ (y : ℝ≥0∞) + (k + 1 : ℝ≥0)⁻¹) :
    Filter.atTop.liminf (fun n ↦ f (g n) n) ≤ y := by
  rw [ Filter.liminf_eq ];
  simp_all only [Set.mem_Ico, and_imp, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one,
    Filter.eventually_atTop, ge_iff_le, sSup_le_iff, Set.mem_setOf_eq, forall_exists_index]
  intro b x_1 h
  -- Fix an arbitrary $k \geq x_1$.
  suffices h_suff : ∀ k ≥ x_1, ∃ n ≥ k, f (g n) n ≤ y + 1 / (k + 1) by
    -- By taking the limit as $k$ approaches infinity, we get $b \leq y$.
    have h_lim : Filter.Tendsto (fun k : ℕ => y + 1 / (k + 1 : ℝ≥0∞)) Filter.atTop (𝓝 y) := by
      have h_lim : Filter.Tendsto (fun k : ℕ => (k + 1 : ℝ≥0∞)⁻¹) Filter.atTop (𝓝 0) := by
        rw [ ENNReal.tendsto_nhds_zero ]
        intro ε a
        simp_all only [ge_iff_le, one_div, gt_iff_lt, Filter.eventually_atTop]
        rcases ENNReal.exists_inv_nat_lt a.ne' with ⟨ N, hN ⟩;
        exact ⟨ N, fun n hn => le_trans ( by gcongr ; norm_cast ; linarith ) hN.le ⟩;
      simpa using tendsto_const_nhds.add h_lim;
    refine' le_of_tendsto_of_tendsto tendsto_const_nhds h_lim _;
    filter_upwards [ Filter.eventually_ge_atTop x_1 ] with k hk using by obtain ⟨ n, hn₁, hn₂ ⟩ := h_suff k hk; exact le_trans ( h n ( by linarith ) ) hn₂;
  intro k hk
  obtain ⟨n, hn₁, hn₂⟩ := hwit k;
  exact ⟨ n, le_trans ( show k ≤ T k from hT.id_le _ ) hn₁.1, by rw [ hg k n hn₁.1 hn₁.2 ] ; simpa using hn₂ ⟩

/-
If g is a block sequence constructed from x and T, and f is bounded by y + 1/(k+1) on each block, then limsup f(g) <= y.
-/
lemma limsup_le_of_block_sequence_bound {α : Type*} (y : ℝ≥0) (f : α → ℕ → ℝ≥0∞)
  (T : ℕ → ℕ) (hT : StrictMono T) (x : ℕ → α) (g : ℕ → α)
  (hg : ∀ k, ∀ n ∈ Set.Ico (T k) (T (k + 1)), g n = x k)
  (hbound : ∀ k, ∀ n ∈ Set.Ico (T k) (T (k + 1)), f (x k) n ≤ (y : ℝ≥0∞) + (k + 1 : ℝ≥0)⁻¹) :
  Filter.atTop.limsup (fun n ↦ f (g n) n) ≤ y := by
    refine' le_of_forall_pos_le_add fun ε hε => _;
    refine' csInf_le _ _
    · aesop
    simp_all only [Set.mem_Ico, and_imp, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one,
      Filter.eventually_map, Filter.eventually_atTop, ge_iff_le, Set.mem_setOf_eq]
    -- Choose $K$ such that for all $k \ge K$, we have $1/(k+1) \le \epsilon$.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k ≥ K, (k + 1 : ℝ≥0)⁻¹ ≤ ε := by
      rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hε with ⟨ δ, hδ, hδε ⟩
      simp_all only [ENNReal.coe_pos, ge_iff_le, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false,
        not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one]
      refine' ⟨ ⌈δ⁻¹⌉₊, fun k hk => le_trans _ hδε.le ⟩
      norm_cast
      rw [ ENNReal.inv_le_iff_le_mul ] <;> norm_cast
      · rw [ ← div_le_iff₀ ] at * <;> norm_cast at *
        simp_all only [Nat.ceil_le, Nat.cast_add, Nat.cast_one, one_div]
        exact le_add_of_le_of_nonneg hk zero_le_one;
      · aesop
      · aesop
    use T K
    intro b a
    simp_all only [ge_iff_le, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one]
    -- Let $k$ be such that $b \in [T_k, T_{k+1})$.
    obtain ⟨k, hk⟩ : ∃ k, T k ≤ b ∧ b < T (k + 1) := by
      -- Since $T$ is strictly increasing and unbounded, the set $\{n \mid T n \leq b\}$ is finite and non-empty.
      have h_finite : Set.Finite {n | T n ≤ b} := by
        exact Set.finite_iff_bddAbove.2 ⟨ b, fun n hn => le_trans ( hT.id_le _ ) hn ⟩;
      exact ⟨ Finset.max' ( h_finite.toFinset ) ⟨ K, h_finite.mem_toFinset.mpr a ⟩, h_finite.mem_toFinset.mp ( Finset.max'_mem _ _ ), not_le.mp fun h => not_lt_of_ge ( Finset.le_max' _ _ ( h_finite.mem_toFinset.mpr h ) ) ( Nat.lt_succ_self _ ) ⟩;
    rw [ hg k b hk.1 hk.2 ];
    exact le_trans ( hbound k b hk.1 hk.2 ) ( add_le_add_left ( hK k ( le_of_not_gt fun hk' => by linarith [ hT.monotone hk'.nat_succ_le ] ) ) _ )

/- Version of `exists_liminf_zero_of_forall_liminf_le_with_UB` that lets you stipulate it for
two different functions simultaneously, one with liminf and one with limsup. -/
lemma exists_liminf_zero_of_forall_liminf_limsup_le_with_UB (y₁ y₂ : ℝ≥0) (f₁ f₂ : ℝ≥0 → ℕ → ℝ≥0∞)
    {z : ℝ≥0} (hz : 0 < z)
    (hf₁ : ∀ x > 0, Filter.atTop.liminf (f₁ x) ≤ y₁)
    (hf₂ : ∀ x > 0, Filter.atTop.limsup (f₂ x) ≤ y₂) :
      ∃ g : ℕ → ℝ≥0, (∀ x, g x > 0) ∧ (∀ x, g x < z) ∧
        Filter.atTop.Tendsto g (𝓝 0) ∧
        Filter.atTop.liminf (fun n ↦ f₁ (g n) n) ≤ y₁ ∧
      Filter.atTop.limsup (fun n ↦ f₂ (g n) n) ≤ y₂ := by
  -- Fix some sequences of positive real numbers $x_k$ and $N_0(k)$.
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ≥0, (∀ k, 0 < x k) ∧ (∀ k, x k ≤ z / 2) ∧ (∀ k, x k ≤ 1 / (k + 1)) ∧ Filter.Tendsto x Filter.atTop (𝓝 0) := by
    use fun k => Min.min ( z / 2 ) ( 1 / ( k + 1 ) )
    simp_all only [gt_iff_lt, one_div, lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, inv_pos, add_pos_iff,
      Nat.cast_pos, zero_lt_one, or_true, and_self, implies_true, inf_le_left, inf_le_right, true_and]
    rw [ Filter.tendsto_congr' ];
    any_goals filter_upwards [ Filter.eventually_gt_atTop ⌈ ( z / 2 ) ⁻¹⌉₊ ] with k hk; rw [ min_eq_right ];
    · refine' tendsto_order.2 ⟨ fun x => _, fun x hx => _ ⟩
      · aesop
      · simp_all only [gt_iff_lt, Filter.eventually_atTop, ge_iff_le]
        exact ⟨ ⌈x⁻¹⌉₊, fun n hn => inv_lt_of_inv_lt₀ hx <| lt_of_le_of_lt ( Nat.le_ceil _ ) <| mod_cast Nat.lt_succ_of_le hn ⟩;
    · rw [ inv_le_comm₀ ] <;> norm_cast
      · simp_all only [inv_div, Nat.cast_add, Nat.cast_one]
        exact le_trans ( Nat.le_ceil _ ) ( mod_cast by linarith )
      · aesop
      · aesop
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ → ℕ, ∀ k, ∀ n ≥ N0 k, f₂ (x k) n ≤ y₂ + (k + 1 : ℝ≥0)⁻¹ := by
    have h_limsup : ∀ k, Filter.limsup (f₂ (x k)) Filter.atTop ≤ y₂ := by
      exact fun k => hf₂ _ ( hx.1 k );
    have h_limsup_le : ∀ k, ∀ ε > 0, ∃ N, ∀ n ≥ N, f₂ (x k) n ≤ y₂ + ε := by
      intro k ε hε_pos
      have h_limsup_le : Filter.limsup (f₂ (x k)) Filter.atTop ≤ y₂ := h_limsup k;
      rw [ Filter.limsup_eq ] at h_limsup_le;
      have := exists_lt_of_csInf_lt ( show { a : ℝ≥0∞ | ∀ᶠ n in Filter.atTop, f₂ ( x k ) n ≤ a }.Nonempty from ⟨ _, Filter.Eventually.of_forall fun n => le_top ⟩ ) ( show InfSet.sInf { a : ℝ≥0∞ | ∀ᶠ n in Filter.atTop, f₂ ( x k ) n ≤ a } < ( y₂ : ℝ≥0∞ ) + ε from lt_of_le_of_lt h_limsup_le <| ENNReal.lt_add_right ( by aesop ) <| by aesop )
      simp_all only [gt_iff_lt, one_div, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false,
        not_false_eq_true, NNReal.le_inv_iff_mul_le, implies_true, Filter.eventually_atTop, ge_iff_le, Set.mem_setOf_eq]
      obtain ⟨left, right⟩ := hx
      obtain ⟨w, h⟩ := this
      obtain ⟨left_1, right⟩ := right
      obtain ⟨left_2, right_1⟩ := h
      obtain ⟨left_3, right⟩ := right
      obtain ⟨w_1, h⟩ := left_2
      exact ⟨ w_1, fun n hn => le_trans ( h n hn ) right_1.le ⟩;
    exact ⟨ fun k => Classical.choose ( h_limsup_le k _ <| by positivity ), fun k n hn => Classical.choose_spec ( h_limsup_le k _ <| by positivity ) n hn ⟩;
  -- Define the sequence $T_k$ such that $T_k \geq N_0(k)$ and each interval $[T_k, T_{k+1})$ contains some $n_k$ with $P(k, n_k)$.
  obtain ⟨T, hT_mono, hT_bound, hT_wit⟩ : ∃ T : ℕ → ℕ, StrictMono T ∧ (∀ k, T k ≥ N0 k) ∧ (∀ k, ∃ n ∈ Set.Ico (T k) (T (k + 1)), f₁ (x k) n ≤ y₁ + (k + 1 : ℝ≥0)⁻¹) := by
    have hP : ∀ k L, ∃ n ≥ L, f₁ (x k) n ≤ y₁ + (k + 1 : ℝ≥0)⁻¹ := by
      intro k L; specialize hf₁ ( x k ) ( hx.1 k ) ; rw [ Filter.liminf_eq ] at hf₁; simp_all +decide [ Filter.limsup_eq ] ;
      contrapose! hf₁;
      exact ⟨ y₁ + ( k + 1 : ℝ≥0∞ ) ⁻¹, L, fun n hn => le_of_lt ( hf₁ n hn ), ENNReal.lt_add_right ( by aesop ) ( by aesop ) ⟩;
    have := exists_increasing_sequence_with_property ( fun k => N0 k ) ( fun k n => f₁ ( x k ) n ≤ y₁ + ( k + 1 : ℝ≥0 ) ⁻¹ ) hP; aesop;
  refine' ⟨ fun n => x ( Nat.find ( show ∃ k, n < T ( k + 1 ) from _ ) ), _, _, _, _, _ ⟩;
  exact ⟨ n, hT_mono.id_le _ ⟩;
  · exact fun n => hx.1 _;
  · intro n
    specialize hx
    simp_all only [gt_iff_lt, ge_iff_le, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one, Set.mem_Ico, one_div,
      NNReal.le_inv_iff_mul_le]
    obtain ⟨left, right⟩ := hx
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    exact lt_of_le_of_lt ( left_1 _ ) ( half_lt_self hz );
  · refine' hx.2.2.2.comp _;
    refine' Filter.tendsto_atTop_atTop.mpr _;
    intro b; use T b; intro a ha; contrapose! ha
    simp_all only [gt_iff_lt, one_div, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, NNReal.le_inv_iff_mul_le, ge_iff_le, ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast,
      ENNReal.coe_one, Set.mem_Ico, Nat.find_lt_iff]
    obtain ⟨left, right⟩ := hx
    obtain ⟨w, h⟩ := ha
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right_1⟩ := h
    obtain ⟨left_3, right⟩ := right
    exact right_1.trans_le ( hT_mono.monotone ( by linarith ) );
  · refine liminf_le_of_block_sequence_witnesses y₁ f₁ T hT_mono x _ ?_ hT_wit
    intro k n hn
    congr
    simp_all only [gt_iff_lt, one_div, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, NNReal.le_inv_iff_mul_le, ge_iff_le, ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast,
      ENNReal.coe_one, Set.mem_Ico]
    obtain ⟨left, right⟩ := hx
    obtain ⟨left_1, right_1⟩ := hn
    obtain ⟨left_2, right⟩ := right
    obtain ⟨left_3, right⟩ := right
    rw [ Nat.find_eq_iff ]
    simp_all only [not_lt, true_and]
    intro n_1 a
    exact le_trans ( hT_mono.monotone ( by linarith ) ) left_1
  · -- By definition of $g$, we know that for each $k$, $g(n) = x_k$ for $n \in [T_k, T_{k+1})$.
    apply limsup_le_of_block_sequence_bound
    · exact hT_mono
    · intro k n hn
      congr! 1;
      rw [ Nat.find_eq_iff ]
      simp_all only [gt_iff_lt, one_div, ne_eq, add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false,
        not_false_eq_true, NNReal.le_inv_iff_mul_le, ge_iff_le, ENNReal.coe_inv, ENNReal.coe_add, ENNReal.coe_natCast,
        ENNReal.coe_one, Set.mem_Ico, not_lt, true_and]
      intro n_1 a
      obtain ⟨left, right⟩ := hx
      obtain ⟨left_1, right_1⟩ := hn
      obtain ⟨left_2, right⟩ := right
      obtain ⟨left_3, right⟩ := right
      exact le_trans ( hT_mono.monotone ( by linarith ) ) left_1
    · grind


--PULLOUT.
--PR? This is "not specific to our repo", but might be a bit too specialized to be in Mathlib. Not sure.
--Definitely would need to clean up the proof first
theorem extracted_limsup_inequality (z : ℝ≥0∞) (hz : z ≠ ⊤) (y x : ℕ → ℝ≥0∞) (h_lem5 : ∀ (n : ℕ), x n ≤ y n + z)
    : Filter.atTop.limsup (fun n ↦ x n / n) ≤ Filter.atTop.limsup (fun n ↦ y n / n) := by
  --Thanks Aristotle!
  simp? [Filter.limsup_eq] says simp only [Filter.limsup_eq, Filter.eventually_atTop,
    ge_iff_le, le_sInf_iff, Set.mem_setOf_eq, forall_exists_index]
  -- Taking the limit superior of both sides of the inequality x n / n ≤ y_n / n + z / n, we
  -- get limsup x n / n ≤ limsup (y n / n + z / n).
  intro b n h_bn
  have h_le : ∀ m ≥ n, x m / (m : ℝ≥0∞) ≤ b + z / (m : ℝ≥0∞) := by
    intro m hm
    grw [← h_bn m hm, ← ENNReal.add_div, h_lem5 m]
  -- Since z is finite, we have lim z / n = 0.
  have h_z_div_n_zero : Filter.atTop.Tendsto (fun n : ℕ ↦ z / (n : ℝ≥0∞)) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rw [gt_iff_lt, ENNReal.lt_iff_exists_real_btwn] at hε
    rcases hε with ⟨ε', hε₁, hε₂⟩
    rw [ENNReal.ofReal_pos] at hε₂
    -- Since z is finite, we can choose k such that for all b ≥ k, z ≤ b * ε'.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ b ≥ k, z ≤ b * ENNReal.ofReal ε' := by
      rcases ENNReal.lt_iff_exists_real_btwn.mp (show z < ⊤ by finiteness) with ⟨a, _, ha, _⟩
      use ⌈a / ε'⌉₊
      intro n hn
      grw [ha.le, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      gcongr
      nlinarith [Nat.ceil_le.mp hn, mul_div_cancel₀ a hε₂.1.ne']
    -- Since z ≤ b * ε' for all b ≥ k, dividing both sides by b (which is positive) gives z / b ≤ ε'.
    rw [Filter.eventually_atTop]
    use k + 1
    intros b _
    grw [ENNReal.div_le_iff_le_mul (by aesop) (by simp), hk b (by omega), mul_comm, hε₂.right.le]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rcases Filter.eventually_atTop.mp (h_z_div_n_zero.eventually <| gt_mem_nhds hε) with ⟨m, hm⟩
  apply sInf_le
  use n + m
  intro n hn
  grw [h_le n (by omega), (hm n (by omega)).le]

--PULLOUT and PR
open Filter in
/-- Like `Filter.tendsto_add_atTop_iff_nat`, but with nat subtraction. -/
theorem _root_.Filter.tendsto_sub_atTop_iff_nat {α : Type*} {f : ℕ → α} {l : Filter α} (k : ℕ) :
    Tendsto (fun (n : ℕ) ↦ f (n - k)) atTop l ↔ Tendsto f atTop l :=
  show Tendsto (f ∘ fun n ↦ n - k) atTop l ↔ Tendsto f atTop l by
    rw [← tendsto_map'_iff, map_sub_atTop_eq_nat]

--PULLOUT and PR
open ENNReal Filter in
/-- Sort of dual to `ENNReal.tendsto_const_sub_nhds_zero_iff`. Takes a substantially different form though, since
we don't actually have equality of the limits, or even the fact that the other one converges, which is why we
need to use `limsup`. -/
theorem _root_.ENNReal.tendsto_sub_const_nhds_zero_iff {α : Type*} {l : Filter α} {f : α → ℝ≥0∞} {a : ℝ≥0∞}
    : Tendsto (f · - a) l (𝓝 0) ↔ limsup f l ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [tendsto_const_nhds]
  rw [ENNReal.tendsto_nhds_zero, limsup_le_iff']
  simp only [tsub_le_iff_left]
  constructor
  · intro h y hy
    specialize h (y - a) (tsub_pos_of_lt hy)
    rwa [add_comm, tsub_add_cancel_of_le hy.le] at h
  · intro h ε hε
    exact h (a + ε) (lt_add_right ha hε.ne')
