import Mathlib

import Mathlib.Tactic.Bound

open Topology

theorem Filter.liminf_add_tendsTo_zero {T : Type*} [Preorder T] [IsDirected T fun x1 x2 => x1 ≤ x2] [Nonempty T]
  (f g : T → ENNReal) (hg : Filter.atTop.Tendsto g (𝓝 0)) :
    Filter.atTop.liminf (f + g) = Filter.atTop.liminf f := by
  -- Since $g$ tends to $0$, for any $\epsilon > 0$, there exists $N$ such that for all $n \geq N$, $g(n) < \epsilon$.
  have h_eps : ∀ ε > 0, ∃ N, ∀ n ≥ N, g n < ε := by
    intro ε hε;
    simpa using ( hg.eventually ( gt_mem_nhds hε ) );
  refine' le_antisymm _ _;
  -- Case 1
  · refine' le_of_forall_gt_imp_ge_of_dense fun b hb => _;
    simp only [ Filter.liminf_eq ] at *;
    refine' csSup_le _ _;
    -- Case 1
    · -- Since $f$ and $g$ are non-negative, $0 \leq f n + g n$ for all $n$. Therefore, $0$ is in the set.
      use 0
      simp;
    -- Case 2
    · intro b_1 a
      simp_all only [gt_iff_lt, ge_iff_le, eventually_atTop, Pi.add_apply, Set.mem_setOf_eq]
      obtain ⟨w, h⟩ := a
      contrapose! hb;
      -- Since $b < b_1$, we can choose $\epsilon = b_1 - b$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, g n < b_1 - b := by
        exact h_eps _ ( tsub_pos_iff_lt.mpr hb );
      refine' le_csSup _ _;
      -- Case 1
      · norm_num +zetaDelta at *;
      -- Case 2
      · dsimp
        obtain ⟨w_max, hw⟩ := directed_of (· ≤ ·) N w
        use w_max
        intro n hn;
        specialize h n ( hw.2.trans hn );
        specialize hN n ( hw.1.trans hn ) ;
        contrapose! hN;
        exact tsub_le_iff_left.mpr ( by simpa only [ add_comm ] using le_trans h ( add_le_add_right hN.le _ ) );
  -- Case 2
  · refine' ( csSup_le _ _ );
    -- Case 1
    · norm_num;
      exact ⟨ 0, ⟨ Classical.choice ‹_›, fun _ _ => zero_le _ ⟩ ⟩;
    -- Case 2
    · -- Given that $b$ is a lower bound for $f$, we need to show that $b$ is also a lower bound for $f + g$.
      intros b hb
      have h_lower_bound : ∀ᶠ n in Filter.atTop, b ≤ f n + g n := by
        simp_all only [gt_iff_lt, ge_iff_le, eventually_map, eventually_atTop, Set.mem_setOf_eq]
        obtain ⟨w, h⟩ := hb
        exact ⟨ w, fun n hn => le_add_right ( h n hn ) ⟩;
      refine' le_csSup _ _;
      -- Case 1
      · simp;
      -- Case 2
      · bound

theorem Filter.limsup_add_tendsTo_zero {T : Type*} [Preorder T] [IsDirected T fun x1 x2 => x1 ≤ x2] [Nonempty T]
  (f g : T → ENNReal) (hg : Filter.atTop.Tendsto g (𝓝 0)) :
    Filter.atTop.limsup (f + g) = Filter.atTop.limsup f := by
  -- Since $g$ tends to $0$, for any $\epsilon > 0$, there exists an $N$ such that for all $n \geq N$, $g(n) < \epsilon$.
  have h_eps : ∀ ε > 0, ∃ N, ∀ n ≥ N, g n < ε := by
    intro ε hε;
    simpa using ( hg.eventually ( gt_mem_nhds hε ) );
  rw [ Filter.limsup_eq, Filter.limsup_eq ];
  -- To prove the equality of the infimums, it suffices to show that for any $a$ in the set where $f n$ is eventually $\leq a$, there exists an $a'$ in the set where $f + g n$ is eventually $\leq a'$, and vice versa.
  apply le_antisymm;
  -- Case 1
  · -- For any $a$ in the set where $f$ is eventually $\leq a$, we can find an $a' = a + \epsilon$ in the set where $f + g$ is eventually $\leq a'$.
    have h_forall_a : ∀ a ∈ {a : ENNReal | ∀ᶠ n in Filter.atTop, f n ≤ a}, ∀ ε > 0, ∃ a' ∈ {a : ENNReal | ∀ᶠ n in Filter.atTop, (f + g) n ≤ a}, a' ≤ a + ε := by
      simp +zetaDelta at *;
      intro a x hx ε ε_pos;
      rcases h_eps ε ε_pos with ⟨ N, hN ⟩ ;
      refine ⟨ a + ε, ?_, le_rfl ⟩;
      obtain ⟨ w_max , hw ⟩ := directed_of (· ≤ ·) x N
      use w_max
      intro n hn
      exact add_le_add ( hx n ( hw.1.trans hn ) ) ( le_of_lt ( hN n ( hw.2.trans hn ) ) )
    apply le_of_forall_le;
    intro c a
    simp_all only [gt_iff_lt, ge_iff_le, eventually_atTop, Set.mem_setOf_eq, Pi.add_apply, forall_exists_index,
      le_sInf_iff]
    intro b x h
    contrapose! a;
    rcases ENNReal.lt_iff_exists_add_pos_lt.1 a with ⟨ ε, ε_pos, hε ⟩;
    rcases h_forall_a b x h ε ( by simpa using ε_pos ) with ⟨ a', ⟨ x', hx' ⟩, ha' ⟩ ; exact ⟨ a', x', hx', lt_of_le_of_lt ha' hε ⟩;
  -- Case 2
  · refine' le_csInf _ _;
    -- Case 1
    · simp_all only [gt_iff_lt, ge_iff_le, Pi.add_apply, eventually_atTop]
      rcases h_eps 1 zero_lt_one with ⟨ N, hN ⟩;
      -- Since $g(n) < 1$ for all $n \geq N$, we have $f(n) + g(n) \leq f(n) + 1$ for all $n \geq N$.
      have h_le : ∀ n ≥ N, f n + g n ≤ f n + 1 := by
        exact fun n hn => add_le_add_left ( le_of_lt ( hN n hn ) ) _;
      exact ⟨ ⊤, ⟨ N, fun n hn => le_trans ( h_le n hn ) ( by norm_num ) ⟩ ⟩;
    -- Case 2
    · intro b a
      simp_all only [gt_iff_lt, ge_iff_le, Pi.add_apply, eventually_atTop, Set.mem_setOf_eq]
      refine' csInf_le _ _;
      -- Case 1
      · exact ⟨ 0, by rintro x ⟨ N, hN ⟩ ; exact zero_le _ ⟩;
      -- Case 2
      · obtain ⟨w, h⟩ := a
        exact ⟨ w, fun n hn => le_trans ( le_add_right le_rfl ) ( h n hn ) ⟩

--This is a stupid name for a stupid lemma
theorem Filter.Tendsto_inv_nat_mul_div_real (m : ℕ)
   : Filter.Tendsto (fun (x : ℕ) => ((↑x)⁻¹ * ↑(x / m) : ℝ)) Filter.atTop (𝓝 (1 / ↑m)) := by
  --Thanks aristotle!
  -- This simplifies to $\lim_{x \to \infty} \frac{\lfloor x / m \rfloor}{x} = \frac{1}{m}$ because the floor function grows asymptotically like $x / m$.
  have h_floor : Filter.Tendsto (fun x : ℕ => (Nat.floor (x / m : ℝ) : ℝ) / x) Filter.atTop (nhds (1 / (m : ℝ))) := by
    -- We'll use the fact that the floor function is bounded and apply the squeeze theorem.
    have h_floor_bound : ∀ x : ℕ, x > 0 → (Nat.floor (x / m : ℝ) : ℝ) / x ≥ (1 / m - 1 / x) ∧ (Nat.floor (x / m : ℝ) : ℝ) / x ≤ 1 / m := by
      cases eq_or_ne m 0
      · rename_i h
        intro x a
        subst h
        simp_all only [gt_iff_lt, CharP.cast_eq_zero, div_zero, Nat.floor_zero, zero_div, one_div, zero_sub, ge_iff_le,
          Left.neg_nonpos_iff, inv_nonneg, Nat.cast_nonneg, le_refl, and_self]
      · intro x a
        simp_all only [ne_eq, gt_iff_lt, one_div, ge_iff_le, tsub_le_iff_right]
        apply And.intro
        · rw [ inv_eq_one_div, div_add', div_le_div_iff₀ ] <;> first | positivity | nlinarith [ Nat.lt_floor_add_one ( ( x : ℝ ) / m ), show ( x : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr a, mul_div_cancel₀ ( x : ℝ ) ( show ( m : ℝ ) ≠ 0 by positivity ), inv_mul_cancel₀ ( show ( x : ℝ ) ≠ 0 by positivity ) ] ;
        · rw [ div_le_iff₀ ( by positivity ) ];
          simpa [ div_eq_inv_mul ] using Nat.floor_le ( by positivity : 0 ≤ ( x : ℝ ) / m );
    -- Apply the squeeze theorem to conclude the proof.
    have h_squeeze : Filter.Tendsto (fun x : ℕ => (1 / m : ℝ) - 1 / x) Filter.atTop (nhds (1 / m)) := by
      simpa using tendsto_const_nhds.sub ( _root_.tendsto_inverse_atTop_nhds_zero_nat );
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_squeeze tendsto_const_nhds ( Filter.eventually_atTop.mpr ⟨ 1, fun x hx => h_floor_bound x hx |>.1 ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 1, fun x hx => h_floor_bound x hx |>.2 ⟩ );
  -- Apply the hypothesis `h_floor` to conclude the proof.
  convert h_floor using 1;
  -- By definition of floor function, we know that ⌊(x : ℝ) / m⌋₊ is the greatest integer less than or equal to (x : ℝ) / m.
  funext x; simp [Nat.floor_div_natCast];
  ring

--Similar to `ENNReal.tendsto_toReal_iff` in `Mathlib/Topology/Instances/ENNReal/Lemmas`, but
-- instead of requiring finiteness for all values, just eventually is needed.
open Filter Topology ENNReal in
theorem ENNReal.tendsto_toReal_iff_of_eventually_ne_top
  {ι} {fi : Filter ι} {f : ι → ℝ≥0∞} (hf : ∀ᶠ i in fi, f i ≠ ∞) {x : ℝ≥0∞}
    (hx : x ≠ ∞) : Tendsto (fun n => (f n).toReal) fi (𝓝 x.toReal) ↔ Tendsto f fi (𝓝 x) := by
  have he₁ : f =ᶠ[fi] (fun n ↦ (f n).toNNReal) := by
    rw [EventuallyEq]
    peel hf with h
    simp [h]
  have he₂ : (fun n ↦ (f n).toReal) = (fun n ↦ ((f n).toNNReal : ℝ≥0∞).toReal) :=
    rfl
  rw [Filter.tendsto_congr' he₁, he₂]
  exact tendsto_toReal_iff (by finiteness) hx
