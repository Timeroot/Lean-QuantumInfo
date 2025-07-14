import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.LiminfLimsup

import Mathlib.Tactic.Bound

open Topology

theorem Filter.liminf_add_tendsTo_zero {T : Type*} [LinearOrder T] [Nonempty T] (f g : T → ENNReal)
      (hg : Filter.atTop.Tendsto g (𝓝 0)) :
    Filter.atTop.liminf (f + g) = Filter.atTop.liminf f := by
  -- Since $g$ tends to $0$, for any $\epsilon > 0$, there exists $N$ such that for all $n \geq N$, $g(n) < \epsilon$.
  have h_eps : ∀ ε > 0, ∃ N, ∀ n ≥ N, g n < ε := by
    intro ε hε;
    simpa using ( hg.eventually ( gt_mem_nhds hε ) );
  refine' le_antisymm _ _;
  -- Case 1
  · refine' le_of_forall_gt_imp_ge_of_dense fun b hb => _;
    rw [ Filter.liminf_eq ] at *;
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
      · use Max.max N w;
        intro n hn;
        specialize h n ( le_of_max_le_right hn ) ;
        specialize hN n ( le_of_max_le_left hn ) ;
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

theorem Filter.limsup_add_tendsTo_zero {T : Type*} [LinearOrder T] [Nonempty T] (f g : T → ENNReal) (hg : Filter.atTop.Tendsto g (𝓝 0)) :
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
      intro a x hx ε ε_pos; rcases h_eps ε ε_pos with ⟨ N, hN ⟩ ; exact ⟨ a + ε, ⟨ Max.max x N, fun n hn => add_le_add ( hx n ( le_of_max_le_left hn ) ) ( le_of_lt ( hN n ( le_of_max_le_right hn ) ) ) ⟩, le_rfl ⟩;
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
