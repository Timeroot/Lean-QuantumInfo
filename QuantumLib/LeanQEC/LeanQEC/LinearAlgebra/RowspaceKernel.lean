import Mathlib

noncomputable instance Submodule_set_fintype (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : Fintype ↑(C : Set (Fin n → ZMod 2)) := by
  classical
  infer_instance

 lemma zmod2_val_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a.1 = 1 := by
  have hlt : a.1 < 2 := a.2
  have hne : a.1 ≠ 0 := by simpa using ha
  omega

lemma zmod2_val_eq_zero_of_ne_one (a : ZMod 2) (ha : a ≠ 1) : a.1 = 0 := by
  fin_cases a
  · rfl
  contradiction

def Matrix.rowSpace {α β γ : Type*} [Semiring γ] (M : Matrix α β γ) := (Submodule.span γ (Set.range M))

lemma Matrix.row_mem_rowSpace {α β γ : Type*} {i : α} [Semiring γ] {M : Matrix α β γ} :
  M i ∈ M.rowSpace := by
  apply Submodule.mem_span_of_mem (Set.mem_range_self _)

lemma Submodule.mem_span_range_iff_sum {α : Type*} [Fintype α] {n : ℕ} (x : Fin n → (ZMod 2)) (v : α → Fin n → (ZMod 2))
  : x ∈ Submodule.span (ZMod 2) (Set.range v) ↔ ∃ S : Finset α, ∑ s ∈ S, v s = x := by
  refine' ⟨ fun hx => _, _ ⟩;
  ·
    rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hx;
    obtain ⟨ c, rfl ⟩ := hx;
    use c.support.filter (fun s => c s = 1);
    rw [ Finset.sum_filter ] ; congr ; ext x i;
    rcases Fin.exists_fin_two.mp ⟨ c x, rfl ⟩ with h | h;
    · have h01 : ¬ ((0 : ZMod 2) = 1) := by norm_num;
      rw [ h ];
      change (if (0 : ZMod 2) = 1 then v x i else 0) = (0 : ZMod 2) * v x i;
      simp [ h01 ];
    · rw [ h ];
      change (if (1 : ZMod 2) = 1 then v x i else 0) = (1 : ZMod 2) * v x i;
      simp;
  · exact fun ⟨ S, hS ⟩ => hS ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ( Set.mem_range_self _ )

-- rowspace already contains the zero vector
-- no need to remove it again
noncomputable def min_weight_ker_not_mem_rowspace {n k₁ k₂ : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) : ℕ :=
  let undetectable_errors : Set (Fin n → ZMod 2) :=
    (LinearMap.ker M₁.toLin' \ M₂.rowSpace)
  match Finset.min (Finset.image hammingNorm undetectable_errors.toFinset) with
  | ⊤ => n + 1
  | some a => a

lemma min_weight_ker_not_mem_rowspace_pos {n k₁ k₂ : ℕ}
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)} :
  0 < min_weight_ker_not_mem_rowspace M₁ M₂ := by
  unfold min_weight_ker_not_mem_rowspace
  extract_lets undetectable_errors
  rcases h: (Finset.image hammingNorm undetectable_errors.toFinset).min with _ | m'
  · simp
  simp only
  apply Finset.mem_of_min at h
  simp only [Finset.mem_image] at h
  rcases h with ⟨nontrivial_error, h, rfl⟩
  by_contra
  apply Nat.eq_zero_of_not_pos at this
  rw [hammingNorm_eq_zero] at this
  subst this undetectable_errors
  simp at h

lemma mem_ker_iff_dotProd_rows_eq_zero {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) :
  x ∈ ((LinearMap.ker M.toLin')) ↔ ∀ i, (M i) ⬝ᵥ x = 0 := by
  exact ⟨ fun h i => by simpa [ Matrix.mulVec, dotProduct ] using congr_fun h i, fun h => by ext i; simpa [ Matrix.mulVec, dotProduct ] using h i ⟩

/-
Helper: backward direction - if y is in ker and y ⬝ x = 1, then x is not in rowSpace
-/
lemma ker_dotProduct_rowSpace_eq_zero {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) (x : Fin n → ZMod 2)
    (hy : y ∈ LinearMap.ker M.toLin') (hx : x ∈ M.rowSpace) : y ⬝ᵥ x = 0 := by
  revert x;
  intro x hx; induction hx using Submodule.span_induction <;> simp_all +decide [ dotProduct ] ;
  · obtain ⟨ i, rfl ⟩ := ‹_›; simp_all +decide [ funext_iff, Matrix.mulVec, dotProduct ] ;
    simpa only [ mul_comm ] using hy i;
  · simp_all +decide [ mul_add, Finset.sum_add_distrib ];
  · rename_i a x hx ih; rw [ ← Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _ ] ; simp_all +decide [ ← Finset.mul_sum _ _ _ ] ;

lemma dual_eq_dotProduct {n : ℕ} (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2) :
    f v = (fun i => f (Pi.single i 1)) ⬝ᵥ v := by
  convert f.pi_apply_eq_sum_univ v using 1;
  simp +decide [ dotProduct, mul_comm ];
  exact Finset.sum_congr rfl fun i _ => by congr; ext j; aesop;

/-
Helper: if x ∉ rowSpace, we can construct a y in ker with y ⬝ x = 1
-/
lemma exists_ker_dotProduct_eq_one_of_not_mem_rowSpace {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) (hx : x ∉ M.rowSpace) :
    ∃ y ∈ LinearMap.ker M.toLin', y ⬝ᵥ x = 1 := by
  unfold Matrix.rowSpace at hx
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Module.Free (ZMod 2) ((Fin n → ZMod 2) ⧸ Submodule.span (ZMod 2) (Set.range M.row)) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace (ZMod 2) _)

  obtain ⟨f, hfx, hf_bot⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
  · rw [mem_ker_iff_dotProd_rows_eq_zero]
    intro i
    rw [dotProduct_comm]
    rw [← dual_eq_dotProduct]
    have : f (M i) ∈ Submodule.map f (Submodule.span (ZMod 2) (Set.range M)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self i))
    rw [hf_bot] at this
    exact (Submodule.mem_bot _).mp this
  ·
    -- Since $f x \neq 0$, we have $f x = 1$.
    have hfx_one : f x = 1 := by
      exact Or.resolve_left ( Fin.exists_fin_two.mp ( by aesop ) ) hfx;
    convert hfx_one using 1;
    convert dual_eq_dotProduct f x |> Eq.symm

lemma not_mem_rowspace_iff_exists_mem_ker {n k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) :
  x ∉ M.rowSpace ↔ ∃ y ∈ (LinearMap.ker M.toLin'), y ⬝ᵥ x = 1 := by
  constructor
  · exact exists_ker_dotProduct_eq_one_of_not_mem_rowSpace M x
  · rintro ⟨y, hy_ker, hy_dot⟩ hx
    have := ker_dotProduct_rowSpace_eq_zero M y x hy_ker hx
    simp_all


lemma ex_mem_submodule_non_orth_iff_non_orth_mem_basis {n : ℕ} (S : Set (Fin n → (ZMod 2))) (x : Fin n → (ZMod 2))
  : ∃ y ∈ (Submodule.span (ZMod 2) S), y ⬝ᵥ x = 1 ↔ ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  by_cases h : ∃ s ∈ S, s ⬝ᵥ x = 1;
  · exact ⟨ h.choose, Submodule.subset_span h.choose_spec.1, by simpa [ h.choose_spec.2 ] ⟩;
  · exact ⟨ 0, Submodule.zero_mem _, by simp +decide [ h ] ⟩

lemma weight_le_disj {n k : ℕ} {z : Fin n → (ZMod 2)} : hammingNorm z ≤ k ↔ ∑ i, (z i).1 ≤ k := by
  simp +decide only [hammingNorm];
  rw [ Finset.card_filter ];
  exact iff_of_eq ( by congr; ext i; rcases z i with ( _ | _ | i ) <;> trivial )


lemma sum_id_dotProduct_eq {n : ℕ} (S : Finset (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
  S.sum id ⬝ᵥ x = S.sum (fun s => s ⬝ᵥ x) := by
  induction' S using Finset.induction_on with a s ha ih
  · simp [dotProduct]
  · rw [Finset.sum_insert ha, Finset.sum_insert ha, id, add_dotProduct]; congr 1


lemma exists_dotProduct_one_of_sum
  {n : ℕ} {S : Finset (Fin n → ZMod 2)} {y x : Fin n → ZMod 2}
  (hS_sum : S.sum id = y) (hy : y ⬝ᵥ x = 1) :
  ∃ s ∈ S, s ⬝ᵥ x = 1 := by
  by_contra h_all
  push_neg at h_all
  have h_zero : ∀ s ∈ S, s ⬝ᵥ x = 0 := by
    intro s hs
    rcases Fin.exists_fin_two.mp ⟨s ⬝ᵥ x, rfl⟩ with h | h
    · exact h
    · exact absurd h (h_all s hs)
  have : S.sum id ⬝ᵥ x = 0 := by
    rw [sum_id_dotProduct_eq]
    exact Finset.sum_eq_zero (fun s hs => h_zero s hs)
  rw [hS_sum] at this
  exact absurd this (by rw [hy]; decide)

lemma Matrix.mem_rowSpace_ZMod2 {n₁ n₂ : ℕ}
  {M : Matrix (Fin n₁) (Fin n₂) (ZMod 2)}
  {x : Fin n₂ → (ZMod 2)} :
  x ∈ M.rowSpace ↔
  ∃ (S : Finset ((Fin n₂) → (ZMod 2))),
    S ⊆ (Finset.image M Finset.univ) ∧ S.sum id = x := by
  refine' ⟨ _, fun ⟨ S, hS₁, hS₂ ⟩ => _ ⟩ <;> simp_all +decide [ SetLike.mem_coe, Submodule.mem_span ];
  · have h_sum : ∀ (y : Fin n₂ → ZMod 2), y ∈ Submodule.span (ZMod 2) (Set.range M) → ∃ S : Finset (Fin n₂ → ZMod 2), S ⊆ Finset.image M Finset.univ ∧ ∑ s ∈ S, s = y := by
      intro y hy; induction hy using Submodule.span_induction <;> simp_all +decide [ Finset.subset_iff ] ;
      · rename_i h; obtain ⟨ y, rfl ⟩ := h; exact ⟨ { M y }, by aesop ⟩ ;
      · exact ⟨ ∅, by norm_num ⟩;
      · rename_i hx hy; obtain ⟨ S₁, hS₁, hS₁' ⟩ := hx; obtain ⟨ S₂, hS₂, hS₂' ⟩ := hy; use S₁ \ S₂ ∪ S₂ \ S₁; simp_all +decide [ Finset.sum_sdiff, Finset.subset_iff ] ;
        rw [ ← hS₁', ← hS₂', Finset.sum_union ];
        · rw [ ← Finset.sum_sdiff ( Finset.inter_subset_left : S₁ ∩ S₂ ⊆ S₁ ), ← Finset.sum_sdiff ( Finset.inter_subset_right : S₁ ∩ S₂ ⊆ S₂ ) ] ; ring;
          simp +decide [ Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right, mul_two ];
          exact ⟨ fun x hx => hx.elim ( fun hx => hS₁ hx.1 ) fun hx => hS₂ hx.1, by rw [ ← two_smul ( ZMod 2 ) ] ; simp +decide ⟩;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop;
      · rename_i k hk₁ hk₂;
        rename_i a; fin_cases a;
        · refine ⟨ ∅, ?_, ?_ ⟩;
          · intro x hx; simp at hx;
          · ext i;
            change (0 : ZMod 2) = (0 : ZMod 2) * k i;
            ring;
        · obtain ⟨ S, hS, hsum ⟩ := hk₂;
          refine ⟨ S, hS, ?_ ⟩;
          rw [ hsum ];
          ext i;
          change k i = (1 : ZMod 2) * k i;
          ring;
    exact h_sum x;
  · exact hS₂ ▸ Submodule.sum_mem _ fun s hs => Submodule.subset_span <| by have := hS₁ hs; aesop;

lemma exists_row_of_exists_mem_rowspace_non_orth {n k : ℕ}
  {M : Matrix (Fin k) (Fin n) (ZMod 2)}
  {x y : Fin n → (ZMod 2)}
  (hy₁ : y ∈ M.rowSpace)
  (hy₂ : y ⬝ᵥ x = 1) :
  ∃ r, (M r) ⬝ᵥ x = 1 := by
  rw [Matrix.mem_rowSpace_ZMod2] at hy₁
  obtain ⟨S, hS_sub, hS_sum⟩ := hy₁
  obtain ⟨s, hs_mem, hs_dot⟩ := exists_dotProduct_one_of_sum hS_sum hy₂
  have hs_row := hS_sub hs_mem
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hs_row
  obtain ⟨i, hi⟩ := hs_row
  refine ⟨i, ?_⟩
  rwa [hi]

def Matrix.mutually_orth_rows {α β γ δ : Type*} [Fintype γ] [Mul δ] [AddCommMonoid δ]
  (M₁ : Matrix α γ δ) (M₂ : Matrix β γ δ) : Prop := ∀ a b, M₁ a ⬝ᵥ M₂ b = 0

def Matrix.is_ker_for {k₁ k₂ n : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  : Prop := M₁.rowSpace = LinearMap.ker M₂.toLin'

lemma Matrix.is_ker_for_of_rank_sum_mutually_orth
  {k₁ k₂ r₁ r₂ n : ℕ}
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (hr₁ : r₁ ≤ M₁.rank)
  (hr₂ : r₂ ≤ M₂.rank)
  (hrn : r₁ + r₂ = n)
  (ho : M₁.mutually_orth_rows M₂) :
  M₂.is_ker_for M₁ := by
    have h_dim_ker : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' M₁)) = n - Matrix.rank M₁ := by
      have := LinearMap.finrank_range_add_finrank_ker ( Matrix.mulVecLin M₁ );
      exact eq_tsub_of_add_eq ( by norm_num at *; linarith! );
    have h_finrank_M₂ : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range M₂)) = Matrix.rank M₂ := by
      rw [ ← Matrix.rank_transpose, Matrix.rank ];
      congr;
      · simp +decide [ funext_iff, Matrix.mulVec, Submodule.mem_span_range_iff_exists_fun ];
        simp +decide [ Matrix.vecMul, dotProduct ];
      · ext; simp [Matrix.mulVecLin];
        simp +decide [ Submodule.mem_span_range_iff_exists_fun, Matrix.vecMul, funext_iff ];
        simp +decide [ dotProduct, mul_comm ];
      · ext; simp [Matrix.mulVecLin];
        rw [ Submodule.mem_span_range_iff_exists_fun ];
        simp +decide [ funext_iff, Matrix.vecMul, dotProduct ];
      · infer_instance;
    have h_subspace : Submodule.span (ZMod 2) (Set.range M₂) ≤ LinearMap.ker (Matrix.toLin' M₁) := by
      rw [ Submodule.span_le ];
      rintro _ ⟨ i, rfl ⟩ ; specialize ho; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
      exact funext fun j => by simpa [ Matrix.mulVec, dotProduct ] using ho j i;
    have h_eq : Submodule.span (ZMod 2) (Set.range M₂) = LinearMap.ker (Matrix.toLin' M₁) := by
      exact Submodule.eq_of_le_of_finrank_le h_subspace ( by omega );
    exact h_eq

lemma Matrix.rank_le_of_submatrix_independent
  {k r n : ℕ}
  (M : Matrix (Fin r) (Fin n) (ZMod 2))
  (inds : Fin k → Fin r)
  (inds_mono : StrictMono inds)
  (h_ind : LinearIndependent (ZMod 2) (M.submatrix inds id)) :
  k ≤ M.rank := by
    have h_submatrix_rank : Matrix.rank (Matrix.submatrix M inds id) = k := by
      rw [ ← Matrix.rank_transpose, Matrix.rank ];
      rw [ @LinearMap.finrank_range_of_inj ];
      · norm_num;
      · intro x y hxy; simp_all +decide [ funext_iff, Matrix.mulVec ] ;
        rw [ Fintype.linearIndependent_iff ] at h_ind;
        specialize h_ind ( x - y ) ; simp_all +decide [ sub_eq_zero, dotProduct, Finset.sum_sub_distrib, sub_smul ];
        exact h_ind ( by ext i; simpa [ Matrix.mulVec, dotProduct, mul_comm ] using hxy i );
    rw [ ← h_submatrix_rank ];
    have h_submatrix_rank : ∃ (P : Matrix (Fin k) (Fin r) (ZMod 2)), P * M = M.submatrix inds id := by
      use Matrix.of (fun i j => if j = inds i then 1 else 0);
      ext i j; simp +decide [ Matrix.mul_apply ] ;
    exact h_submatrix_rank.elim fun P hP => hP ▸ Matrix.rank_mul_le_right _ _
