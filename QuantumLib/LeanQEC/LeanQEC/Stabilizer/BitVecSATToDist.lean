import LeanQEC.Stabilizer.CSS
import LeanQEC.ComputerAlgebra.BitVecCorrectness

lemma min_weight_ker_not_mem_rowspace_empty
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (is_empty : ¬∃x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace) :
  min_weight_ker_not_mem_rowspace H₁ H₂ = n + 1 := by
  unfold min_weight_ker_not_mem_rowspace at *
  simp_all +decide
  rw [show (LinearMap.ker (Matrix.toLin' H₁) : Set (Fin n → ZMod 2)).toFinset \
    (H₂.rowSpace : Set (Fin n → ZMod 2)).toFinset = ∅ from by ext x; aesop]
  simp +decide

-- property of minimum
-- if minimum is less than a certain number, then there exists a witness
lemma dist_index_some
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (dist : ℕ)
  (non_empty : ∃x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace)
  (hdist : min_weight_ker_not_mem_rowspace H₁ H₂ < dist) :
  ∃x, x ∈ LinearMap.ker H₁.toLin' /\
    x ∉ H₂.rowSpace /\ hammingNorm x < dist := by
  contrapose! hdist
  simp_all +decide [min_weight_ker_not_mem_rowspace]
  rcases h : Finset.min (Finset.image hammingNorm
    ((LinearMap.ker H₁.toLin' : Set (Fin n → ZMod 2)).toFinset \
    (H₂.rowSpace : Set (Fin n → ZMod 2)).toFinset)) with (_ | a) <;> simp_all +decide
  · simp_all +decide [Finset.min]
    simp_all +decide [Finset.inf_eq_iInf]
    simp_all +decide [WithTop.none_eq_top, iInf]
    exact False.elim <| non_empty.choose_spec.2 <| h _ non_empty.choose_spec.1
  · have := Finset.mem_of_min h; aesop

lemma index_vec_monotone {n k : ℕ} {x : Fin n → ZMod 2}
    {hx : hammingNorm x ≤ k} {hx' : hammingNorm x ≠ 0} :
    ∀ i j : Fin k, i ≤ j → index_vec x hx hx' i ≤ index_vec x hx hx' j := by
  intro i j hij
  let S := Finset.univ.filter (fun j : Fin n => x j ≠ 0)
  let I : Fin (hammingNorm x) → Fin n := fun j => S.orderEmbOfFin rfl j
  change (if hi : (i : ℕ) < hammingNorm x then I ⟨i, hi⟩
      else I ⟨hammingNorm x - 1, Nat.sub_one_lt hx'⟩) ≤
    (if hj : (j : ℕ) < hammingNorm x then I ⟨j, hj⟩
      else I ⟨hammingNorm x - 1, Nat.sub_one_lt hx'⟩)
  by_cases hj : (j : ℕ) < hammingNorm x
  · have hi : (i : ℕ) < hammingNorm x := lt_of_le_of_lt (Fin.le_def.mp hij) hj
    simp [hi, hj]
    apply (S.orderEmbOfFin rfl).monotone
    exact Fin.mk_le_mk.mpr (Fin.le_def.mp hij)
  · by_cases hi : (i : ℕ) < hammingNorm x
    · simp [hi, hj]
      apply (S.orderEmbOfFin rfl).monotone
      exact Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt hi)
    · simp [hi, hj]

lemma lt_dist_sat_sound_contrapositive
  {n k₁ k₂ kersize : ℕ} [NeZero n] [NeZero k₁] [NeZero kersize] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_ker : Matrix (Fin kersize) (Fin n) (ZMod 2))
  (H₂_ker_correct : H₂_ker.is_ker_for H₂)
  (dist : ℕ)
  (dist_le : dist ≤ n)
  (hdist : min_weight_ker_not_mem_rowspace H₁ H₂ < dist) :
  ¬(lt_dist_sat (flatten_matrix H₁) (flatten_matrix (H₂_ker)) (dist - 1) (Nat.clog 2 n))
     := by
  let undetectable_errors : Set (Fin n → ZMod 2) :=
    LinearMap.ker H₁.toLin' \ H₂.rowSpace
  intro htest
  by_cases h_empty : undetectable_errors = ∅
  · have hmin : min_weight_ker_not_mem_rowspace H₁ H₂ = n + 1 := by
      apply min_weight_ker_not_mem_rowspace_empty H₁ H₂
      intro h_nonempty
      rcases h_nonempty with ⟨x, hxker, hxrow⟩
      have : x ∈ undetectable_errors := ⟨hxker, hxrow⟩
      simp [h_empty] at this
    rw [hmin] at hdist
    linarith [dist_le, hdist]
  · have h_nonempty : ∃ x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace := by
      rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨x, hx⟩
      exact ⟨x, hx.1, hx.2⟩
    rcases dist_index_some H₁ H₂ dist h_nonempty hdist with
      ⟨x, ker_x, rowspace_x, hamming_x⟩
    have hx_ne_zero : x ≠ 0 := by
      intro hx0
      apply rowspace_x
      rw [hx0]
      simp only [zero_mem]
    rw [←Nat.le_sub_one_iff_lt] at hamming_x
    swap
    · apply lt_of_le_of_lt (Nat.zero_le _) hamming_x
    let I := index_vec x hamming_x (hammingNorm_ne_zero_iff.2 hx_ne_zero)
    apply (htest (vec_to_BitVec' I) (vec_to_BitVec x))
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply loc_constraints_of_index
    · rw [symmetry_constraints_iff_index]
      exact index_vec_monotone
    · rw [parity_constraints_correct]
      exact ker_x
    apply (rowspace_constraints_correct H₂_ker_correct).2 rowspace_x




lemma lt_dist_sat_sound
  {n k₁ k₂ kersize : ℕ} [NeZero n] [NeZero k₁] [NeZero kersize] [NeZero (n - k₂)]
  {H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)}
  {H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)}
  (H₂_ker : Matrix (Fin kersize) (Fin n) (ZMod 2))
  (H₂_kergen_correct : H₂_ker.is_ker_for H₂)
  {dist : ℕ}
  (dist_le : dist ≤ n)
  (test_dist : lt_dist_sat (flatten_matrix H₁) (flatten_matrix H₂_ker) (dist - 1) (Nat.clog 2 n)) :
  dist ≤ min_weight_ker_not_mem_rowspace H₁ H₂ := by
  by_contra!
  suffices: ¬lt_dist_sat (flatten_matrix H₁) (flatten_matrix H₂_ker) (dist - 1) (Nat.clog 2 n)
  · simp_all only
  apply lt_dist_sat_sound_contrapositive _ H₂ _ _ _ dist_le
  · assumption
  · assumption


theorem bitvec_sat_translation_correct
  {n k₁ k₂ xkersize zkersize : ℕ} [NeZero n] [NeZero k₁]
  [NeZero k₂] [NeZero xkersize] [NeZero zkersize] [NeZero (n - k₁)] [NeZero (n - k₂)]
  (css : CSS_pair n k₁ k₂)
  (xker : Matrix (Fin xkersize) (Fin n) (ZMod 2))
  (xker_correct : xker.is_ker_for css.H₂)
  (zker : Matrix (Fin zkersize) (Fin n) (ZMod 2))
  (zker_correct : zker.is_ker_for css.H₁)
  {dist : ℕ}
  (dist_le : dist ≤ n)
   :
  lt_dist_sat (flatten_matrix css.H₁) (flatten_matrix xker) (dist - 1) (Nat.clog 2 n) →
  lt_dist_sat (flatten_matrix css.H₂) (flatten_matrix zker) (dist - 1) (Nat.clog 2 n) →
  dist ≤ css.toBSM.distance (by apply NeZero.pos) := by
  rw [CSS.toBSM_dist_eq]
  intro hdist_z hdist_x
  unfold CSS_pair.dX CSS_pair.dZ
  apply le_min
  · apply lt_dist_sat_sound zker zker_correct dist_le hdist_x
  apply lt_dist_sat_sound xker xker_correct dist_le hdist_z
