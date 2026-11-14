import Mathlib
import LeanQEC.LinearAlgebra.RowspaceKernel
import LeanQEC.ComputerAlgebra.BitVecSAT

instance {n : Nat} : Coe ((Fin n) → ZMod 2) ((Fin n) → Bool) where
  coe f := fun i => (f i).val == 1

def vec_to_BitVec {j : ℕ} (r : (Fin j) → (ZMod 2)) : BitVec j := BitVec.ofFnLE r

def BitVec_to_vec {n : ℕ} (x : BitVec n) : (Fin n) → (ZMod 2) := fun i => x[i].toNat




--for Fin j → Fin n
def vec_to_BitVec' {j n : ℕ} (r : (Fin j) → (Fin n)) : BitVec (j * (Nat.clog 2 n)) :=
  match j with
  | 0 => (BitVec.zero 0).cast (by rw [zero_mul])
  | 1 => (r 0)
  | j' + 1 => ((r ⟨j', Nat.lt_succ_self _⟩ : BitVec (Nat.clog 2 n)).append (vec_to_BitVec' (fun i : Fin j' => r ⟨i, by simp⟩))).cast (by rw [Nat.succ_mul, Nat.add_comm])

def BitVec.appendList {i j : ℕ} (f : (Fin i) → (BitVec j)) : BitVec (i * j) :=
  match i with
  | 0 => (BitVec.zero 0).cast (by rw [MulZeroClass.zero_mul])
  | 1 => (f 0).cast (by rw [one_mul])
  | i' + 1 => ((f ⟨i', Nat.lt_succ_self _⟩).append (BitVec.appendList (fun (j : Fin i') => f ⟨j, by simp⟩))).cast (by rw [Nat.succ_mul, add_comm])

def Matrix.toBitVecs {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : (Fin i) → (BitVec j) :=
  fun a => vec_to_BitVec (M a)

def flatten_matrix {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : BitVec (i * j) :=
  BitVec.appendList M.toBitVecs

def BitVecMatrix {r n : Nat} (M : BitVec (r * n)) : Matrix (Fin r) (Fin n) (ZMod 2) :=
  fun i j => if M[i.val * n + j.val]! then 1 else 0

--function transforming error vector with limited support into index vector
def index_vec {n k : ℕ} (x : Fin n → ZMod 2) (hx : hammingNorm x ≤ k) (hx' : hammingNorm x ≠ 0) : Fin k → Fin n :=
  let S := Finset.univ.filter (fun j : Fin n => x j ≠ 0);
  let I : Fin (hammingNorm x) → Fin n := fun j =>
        (S.orderEmbOfFin rfl j)
  fun y => if h : y < hammingNorm x then I ⟨y, h⟩ else I ⟨hammingNorm x - 1, by apply Nat.sub_one_lt hx'⟩

lemma index_vec_eq_one_of_exists {n k : ℕ} {x : Fin n → ZMod 2} {hx : hammingNorm x ≤ k} {hx' : hammingNorm x ≠ 0}
  {y : Fin k} {i : Fin n}
  (h_ind : index_vec x hx hx' y = i) :
  x i ≠ 0 := by
    subst h_ind;
    unfold index_vec; split_ifs;
    · exact Finset.mem_filter.mp ( Finset.orderEmbOfFin_mem ( Finset.univ.filter fun j => x j ≠ 0 ) ( by aesop ) _ ) |>.2;
    · exact Finset.mem_filter.mp ( Finset.orderEmbOfFin_mem ( Finset.univ.filter fun j => x j ≠ 0 ) rfl _ ) |>.2

def T : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 1, 1;
    0, 1, 0, 1, 1, 0, 1;
    0, 0, 1, 0, 1, 1, 1]



lemma vec_to_BitVec'_correct {i n : ℕ} {r : (Fin i) → (Fin n)} (j : Fin i) :
  (vec_to_BitVec' r).extractLsb' (j * (Nat.clog 2 n)) (Nat.clog 2 n) = r j := by
  induction' i with i ih
  · fin_cases j
  · refine Fin.lastCases ?last ?cast j
    · rcases i with _ | i
      · refine BitVec.eq_of_getElem_eq ?_
        intro bit hbit
        rw [BitVec.getElem_extractLsb' hbit]
        simp [vec_to_BitVec']
        rw [BitVec.getLsbD_ofNat]
        rw [BitVec.getElem_eq_testBit_toNat]
        simp only [BitVec.toNat_ofNat]
        have hlt : (r 0).val < 2 ^ Nat.clog 2 n :=
          lt_of_lt_of_le (r 0).2 (Nat.le_pow_clog one_lt_two n)
        rw [Nat.mod_eq_of_lt hlt]
        simp [hbit]
      · refine BitVec.eq_of_getElem_eq ?_
        intro bit hbit
        rw [BitVec.getElem_extractLsb' hbit]
        simp [vec_to_BitVec']
        rw [BitVec.getLsbD_append]
        have hnot : ¬(i.succ * Nat.clog 2 n + bit < i.succ * Nat.clog 2 n) := by omega
        simp [hnot]
        rw [BitVec.getLsbD_eq_getElem hbit]
        have hfin : (⟨i + 1, by simp⟩ : Fin (i + 1 + 1)) = Fin.last (i + 1) := by
          ext
          simp [Fin.last]
        simp [hfin]
    · intro j
      rcases i with _ | i
      · fin_cases j
      · refine BitVec.eq_of_getElem_eq ?_
        intro bit hbit
        rw [BitVec.getElem_extractLsb' hbit]
        simp [vec_to_BitVec']
        rw [BitVec.getLsbD_append]
        have hlow : (↑j * Nat.clog 2 n + bit) < i.succ * Nat.clog 2 n := by
          nlinarith [j.2, hbit]
        simp [hlow]
        have hrec := congrArg (fun bv : BitVec (Nat.clog 2 n) => bv[bit])
          (ih (r := fun i : Fin (i + 1) => r ⟨i, by simp⟩) j)
        simpa only [BitVec.getElem_extractLsb' hbit] using hrec




lemma vec_to_BitVec_correct {j : ℕ} (r : (Fin j) → (ZMod 2)) (i : Fin j) : (vec_to_BitVec r)[i]! = ((r i).val == 1) := by
  simp [vec_to_BitVec]

lemma BitVec.getElemBang_eq_getLsbD {w : Nat} (x : BitVec w) (i : Nat) : x[i]! = x.getLsbD i := by
  change x[i]?.getD false = x.getLsbD i
  rw [←BitVec.getLsbD_eq_getElem?_getD]

lemma vec_to_BitVec_getElemBang {j : ℕ} (r : Fin j → ZMod 2) {i : ℕ} (hi : i < j) :
    (vec_to_BitVec r)[i]! = ((r ⟨i, hi⟩).val == 1) := by
  rw [BitVec.getElemBang_eq_getLsbD]
  simp [vec_to_BitVec, hi]

lemma BitVec_to_vec_correct {n : ℕ} (x : BitVec n) (i : Fin n) : (BitVec_to_vec x) i = x[i].toNat := by
  unfold BitVec_to_vec;
  grind

lemma vec_to_BitVec_BitVec_to_vec {n : ℕ} (x : BitVec n) : x = (vec_to_BitVec (BitVec_to_vec x)) := by
  ext i;
  unfold vec_to_BitVec;
  simp +decide [ BitVec_to_vec, BitVec.getElem_ofFnLE ];
  grind

/- --unused
lemma flatten_matrix_correct {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) (r : Fin i) (c : Fin j) :
   (flatten_matrix M)[(r * j) + c]! = ((M r c).val == 1) := sorry
-/

lemma loc_constraints_ascent
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (hl : ∀ (i : Fin n), loc_constraints_ith locs errs i)
  (hn : 0 < n := by omega)
 : loc_constraints locs errs := by
   -- We need to show that the constraints hold for each `c` in the base case.
   have h_loc_aux (c : ℕ) (hc : c < n) : loc_constraints_aux locs errs c := by
     induction' c with c ih;
     · exact hl ⟨ 0, hn ⟩;
     · exact ⟨ hl ⟨ c + 1, hc ⟩, ih ( Nat.lt_of_succ_lt hc ) ⟩;
   exact h_loc_aux _ ( Nat.sub_lt hn zero_lt_one )

lemma loc_constraints_descent
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (hl : loc_constraints locs errs)
  (i : Fin n)
  : loc_constraints_ith locs errs i := by
    contrapose! hl;
    -- By definition of `loc_constraints_aux`, if `loc_constraints_ith locs errs i` is false, then `loc_constraints_aux locs errs (n - 1)` must also be false.
    have h_aux_false : ∀ (c : ℕ), i.val ≤ c → ¬loc_constraints_aux locs errs c := by
      intro c hc
      induction' c with c ih;
      · cases i ; aesop;
      · cases hc.eq_or_lt <;> simp_all +decide [ loc_constraints_aux ];
    exact h_aux_false _ ( Nat.le_sub_one_of_lt i.2 )

lemma loc_constraints_ith_jth_aux_correct
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (i : ℕ) (hk : 0 < k)
  : loc_constraints_ith_jth_aux locs i (k - 1) =
      (∃ l : Fin k, locs.extractLsb' (l * nlog) nlog = i) := by
  have h_aux : ∀ j, j < k →
      (loc_constraints_ith_jth_aux locs i j ↔
        ∃ l : Fin k, l.val ≤ j ∧ locs.extractLsb' (l * nlog) nlog = i) := by
    intro j hj
    induction' j with j ih
    · constructor
      · intro h
        exact ⟨⟨0, hj⟩, by simp, by simpa [loc_constraints_ith_jth_aux, loc_constraints_ith_jth] using h⟩
      · rintro ⟨l, hl, hloc⟩
        have hl0 : l = ⟨0, hj⟩ := by
          apply Fin.ext
          exact Nat.eq_zero_of_le_zero hl
        simpa [loc_constraints_ith_jth_aux, loc_constraints_ith_jth, hl0] using hloc
    · constructor
      · intro h
        simp only [loc_constraints_ith_jth_aux, loc_constraints_ith_jth] at h
        rcases h with h | h
        · exact ⟨⟨j + 1, hj⟩, le_rfl, by simpa⟩
        · rcases (ih (Nat.lt_of_succ_lt hj)).1 h with ⟨l, hl, hloc⟩
          exact ⟨l, Nat.le_trans hl (Nat.le_succ j), hloc⟩
      · rintro ⟨l, hl, hloc⟩
        simp only [loc_constraints_ith_jth_aux, loc_constraints_ith_jth]
        by_cases hlj : l.val = j + 1
        · left
          have hlfin : l = ⟨j + 1, hj⟩ := Fin.ext hlj
          simpa [hlfin] using hloc
        · right
          apply (ih (Nat.lt_of_succ_lt hj)).2
          exact ⟨l, Nat.le_of_lt_succ (lt_of_le_of_ne hl hlj), hloc⟩
  apply propext
  constructor
  · intro h
    rcases (h_aux (k - 1) (Nat.sub_lt hk zero_lt_one)).1 h with ⟨l, _, hloc⟩
    exact ⟨l, hloc⟩
  · rintro ⟨l, hloc⟩
    apply (h_aux (k - 1) (Nat.sub_lt hk zero_lt_one)).2
    exact ⟨l, Nat.le_sub_one_of_lt l.2, hloc⟩

lemma fin_to_bitvec_clog {n : ℕ} {x : Fin n} : (x : BitVec (Nat.clog 2 n)) = BitVec.ofNat (Nat.clog 2 n) x := by
  simp only [BitVec.natCast_eq_ofNat]

lemma BitVec.ofNat_clog_eq_iff {n : ℕ} {x y : Fin n} :
  BitVec.ofNat (Nat.clog 2 n) x = BitVec.ofNat (Nat.clog 2 n) y ↔ x = y := by
  constructor
  · intro h
    apply Fin.ext
    have ht := congrArg BitVec.toNat h
    simp [
      BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_of_lt_of_le x.2 (Nat.le_pow_clog one_lt_two n)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le y.2 (Nat.le_pow_clog one_lt_two n))] at ht
    exact ht
  · intro h
    rw [h]

lemma loc_constraints_of_index {n k : ℕ} (x : Fin n → (ZMod 2)) (hx : hammingNorm x ≤ k) (hx' : hammingNorm x ≠ 0) :
  loc_constraints (vec_to_BitVec' (index_vec x hx hx')) (vec_to_BitVec x) := by
  have hk : 0 < k := lt_of_lt_of_le (Nat.pos_of_ne_zero hx') hx
  apply loc_constraints_ascent (hn := by
    by_contra h
    push_neg at h
    interval_cases n
    simp [hammingNorm] at hx')
  intro i
  unfold loc_constraints_ith
  rw [loc_constraints_ith_jth_aux_correct _ _ hk]
  by_cases h : (x i = 0)
  · simp [vec_to_BitVec, h]
    intro y
    rw [vec_to_BitVec'_correct, fin_to_bitvec_clog, BitVec.ofNat_clog_eq_iff]
    intro h_f
    apply absurd h
    apply index_vec_eq_one_of_exists h_f
  · have hval : (x i).val = 1 := zmod2_val_eq_one_of_ne_zero (x i) h
    simp [vec_to_BitVec, hval]
    let S := Finset.univ.filter (fun j : Fin n => x j ≠ 0)
    have hiS : i ∈ S := by simp [S, h]
    have hi_range : i ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin S rfl]
      exact hiS
    rcases hi_range with ⟨j, hj⟩
    have hjlt : (j : ℕ) < hammingNorm x := by
      simpa [S, hammingNorm] using j.2
    refine ⟨⟨j, lt_of_lt_of_le hjlt hx⟩, ?_⟩
    rw [vec_to_BitVec'_correct, fin_to_bitvec_clog, BitVec.ofNat_clog_eq_iff]
    simp [index_vec, S]
    rw [if_pos hjlt]
    simpa [S] using hj

lemma fin_toBitVec_clog_le_iff {n : ℕ} {x y : Fin n} :
    (x : BitVec (Nat.clog 2 n)) ≤ (y : BitVec (Nat.clog 2 n)) ↔ x ≤ y := by
  simp only [BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Fin.le_def]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le x.2 (Nat.le_pow_clog one_lt_two n))]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le y.2 (Nat.le_pow_clog one_lt_two n))]

lemma fin_toBitVec_clog_le_allOnes {n : ℕ} (x : Fin n) :
    (x : BitVec (Nat.clog 2 n)) ≤ BitVec.allOnes (Nat.clog 2 n) := by
  rw [BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le x.2 (Nat.le_pow_clog one_lt_two n))]
  rw [BitVec.toNat_allOnes]
  exact Nat.le_sub_one_of_lt (lt_of_lt_of_le x.2 (Nat.le_pow_clog one_lt_two n))

lemma symmetry_constraints_aux_iff_index
    {n k : ℕ} (x : Fin k → Fin n) :
    ∀ c, c < k → ∀ prev : BitVec (Nat.clog 2 n),
      symmetry_constraints_aux (vec_to_BitVec' x) c prev ↔
        (∀ i : Fin k, i.val ≤ c → (x i : BitVec (Nat.clog 2 n)) ≤ prev) ∧
        (∀ i j : Fin k, i ≤ j → j.val ≤ c → x i ≤ x j) := by
  intro c
  induction' c with c ih
  · intro hc prev
    constructor
    · intro h
      constructor
      · intro i hi
        have hi0 : i = ⟨0, hc⟩ := by
          apply Fin.ext
          exact Nat.eq_zero_of_le_zero hi
        subst hi0
        have h0 := vec_to_BitVec'_correct (r := x) ⟨0, hc⟩
        simp only [symmetry_constraints_aux, decide_eq_true_eq] at h
        rw [h0] at h
        exact h
      · intro i j hij hj
        have hj0 : j = ⟨0, hc⟩ := by
          apply Fin.ext
          exact Nat.eq_zero_of_le_zero hj
        subst hj0
        have hi0 : i = ⟨0, hc⟩ := by
          apply Fin.ext
          exact Nat.eq_zero_of_le_zero (Fin.le_def.mp hij)
        subst hi0
        exact le_rfl
    · intro h
      have h0 := vec_to_BitVec'_correct (r := x) ⟨0, hc⟩
      rw [symmetry_constraints_aux, h0]
      simpa only [decide_eq_true_eq] using h.1 ⟨0, hc⟩ le_rfl
  · intro hc prev
    have hc' : c < k := Nat.lt_of_succ_lt hc
    have hval :
        (vec_to_BitVec' x).extractLsb' ((c + 1) * Nat.clog 2 n) (Nat.clog 2 n) =
          (x ⟨c + 1, hc⟩ : BitVec (Nat.clog 2 n)) := by
      simpa using vec_to_BitVec'_correct (r := x) ⟨c + 1, hc⟩
    constructor
    · intro h
      simp only [symmetry_constraints_aux, hval, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hle_prev, htail⟩
      rcases (ih hc' (x ⟨c + 1, hc⟩)).1 htail with ⟨hprev, hmono⟩
      constructor
      · intro i hi
        rcases hi.eq_or_lt with hi_eq | hi_lt
        · have hi_fin : i = ⟨c + 1, hc⟩ := by
            apply Fin.ext
            exact hi_eq
          subst hi_fin
          exact hle_prev
        · have hi_prev := hprev i (Nat.le_of_lt_succ hi_lt)
          rw [BitVec.le_def] at hi_prev hle_prev ⊢
          omega
      · intro i j hij hj
        rcases hj.eq_or_lt with hj_eq | hj_lt
        · have hj_fin : j = ⟨c + 1, hc⟩ := by
            apply Fin.ext
            exact hj_eq
          subst hj_fin
          rcases (Fin.le_def.mp hij).eq_or_lt with hi_eq | hi_lt
          · have hi_fin : i = ⟨c + 1, hc⟩ := by
              apply Fin.ext
              exact hi_eq
            subst hi_fin
            exact le_rfl
          · rw [←fin_toBitVec_clog_le_iff]
            exact hprev i (Nat.le_of_lt_succ hi_lt)
        · exact hmono i j hij (Nat.le_of_lt_succ hj_lt)
    · intro h
      simp only [symmetry_constraints_aux, hval, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact h.1 ⟨c + 1, hc⟩ le_rfl
      · apply (ih hc' (x ⟨c + 1, hc⟩)).2
        constructor
        · intro i hi
          rw [fin_toBitVec_clog_le_iff]
          exact h.2 i ⟨c + 1, hc⟩ (Fin.mk_le_mk.mpr (Nat.le_succ_of_le hi)) le_rfl
        · intro i j hij hj
          exact h.2 i j hij (Nat.le_trans hj (Nat.le_succ c))

lemma symmetry_constraints_iff_index {n k : ℕ} (x : Fin k → Fin n) :
  symmetry_constraints (vec_to_BitVec' x) ↔ ∀ i j, i ≤ j → x i ≤ x j := by
  by_cases hk : k = 0
  · subst hk
    simp [symmetry_constraints, symmetry_constraints_aux, BitVec.le_def, BitVec.toNat_allOnes]
    exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (pow_pos (by norm_num) _))
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [symmetry_constraints]
    rw [symmetry_constraints_aux_iff_index x (k - 1) (Nat.sub_lt hkpos zero_lt_one)]
    constructor
    · intro h i j hij
      exact h.2 i j hij (Nat.le_sub_one_of_lt j.2)
    · intro h
      constructor
      · intro i _
        exact fin_toBitVec_clog_le_allOnes (x i)
      · intro i j hij _
        exact h i j hij

lemma BitVec.shift_extract_eq {n k : ℕ} (M : BitVec (k * n)) (r : ℕ) :
   (M >>> (r * n)).extractLsb' 0 n = M.extractLsb' (r * n) n := by
   -- 1. Bitvectors are equal if all their bits are equal.
  ext i hi
  simp only [getElem_extractLsb', zero_add, getLsbD_ushiftRight]



lemma row_correct {k n : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (r : Fin k) :
  (flatten_matrix M).row r = vec_to_BitVec (M r) := by
    unfold BitVec.row
    rw [BitVec.shift_extract_eq]
    -- We'll use induction on the number of rows `k` to prove the equality.
    induction' k with k ih;
    · fin_cases r;
    · refine' Fin.lastCases _ _ r;
      · rcases k with ( _ | k ) <;> simp +decide [ *, flatten_matrix ];
        · aesop;
        · refine' BitVec.eq_of_getElem_eq _;
          intro i hi; simp +decide [ BitVec.row, BitVec.appendList ] ;
          nontriviality;
          rw [ BitVec.getLsbD_append ] ; aesop;
      · intro i;
        convert ih ( fun r => M ( Fin.castSucc r ) ) i using 1;
        unfold flatten_matrix;
        rcases k with ( _ | k ) <;> simp_all +decide [ BitVec.appendList ];
        · fin_cases i;
        ·
          ext j;
          rw [ BitVec.getElem_extractLsb', BitVec.getElem_extractLsb' ];
          rw [ BitVec.getLsbD_cast ];
          rw [ BitVec.getLsbD_append ];
          split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
          · congr! 1;
          · nlinarith [ Fin.is_lt i ]

def bitVecToFin {k : ℕ} [NeZero k] (x : BitVec (Nat.clog 2 k)) : Fin k :=
  ⟨x.toNat % k, Nat.mod_lt _ (Nat.pos_of_neZero _)⟩

theorem bitVecToFin_val_eq {k : ℕ} [NeZero k] (x : BitVec (Nat.clog 2 k)) (hx : x.toNat < k) :
    (bitVecToFin x).val = x.toNat := by
  -- Unfold the definition of bitVecToFin
  simp [bitVecToFin]
  -- Apply the property that n % k = n when n < k
  apply Nat.mod_eq_of_lt hx

theorem fin_toBitVec_toNat_eq {k : ℕ} [NeZero k] (x : Fin k) :
  (x : BitVec (Nat.clog 2 k)).toNat = x := by
  simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  apply lt_of_lt_of_le x.isLt
  apply Nat.le_pow_clog (one_lt_two)

theorem fin_toBitVec_toNat_eq' {k : ℕ} [NeZero k] (x : Fin k) :
  bitVecToFin x = x := by
  simp only [Fin.ext_iff, bitVecToFin, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.mod_eq_of_lt]
    apply lt_of_lt_of_le x.isLt _
    apply Nat.le_pow_clog (one_lt_two)
  apply Nat.mod_lt_of_lt x.isLt


/-
Older runtime-indexed row extraction.  The maintained examples use the
nat-indexed `BitVec.row` path and `mutually_orth_nat_correct` below.
lemma row_bv_correct {k n : ℕ} [NeZero k] (M : Matrix (Fin k) (Fin n) (ZMod 2)) (r : BitVec (Nat.clog 2 k)) :
  (flatten_matrix M).row_bv r = vec_to_BitVec (M (bitVecToFin r)) := by
  ...
-/


lemma BitVec_row_correct {k n : ℕ} [NeZero k] (M : Matrix (Fin k) (Fin n) (ZMod 2)) (r : BitVec (Nat.clog 2 k)) (hr : r.toNat < k) :
  (flatten_matrix M).row r.toNat = vec_to_BitVec (M (bitVecToFin r)) := by
  rw [←row_correct, bitVecToFin_val_eq _ hr]





lemma flatten_matrix_get {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) (r : Fin i) (c : Fin j) :
    (flatten_matrix M)[r.val * j + c.val]! = ((M r c).val == 1) := by
  rw [BitVec.getElemBang_eq_getLsbD]
  have h := congrArg (fun bv : BitVec j => bv.getLsbD c.val) (row_correct M r)
  simp [BitVec.row, vec_to_BitVec] at h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

lemma flatten_BitVecMatrix_id {r n : ℕ} (M : BitVec (r * n)) : flatten_matrix (BitVecMatrix M) = M := by
  by_cases hn : n = 0
  · subst hn
    apply BitVec.eq_of_getElem_eq
    intro i hi
    omega
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hr : i / n < r := (Nat.div_lt_iff_lt_mul hn_pos).mpr hi
    have hc : i % n < n := Nat.mod_lt i hn_pos
    have hget := flatten_matrix_get (BitVecMatrix M) ⟨i / n, hr⟩ ⟨i % n, hc⟩
    have heq : (⟨i / n, hr⟩ : Fin r).val * n + (⟨i % n, hc⟩ : Fin n).val = i := by
      change i / n * n + i % n = i
      rw [Nat.mul_comm (i / n) n]
      exact Nat.div_add_mod i n
    simp only [BitVecMatrix, heq] at hget
    rw [BitVec.getElemBang_eq_getLsbD, BitVec.getLsbD_eq_getElem hi] at hget
    generalize hbit : M[i]! = bit at hget
    rw [BitVec.getElemBang_eq_getLsbD, BitVec.getLsbD_eq_getElem hi] at hbit
    rw [hget, ←hbit]
    cases M[i] <;> decide

lemma zmod2_dot_bool_step (a b s : ZMod 2) :
    (((a.val == 1) && (b.val == 1)) ^^ (s == 1)) =
      (s + a * b == 1) := by
  fin_cases a <;> fin_cases b <;> fin_cases s <;> native_decide

def dot_product_correct {n : ℕ} [NeZero n] (x y : Fin n → (ZMod 2)):
  (vec_to_BitVec x).dot_product (vec_to_BitVec y) =  ( x ⬝ᵥ y == 1) := by
  have h_aux : ∀ idx, (hidx : idx < n) →
      dot_product_aux (vec_to_BitVec x) (vec_to_BitVec y) idx hidx =
        ((∑ t ∈ Finset.range (idx + 1),
            if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0) == 1) := by
    intro idx hidx
    induction' idx with idx ih
    · change ((vec_to_BitVec x)[0] && (vec_to_BitVec y)[0]) =
        ((∑ t ∈ Finset.range (0 + 1),
            if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0) == 1)
      simp [hidx]
      simp [vec_to_BitVec, hidx]
      have hbool (a b : ZMod 2) : ((a.val == 1) && (b.val == 1)) = (a * b == 1) := by
        fin_cases a <;> fin_cases b <;> native_decide
      exact hbool (x ⟨0, hidx⟩) (y ⟨0, hidx⟩)
    · have hidx' : idx < n := Nat.lt_of_succ_lt hidx
      change (((vec_to_BitVec x)[idx + 1] && (vec_to_BitVec y)[idx + 1]) ^^
              dot_product_aux (vec_to_BitVec x) (vec_to_BitVec y) idx hidx') =
        ((∑ t ∈ Finset.range (idx + 1 + 1),
            if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0) == 1)
      rw [ih hidx']
      conv_rhs => rw [Finset.sum_range_succ]
      simp [vec_to_BitVec, hidx]
      simpa +decide using
        (zmod2_dot_bool_step (x ⟨idx + 1, hidx⟩) (y ⟨idx + 1, hidx⟩)
          (∑ t ∈ Finset.range (idx + 1),
            if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0))
  unfold BitVec.dot_product dotProduct
  rw [h_aux (n - 1) (Nat.sub_lt (NeZero.pos n) zero_lt_one)]
  congr 1
  rw [Nat.sub_one_add_one (NeZero.ne n)]
  rw [← Fin.sum_univ_eq_sum_range
    (fun t => if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0) n]
  apply Finset.sum_congr rfl
  intro i _hi
  simp

lemma parity_constraints_descent {stabdim n : ℕ} [NeZero n] {stabs : BitVec (stabdim * n)} {errs : BitVec n} {r : Fin stabdim} (hpc : parity_constraints stabs errs) :
  !(errs.dot_product (stabs.row r)) := by
    contrapose! hpc; simp_all +decide [ parity_constraints ] ;
    have h_ind : ∀ r' : ℕ, r' ≤ stabdim - 1 → r.val ≤ r' → parity_constraints_aux stabs errs r' = false := by
      intro r' hr' hr'_le; induction' hr' : r' - r.val using Nat.strong_induction_on with r' ih generalizing r'; rcases r' with ( _ | r' ) <;> simp_all +decide [ Nat.succ_eq_add_one, parity_constraints_aux ] ;
      grind +ring;
    exact h_ind _ le_rfl ( Nat.le_sub_one_of_lt r.2 )

lemma parity_constraints_ascent {stabdim n : ℕ} [NeZero n] {stabs : BitVec (stabdim * n)}
{errs : BitVec n} (hpaux : ∀ (r : Fin stabdim), !(errs.dot_product (stabs.row r)))
 : parity_constraints stabs errs := by
   by_cases h : 0 < stabdim <;> simp_all +decide [ parity_constraints ];
   · -- By induction on $c$, we can show that $parity\_constraints\_aux stabs errs c$ is true for all $c < stabdim$.
     have h_ind : ∀ c < stabdim, parity_constraints_aux stabs errs c = true := by
       intro c hc; induction' c with c ih <;> simp_all +decide [ parity_constraints_aux ] ;
       · exact hpaux ⟨ 0, hc ⟩;
       · exact ⟨ hpaux ⟨ c + 1, hc ⟩, ih ( Nat.lt_of_succ_lt hc ) ⟩;
     exact h_ind _ ( Nat.pred_lt h.ne' );
   · cases stabs;
     cases ‹Fin ( 2 ^ ( stabdim * n ) ) › ; simp_all +decide [ BitVec.row ];
     have h_dot_product_zero : ∀ (x : Fin n → ZMod 2), (vec_to_BitVec x).dot_product (vec_to_BitVec (fun _ => 0)) = false := by
       intros x
       have h_dot_product_zero : (vec_to_BitVec x).dot_product (vec_to_BitVec (fun _ => 0)) = (x ⬝ᵥ (fun _ => 0) == 1) := by
         convert dot_product_correct x ( fun _ => 0 ) using 1;
       simp_all +decide [ dotProduct ];
     convert h_dot_product_zero ( BitVec_to_vec errs ) using 1;
     congr! 1;
     · grind +suggestions;
     · simp +decide [ BitVec.extractLsb', vec_to_BitVec ];
       aesop

lemma parity_constraints_correct {k n : ℕ} [NeZero n] {M : Matrix (Fin k) (Fin n) (ZMod 2)}
  {x : Fin n → ZMod 2} :
  parity_constraints (flatten_matrix M) (vec_to_BitVec x) ↔ x ∈ LinearMap.ker M.toLin' := by
  rw [LinearMap.mem_ker]
  have pc_correct_aux : ∀ (i : Fin k),
  !((vec_to_BitVec x).dot_product ((flatten_matrix M).row i)) ↔ (M.mulVec x) i = 0 := by
    intro i
    rw [row_correct, dot_product_correct]
    simp only [Matrix.mulVec, dotProduct]
    rw [show ∑ i_1, x i_1 * M i i_1 = ∑ x_1, M i x_1 * x x_1 from
      Finset.sum_congr rfl (fun j _ => mul_comm (x j) (M i j))]
    constructor
    · intro h
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at h
      exact (ZMod.val_eq_zero _).mp (zmod2_val_eq_zero_of_ne_one _ h)
    · intro h
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne]
      rw [h]; decide
  rw [Matrix.toLin'_apply]
  constructor
  · intro hpar
    ext i
    apply (pc_correct_aux i).1
    apply parity_constraints_descent hpar
  intro hmul
  apply parity_constraints_ascent
  intro r
  apply (pc_correct_aux r).2
  rw [hmul]
  simp only [Pi.zero_apply]

lemma rowspace_constraints_descent {kerdim n} [NeZero n] {ker : BitVec (kerdim * n)}
{errs : BitVec n} (r : Fin kerdim) (hr : (errs.dot_product (ker.row r)))
: rowspace_constraints ker errs := by
  have h_aux : ∀ (r : ℕ), r ≤ kerdim - 1 → (∃ i : Fin kerdim, i.val ≤ r ∧ !(errs.dot_product (ker.row i)) = false) → rowspace_constraints_aux ker errs r = true := by
    intros r hr ih; induction' r with r ih <;> simp_all +decide [ rowspace_constraints_aux ] ;
    · grind;
    · grind +ring
  generalize_proofs at *; (
  exact h_aux _ le_rfl ⟨ r, Nat.le_sub_one_of_lt r.2, by simpa using hr ⟩)

lemma rowspace_constraints_ascent {kerdim n : ℕ} [NeZero kerdim] [NeZero n] {ker : BitVec (kerdim * n)}
{errs : BitVec n} (hconstr : rowspace_constraints ker errs)
: ∃ (r : Fin kerdim), (errs.dot_product (ker.row r)) := by
  unfold rowspace_constraints at hconstr
  have h_aux : ∀ idx, idx < kerdim →
      rowspace_constraints_aux ker errs idx = true →
      ∃ r : Fin kerdim, r.val ≤ idx ∧ errs.dot_product (ker.row r) := by
    intro idx hidx h
    induction' idx with idx ih
    · exact ⟨⟨0, hidx⟩, le_rfl, by simpa [rowspace_constraints_aux] using h⟩
    · by_cases hlast : errs.dot_product (ker.row (idx + 1))
      · exact ⟨⟨idx + 1, hidx⟩, le_rfl, hlast⟩
      · have hprev : rowspace_constraints_aux ker errs idx = true := by
          simpa [rowspace_constraints_aux, hlast] using h
        rcases ih (Nat.lt_of_succ_lt hidx) hprev with ⟨r, hrle, hr⟩
        exact ⟨r, Nat.le_trans hrle (Nat.le_succ idx), hr⟩
  rcases h_aux (kerdim - 1) (Nat.sub_lt (NeZero.pos kerdim) zero_lt_one) hconstr with
    ⟨r, _, hr⟩
  exact ⟨r, hr⟩

lemma rowspace_constraints_correct {k₁ k₂ n : ℕ}
  [NeZero k₂] [NeZero n]
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)}
  {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)}
  (hK : M₂.rowSpace = (LinearMap.ker (M₁.toLin')))
  {x : Fin n → ZMod 2} :
  rowspace_constraints (flatten_matrix M₂) (vec_to_BitVec x) ↔ x ∉ M₁.rowSpace := by
  rw [not_mem_rowspace_iff_exists_mem_ker]
  constructor
  · intro hrc
    rcases rowspace_constraints_ascent hrc with ⟨r, hrp⟩
    refine ⟨M₂ r, ⟨?_, ?_⟩⟩
    · rw [←hK]
      exact Matrix.row_mem_rowSpace
    rw [row_correct, dot_product_correct x (M₂ r), dotProduct_comm] at hrp
    simp only [beq_iff_eq] at hrp
    assumption
  rintro ⟨y, ⟨hy₁, hy₂⟩⟩
  rw [←hK] at hy₁
  obtain ⟨s, hs⟩ := exists_row_of_exists_mem_rowspace_non_orth hy₁ hy₂
  apply rowspace_constraints_descent s
  rwa [row_correct, dot_product_correct, dotProduct_comm, beq_iff_eq]

lemma nonzero_correct {r : ℕ} (x : Fin r → (ZMod 2))
  : nonzero (vec_to_BitVec x) ↔ x ≠ 0 := by
    -- By definition of `nonzero`, we have that `nonzero (vec_to_BitVec x) = true` if and only if there exists some `i` such that `x i ≠ 0`.
    simp [nonzero];
    by_cases hr : r = 0 <;> simp_all +decide [ funext_iff, nonzero_aux ];
    · subst hr; exact fun i => Fin.elim0 i;
    · constructor;
      · intro h_nonzero
        by_contra h_contra
        push_neg at h_contra
        have h_zero : ∀ i : Fin r, x i = 0 := by
          exact h_contra
        have h_zero_bitvec : vec_to_BitVec x = 0 := by
          ext i; simp [vec_to_BitVec, h_zero]
        have h_zero_nonzero : nonzero_aux (vec_to_BitVec x) (r - 1) = false := by
          rw [h_zero_bitvec];
          induction' r - 1 with r ih <;> simp +decide [ *, nonzero_aux ];
          · cases r <;> aesop;
          · cases ‹ℕ› <;> simp_all +decide [ nonzero_aux ];
            · rcases r with ( _ | _ | r ) <;> simp_all +decide [ BitVec.getLsb ];
            · cases r <;> simp_all +decide [ BitVec.getLsb ];
              cases ‹ℕ› <;> simp_all +decide [ BitVec.getLsb ];
              grind
        exact absurd h_zero_nonzero (by simp [h_nonzero]);
      · rintro ⟨ i, hi ⟩;
        -- Since $x i \neq 0$, the $i$-th bit of $vec_to_BitVec x$ is 1.
        have h_bit : (vec_to_BitVec x)[i]! = true := by
          rw [ vec_to_BitVec_correct ];
          have hval : (x i).val = 1 := zmod2_val_eq_one_of_ne_zero (x i) hi;
          simpa [ hval ];
        -- Since the i-th bit is 1, the nonzero_aux function will return true.
        have h_nonzero_aux : ∀ (j : ℕ) (hj : i.val ≤ j), nonzero_aux (vec_to_BitVec x) j = true := by
          intro j hj; induction' j with j ih <;> simp_all +decide [ nonzero_aux ] ;
          · grind;
          · grind +splitImp;
        exact h_nonzero_aux _ ( Nat.le_sub_one_of_lt i.2 )

lemma dot_col_aux_eq_dot_product_aux {r n : ℕ} [NeZero r]
    (M : Matrix (Fin r) (Fin n) (ZMod 2)) (coeffs : Fin r → ZMod 2) (c : Fin n) :
    ∀ idx, (hr : idx < r) →
      dot_col_aux (vec_to_BitVec coeffs) (flatten_matrix M) c.val idx =
        dot_product_aux (vec_to_BitVec coeffs) (vec_to_BitVec (fun row => M row c)) idx hr := by
  intro idx hidx
  induction' idx with idx ih
  · change ((vec_to_BitVec coeffs)[0]! &&
        (flatten_matrix M)[0 * n + c.val]!) =
      ((vec_to_BitVec coeffs)[0] &&
        (vec_to_BitVec (fun row => M row c))[0])
    rw [vec_to_BitVec_getElemBang coeffs hidx]
    rw [flatten_matrix_get M ⟨0, hidx⟩ c]
    simp [vec_to_BitVec, hidx]
  · have hidx' : idx < r := Nat.lt_of_succ_lt hidx
    change (((vec_to_BitVec coeffs)[idx + 1]! &&
        (flatten_matrix M)[(idx + 1) * n + c.val]!) ^^
        dot_col_aux (vec_to_BitVec coeffs) (flatten_matrix M) c.val idx) =
      (((vec_to_BitVec coeffs)[idx + 1] &&
        (vec_to_BitVec (fun row => M row c))[idx + 1]) ^^
        dot_product_aux (vec_to_BitVec coeffs)
          (vec_to_BitVec (fun row => M row c)) idx hidx')
    rw [ih hidx']
    rw [vec_to_BitVec_getElemBang coeffs hidx]
    rw [flatten_matrix_get M ⟨idx + 1, hidx⟩ c]
    simp [vec_to_BitVec, hidx]

lemma dot_col_zero_correct {r n : ℕ} [NeZero r]
    (M : Matrix (Fin r) (Fin n) (ZMod 2)) (coeffs : Fin r → ZMod 2) (c : Fin n) :
    dot_col_zero (vec_to_BitVec coeffs) (flatten_matrix M) c.val =
      !((M.vecMul coeffs c) == 1) := by
  by_cases hr : r = 0
  · subst r
    simp [dot_col_zero, dot_col_aux, Matrix.vecMul, dotProduct]
  · have hidx : r - 1 < r := Nat.sub_lt (Nat.pos_of_ne_zero hr) zero_lt_one
    have hd := dot_col_aux_eq_dot_product_aux M coeffs c (r - 1) hidx
    unfold dot_col_zero
    rw [hd]
    have hdp := dot_product_correct coeffs (fun row => M row c)
    unfold BitVec.dot_product at hdp
    rw [hdp]
    simp [Matrix.vecMul, dotProduct]

lemma zmod2_ne_one_iff_eq_zero (a : ZMod 2) : a ≠ 1 ↔ a = 0 := by
  constructor
  · intro h
    exact (ZMod.val_eq_zero a).mp (zmod2_val_eq_zero_of_ne_one a h)
  · intro h
    rw [h]
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1)

lemma all_dot_zero_aux_correct {r n : ℕ} [NeZero r]
    (M : Matrix (Fin r) (Fin n) (ZMod 2)) (coeffs : Fin r → ZMod 2) :
    ∀ idx, idx < n →
      (all_dot_zero_aux (vec_to_BitVec coeffs) (flatten_matrix M) idx ↔
        ∀ c : Fin n, c.val ≤ idx → M.vecMul coeffs c = 0) := by
  intro idx hidx
  induction' idx with idx ih
  · rw [show all_dot_zero_aux (vec_to_BitVec coeffs) (flatten_matrix M) 0 =
        dot_col_zero (vec_to_BitVec coeffs) (flatten_matrix M) 0 by rfl]
    have hdz := dot_col_zero_correct M coeffs ⟨0, hidx⟩
    rw [hdz]
    constructor
    · intro h c hc
      have hc0 : c = ⟨0, hidx⟩ := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero hc
      subst hc0
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at h
      exact (zmod2_ne_one_iff_eq_zero _).1 h
    · intro h
      have hz := h ⟨0, hidx⟩ le_rfl
      rw [hz]
      decide
  · have hidx' : idx < n := Nat.lt_of_succ_lt hidx
    change ((dot_col_zero (vec_to_BitVec coeffs) (flatten_matrix M) (idx + 1) &&
        all_dot_zero_aux (vec_to_BitVec coeffs) (flatten_matrix M) idx) = true) ↔
      ∀ c : Fin n, c.val ≤ idx + 1 → M.vecMul coeffs c = 0
    rw [dot_col_zero_correct M coeffs ⟨idx + 1, hidx⟩]
    simp [ih hidx']
    constructor
    · rintro ⟨hlast, hprev⟩ c hc
      by_cases hcval : c.val = idx + 1
      · have hcfin : c = ⟨idx + 1, hidx⟩ := Fin.ext hcval
        subst hcfin
        exact (zmod2_ne_one_iff_eq_zero _).1 hlast
      · exact hprev c (Nat.le_of_lt_succ (lt_of_le_of_ne hc hcval))
    · intro h
      constructor
      · exact (zmod2_ne_one_iff_eq_zero _).2 (h ⟨idx + 1, hidx⟩ le_rfl)
      · intro c hc
        exact h c (Nat.le_trans hc (Nat.le_succ idx))

lemma all_dot_zero_correct {r n : ℕ} [NeZero r] (M : Matrix (Fin r) (Fin n) (ZMod 2)) (coeffs : Fin r → (ZMod 2))
  : all_dot_zero (vec_to_BitVec coeffs) (flatten_matrix M) ↔ M.vecMul coeffs = 0 := by
  by_cases hn : n = 0
  · subst n
    have hdot : dot_col_aux (vec_to_BitVec coeffs) (flatten_matrix M) 0 (r - 1) = false := by
      have haux0 : ∀ idx, dot_col_aux (vec_to_BitVec coeffs) (flatten_matrix M) 0 idx = false := by
        intro idx
        induction' idx with idx ih
        · simp [dot_col_aux, BitVec.getElemBang_eq_getLsbD]
        · simp [dot_col_aux, ih, BitVec.getElemBang_eq_getLsbD]
      exact haux0 (r - 1)
    simp [all_dot_zero, all_dot_zero_aux, dot_col_zero, hdot]
  · unfold all_dot_zero
    rw [all_dot_zero_aux_correct M coeffs (n - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hn) zero_lt_one)]
    constructor
    · intro h
      ext c
      exact h c (Nat.le_sub_one_of_lt c.2)
    · intro h c _
      rw [h]
      simp

lemma linear_indep_of_forall_vecmul_nz {r n : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod 2))
  : LinearIndependent (ZMod 2) M ↔ ∀ coeffs, coeffs ≠ 0 → M.vecMul coeffs ≠ 0 := by
    rw [ Fintype.linearIndependent_iff ];
    simp +decide [ funext_iff, Matrix.vecMul ];
    constructor;
    · exact fun h coeffs x hx => not_forall.mp fun h' => hx <| h coeffs h' x;
    · intro h g hg i; specialize h g i; contrapose! h; aesop;

lemma linear_indep_SAT_correct {r n : ℕ} [NeZero r] (M : Matrix (Fin r) (Fin n) (ZMod 2)) :
  LinearIndependent (ZMod 2) M ↔ linear_indep_SAT (flatten_matrix M) := by
  rw [linear_indep_of_forall_vecmul_nz]
  constructor
  · intro hcoeffs coeffs
    simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    by_cases h: BitVec_to_vec coeffs ≠ 0
    · right
      rw [←Bool.not_eq_true]
      rw [vec_to_BitVec_BitVec_to_vec coeffs, all_dot_zero_correct M]
      apply hcoeffs _ h
    left
    rwa [←Bool.not_eq_true, vec_to_BitVec_BitVec_to_vec coeffs, nonzero_correct]
  intro hlin coeffs hnz
  rw [ne_eq, ←all_dot_zero_correct]
  intro h_f
  unfold linear_indep_SAT at hlin
  simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
  ←Bool.not_eq_true] at hlin
  rcases hlin (vec_to_BitVec coeffs) with hz | hd
  · apply hz
    rwa [nonzero_correct]
  apply (hd h_f)

lemma mutually_orth_row_sat_aux_correct
    {k₁ k₂ n : ℕ}
    [NeZero n]
    (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
    (i : Fin k₁) :
    ∀ idx, idx < k₂ →
      (mutually_orth_row_sat_aux (flatten_matrix M₁) (flatten_matrix M₂) i.val idx ↔
        ∀ j : Fin k₂, j.val ≤ idx → M₁ i ⬝ᵥ M₂ j = 0) := by
  intro idx hidx
  induction' idx with idx ih
  · rw [show mutually_orth_row_sat_aux (flatten_matrix M₁) (flatten_matrix M₂) i.val 0 =
        !(((flatten_matrix M₁).row i.val).dot_product ((flatten_matrix M₂).row 0)) by rfl]
    rw [row_correct M₁ i, row_correct M₂ ⟨0, hidx⟩, dot_product_correct]
    constructor
    · intro h j hj
      have hj0 : j = ⟨0, hidx⟩ := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero hj
      subst hj0
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at h
      exact (zmod2_ne_one_iff_eq_zero _).1 h
    · intro h
      have hz := h ⟨0, hidx⟩ le_rfl
      rw [hz]
      decide
  · have hidx' : idx < k₂ := Nat.lt_of_succ_lt hidx
    change (!(((flatten_matrix M₁).row i.val).dot_product ((flatten_matrix M₂).row (idx + 1))) &&
        mutually_orth_row_sat_aux (flatten_matrix M₁) (flatten_matrix M₂) i.val idx ↔
      ∀ j : Fin k₂, j.val ≤ idx + 1 → M₁ i ⬝ᵥ M₂ j = 0)
    rw [row_correct M₁ i, row_correct M₂ ⟨idx + 1, hidx⟩, dot_product_correct]
    simp only [Bool.and_eq_true, ih hidx']
    constructor
    · rintro ⟨hlast, hprev⟩ j hj
      by_cases hjval : j.val = idx + 1
      · have hjfin : j = ⟨idx + 1, hidx⟩ := Fin.ext hjval
        subst hjfin
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at hlast
        exact (zmod2_ne_one_iff_eq_zero _).1 hlast
      · exact hprev j (Nat.le_of_lt_succ (lt_of_le_of_ne hj hjval))
    · intro h
      constructor
      · have hz := h ⟨idx + 1, hidx⟩ le_rfl
        rw [hz]
        decide
      · intro j hj
        exact h j (Nat.le_trans hj (Nat.le_succ idx))

lemma mutually_orth_sat_aux_correct
    {k₁ k₂ n : ℕ}
    [NeZero n]
    [NeZero k₂]
    (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
    ∀ idx, idx < k₁ →
      (mutually_orth_sat_aux (flatten_matrix M₁) (flatten_matrix M₂) idx ↔
        ∀ i : Fin k₁, i.val ≤ idx → ∀ j : Fin k₂, M₁ i ⬝ᵥ M₂ j = 0) := by
  intro idx hidx
  induction' idx with idx ih
  · rw [show mutually_orth_sat_aux (flatten_matrix M₁) (flatten_matrix M₂) 0 =
        mutually_orth_row_sat_aux (flatten_matrix M₁) (flatten_matrix M₂) 0 (k₂ - 1) by rfl]
    rw [mutually_orth_row_sat_aux_correct M₁ M₂ ⟨0, hidx⟩ (k₂ - 1)
      (Nat.sub_lt (NeZero.pos k₂) zero_lt_one)]
    constructor
    · intro h i hi j
      have hi0 : i = ⟨0, hidx⟩ := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero hi
      subst hi0
      exact h j (Nat.le_sub_one_of_lt j.2)
    · intro h j hj
      exact h ⟨0, hidx⟩ le_rfl j
  · have hidx' : idx < k₁ := Nat.lt_of_succ_lt hidx
    change (mutually_orth_row_sat_aux (flatten_matrix M₁) (flatten_matrix M₂) (idx + 1) (k₂ - 1) &&
        mutually_orth_sat_aux (flatten_matrix M₁) (flatten_matrix M₂) idx ↔
      ∀ i : Fin k₁, i.val ≤ idx + 1 → ∀ j : Fin k₂, M₁ i ⬝ᵥ M₂ j = 0)
    simp only [
      Bool.and_eq_true,
      mutually_orth_row_sat_aux_correct M₁ M₂ ⟨idx + 1, hidx⟩ (k₂ - 1)
        (Nat.sub_lt (NeZero.pos k₂) zero_lt_one),
      ih hidx']
    constructor
    · rintro ⟨hlast, hprev⟩ i hi j
      by_cases hival : i.val = idx + 1
      · have hifin : i = ⟨idx + 1, hidx⟩ := Fin.ext hival
        subst hifin
        exact hlast j (Nat.le_sub_one_of_lt j.2)
      · exact hprev i (Nat.le_of_lt_succ (lt_of_le_of_ne hi hival)) j
    · intro h
      constructor
      · intro j hj
        exact h ⟨idx + 1, hidx⟩ le_rfl j
      · intro i hi j
        exact h i (Nat.le_trans hi (Nat.le_succ idx)) j

theorem mutually_orth_nat_correct
  {k₁ k₂ n : ℕ}
  [NeZero k₁]
  [NeZero k₂]
  [NeZero n]
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
  bitvec_mutually_orth_nat (flatten_matrix M₁) (flatten_matrix M₂) ↔ M₁.mutually_orth_rows M₂ := by
  unfold bitvec_mutually_orth_nat
  rw [mutually_orth_sat_aux_correct M₁ M₂ (k₁ - 1) (Nat.sub_lt (NeZero.pos k₁) zero_lt_one)]
  constructor
  · intro h i j
    exact h i (Nat.le_sub_one_of_lt i.2) j
  · intro h i _hi j
    exact h i j

/-
Deprecated: this theorem uses `BitVec.row_bv`, whose runtime-indexed proof
path is not used by the maintained distance theorems.  Use
`mutually_orth_nat_correct` instead.
theorem mutually_orth_correct
  {k₁ k₂ n : ℕ}
  [NeZero k₁]
  [NeZero k₂]
  [NeZero n]
  (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
  bitvec_mutually_orth (flatten_matrix M₁) (flatten_matrix M₂) ↔ M₁.mutually_orth_rows M₂ := by
  constructor
  · intro h_orth i j
    unfold bitvec_mutually_orth at h_orth
    have hij:= (h_orth i j)
    simp only [Bool.not_and, Bool.or_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt, fin_toBitVec_toNat_eq] at hij
    rcases hij with (hij | hge) | hge
    · rw [row_bv_correct, row_bv_correct, dot_product_correct] at hij
      simp only [beq_eq_false_iff_ne, ne_eq, zmod2_ne_one_iff_eq_zero] at hij
      rw [fin_toBitVec_toNat_eq', fin_toBitVec_toNat_eq'] at hij
      assumption
    · sorry
    sorry


  intro h_orth i j
  simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, not_lt]
  by_cases hi : i.toNat < k₁
  · by_cases hj : j.toNat < k₂
    · refine Or.inl (Or.inl ?_)
      rw [row_bv_correct, row_bv_correct, dot_product_correct]
      simp only [beq_eq_false_iff_ne]
      rw [zmod2_ne_one_iff_eq_zero]
      apply h_orth
    refine Or.inr ?_
    sorry
  refine Or.inl (Or.inr ?_)
  sorry

-/



lemma inds_strict_mono_aux_descent {k r : ℕ} (inds : Fin r → Fin k) :
    ∀ (idx : ℕ) (hidx : idx < r) (prev : ℕ),
      inds_strict_mono_aux inds ⟨idx, hidx⟩ prev →
      (inds ⟨idx, hidx⟩).val < prev ∧
        ∀ t, (ht : t < idx) →
          inds ⟨t, Nat.lt_trans ht hidx⟩ <
            inds ⟨t + 1, lt_of_le_of_lt (Nat.succ_le_of_lt ht) hidx⟩ := by
  intro idx
  induction' idx with idx ih
  · intro hidx prev h
    simp [inds_strict_mono_aux] at h
    constructor
    · exact h
    · intro t ht
      omega
  · intro hidx prev h
    simp [inds_strict_mono_aux] at h
    rcases h with ⟨hhead, htail⟩
    have htail' := ih (Nat.lt_of_succ_lt hidx) (inds ⟨idx + 1, hidx⟩).val htail
    constructor
    · exact hhead
    · intro t ht
      by_cases htidx : t = idx
      · subst htidx
        exact htail'.1
      · exact htail'.2 t (lt_of_lt_of_le (lt_of_le_of_ne (Nat.le_of_lt_succ ht) htidx) le_rfl)

lemma inds_strict_mono_aux_ascent {k r : ℕ} (inds : Fin r → Fin k) :
    ∀ (idx : ℕ) (hidx : idx < r) (prev : ℕ),
      (inds ⟨idx, hidx⟩).val < prev →
      (∀ t, (ht : t < idx) →
          inds ⟨t, Nat.lt_trans ht hidx⟩ <
            inds ⟨t + 1, lt_of_le_of_lt (Nat.succ_le_of_lt ht) hidx⟩) →
      inds_strict_mono_aux inds ⟨idx, hidx⟩ prev := by
  intro idx
  induction' idx with idx ih
  · intro hidx prev hprev _hadj
    simp [inds_strict_mono_aux, hprev]
  · intro hidx prev hprev hadj
    simp [inds_strict_mono_aux, hprev]
    apply ih (Nat.lt_of_succ_lt hidx) (inds ⟨idx + 1, hidx⟩).val
    · exact hadj idx (Nat.lt_succ_self idx)
    · intro t ht
      exact hadj t (Nat.lt_trans ht (Nat.lt_succ_self idx))

lemma inds_strict_mono_correct {k r : ℕ} [NeZero r] (inds : Fin r → Fin k) :
  StrictMono inds ↔ inds_strict_mono inds := by
  rcases r with _ | r
  · exact False.elim (NeZero.ne (n := 0) rfl)
  · rw [Fin.strictMono_iff_lt_succ]
    constructor
    · intro h
      unfold inds_strict_mono
      apply inds_strict_mono_aux_ascent
      · exact (inds (Fin.last r)).2
      · intro t ht
        have hstep := h ⟨t, ht⟩
        simpa [Fin.castSucc, Fin.succ] using hstep
    · intro haux i
      unfold inds_strict_mono at haux
      have hd := inds_strict_mono_aux_descent inds r (Nat.lt_succ_self r) k haux
      have hstep := hd.2 i.val i.2
      simpa [Fin.castSucc, Fin.succ] using hstep
