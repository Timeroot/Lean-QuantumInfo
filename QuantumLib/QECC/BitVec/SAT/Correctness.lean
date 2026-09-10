/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Yi Lee, Runzhou Tao
-/

import Batteries.Data.BitVec.Lemmas
import Mathlib.Tactic.Cases
import Std.Tactic.BVDecide.LRAT.Internal.Clause
import QuantumLib.QECC.BitVec.LinearAlgebra.RowspaceKernel
import QuantumLib.QECC.BitVec.SAT.Encoding

/-!
# Correctness of the SAT encoding

Every constraint of `QuantumLib.QECC.BitVec.SAT.Encoding` is proved to say what it is meant to say:
`locConstraints` picks out an index vector, `symmetryConstraints` forces it to be monotone,
`parityConstraints` says the error is in the kernel, `rowspaceConstraints` says it is outside the
row space, and `linearIndepSAT` and `bitVecMutuallyOrthNat` characterise linear independence
and orthogonality of rows. This is what lets a `bv_decide` run on `BitVec`s discharge a statement
about matrices over `ZMod 2`.
-/

namespace QuantumLib

/-- A `ZMod 2` vector read as a vector of booleans, `1` becoming `true`. -/
instance coeVecZModTwoBool {n : ℕ} : Coe ((Fin n) → ZMod 2) ((Fin n) → Bool) where
  coe f := fun i => (f i).val == 1

/-- A `ZMod 2` vector as a bit vector, entry `i` becoming bit `i`. -/
def vecToBitVec {j : ℕ} (r : (Fin j) → (ZMod 2)) : BitVec j := BitVec.ofFnLE r

/-- A bit vector as a `ZMod 2` vector, inverse to `vecToBitVec`. -/
def bitVecToVec {n : ℕ} (x : BitVec n) : (Fin n) → (ZMod 2) := fun i => x[i].toNat

/-- A tuple of `j` indices below `n`, packed into a single bit vector giving each of them
`⌈log₂ n⌉` bits. -/
def vecToBitVec' {j n : ℕ} (r : (Fin j) → (Fin n)) : BitVec (j * (Nat.clog 2 n)) :=
  match j with
  | 0 => (BitVec.zero 0).cast (by rw [zero_mul])
  | 1 => (r 0)
  | j' + 1 => ((r ⟨j', Nat.lt_succ_self _⟩ : BitVec (Nat.clog 2 n)).append
      (vecToBitVec' (fun i : Fin j' => r ⟨i, by simp⟩))).cast (by rw [Nat.succ_mul, Nat.add_comm])

/-- The concatenation of `i` bit vectors of width `j`, with `f 0` in the low bits. -/
def _root_.BitVec.appendList {i j : ℕ} (f : (Fin i) → (BitVec j)) : BitVec (i * j) :=
  match i with
  | 0 => (BitVec.zero 0).cast (by rw [MulZeroClass.zero_mul])
  | 1 => (f 0).cast (by rw [one_mul])
  | i' + 1 => ((f ⟨i', Nat.lt_succ_self _⟩).append
      (BitVec.appendList (fun (j : Fin i') => f ⟨j, by simp⟩))).cast (by rw [Nat.succ_mul, add_comm])

/-- The rows of `M`, each as a bit vector. -/
def _root_.Matrix.toBitVecs {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : (Fin i) → (BitVec j) :=
  fun a => vecToBitVec (M a)

/-- An `i × j` matrix over `ZMod 2` as a single `BitVec (i * j)`, one row after another. -/
def flattenMatrix {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : BitVec (i * j) :=
  BitVec.appendList M.toBitVecs

/-- A `BitVec (r * n)` read back as an `r × n` matrix, inverse to `flattenMatrix`. -/
def BitVecMatrix {r n : ℕ} (M : BitVec (r * n)) : Matrix (Fin r) (Fin n) (ZMod 2) :=
  fun i j => if M[i.val * n + j.val]! then 1 else 0

/-- The support of a nonzero error of weight at most `k`, listed in increasing order as `k`
indices. When the weight is below `k` the list is padded with its last entry. -/
def indexVec {n k : ℕ} (x : Fin n → ZMod 2) (_hx : hammingNorm x ≤ k) (hx' : hammingNorm x ≠ 0) :
    Fin k → Fin n :=
  let S := Finset.univ.filter (fun j : Fin n => x j ≠ 0)
  let I : Fin (hammingNorm x) → Fin n := fun j =>
        (S.orderEmbOfFin rfl j)
  fun y => if h : y < hammingNorm x then I ⟨y, h⟩ else I ⟨hammingNorm x - 1, by apply Nat.sub_one_lt hx'⟩

/-- Every index listed by `indexVec` really is in the support. -/
lemma indexVec_eq_one_of_exists {n k : ℕ} {x : Fin n → ZMod 2} {hx : hammingNorm x ≤ k} {hx' : hammingNorm x ≠ 0}
    {y : Fin k} {i : Fin n}
    (h_ind : indexVec x hx hx' y = i) :
    x i ≠ 0 := by
  subst h_ind
  unfold indexVec
  split_ifs <;>
    exact Finset.mem_filter.mp
      (Finset.orderEmbOfFin_mem (Finset.univ.filter fun j => x j ≠ 0) rfl _) |>.2

/-- Reading the `j`-th field back out of a packed tuple of indices returns `r j`. -/
lemma vecToBitVec'_correct {i n : ℕ} {r : (Fin i) → (Fin n)} (j : Fin i) :
    (vecToBitVec' r).extractLsb' (j * (Nat.clog 2 n)) (Nat.clog 2 n) = r j := by
  induction' i with i ih
  · fin_cases j
  · refine Fin.lastCases ?last ?cast j
    · rcases i with _ | i
      · refine BitVec.eq_of_getElem_eq ?_
        intro bit hbit
        rw [BitVec.getElem_extractLsb' hbit]
        simp [vecToBitVec']
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
        simp [vecToBitVec']
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
        simp [vecToBitVec']
        rw [BitVec.getLsbD_append]
        have hlow : (↑j * Nat.clog 2 n + bit) < i.succ * Nat.clog 2 n := by
          nlinarith [j.2, hbit]
        simp [hlow]
        have hrec := congrArg (fun bv : BitVec (Nat.clog 2 n) => bv[bit])
          (ih (r := fun i : Fin (i + 1) => r ⟨i, by simp⟩) j)
        simp only [BitVec.getElem_extractLsb' hbit] at hrec
        rw [← BitVec.getLsbD_eq_getElem hlow, hrec]
        rfl

/-- Bit `i` of `vecToBitVec r` is set exactly when `r i = 1`. -/
lemma vecToBitVec_correct {j : ℕ} (r : (Fin j) → (ZMod 2)) (i : Fin j) :
    (vecToBitVec r)[i]! = ((r i).val == 1) := by
  simp [vecToBitVec]

/-- Panicking indexing of a bit vector agrees with `getLsbD`, both being `false` out of range. -/
lemma _root_.BitVec.getElemBang_eq_getLsbD {w : ℕ} (x : BitVec w) (i : ℕ) : x[i]! = x.getLsbD i := by
  change x[i]?.getD false = x.getLsbD i
  rw [←BitVec.getLsbD_eq_getElem?_getD]

/-- `vecToBitVec_correct` for an index given as a bare natural number. -/
lemma vecToBitVec_getElemBang {j : ℕ} (r : Fin j → ZMod 2) {i : ℕ} (hi : i < j) :
    (vecToBitVec r)[i]! = ((r ⟨i, hi⟩).val == 1) := by
  rw [BitVec.getElemBang_eq_getLsbD]
  simp [vecToBitVec, hi]

/-- Entry `i` of `bitVecToVec x` is bit `i` of `x`. -/
lemma bitVecToVec_correct {n : ℕ} (x : BitVec n) (i : Fin n) : (bitVecToVec x) i = x[i].toNat := by
  unfold bitVecToVec
  grind

/-- `vecToBitVec` undoes `bitVecToVec`. -/
lemma vecToBitVec_bitVecToVec {n : ℕ} (x : BitVec n) : x = (vecToBitVec (bitVecToVec x)) := by
  ext i
  unfold vecToBitVec
  simp +decide [bitVecToVec, BitVec.getElem_ofFnLE]
  grind

/-- `locConstraints` follows from its instance at each qubit. -/
lemma locConstraints_ascent
    {n nlog k : ℕ}
    (locs : BitVec (k * nlog))
    (errs : BitVec n)
    (hl : ∀ (i : Fin n), locConstraintsIth locs errs i)
    (hn : 0 < n := by omega) :
    locConstraints locs errs := by
  have h_loc_aux (c : ℕ) (hc : c < n) : locConstraintsAux locs errs c := by
    induction' c with c ih
    · exact hl ⟨0, hn⟩
    · exact ⟨hl ⟨c + 1, hc⟩, ih (Nat.lt_of_succ_lt hc)⟩
  exact h_loc_aux _ (Nat.sub_lt hn zero_lt_one)

/-- `locConstraints` gives its instance at each qubit. -/
lemma locConstraints_descent
    {n nlog k : ℕ}
    (locs : BitVec (k * nlog))
    (errs : BitVec n)
    (hl : locConstraints locs errs)
    (i : Fin n) :
    locConstraintsIth locs errs i := by
  contrapose! hl
  -- By definition of `locConstraintsAux`, if `locConstraintsIth locs errs i` is false, then
  -- `locConstraintsAux locs errs (n - 1)` must also be false.
  have h_aux_false : ∀ (c : ℕ), i.val ≤ c → ¬locConstraintsAux locs errs c := by
    intro c hc
    induction' c with c ih
    · rw [Nat.le_zero.mp hc] at hl
      exact hl
    · cases hc.eq_or_lt <;> simp_all +decide [locConstraintsAux]
  exact h_aux_false _ (Nat.le_sub_one_of_lt i.2)

/-- The unrolled disjunction `locConstraintsIthJthAux locs i (k - 1)` says that some field
of `locs` holds `i`. -/
lemma locConstraintsIthJthAux_correct
    {nlog k : ℕ}
    (locs : BitVec (k * nlog))
    (i : ℕ) (hk : 0 < k) :
    locConstraintsIthJthAux locs i (k - 1) =
      (∃ l : Fin k, locs.extractLsb' (l * nlog) nlog = i) := by
  have h_aux : ∀ j, j < k →
      (locConstraintsIthJthAux locs i j ↔
        ∃ l : Fin k, l.val ≤ j ∧ locs.extractLsb' (l * nlog) nlog = i) := by
    intro j hj
    induction' j with j ih
    · constructor
      · intro h
        exact ⟨⟨0, hj⟩, by simp, by simpa [locConstraintsIthJthAux, locConstraintsIthJth] using h⟩
      · rintro ⟨l, hl, hloc⟩
        have hl0 : l = ⟨0, hj⟩ := by
          apply Fin.ext
          exact Nat.eq_zero_of_le_zero hl
        simpa [locConstraintsIthJthAux, locConstraintsIthJth, hl0] using hloc
    · constructor
      · intro h
        simp only [locConstraintsIthJthAux, locConstraintsIthJth] at h
        rcases h with h | h
        · exact ⟨⟨j + 1, hj⟩, le_rfl, by simpa⟩
        · rcases (ih (Nat.lt_of_succ_lt hj)).1 h with ⟨l, hl, hloc⟩
          exact ⟨l, Nat.le_trans hl (Nat.le_succ j), hloc⟩
      · rintro ⟨l, hl, hloc⟩
        simp only [locConstraintsIthJthAux, locConstraintsIthJth]
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

/-- The coercion of `Fin n` into `⌈log₂ n⌉` bits is `BitVec.ofNat`. -/
lemma fin_to_bitvec_clog {n : ℕ} {x : Fin n} : (x : BitVec (Nat.clog 2 n)) = BitVec.ofNat (Nat.clog 2 n) x := by
  simp only [BitVec.natCast_eq_ofNat]

/-- `⌈log₂ n⌉` bits are enough to tell the elements of `Fin n` apart. -/
lemma _root_.BitVec.ofNat_clog_eq_iff {n : ℕ} {x y : Fin n} :
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

/-- An error of weight at most `k` and its `indexVec` satisfy `locConstraints`. -/
lemma locConstraints_of_index {n k : ℕ} (x : Fin n → (ZMod 2)) (hx : hammingNorm x ≤ k) (hx' : hammingNorm x ≠ 0) :
    locConstraints (vecToBitVec' (indexVec x hx hx')) (vecToBitVec x) := by
  have hk : 0 < k := lt_of_lt_of_le (Nat.pos_of_ne_zero hx') hx
  apply locConstraints_ascent (hn := by
    by_contra h
    push Not at h
    interval_cases n
    simp [hammingNorm] at hx')
  intro i
  unfold locConstraintsIth
  rw [locConstraintsIthJthAux_correct _ _ hk]
  by_cases h : (x i = 0)
  · simp [vecToBitVec, h]
    intro y
    rw [vecToBitVec'_correct, fin_to_bitvec_clog, BitVec.ofNat_clog_eq_iff]
    intro h_f
    apply absurd h
    apply indexVec_eq_one_of_exists h_f
  · have hval : (x i).val = 1 := zmod2_val_eq_one_of_ne_zero (x i) h
    simp [vecToBitVec, hval]
    let S := Finset.univ.filter (fun j : Fin n => x j ≠ 0)
    have hiS : i ∈ S := by simp [S, h]
    have hi_range : i ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin S rfl]
      exact hiS
    rcases hi_range with ⟨j, hj⟩
    have hjlt : (j : ℕ) < hammingNorm x := by
      simp [S, hammingNorm]
    refine ⟨⟨j, lt_of_lt_of_le hjlt hx⟩, ?_⟩
    rw [vecToBitVec'_correct, fin_to_bitvec_clog, BitVec.ofNat_clog_eq_iff]
    simp [indexVec, S]
    rw [dif_pos hjlt]
    exact hj

/-- The coercion `Fin n → BitVec ⌈log₂ n⌉` preserves and reflects `≤`. -/
lemma fin_toBitVec_clog_le_iff {n : ℕ} {x y : Fin n} :
    (x : BitVec (Nat.clog 2 n)) ≤ (y : BitVec (Nat.clog 2 n)) ↔ x ≤ y := by
  simp only [BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Fin.le_def]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le x.2 (Nat.le_pow_clog one_lt_two n))]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le y.2 (Nat.le_pow_clog one_lt_two n))]

/-- Every element of `Fin n` fits below the all-ones bit vector of width `⌈log₂ n⌉`. -/
lemma fin_toBitVec_clog_le_allOnes {n : ℕ} (x : Fin n) :
    (x : BitVec (Nat.clog 2 n)) ≤ BitVec.allOnes (Nat.clog 2 n) := by
  rw [BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le x.2 (Nat.le_pow_clog one_lt_two n))]
  rw [BitVec.toNat_allOnes]
  exact Nat.le_sub_one_of_lt (lt_of_lt_of_le x.2 (Nat.le_pow_clog one_lt_two n))

/-- `symmetryConstraintsAux` on a packed tuple says that its entries up to `c` are monotone
and bounded by `prev`. -/
lemma symmetryConstraintsAux_iff_index
    {n k : ℕ} (x : Fin k → Fin n) :
    ∀ c, c < k → ∀ prev : BitVec (Nat.clog 2 n),
      symmetryConstraintsAux (vecToBitVec' x) c prev ↔
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
        have h0 := vecToBitVec'_correct (r := x) ⟨0, hc⟩
        simp only [symmetryConstraintsAux, decide_eq_true_eq] at h
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
      have h0 := vecToBitVec'_correct (r := x) ⟨0, hc⟩
      rw [symmetryConstraintsAux, h0]
      simpa only [decide_eq_true_eq] using h.1 ⟨0, hc⟩ le_rfl
  · intro hc prev
    have hc' : c < k := Nat.lt_of_succ_lt hc
    have hval :
        (vecToBitVec' x).extractLsb' ((c + 1) * Nat.clog 2 n) (Nat.clog 2 n) =
          (x ⟨c + 1, hc⟩ : BitVec (Nat.clog 2 n)) := by
      simpa using vecToBitVec'_correct (r := x) ⟨c + 1, hc⟩
    constructor
    · intro h
      simp only [symmetryConstraintsAux, hval, Bool.and_eq_true, decide_eq_true_eq] at h
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
      simp only [symmetryConstraintsAux, hval, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact h.1 ⟨c + 1, hc⟩ le_rfl
      · apply (ih hc' (x ⟨c + 1, hc⟩)).2
        constructor
        · intro i hi
          rw [fin_toBitVec_clog_le_iff]
          exact h.2 i ⟨c + 1, hc⟩ (Fin.mk_le_mk.mpr (Nat.le_succ_of_le hi)) le_rfl
        · intro i j hij hj
          exact h.2 i j hij (Nat.le_trans hj (Nat.le_succ c))

/-- `symmetryConstraints` on a packed tuple says exactly that the tuple is monotone. -/
lemma symmetryConstraints_iff_index {n k : ℕ} (x : Fin k → Fin n) :
    symmetryConstraints (vecToBitVec' x) ↔ ∀ i j, i ≤ j → x i ≤ x j := by
  by_cases hk : k = 0
  · subst hk
    simp [symmetryConstraints, symmetryConstraintsAux, BitVec.le_def, BitVec.toNat_allOnes]
    exact Nat.le_sub_one_of_lt (Nat.mod_lt _ (pow_pos (by norm_num) _))
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [symmetryConstraints]
    rw [symmetryConstraintsAux_iff_index x (k - 1) (Nat.sub_lt hkpos zero_lt_one)]
    constructor
    · intro h i j hij
      exact h.2 i j hij (Nat.le_sub_one_of_lt j.2)
    · intro h
      constructor
      · intro i _
        exact fin_toBitVec_clog_le_allOnes (x i)
      · intro i j hij _
        exact h i j hij

/-- Shifting down by `r * n` and keeping the low `n` bits extracts the same field as
`extractLsb'`. -/
lemma _root_.BitVec.shift_extract_eq {n k : ℕ} (M : BitVec (k * n)) (r : ℕ) :
   (M >>> (r * n)).extractLsb' 0 n = M.extractLsb' (r * n) n := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', zero_add, BitVec.getLsbD_ushiftRight]

/-- Row `r` of a flattened matrix is the flattening of row `r`. -/
lemma row_correct {k n : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (r : Fin k) :
    (flattenMatrix M).row r = vecToBitVec (M r) := by
  unfold BitVec.row
  rw [BitVec.shift_extract_eq]
  induction' k with k ih
  · fin_cases r
  · refine' Fin.lastCases _ _ r
    · rcases k with (_ | k) <;> simp +decide [*, flattenMatrix]
      · simp only [BitVec.appendList, Matrix.toBitVecs]
        ext i hi
        simp [BitVec.getLsbD_eq_getElem hi]
      · refine' BitVec.eq_of_getElem_eq _
        intro i hi
        simp +decide [BitVec.appendList]
        nontriviality
        rw [BitVec.getLsbD_append, if_neg (by omega), Nat.add_sub_cancel_left]
        simp [Matrix.toBitVecs, Fin.last, BitVec.getLsbD_eq_getElem hi]
    · intro i
      convert ih (fun r => M (Fin.castSucc r)) i using 1
      unfold flattenMatrix
      rcases k with (_ | k) <;> simp_all +decide [BitVec.appendList]
      · fin_cases i
      ·
        ext j
        rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb']
        rw [BitVec.getLsbD_cast]
        rw [BitVec.getLsbD_append]
        split_ifs <;> simp_all +decide
        · congr! 1
        · nlinarith [Fin.is_lt i]

/-- A bit vector of width `⌈log₂ k⌉` as an element of `Fin k`, wrapping around if it is too
large. -/
def bitVecToFin {k : ℕ} [NeZero k] (x : BitVec (Nat.clog 2 k)) : Fin k :=
  ⟨x.toNat % k, Nat.mod_lt _ (Nat.pos_of_neZero _)⟩

/-- Below `k` there is no wraparound. -/
theorem bitVecToFin_val_eq {k : ℕ} [NeZero k] (x : BitVec (Nat.clog 2 k)) (hx : x.toNat < k) :
    (bitVecToFin x).val = x.toNat := by
  simp [bitVecToFin]
  apply Nat.mod_eq_of_lt hx

/-- Coercing `x : Fin k` to `⌈log₂ k⌉` bits keeps its value. -/
theorem fin_toBitVec_toNat_eq {k : ℕ} [NeZero k] (x : Fin k) :
    (x : BitVec (Nat.clog 2 k)).toNat = x := by
  simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  apply lt_of_lt_of_le x.isLt
  apply Nat.le_pow_clog (one_lt_two)

/-- `bitVecToFin` undoes the coercion `Fin k → BitVec ⌈log₂ k⌉`. -/
theorem fin_toBitVec_toNat_eq' {k : ℕ} [NeZero k] (x : Fin k) :
    bitVecToFin x = x := by
  simp only [Fin.ext_iff, bitVecToFin, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.mod_eq_of_lt]
    apply lt_of_lt_of_le x.isLt _
    apply Nat.le_pow_clog (one_lt_two)
  apply Nat.mod_lt_of_lt x.isLt

/-- `row_correct` for a row index given as a bit vector. -/
lemma BitVec_row_correct {k n : ℕ} [NeZero k] (M : Matrix (Fin k) (Fin n) (ZMod 2))
      (r : BitVec (Nat.clog 2 k)) (hr : r.toNat < k) :
    (flattenMatrix M).row r.toNat = vecToBitVec (M (bitVecToFin r)) := by
  rw [←row_correct, bitVecToFin_val_eq _ hr]

/-- Bit `r * j + c` of a flattened matrix is the entry `M r c`. -/
lemma flattenMatrix_get {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) (r : Fin i) (c : Fin j) :
    (flattenMatrix M)[r.val * j + c.val]! = ((M r c).val == 1) := by
  rw [BitVec.getElemBang_eq_getLsbD]
  have h := congrArg (fun bv : BitVec j => bv.getLsbD c.val) (row_correct M r)
  simp [BitVec.row, vecToBitVec] at h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- `flattenMatrix` undoes `BitVecMatrix`. -/
lemma flatten_BitVecMatrix_id {r n : ℕ} (M : BitVec (r * n)) : flattenMatrix (BitVecMatrix M) = M := by
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
    have hget := flattenMatrix_get (BitVecMatrix M) ⟨i / n, hr⟩ ⟨i % n, hc⟩
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

/-- One step of a dot product: adding `a * b` to the running sum `s` is an `and` and an `xor`
on the corresponding bits. -/
lemma zmod2_dot_bool_step (a b s : ZMod 2) :
    (((a.val == 1) && (b.val == 1)) ^^ (s == 1)) =
      (s + a * b == 1) := by
  fin_cases a <;> fin_cases b <;> fin_cases s <;> decide

/-- `BitVec.dotProduct` computes the dot product over `ZMod 2`. -/
theorem dotProduct_correct {n : ℕ} [NeZero n] (x y : Fin n → (ZMod 2)):
    (vecToBitVec x).dotProduct (vecToBitVec y) = (x ⬝ᵥ y == 1) := by
  have h_aux : ∀ idx, (hidx : idx < n) →
      dotProductAux (vecToBitVec x) (vecToBitVec y) idx hidx =
        ((∑ t ∈ Finset.range (idx + 1),
            if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0) == 1) := by
    intro idx hidx
    induction' idx with idx ih
    · change ((vecToBitVec x)[0] && (vecToBitVec y)[0]) =
        ((∑ t ∈ Finset.range (0 + 1),
            if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0) == 1)
      simp [hidx]
      simp [vecToBitVec]
      have hbool (a b : ZMod 2) : ((a.val == 1) && (b.val == 1)) = (a * b == 1) := by
        fin_cases a <;> fin_cases b <;> decide
      exact hbool (x ⟨0, hidx⟩) (y ⟨0, hidx⟩)
    · have hidx' : idx < n := Nat.lt_of_succ_lt hidx
      change (((vecToBitVec x)[idx + 1] && (vecToBitVec y)[idx + 1]) ^^
              dotProductAux (vecToBitVec x) (vecToBitVec y) idx hidx') =
        ((∑ t ∈ Finset.range (idx + 1 + 1),
            if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0) == 1)
      rw [ih hidx']
      conv_rhs => rw [Finset.sum_range_succ]
      simp [vecToBitVec, hidx]
      simpa +decide using
        (zmod2_dot_bool_step (x ⟨idx + 1, hidx⟩) (y ⟨idx + 1, hidx⟩)
          (∑ t ∈ Finset.range (idx + 1),
            if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0))
  unfold BitVec.dotProduct dotProduct
  rw [h_aux (n - 1) (Nat.sub_lt (NeZero.pos n) zero_lt_one)]
  congr 1
  rw [Nat.sub_one_add_one (NeZero.ne n)]
  rw [← Fin.sum_univ_eq_sum_range
    (fun t => if ht : t < n then x ⟨t, ht⟩ * y ⟨t, ht⟩ else 0) n]
  apply Finset.sum_congr rfl
  intro i _hi
  simp

/-- `parityConstraints` gives orthogonality to each single row. -/
lemma parityConstraints_descent {stabdim n : ℕ} [NeZero n] {stabs : BitVec (stabdim * n)}
      {errs : BitVec n} {r : Fin stabdim} (hpc : parityConstraints stabs errs) :
    !(errs.dotProduct (stabs.row r)) := by
  contrapose! hpc
  simp_all +decide [parityConstraints]
  have h_ind : ∀ r' : ℕ, r' ≤ stabdim - 1 → r.val ≤ r' → parityConstraintsAux stabs errs r' = false := by
    intro r' hr' hr'_le
    induction' hr' : r' - r.val using Nat.strong_induction_on with r' ih generalizing r'
    rcases r' with (_ | r') <;> simp_all +decide [parityConstraintsAux]
    grind
  exact h_ind _ le_rfl (Nat.le_sub_one_of_lt r.2)

/-- `parityConstraints` follows from orthogonality to each single row. -/
lemma parityConstraints_ascent {stabdim n : ℕ} [NeZero n] {stabs : BitVec (stabdim * n)}
    {errs : BitVec n} (hpaux : ∀ (r : Fin stabdim), !(errs.dotProduct (stabs.row r))) :
    parityConstraints stabs errs := by
  by_cases h : 0 < stabdim <;> simp_all +decide [parityConstraints]
  · have h_ind : ∀ c < stabdim, parityConstraintsAux stabs errs c = true := by
      intro c hc
      induction' c with c ih <;> simp_all +decide [parityConstraintsAux]
      · exact hpaux ⟨0, hc⟩
      · exact ⟨hpaux ⟨c + 1, hc⟩, ih (Nat.lt_of_succ_lt hc)⟩
    exact h_ind _ (Nat.pred_lt h.ne')
  · cases stabs
    cases ‹Fin (2 ^ (stabdim * n))›
    simp_all +decide [BitVec.row]
    have h_dotProduct_zero : ∀ (x : Fin n → ZMod 2),
        (vecToBitVec x).dotProduct (vecToBitVec (fun _ => 0)) = false := by
      intros x
      have h_dotProduct_zero : (vecToBitVec x).dotProduct (vecToBitVec (fun _ => 0))
          = (x ⬝ᵥ (fun _ => 0) == 1) := by
        convert dotProduct_correct x (fun _ => 0) using 1
      simp_all +decide [dotProduct]
    convert h_dotProduct_zero (bitVecToVec errs) using 1
    congr! 1
    · grind +suggestions
    · simp +decide [BitVec.extractLsb', vecToBitVec]
      rename_i val hval
      simp only [h, zero_mul, pow_zero, Nat.lt_one_iff] at hval
      subst hval
      ext i hi
      simp

/-- `parityConstraints` says exactly that the error lies in the kernel of the check matrix. -/
lemma parityConstraints_correct {k n : ℕ} [NeZero n] {M : Matrix (Fin k) (Fin n) (ZMod 2)}
    {x : Fin n → ZMod 2} :
    parityConstraints (flattenMatrix M) (vecToBitVec x) ↔ x ∈ LinearMap.ker M.toLin' := by
  rw [LinearMap.mem_ker]
  have pc_correct_aux : ∀ (i : Fin k),
  !((vecToBitVec x).dotProduct ((flattenMatrix M).row i)) ↔ (M.mulVec x) i = 0 := by
    intro i
    rw [row_correct, dotProduct_correct]
    simp only [Matrix.mulVec, dotProduct]
    rw [show ∑ i_1, x i_1 * M i i_1 = ∑ x_1, M i x_1 * x x_1 from
      Finset.sum_congr rfl (fun j _ => mul_comm (x j) (M i j))]
    constructor
    · intro h
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at h
      exact (ZMod.val_eq_zero _).mp (zmod2_val_eq_zero_of_ne_one _ h)
    · intro h
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne]
      rw [h]
      decide
  rw [Matrix.toLin'_apply]
  constructor
  · intro hpar
    ext i
    apply (pc_correct_aux i).1
    apply parityConstraints_descent hpar
  intro hmul
  apply parityConstraints_ascent
  intro r
  apply (pc_correct_aux r).2
  rw [hmul]
  simp only [Pi.zero_apply]

/-- A single row that detects the error gives `rowspaceConstraints`. -/
lemma rowspaceConstraints_descent {kerdim n} [NeZero n] {ker : BitVec (kerdim * n)}
{errs : BitVec n} (r : Fin kerdim) (hr : (errs.dotProduct (ker.row r)))
: rowspaceConstraints ker errs := by
  have h_aux : ∀ (r : ℕ), r ≤ kerdim - 1 →
      (∃ i : Fin kerdim, i.val ≤ r ∧ !(errs.dotProduct (ker.row i)) = false) →
      rowspaceConstraintsAux ker errs r = true := by
    intros r hr ih
    induction' r with r ih <;> simp_all +decide [rowspaceConstraintsAux]
    · grind
    · grind
  generalize_proofs at *
  (
  exact h_aux _ le_rfl ⟨r, Nat.le_sub_one_of_lt r.2, by simpa using hr⟩)

/-- `rowspaceConstraints` gives a single row that detects the error. -/
lemma rowspaceConstraints_ascent {kerdim n : ℕ} [NeZero kerdim] [NeZero n] {ker : BitVec (kerdim * n)}
{errs : BitVec n} (hconstr : rowspaceConstraints ker errs)
: ∃ (r : Fin kerdim), (errs.dotProduct (ker.row r)) := by
  unfold rowspaceConstraints at hconstr
  have h_aux : ∀ idx, idx < kerdim →
      rowspaceConstraintsAux ker errs idx = true →
      ∃ r : Fin kerdim, r.val ≤ idx ∧ errs.dotProduct (ker.row r) := by
    intro idx hidx h
    induction' idx with idx ih
    · exact ⟨⟨0, hidx⟩, le_rfl, by simpa [rowspaceConstraintsAux] using h⟩
    · by_cases hlast : errs.dotProduct (ker.row (idx + 1))
      · exact ⟨⟨idx + 1, hidx⟩, le_rfl, hlast⟩
      · have hprev : rowspaceConstraintsAux ker errs idx = true := by
          simpa [rowspaceConstraintsAux, hlast] using h
        rcases ih (Nat.lt_of_succ_lt hidx) hprev with ⟨r, hrle, hr⟩
        exact ⟨r, Nat.le_trans hrle (Nat.le_succ idx), hr⟩
  rcases h_aux (kerdim - 1) (Nat.sub_lt (NeZero.pos kerdim) zero_lt_one) hconstr with
    ⟨r, _, hr⟩
  exact ⟨r, hr⟩

/-- When the rows of `M₂` span the kernel of `M₁`, `rowspaceConstraints` says exactly that the
error lies outside the row space of `M₁`. -/
lemma rowspaceConstraints_correct {k₁ k₂ n : ℕ}
    [NeZero k₂] [NeZero n]
    {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)}
    {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)}
    (hK : M₂.rowSpace = (LinearMap.ker (M₁.toLin')))
    {x : Fin n → ZMod 2} :
    rowspaceConstraints (flattenMatrix M₂) (vecToBitVec x) ↔ x ∉ M₁.rowSpace := by
  rw [not_mem_rowspace_iff_exists_mem_ker]
  constructor
  · intro hrc
    rcases rowspaceConstraints_ascent hrc with ⟨r, hrp⟩
    refine ⟨M₂ r, ⟨?_, ?_⟩⟩
    · rw [←hK]
      exact Matrix.row_mem_rowSpace
    rw [row_correct, dotProduct_correct x (M₂ r), dotProduct_comm] at hrp
    simp only [beq_iff_eq] at hrp
    assumption
  rintro ⟨y, ⟨hy₁, hy₂⟩⟩
  rw [←hK] at hy₁
  obtain ⟨s, hs⟩ := exists_row_of_exists_mem_rowspace_non_orth hy₁ hy₂
  apply rowspaceConstraints_descent s
  rwa [row_correct, dotProduct_correct, dotProduct_comm, beq_iff_eq]

/-- `nonzero` says exactly that the vector is nonzero. -/
lemma nonzero_correct {r : ℕ} (x : Fin r → (ZMod 2)) :
    nonzero (vecToBitVec x) ↔ x ≠ 0 := by
  -- By definition of `nonzero`, `nonzero (vecToBitVec x) = true` exactly when there is some
  -- `i` with `x i ≠ 0`.
  simp [nonzero]
  by_cases hr : r = 0 <;> simp_all +decide [funext_iff, nonzeroAux]
  · subst hr
    exact fun i => Fin.elim0 i
  · constructor
    · intro h_nonzero
      by_contra h_contra
      push Not at h_contra
      have h_zero : ∀ i : Fin r, x i = 0 := by
        exact h_contra
      have h_zero_bitvec : vecToBitVec x = 0 := by
        ext i
        simp [vecToBitVec, h_zero]
      have h_zero_nonzero : nonzeroAux (vecToBitVec x) (r - 1) = false := by
        rw [h_zero_bitvec]
        induction' r - 1 with r ih <;> simp +decide [*, nonzeroAux]
        · cases r <;> simp
        · cases ‹ℕ› <;> simp_all +decide [nonzeroAux]
          · rcases r with (_ | _ | r) <;> simp_all +decide
          · cases r <;> simp_all +decide
            cases ‹ℕ› <;> simp_all +decide
            grind
      exact absurd h_zero_nonzero (by simp [h_nonzero])
    · rintro ⟨i, hi⟩
      -- Since `x i ≠ 0`, bit `i` of `vecToBitVec x` is set.
      have h_bit : (vecToBitVec x)[i]! = true := by
        rw [vecToBitVec_correct]
        have hval : (x i).val = 1 := zmod2_val_eq_one_of_ne_zero (x i) hi
        simp [hval]
      -- Since bit `i` is set, `nonzeroAux` returns `true`.
      have h_nonzeroAux : ∀ (j : ℕ) (hj : i.val ≤ j), nonzeroAux (vecToBitVec x) j = true := by
        intro j hj
        induction' j with j ih <;> simp_all +decide [nonzeroAux]
        · grind
        · grind +splitImp
      exact h_nonzeroAux _ (Nat.le_sub_one_of_lt i.2)

/-- Combining the rows of `M` up to `idx` in column `c` is the dot product of the coefficients
with that column. -/
lemma dotColAux_eq_dotProductAux {r n : ℕ} [NeZero r]
    (M : Matrix (Fin r) (Fin n) (ZMod 2)) (coeffs : Fin r → ZMod 2) (c : Fin n) :
    ∀ idx, (hr : idx < r) →
      dotColAux (vecToBitVec coeffs) (flattenMatrix M) c.val idx =
        dotProductAux (vecToBitVec coeffs) (vecToBitVec (fun row => M row c)) idx hr := by
  intro idx hidx
  induction' idx with idx ih
  · change ((vecToBitVec coeffs)[0]! &&
        (flattenMatrix M)[0 * n + c.val]!) =
      ((vecToBitVec coeffs)[0] &&
        (vecToBitVec (fun row => M row c))[0])
    rw [vecToBitVec_getElemBang coeffs hidx]
    rw [flattenMatrix_get M ⟨0, hidx⟩ c]
    simp [vecToBitVec]
  · have hidx' : idx < r := Nat.lt_of_succ_lt hidx
    change (((vecToBitVec coeffs)[idx + 1]! &&
        (flattenMatrix M)[(idx + 1) * n + c.val]!) ^^
        dotColAux (vecToBitVec coeffs) (flattenMatrix M) c.val idx) =
      (((vecToBitVec coeffs)[idx + 1] &&
        (vecToBitVec (fun row => M row c))[idx + 1]) ^^
        dotProductAux (vecToBitVec coeffs)
          (vecToBitVec (fun row => M row c)) idx hidx')
    rw [ih hidx']
    rw [vecToBitVec_getElemBang coeffs hidx]
    rw [flattenMatrix_get M ⟨idx + 1, hidx⟩ c]
    simp [vecToBitVec]

/-- `dotColZero` says exactly that `M.vecMul coeffs` vanishes in column `c`. -/
lemma dotColZero_correct {r n : ℕ} [NeZero r]
    (M : Matrix (Fin r) (Fin n) (ZMod 2)) (coeffs : Fin r → ZMod 2) (c : Fin n) :
    dotColZero (vecToBitVec coeffs) (flattenMatrix M) c.val =
      !((M.vecMul coeffs c) == 1) := by
  by_cases hr : r = 0
  · subst r
    simp [dotColZero, dotColAux, Matrix.vecMul, dotProduct]
  · have hidx : r - 1 < r := Nat.sub_lt (Nat.pos_of_ne_zero hr) zero_lt_one
    have hd := dotColAux_eq_dotProductAux M coeffs c (r - 1) hidx
    unfold dotColZero
    rw [hd]
    have hdp := dotProduct_correct coeffs (fun row => M row c)
    unfold BitVec.dotProduct at hdp
    rw [hdp]
    simp [Matrix.vecMul, dotProduct]

/-- In `ZMod 2`, not being `1` is being `0`. -/
lemma zmod2_ne_one_iff_eq_zero (a : ZMod 2) : a ≠ 1 ↔ a = 0 := by
  constructor
  · intro h
    exact (ZMod.val_eq_zero a).mp (zmod2_val_eq_zero_of_ne_one a h)
  · intro h
    rw [h]
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1)

/-- `allDotZeroAux` says exactly that `M.vecMul coeffs` vanishes in the columns up to `idx`. -/
lemma allDotZeroAux_correct {r n : ℕ} [NeZero r]
    (M : Matrix (Fin r) (Fin n) (ZMod 2)) (coeffs : Fin r → ZMod 2) :
    ∀ idx, idx < n →
      (allDotZeroAux (vecToBitVec coeffs) (flattenMatrix M) idx ↔
        ∀ c : Fin n, c.val ≤ idx → M.vecMul coeffs c = 0) := by
  intro idx hidx
  induction' idx with idx ih
  · rw [show allDotZeroAux (vecToBitVec coeffs) (flattenMatrix M) 0 =
        dotColZero (vecToBitVec coeffs) (flattenMatrix M) 0 by rfl]
    have hdz := dotColZero_correct M coeffs ⟨0, hidx⟩
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
    change ((dotColZero (vecToBitVec coeffs) (flattenMatrix M) (idx + 1) &&
        allDotZeroAux (vecToBitVec coeffs) (flattenMatrix M) idx) = true) ↔
      ∀ c : Fin n, c.val ≤ idx + 1 → M.vecMul coeffs c = 0
    rw [dotColZero_correct M coeffs ⟨idx + 1, hidx⟩]
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

/-- `allDotZero` says exactly that `M.vecMul coeffs` is zero. -/
lemma allDotZero_correct {r n : ℕ} [NeZero r] (M : Matrix (Fin r) (Fin n) (ZMod 2))
    (coeffs : Fin r → (ZMod 2)) :
    allDotZero (vecToBitVec coeffs) (flattenMatrix M) ↔ M.vecMul coeffs = 0 := by
  by_cases hn : n = 0
  · subst n
    have hdot : dotColAux (vecToBitVec coeffs) (flattenMatrix M) 0 (r - 1) = false := by
      have haux0 : ∀ idx, dotColAux (vecToBitVec coeffs) (flattenMatrix M) 0 idx = false := by
        intro idx
        induction' idx with idx ih
        · simp [dotColAux, BitVec.getElemBang_eq_getLsbD]
        · simp [dotColAux, ih, BitVec.getElemBang_eq_getLsbD]
      exact haux0 (r - 1)
    simp [allDotZero, allDotZeroAux, dotColZero, hdot]
  · unfold allDotZero
    rw [allDotZeroAux_correct M coeffs (n - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hn) zero_lt_one)]
    constructor
    · intro h
      ext c
      exact h c (Nat.le_sub_one_of_lt c.2)
    · intro h c _
      rw [h]
      simp

/-- The rows of `M` are independent exactly when no nonzero coefficient vector annihilates
them. -/
lemma linear_indep_of_forall_vecmul_nz {r n : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod 2)) :
    LinearIndependent (ZMod 2) M.row ↔ ∀ coeffs, coeffs ≠ 0 → M.vecMul coeffs ≠ 0 := by
  rw [Fintype.linearIndependent_iff]
  simp +decide [funext_iff, Matrix.vecMul, Matrix.row]
  constructor
  · exact fun h coeffs x hx => not_forall.mp fun h' => hx <| h coeffs h' x
  · intro h g hg i
    specialize h g i
    contrapose! h
    exact ⟨h, hg⟩

/-- `linearIndepSAT` says exactly that the rows of `M` are linearly independent. -/
lemma linearIndepSAT_correct {r n : ℕ} [NeZero r] (M : Matrix (Fin r) (Fin n) (ZMod 2)) :
    LinearIndependent (ZMod 2) M.row ↔ linearIndepSAT (flattenMatrix M) := by
  rw [linear_indep_of_forall_vecmul_nz]
  constructor
  · intro hcoeffs coeffs
    simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    by_cases h: bitVecToVec coeffs ≠ 0
    · right
      rw [←Bool.not_eq_true]
      rw [vecToBitVec_bitVecToVec coeffs, allDotZero_correct M]
      apply hcoeffs _ h
    left
    rwa [←Bool.not_eq_true, vecToBitVec_bitVecToVec coeffs, nonzero_correct]
  intro hlin coeffs hnz
  rw [ne_eq, ←allDotZero_correct]
  intro h_f
  unfold linearIndepSAT at hlin
  simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
  ←Bool.not_eq_true] at hlin
  rcases hlin (vecToBitVec coeffs) with hz | hd
  · apply hz
    rwa [nonzero_correct]
  apply (hd h_f)

/-- `mutuallyOrthRowSatAux` says exactly that row `i` of `M₁` is orthogonal to the rows of
`M₂` up to `idx`. -/
lemma mutuallyOrthRowSatAux_correct
    {k₁ k₂ n : ℕ}
    [NeZero n]
    (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
    (i : Fin k₁) :
    ∀ idx, idx < k₂ →
      (mutuallyOrthRowSatAux (flattenMatrix M₁) (flattenMatrix M₂) i.val idx ↔
        ∀ j : Fin k₂, j.val ≤ idx → M₁ i ⬝ᵥ M₂ j = 0) := by
  intro idx hidx
  induction' idx with idx ih
  · rw [show mutuallyOrthRowSatAux (flattenMatrix M₁) (flattenMatrix M₂) i.val 0 =
        !(((flattenMatrix M₁).row i.val).dotProduct ((flattenMatrix M₂).row 0)) by rfl]
    rw [row_correct M₁ i, row_correct M₂ ⟨0, hidx⟩, dotProduct_correct]
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
    change (!(((flattenMatrix M₁).row i.val).dotProduct ((flattenMatrix M₂).row (idx + 1))) &&
        mutuallyOrthRowSatAux (flattenMatrix M₁) (flattenMatrix M₂) i.val idx ↔
      ∀ j : Fin k₂, j.val ≤ idx + 1 → M₁ i ⬝ᵥ M₂ j = 0)
    rw [row_correct M₁ i, row_correct M₂ ⟨idx + 1, hidx⟩, dotProduct_correct]
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

/-- `mutuallyOrthSatAux` says exactly that the rows of `M₁` up to `idx` are orthogonal to
every row of `M₂`. -/
lemma mutuallyOrthSatAux_correct
    {k₁ k₂ n : ℕ}
    [NeZero n]
    [NeZero k₂]
    (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
    ∀ idx, idx < k₁ →
      (mutuallyOrthSatAux (flattenMatrix M₁) (flattenMatrix M₂) idx ↔
        ∀ i : Fin k₁, i.val ≤ idx → ∀ j : Fin k₂, M₁ i ⬝ᵥ M₂ j = 0) := by
  intro idx hidx
  induction' idx with idx ih
  · rw [show mutuallyOrthSatAux (flattenMatrix M₁) (flattenMatrix M₂) 0 =
        mutuallyOrthRowSatAux (flattenMatrix M₁) (flattenMatrix M₂) 0 (k₂ - 1) by rfl]
    rw [mutuallyOrthRowSatAux_correct M₁ M₂ ⟨0, hidx⟩ (k₂ - 1)
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
    change (mutuallyOrthRowSatAux (flattenMatrix M₁) (flattenMatrix M₂) (idx + 1) (k₂ - 1) &&
        mutuallyOrthSatAux (flattenMatrix M₁) (flattenMatrix M₂) idx ↔
      ∀ i : Fin k₁, i.val ≤ idx + 1 → ∀ j : Fin k₂, M₁ i ⬝ᵥ M₂ j = 0)
    simp only [
      Bool.and_eq_true,
      mutuallyOrthRowSatAux_correct M₁ M₂ ⟨idx + 1, hidx⟩ (k₂ - 1)
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

/-- `bitVecMutuallyOrthNat` says exactly that every row of `M₁` is orthogonal to every row
of `M₂`. -/
theorem mutually_orth_nat_correct
    {k₁ k₂ n : ℕ}
    [NeZero k₁]
    [NeZero k₂]
    [NeZero n]
    (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
    bitVecMutuallyOrthNat (flattenMatrix M₁) (flattenMatrix M₂) ↔ M₁.mutuallyOrthRows M₂ := by
  unfold bitVecMutuallyOrthNat
  rw [mutuallyOrthSatAux_correct M₁ M₂ (k₁ - 1) (Nat.sub_lt (NeZero.pos k₁) zero_lt_one)]
  constructor
  · intro h i j
    exact h i (Nat.le_sub_one_of_lt i.2) j
  · intro h i _hi j
    exact h i j

/-- `indsStrictMonoAux` gives `inds idx < prev` and strict growth below `idx`. -/
lemma indsStrictMonoAux_descent {k r : ℕ} (inds : Fin r → Fin k) :
    ∀ (idx : ℕ) (hidx : idx < r) (prev : ℕ),
      indsStrictMonoAux inds ⟨idx, hidx⟩ prev →
      (inds ⟨idx, hidx⟩).val < prev ∧
        ∀ t, (ht : t < idx) →
          inds ⟨t, Nat.lt_trans ht hidx⟩ <
            inds ⟨t + 1, lt_of_le_of_lt (Nat.succ_le_of_lt ht) hidx⟩ := by
  intro idx
  induction' idx with idx ih
  · intro hidx prev h
    simp [indsStrictMonoAux] at h
    constructor
    · exact h
    · intro t ht
      omega
  · intro hidx prev h
    simp [indsStrictMonoAux] at h
    rcases h with ⟨hhead, htail⟩
    have htail' := ih (Nat.lt_of_succ_lt hidx) (inds ⟨idx + 1, hidx⟩).val htail
    constructor
    · exact hhead
    · intro t ht
      by_cases htidx : t = idx
      · subst htidx
        exact htail'.1
      · exact htail'.2 t (lt_of_lt_of_le (lt_of_le_of_ne (Nat.le_of_lt_succ ht) htidx) le_rfl)

/-- `indsStrictMonoAux` follows from `inds idx < prev` and strict growth below `idx`. -/
lemma indsStrictMonoAux_ascent {k r : ℕ} (inds : Fin r → Fin k) :
    ∀ (idx : ℕ) (hidx : idx < r) (prev : ℕ),
      (inds ⟨idx, hidx⟩).val < prev →
      (∀ t, (ht : t < idx) →
          inds ⟨t, Nat.lt_trans ht hidx⟩ <
            inds ⟨t + 1, lt_of_le_of_lt (Nat.succ_le_of_lt ht) hidx⟩) →
      indsStrictMonoAux inds ⟨idx, hidx⟩ prev := by
  intro idx
  induction' idx with idx ih
  · intro hidx prev hprev _hadj
    simp [indsStrictMonoAux, hprev]
  · intro hidx prev hprev hadj
    simp [indsStrictMonoAux, hprev]
    apply ih (Nat.lt_of_succ_lt hidx) (inds ⟨idx + 1, hidx⟩).val
    · exact hadj idx (Nat.lt_succ_self idx)
    · intro t ht
      exact hadj t (Nat.lt_trans ht (Nat.lt_succ_self idx))

/-- `indsStrictMono` says exactly that `inds` is strictly monotone. -/
lemma indsStrictMono_correct {k r : ℕ} [NeZero r] (inds : Fin r → Fin k) :
    StrictMono inds ↔ indsStrictMono inds := by
  rcases r with _ | r
  · exact False.elim (NeZero.ne (n := 0) rfl)
  · rw [Fin.strictMono_iff_lt_succ]
    constructor
    · intro h
      unfold indsStrictMono
      apply indsStrictMonoAux_ascent
      · exact (inds (Fin.last r)).2
      · intro t ht
        have hstep := h ⟨t, ht⟩
        simpa [Fin.castSucc, Fin.succ] using hstep
    · intro haux i
      unfold indsStrictMono at haux
      have hd := indsStrictMonoAux_descent inds r (Nat.lt_succ_self r) k haux
      exact hd.2 i.val i.2

end QuantumLib
