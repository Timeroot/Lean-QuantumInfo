/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Concatenation
import QuantumLib.QECC.RandomErrors

/-!
# Iterated concatenation and the threshold theorem

Concatenating a code with itself `L` times gives a code on `m ^ (L+1)` qudits whose correction
radius grows like `(t+1) ^ (L+1)`, where `t` is the radius of the original code: each level of
concatenation multiplies the radius by `t + 1` (`QECC.concat_correctsChannelErrors_mul`).

The worst-case radius is not the whole story. For independent errors of rate `p`, the tower fails
only when a level-`0` block fails, and a level-`(L+1)` block fails only when more than `t` of its
sub-blocks do (`QECC.FailsPat`). Each level therefore renormalises the error rate through
`p ↦ P(Binomial(m, p) > t) ≤ C(m,t+1) · p^(t+1)`, and below the threshold `C(m,t+1) · p^t < 1` the
failure probability is suppressed doubly exponentially, like `(C(m,t+1)·p^t) ^ ((t+1)^L)`.

## Main results

* `QECC.IterIdx` — the physical register of `L` rounds of self-concatenation, and
  `QECC.card_iterIdx` — it has `m ^ (L+1)` qudits;
* `QECC.iterConcat` — the `L`-fold self-concatenation of a code;
* `QECC.iterConcat_correctsChannelErrors` — it corrects `(t+1)^(L+1) - 1` errors;
* `QECC.iterConcat_correctsLocatedErrors` — with the error locations known, a code of distance `d`
  iterates to one of distance `d ^ (L+1)`;
* `QECC.iterConcat_correctsPattern` — the tower corrects every error pattern that does not fail
  recursively;
* `QECC.patProb_failsPat_le` — **the threshold theorem**: the failure probability of the `L`-level
  tower is at most `(C(m,t+1) · p^t) ^ ((t+1)^L)`, and
  `QECC.exists_correctable_event_ge` packages this as a lower bound on the probability of the
  patterns the tower corrects;
* `QECC.exists_level_patProb_lt` — below the threshold, the failure probability can be made
  smaller than any positive `ε` by taking enough levels.
-/

namespace QuantumLib
namespace QECC

universe u

/-- The physical register of `L` rounds of self-concatenation: each round replaces every qudit by a
block of `io` qudits. -/
def IterIdx (io : Type u) : ℕ → Type u
  | 0 => io
  | L + 1 => IterIdx io L × io

instance instFintypeIterIdx (io : Type u) [Fintype io] : (L : ℕ) → Fintype (IterIdx io L)
  | 0 => inferInstanceAs (Fintype io)
  | L + 1 => @instFintypeProd _ _ (instFintypeIterIdx io L) inferInstance

instance instDecidableEqIterIdx (io : Type u) [DecidableEq io] :
    (L : ℕ) → DecidableEq (IterIdx io L)
  | 0 => inferInstanceAs (DecidableEq io)
  | L + 1 => @instDecidableEqProd _ _ (instDecidableEqIterIdx io L) inferInstance

/-- `L` rounds of concatenation multiply the number of physical qudits: `m ^ (L+1)` of them. -/
theorem card_iterIdx (io : Type u) [Fintype io] :
    ∀ L : ℕ, Fintype.card (IterIdx io L) = Fintype.card io ^ (L + 1)
  | 0 => by
      show Fintype.card io = Fintype.card io ^ 1
      rw [pow_one]
  | L + 1 => by
      show Fintype.card (IterIdx io L × io) = _
      rw [Fintype.card_prod, card_iterIdx io L, ← pow_succ]

variable {d1 io : Type u} [Fintype d1] [DecidableEq d1] [Fintype io] [DecidableEq io]

/-- The `L`-fold self-concatenation of a code whose physical qudits are of the same type as its
logical register, so that it can be plugged into itself. -/
noncomputable def iterConcat (C : QECC d1 io d1) : (L : ℕ) → QECC d1 (IterIdx io L) d1
  | 0 => C
  | L + 1 => (iterConcat C L).concat C

/-- **The correction radius grows exponentially in the number of levels.** A code correcting `t`
errors, concatenated with itself `L` times, corrects `(t+1)^(L+1) - 1` errors on its `m^(L+1)`
qudits. -/
theorem iterConcat_correctsChannelErrors (C : QECC d1 io d1) {t : ℕ}
    (h : C.CorrectsChannelErrors t) :
    ∀ L : ℕ, (iterConcat C L).CorrectsChannelErrors ((t + 1) ^ (L + 1) - 1)
  | 0 => by
      have hrw : (t + 1) ^ (0 + 1) - 1 = t := by simp
      rw [hrw]
      exact h
  | L + 1 => by
      have hstep := concat_correctsChannelErrors_mul (iterConcat C L) C
        (iterConcat_correctsChannelErrors C h L) h
      have hpos : 1 ≤ (t + 1) ^ (L + 1) := Nat.one_le_pow _ _ (Nat.succ_pos t)
      have hrw : ((t + 1) ^ (L + 1) - 1 + 1) * (t + 1) - 1 = (t + 1) ^ (L + 1 + 1) - 1 := by
        rw [Nat.sub_add_cancel hpos, ← pow_succ]
      rwa [hrw] at hstep

/-- **Distances multiply at every level.** If the locations of the errors are known — the erasure
model — a code of distance `d` iterated `L` times has distance `d ^ (L+1)`: it recovers from every
error on a known set of `d ^ (L+1) - 1` qudits. -/
theorem iterConcat_correctsLocatedErrors (C : QECC d1 io d1) {t : ℕ}
    (h : C.CorrectsLocatedErrors t) :
    ∀ L : ℕ, (iterConcat C L).CorrectsLocatedErrors ((t + 1) ^ (L + 1) - 1)
  | 0 => by
      have hrw : (t + 1) ^ (0 + 1) - 1 = t := by simp
      rw [hrw]
      exact h
  | L + 1 => by
      have hstep := concat_correctsLocatedErrors_mul (iterConcat C L) C
        (iterConcat_correctsLocatedErrors C h L) h
      have hpos : 1 ≤ (t + 1) ^ (L + 1) := Nat.one_le_pow _ _ (Nat.succ_pos t)
      have hrw : ((t + 1) ^ (L + 1) - 1 + 1) * (t + 1) - 1 = (t + 1) ^ (L + 1 + 1) - 1 := by
        rw [Nat.sub_add_cancel hpos, ← pow_succ]
      rwa [hrw] at hstep

/-- Unitary errors are a special case: `(t+1)^(L+1) - 1` of them are corrected. -/
theorem iterConcat_correctsErrors (C : QECC d1 io d1) {t : ℕ} (h : C.CorrectsChannelErrors t)
    (L : ℕ) : (iterConcat C L).CorrectsErrors ((t + 1) ^ (L + 1) - 1) :=
  (iterConcat_correctsChannelErrors C h L).correctsErrors

/-! ### Random errors and the threshold -/

open RandomErrors

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem blockErrors_errorSet (f : A × B → Bool) (q : A) :
    blockErrors (errorSet f) q = errorSet (blockPat f q) := by
  ext r
  simp [mem_blockErrors, blockPat]

/-- The two notions of "bad block" agree: the blocks carrying more than `t` errors of the pattern
`f` are exactly the ones the concatenation argument has to hand to the outer code. -/
theorem badBlocks_errorSet (t : ℕ) (f : A × B → Bool) :
    badBlocks t (errorSet f) = errorSet (badPat t f) := by
  ext q
  simp [badPat, blockErrors_errorSet]

/-- **The recursive failure predicate of the tower.** A level-`0` block fails when more than `t` of
its qudits carry errors; a level-`(L+1)` block fails when the pattern of its failed sub-blocks makes
the level-`L` tower fail. -/
def FailsPat (t : ℕ) : (L : ℕ) → (IterIdx io L → Bool) → Bool
  | 0, f => decide (t < (errorSet f).card)
  | L + 1, f => FailsPat t L (badPat t f)

/-- **Every non-failing pattern is corrected.** If the recursive failure predicate does not fire,
the `L`-level tower undoes every channel error supported on the pattern. -/
theorem iterConcat_correctsPattern (C : QECC d1 io d1) {t : ℕ}
    (h : ∀ S : Finset io, S.card ≤ t → C.CorrectsPattern S) :
    ∀ (L : ℕ) (f : IterIdx io L → Bool), FailsPat t L f = false →
      (iterConcat C L).CorrectsPattern (errorSet f)
  | 0, f, hf => by
      have hd : decide (t < (errorSet f).card) = false := hf
      exact h (errorSet f) (Nat.le_of_not_lt (of_decide_eq_false hd))
  | L + 1, f, hf => by
      refine concat_correctsPattern (iterConcat C L) C (Bad := badBlocks t (errorSet f))
        (fun q hq => h _ (Nat.le_of_not_lt fun hc => hq (mem_badBlocks.mpr hc))) ?_
      rw [badBlocks_errorSet]
      exact iterConcat_correctsPattern C h L (badPat t f) hf

/-- **One level renormalises the error rate.** The probability that the `L`-level tower fails on an
independent error pattern of rate `p` is the rate obtained by pushing `p` through `L+1` rounds of
the block failure map. -/
theorem patProb_failsPat (t : ℕ) :
    ∀ (L : ℕ) (p : ℝ), patProb p (FailsPat (io := io) t L) = (blockFailProb io t)^[L + 1] p
  | 0, p => by
      show patProb p (fun f : io → Bool => decide (t < (errorSet f).card)) = _
      rw [Function.iterate_one]
      rfl
  | L + 1, p => by
      have h1 := patProb_badPat (A := IterIdx io L) (B := io) t p (FailsPat t L)
      have h2 := patProb_failsPat t L (blockFailProb io t p)
      show patProb p (fun f : IterIdx io L × io → Bool => FailsPat t L (badPat t f)) = _
      rw [h1, h2, ← Function.iterate_succ_apply]

/-- **The threshold theorem.** Each of the `m ^ (L+1)` physical qudits fails independently with
probability `p`. If the code corrects `t` errors on its `m` qudits, then the `L`-level tower fails
with probability at most `(C(m,t+1) · p^t) ^ ((t+1)^L)`: below the threshold `C(m,t+1) · p^t < 1`
this is a doubly exponential suppression in the number of levels. -/
theorem patProb_failsPat_le (t : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L : ℕ) :
    patProb p (FailsPat (io := io) t L)
      ≤ (((Fintype.card io).choose (t + 1) : ℝ) * p ^ t) ^ (t + 1) ^ L := by
  set c : ℝ := ((Fintype.card io).choose (t + 1) : ℝ) with hc
  set x : ℕ → ℝ := fun L => (blockFailProb io t)^[L] p with hx
  have hx0 : ∀ L, 0 ≤ x L := fun L => (iterate_blockFailProb_mem hp0 hp1 t L).1
  have hx1 : ∀ L, x L ≤ 1 := fun L => (iterate_blockFailProb_mem hp0 hp1 t L).2
  have hrec : ∀ L, x (L + 1) ≤ c * x L ^ (t + 1) := by
    intro L
    have hstep : x (L + 1) = blockFailProb io t (x L) :=
      Function.iterate_succ_apply' (blockFailProb io t) L p
    rw [hstep]
    exact blockFailProb_le (hx0 L) (hx1 L) t
  have hmain := le_pow_of_recursion (c := c) (Nat.cast_nonneg _) x hx0 hx1 hrec L
  rw [patProb_failsPat t L p]
  simpa [hx] using hmain

/-- **The threshold theorem, as a statement about what the tower corrects.** Below the threshold,
the patterns that the `L`-level tower corrects carry all but a doubly exponentially small fraction
of the probability. -/
theorem exists_correctable_event_ge (C : QECC d1 io d1) {t : ℕ}
    (h : C.CorrectsChannelErrors t) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L : ℕ) :
    ∃ E : (IterIdx io L → Bool) → Bool,
      (∀ f, E f = true → (iterConcat C L).CorrectsPattern (errorSet f)) ∧
      1 - (((Fintype.card io).choose (t + 1) : ℝ) * p ^ t) ^ (t + 1) ^ L ≤ patProb p E := by
  refine ⟨fun f => !FailsPat t L f, fun f hf => ?_, ?_⟩
  · exact iterConcat_correctsPattern C (fun S hS => h S hS) L f (by simpa using hf)
  · rw [patProb_not]
    have := patProb_failsPat_le (io := io) t hp0 hp1 L
    linarith

/-- **Below the threshold the failure probability vanishes.** For any target `ε > 0`, enough levels
of concatenation bring the failure probability below it. -/
theorem exists_level_patProb_lt {t : ℕ} (ht : 0 < t) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hthr : ((Fintype.card io).choose (t + 1) : ℝ) * p ^ t < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ, patProb p (FailsPat (io := io) t L) < ε := by
  set q : ℝ := ((Fintype.card io).choose (t + 1) : ℝ) * p ^ t with hq
  have hq0 : 0 ≤ q := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 t)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hthr
  refine ⟨n, lt_of_le_of_lt (patProb_failsPat_le t hp0 hp1 n) (lt_of_le_of_lt ?_ hn)⟩
  exact pow_le_pow_of_le_one hq0 hthr.le (Nat.le_of_lt (Nat.lt_pow_self (by omega)))

end QECC
end QuantumLib
