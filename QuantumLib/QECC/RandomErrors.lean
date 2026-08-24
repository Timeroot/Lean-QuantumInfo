/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Independent random error patterns

The combinatorial probability needed for the threshold theorem: each of `n` sites fails
independently with probability `p`, and we need (i) the probability that a block of sites carries
more than `t` failures, (ii) the fact that the coarse-grained pattern of *failed blocks* is again an
independent pattern, with the block failure probability as its parameter, and (iii) a union bound
`P(more than t failures) ≤ C(n, t+1) · p^(t+1)`.

An error pattern is a function `f : ι → Bool`, and `patWeight p f` is its probability. Events are
`Bool`-valued predicates on patterns, so no decidability side conditions appear.

## Main results

* `RandomErrors.sum_patWeight` — the weights sum to `1`, and `RandomErrors.sum_patWeight_of_subset`
  — the marginal probability that a given set of sites all fail is `p ^ |U|`;
* `RandomErrors.patProb_badPat` — **coarse-graining**: for the product index `A × B`, the pattern of
  bad blocks is an independent pattern on `A` with parameter `blockFailProb B t p`;
* `RandomErrors.blockFailProb_le` — the union bound `blockFailProb B t p ≤ C(|B|, t+1) · p^(t+1)`.
-/

open Finset

namespace QuantumLib
namespace RandomErrors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set of sites that the error pattern `f` hits. -/
def errorSet (f : ι → Bool) : Finset ι := univ.filter fun i => f i

omit [DecidableEq ι] in
@[simp]
theorem mem_errorSet {f : ι → Bool} {i : ι} : i ∈ errorSet f ↔ f i = true := by
  simp [errorSet]

/-- The probability of the error pattern `f`, when each site fails independently with
probability `p`. -/
noncomputable def patWeight (p : ℝ) (f : ι → Bool) : ℝ := ∏ i, if f i then p else 1 - p

/-- The probability that the random error pattern satisfies the event `E`. -/
noncomputable def patProb (p : ℝ) (E : (ι → Bool) → Bool) : ℝ :=
  ∑ f : ι → Bool, if E f then patWeight p f else 0

omit [DecidableEq ι] in
theorem patWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : ι → Bool) :
    0 ≤ patWeight p f := by
  refine Finset.prod_nonneg fun i _ => ?_
  cases hf : f i
  · simpa [hf] using hp1
  · simpa [hf] using hp0

/-- **Marginal probability.** The probability that every site of `U` fails is `p ^ |U|`, whatever
happens elsewhere. -/
theorem sum_patWeight_of_subset (p : ℝ) (U : Finset ι) :
    ∑ f ∈ univ.filter (fun f : ι → Bool => ∀ i ∈ U, f i), patWeight p f = p ^ U.card := by
  classical
  have hfil : (univ.filter fun f : ι → Bool => ∀ i ∈ U, f i)
      = Fintype.piFinset (fun i => if i ∈ U then {true} else univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i ∈ U
      · simp [hi, h i hi]
      · simp [hi]
    · intro h i hi
      have := h i
      simpa [hi] using this
  rw [hfil]
  simp only [patWeight]
  rw [← Finset.prod_univ_sum (t := fun i => if i ∈ U then ({true} : Finset Bool) else univ)
    (f := fun (_ : ι) (b : Bool) => if b then p else 1 - p)]
  have hterm : ∀ i : ι, (∑ b ∈ (if i ∈ U then {true} else univ), if b then p else 1 - p)
      = if i ∈ U then p else 1 := by
    intro i
    by_cases hi : i ∈ U
    · simp [hi]
    · rw [if_neg hi, if_neg hi, Fintype.sum_bool]
      norm_num
  rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_ite_mem, Finset.univ_inter,
    Finset.prod_const]

/-- The pattern weights are a probability distribution. -/
theorem sum_patWeight (p : ℝ) : ∑ f : ι → Bool, patWeight p f = 1 := by
  simpa using sum_patWeight_of_subset p (∅ : Finset ι)

theorem patProb_eq_sum_filter (p : ℝ) (E : (ι → Bool) → Bool) :
    patProb p E = ∑ f ∈ univ.filter (fun f => E f), patWeight p f := by
  rw [patProb, Finset.sum_filter]

theorem patProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : (ι → Bool) → Bool) :
    0 ≤ patProb p E :=
  Finset.sum_nonneg fun f _ => by
    by_cases h : E f
    · simpa [h] using patWeight_nonneg hp0 hp1 f
    · simp [h]

theorem patProb_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : (ι → Bool) → Bool) :
    patProb p E ≤ 1 := by
  rw [← sum_patWeight (ι := ι) p]
  refine Finset.sum_le_sum fun f _ => ?_
  by_cases h : E f
  · simp [h]
  · simpa [h] using patWeight_nonneg hp0 hp1 f

/-- The complementary event. -/
theorem patProb_not (p : ℝ) (E : (ι → Bool) → Bool) :
    patProb p (fun f => !E f) = 1 - patProb p E := by
  have hsum : patProb p E + patProb p (fun f => !E f) = 1 := by
    rw [patProb_eq_sum_filter, patProb_eq_sum_filter]
    have hfil : (univ.filter fun f : ι → Bool => (!E f) = true)
        = univ.filter fun f : ι → Bool => ¬ (E f = true) := by
      apply Finset.filter_congr
      intro f _
      simp
    rw [hfil, Finset.sum_filter_add_sum_filter_not]
    exact sum_patWeight p
  linarith

/-! ### Coarse-graining a product of blocks -/

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The restriction of an error pattern to the block `q`. -/
def blockPat (f : A × B → Bool) (q : A) : B → Bool := fun r => f (q, r)

/-- The pattern of *bad blocks*: those carrying more than `t` errors. -/
def badPat (t : ℕ) (f : A × B → Bool) : A → Bool :=
  fun q => decide (t < (errorSet (blockPat f q)).card)

/-- The probability that a block of `B` sites carries more than `t` errors. -/
noncomputable def blockFailProb (B : Type*) [Fintype B] [DecidableEq B] (t : ℕ) (p : ℝ) : ℝ :=
  patProb p fun h : B → Bool => decide (t < (errorSet h).card)

/-- The blocks with a prescribed pattern of failures, as a product of independent choices. -/
theorem sum_fiber_badPat (t : ℕ) (p : ℝ) (u : A → Bool) :
    ∑ F ∈ univ.filter (fun F : A → B → Bool =>
        (fun q => decide (t < (errorSet (F q)).card)) = u), ∏ q, patWeight p (F q)
      = patWeight (blockFailProb B t p) u := by
  classical
  have hfil : (univ.filter fun F : A → B → Bool =>
        (fun q => decide (t < (errorSet (F q)).card)) = u)
      = Fintype.piFinset
          (fun q => univ.filter fun h : B → Bool => decide (t < (errorSet h).card) = u q) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
  rw [hfil, ← Finset.prod_univ_sum]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hall : ∑ h ∈ univ.filter (fun h : B → Bool => decide (t < (errorSet h).card) = true),
        patWeight p h
      + ∑ h ∈ univ.filter (fun h : B → Bool => ¬ (decide (t < (errorSet h).card) = true)),
        patWeight p h = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact sum_patWeight p
  have hgood : ∑ h ∈ univ.filter (fun h : B → Bool => decide (t < (errorSet h).card) = true),
      patWeight p h = blockFailProb B t p := (patProb_eq_sum_filter p _).symm
  cases hu : u q
  · have hset : (univ.filter fun h : B → Bool => decide (t < (errorSet h).card) = false)
        = univ.filter fun h : B → Bool => ¬ (decide (t < (errorSet h).card) = true) := by
      apply Finset.filter_congr
      intro h _
      simp
    rw [hset]
    simp only [Bool.false_eq_true, if_false]
    linarith [hall, hgood]
  · rw [if_pos rfl]
    exact hgood

/-- **Coarse-graining.** For sites indexed by `A × B`, the pattern of blocks carrying more than `t`
errors is itself an independent random pattern on `A`, with the block failure probability
`blockFailProb B t p` as its parameter. This is the step that turns one level of concatenation into
one renormalisation of the error rate. -/
theorem patProb_badPat (t : ℕ) (p : ℝ) (E : (A → Bool) → Bool) :
    patProb p (fun f : A × B → Bool => E (badPat t f)) = patProb (blockFailProb B t p) E := by
  classical
  have hcurry : ∀ F : A → B → Bool, patWeight p ((Equiv.curry A B Bool).symm F)
      = ∏ q, patWeight p (F q) := by
    intro F
    simp only [patWeight]
    rw [Fintype.prod_prod_type (f := fun z : A × B =>
      if (Equiv.curry A B Bool).symm F z = true then p else 1 - p)]
    rfl
  have hbad : ∀ F : A → B → Bool, badPat t ((Equiv.curry A B Bool).symm F)
      = fun q => decide (t < (errorSet (F q)).card) := fun _ => rfl
  rw [patProb, ← Equiv.sum_comp (Equiv.curry A B Bool).symm]
  rw [Finset.sum_congr rfl fun F (_ : F ∈ (univ : Finset (A → B → Bool))) =>
    by rw [hcurry F, hbad F]]
  rw [← Finset.sum_fiberwise (g := fun F : A → B → Bool =>
    (fun q => decide (t < (errorSet (F q)).card))) univ
    (fun F => if E (fun q => decide (t < (errorSet (F q)).card)) then ∏ q, patWeight p (F q)
      else 0)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hcong : ∀ F ∈ univ.filter (fun F : A → B → Bool =>
      (fun q => decide (t < (errorSet (F q)).card)) = u),
      (if E (fun q => decide (t < (errorSet (F q)).card)) then ∏ q, patWeight p (F q) else 0)
        = if E u then ∏ q, patWeight p (F q) else 0 := by
    intro F hF
    rw [(Finset.mem_filter.mp hF).2]
  rw [Finset.sum_congr rfl hcong]
  by_cases hE : E u
  · simp only [hE, if_true]
    exact sum_fiber_badPat t p u
  · simp [hE]

theorem blockFailProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    0 ≤ blockFailProb B t p := patProb_nonneg hp0 hp1 _

theorem blockFailProb_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    blockFailProb B t p ≤ 1 := patProb_le_one hp0 hp1 _

/-- **Union bound.** A block of `n` sites carries more than `t` errors only if some `t+1` of its
sites all fail, and there are `C(n, t+1)` ways for that to happen. -/
theorem blockFailProb_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    blockFailProb B t p ≤ (Fintype.card B).choose (t + 1) * p ^ (t + 1) := by
  classical
  set K : Finset (Finset B) := Finset.powersetCard (t + 1) univ with hK
  have hnn : ∀ (h : B → Bool) (U : Finset B),
      0 ≤ if (∀ i ∈ U, h i = true) then patWeight p h else 0 := by
    intro h U
    by_cases hc : ∀ i ∈ U, h i = true
    · rw [if_pos hc]
      exact patWeight_nonneg hp0 hp1 h
    · rw [if_neg hc]
  have key : ∀ h : B → Bool, (if t < (errorSet h).card then patWeight p h else 0)
      ≤ ∑ U ∈ K, (if (∀ i ∈ U, h i = true) then patWeight p h else 0) := by
    intro h
    by_cases hc : t < (errorSet h).card
    · obtain ⟨U, hUsub, hUcard⟩ := Finset.exists_subset_card_eq (s := errorSet h) hc
      have hUK : U ∈ K := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hUcard⟩
      have hUall : ∀ i ∈ U, h i = true := fun i hi => mem_errorSet.mp (hUsub hi)
      have hsingle := Finset.single_le_sum (f := fun U : Finset B =>
        if (∀ i ∈ U, h i = true) then patWeight p h else 0) (fun U _ => hnn h U) hUK
      rw [if_pos hUall] at hsingle
      rw [if_pos hc]
      exact hsingle
    · rw [if_neg hc]
      exact Finset.sum_nonneg fun U _ => hnn h U
  calc blockFailProb B t p
      = ∑ h : B → Bool, (if t < (errorSet h).card then patWeight p h else 0) := by
        rw [blockFailProb, patProb]
        exact Finset.sum_congr rfl fun h _ => by simp
    _ ≤ ∑ h : B → Bool, ∑ U ∈ K, (if (∀ i ∈ U, h i = true) then patWeight p h else 0) :=
        Finset.sum_le_sum fun h _ => key h
    _ = ∑ U ∈ K, ∑ h : B → Bool, (if (∀ i ∈ U, h i = true) then patWeight p h else 0) :=
        Finset.sum_comm
    _ = ∑ U ∈ K, p ^ (t + 1) := by
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [← Finset.sum_filter]
        rw [sum_patWeight_of_subset p U, (Finset.mem_powersetCard.mp hU).2]
    _ = (Fintype.card B).choose (t + 1) * p ^ (t + 1) := by
        rw [Finset.sum_const, hK, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]

/-! ### Iterating the block failure probability -/

/-- Renormalising an error rate keeps it a probability. -/
theorem iterate_blockFailProb_mem {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    ∀ L : ℕ, 0 ≤ (blockFailProb B t)^[L] p ∧ (blockFailProb B t)^[L] p ≤ 1
  | 0 => ⟨hp0, hp1⟩
  | L + 1 => by
      rw [Function.iterate_succ_apply']
      obtain ⟨h0, h1⟩ := iterate_blockFailProb_mem hp0 hp1 t L
      exact ⟨blockFailProb_nonneg h0 h1 t, blockFailProb_le_one h0 h1 t⟩

/-- **Doubly exponential suppression, in the abstract.** A sequence of probabilities in which each
term is at most `c` times the `(t+1)`-st power of its predecessor has its *renormalised* value
`c · xₗ ^ t` raised to the power `(t+1)^L`: below the threshold `c · x₀ ^ t < 1` this collapses at a
doubly exponential rate. -/
theorem mul_pow_le_of_recursion {c : ℝ} (hc : 0 ≤ c) {t : ℕ} (x : ℕ → ℝ) (hx0 : ∀ L, 0 ≤ x L)
    (hrec : ∀ L, x (L + 1) ≤ c * x L ^ (t + 1)) :
    ∀ L : ℕ, c * x L ^ t ≤ (c * x 0 ^ t) ^ (t + 1) ^ L
  | 0 => by rw [pow_zero, pow_one]
  | L + 1 => by
      have hstep : c * x (L + 1) ^ t ≤ (c * x L ^ t) ^ (t + 1) := by
        have hpow : x (L + 1) ^ t ≤ (c * x L ^ (t + 1)) ^ t :=
          pow_le_pow_left₀ (hx0 (L + 1)) (hrec L) t
        calc c * x (L + 1) ^ t ≤ c * (c * x L ^ (t + 1)) ^ t :=
              mul_le_mul_of_nonneg_left hpow hc
          _ = (c * x L ^ t) ^ (t + 1) := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
              ring
      have hIH := mul_pow_le_of_recursion hc x hx0 hrec L
      have hnn : 0 ≤ c * x L ^ t := mul_nonneg hc (pow_nonneg (hx0 L) t)
      calc c * x (L + 1) ^ t ≤ (c * x L ^ t) ^ (t + 1) := hstep
        _ ≤ ((c * x 0 ^ t) ^ (t + 1) ^ L) ^ (t + 1) := pow_le_pow_left₀ hnn hIH _
        _ = (c * x 0 ^ t) ^ (t + 1) ^ (L + 1) := by rw [← pow_mul, ← pow_succ]

/-- The same recursion, read as a bound on the sequence itself: from the second term on, a rate
below the threshold `c · x₀ ^ t < 1` is suppressed like `(c · x₀ ^ t) ^ (t+1)^L`. -/
theorem le_pow_of_recursion {c : ℝ} (hc : 0 ≤ c) {t : ℕ} (x : ℕ → ℝ) (hx0 : ∀ L, 0 ≤ x L)
    (hx1 : ∀ L, x L ≤ 1) (hrec : ∀ L, x (L + 1) ≤ c * x L ^ (t + 1)) (L : ℕ) :
    x (L + 1) ≤ (c * x 0 ^ t) ^ (t + 1) ^ L := by
  have hnn : 0 ≤ (c * x 0 ^ t) ^ (t + 1) ^ L :=
    pow_nonneg (mul_nonneg hc (pow_nonneg (hx0 0) t)) _
  calc x (L + 1) ≤ c * x L ^ (t + 1) := hrec L
    _ = (c * x L ^ t) * x L := by
      rw [pow_succ]
      ring
    _ ≤ (c * x 0 ^ t) ^ (t + 1) ^ L * 1 :=
        mul_le_mul (mul_pow_le_of_recursion hc x hx0 hrec L) (hx1 L) (hx0 L) hnn
    _ = (c * x 0 ^ t) ^ (t + 1) ^ L := mul_one _

end RandomErrors
end QuantumLib
