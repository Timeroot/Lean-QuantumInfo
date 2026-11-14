/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Real.Basic
public import QIT.Symmetry.SymmetricSubspace

/-!
# Finite classical strong typicality

Finite count/frequency API for the classical strong-typicality step used in
the HSW direct proof.  The key source route is Wilde's
`prop-qt:cond-state-with-uncond-proj`: after pinching a codeword product state
in the average state's eigenbasis, one needs a classical statement saying that
`Z^n | X^n = x^n` is marginally typical with high probability whenever `x^n`
is strongly typical.  This module provides the reusable finite definitions and
the deterministic conditional-to-marginal bridge for that route.

Source: [Wilde2011Qst, qit-notes.tex:28892-28904].
-/

@[expose] public section

open scoped BigOperators NNReal

namespace QIT

universe u v

noncomputable section

/-- A finite classical probability distribution. -/
structure FiniteDistribution (α : Type u) [Fintype α] where
  prob : α → ℝ≥0
  sum_eq_one : ∑ x, prob x = 1

namespace FiniteDistribution

variable {α : Type u} [Fintype α]

theorem prob_le_one (p : FiniteDistribution α) (x : α) :
    p.prob x ≤ 1 := by
  have hx : p.prob x ≤ ∑ y : α, p.prob y := by
    exact Finset.single_le_sum (fun y _ => by positivity) (Finset.mem_univ x)
  simpa [p.sum_eq_one] using hx

end FiniteDistribution

/-- A finite stochastic kernel `α → β`. -/
structure StochasticKernel (α : Type u) (β : Type v) [Fintype β] where
  prob : α → β → ℝ≥0
  sum_eq_one : ∀ x, ∑ z, prob x z = 1

namespace StochasticKernel

variable {α : Type u} {β : Type v} [Fintype β]

theorem prob_le_one (K : StochasticKernel α β) (x : α) (z : β) :
    K.prob x z ≤ 1 := by
  have hz : K.prob x z ≤ ∑ y : β, K.prob x y := by
    exact Finset.single_le_sum (fun y _ => by positivity) (Finset.mem_univ z)
  simpa [K.sum_eq_one x] using hz

end StochasticKernel

namespace ClassicalTypicality

variable {α : Type u} {β : Type v}

/-- Count occurrences of a symbol in a finite word. -/
def wordCount [DecidableEq α] {n : ℕ} (w : Fin n → α) (x : α) : ℕ :=
  (Finset.univ.filter fun i : Fin n => w i = x).card

/-- Joint count of the pair `(x,z)` in two same-length words. -/
def pairCount [DecidableEq α] [DecidableEq β] {n : ℕ}
    (xseq : Fin n → α) (zseq : Fin n → β) (x : α) (z : β) : ℕ :=
  (Finset.univ.filter fun i : Fin n => xseq i = x ∧ zseq i = z).card

/-- Empirical frequency of a symbol in a finite word. -/
def wordFreq [DecidableEq α] {n : ℕ} (w : Fin n → α) (x : α) : ℝ :=
  (wordCount w x : ℝ) / (n : ℝ)

/-- Empirical joint frequency of `(x,z)` in two same-length words. -/
def pairFreq [DecidableEq α] [DecidableEq β] {n : ℕ}
    (xseq : Fin n → α) (zseq : Fin n → β) (x : α) (z : β) : ℝ :=
  (pairCount xseq zseq x z : ℝ) / (n : ℝ)

/-- Strong typicality of a word relative to a finite distribution, using an
absolute per-symbol frequency tolerance. -/
def StrongTypical [Fintype α] [DecidableEq α] {n : ℕ}
    (p : QIT.FiniteDistribution α) (w : Fin n → α) (δ : ℝ) : Prop :=
  ∀ x, |wordFreq w x - (p.prob x : ℝ)| ≤ δ

/-- I.i.d. product mass of an input word under a finite distribution. -/
def iidProductMass [Fintype α] {n : ℕ}
    (p : QIT.FiniteDistribution α) (w : Fin n → α) : ℝ≥0 :=
  ∏ i : Fin n, p.prob (w i)

/-- The i.i.d. product law over length-`n` words is normalized. -/
theorem iidProductMass_sum_eq_one [Fintype α] [DecidableEq α] {n : ℕ}
    (p : QIT.FiniteDistribution α) :
    ∑ w : Fin n → α, iidProductMass p w = 1 := by
  classical
  unfold iidProductMass
  calc
    ∑ w : Fin n → α, ∏ i : Fin n, p.prob (w i)
        = ∑ w ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset α)),
            ∏ i : Fin n, p.prob (w i) := by
              rw [Fintype.piFinset_univ]
      _ = ∏ i : Fin n, ∑ x ∈ (Finset.univ : Finset α), p.prob x := by
              rw [Finset.sum_prod_piFinset]
      _ = ∏ _i : Fin n, (1 : ℝ≥0) := by
              refine Finset.prod_congr rfl fun _i _ => ?_
              simpa using p.sum_eq_one
      _ = 1 := by simp

/-- Finite event mass under the i.i.d. input product law. -/
def iidEventMass [Fintype α] {n : ℕ}
    (p : QIT.FiniteDistribution α) (event : (Fin n → α) → Prop)
    [DecidablePred event] : ℝ≥0 :=
  ∑ w : Fin n → α, if event w then iidProductMass p w else 0

/-- View a finite distribution as a stochastic kernel from the one-point
alphabet.  This lets the ordinary i.i.d. typical-set estimate reuse the
conditional-product Chebyshev/union-bound API below. -/
def distributionKernel [Fintype α] (p : QIT.FiniteDistribution α) :
    QIT.StochasticKernel Unit α where
  prob _ x := p.prob x
  sum_eq_one _ := p.sum_eq_one

@[simp]
theorem distributionKernel_prob [Fintype α] (p : QIT.FiniteDistribution α)
    (x : Unit) (a : α) :
    (distributionKernel p).prob x a = p.prob a :=
  rfl

/-- The subtype of length-`n` words strongly typical with respect to `p`. -/
def StrongTypicalWord [Fintype α] [DecidableEq α] (p : QIT.FiniteDistribution α)
    (n : ℕ) (δ : ℝ) : Type u :=
  { w : Fin n → α // StrongTypical p w δ }

namespace StrongTypicalWord

variable [Fintype α] [DecidableEq α] {n : ℕ}

instance (p : QIT.FiniteDistribution α) (δ : ℝ) :
    Fintype (StrongTypicalWord p n δ) :=
  by
    classical
    exact inferInstanceAs (Fintype { w : Fin n → α // StrongTypical p w δ })

instance (p : QIT.FiniteDistribution α) (δ : ℝ) :
    DecidableEq (StrongTypicalWord p n δ) :=
  by
    classical
    exact inferInstanceAs (DecidableEq { w : Fin n → α // StrongTypical p w δ })

/-- Inclusion of the strongly typical subtype into all words. -/
def codeword (p : QIT.FiniteDistribution α) (δ : ℝ)
    (x : StrongTypicalWord p n δ) : Fin n → α :=
  x.1

@[simp]
theorem strongTypical (p : QIT.FiniteDistribution α) (δ : ℝ)
    (x : StrongTypicalWord p n δ) :
    StrongTypical p (codeword p δ x) δ :=
  x.2

end StrongTypicalWord

/-- I.i.d. mass of the strongly typical set. -/
def strongTypicalMass [Fintype α] [DecidableEq α] {n : ℕ}
    (p : QIT.FiniteDistribution α) (δ : ℝ) : ℝ≥0 :=
  ∑ x : StrongTypicalWord p n δ, iidProductMass p (StrongTypicalWord.codeword p δ x)

/-- The sum over the strongly typical subtype is the strongly typical event mass. -/
theorem sum_iidProductMass_strongTypicalWord_eq_mass
    [Fintype α] [DecidableEq α] {n : ℕ}
    (p : QIT.FiniteDistribution α) (δ : ℝ) :
    (∑ x : StrongTypicalWord p n δ,
        iidProductMass p (StrongTypicalWord.codeword p δ x)) =
      strongTypicalMass (n := n) p δ := by
  rfl

/-- The strongly-typical subtype mass is the same as the finite event mass of
the strongly-typical predicate. -/
theorem strongTypicalMass_eq_iidEventMass
    [Fintype α] [DecidableEq α] {n : ℕ}
    (p : QIT.FiniteDistribution α) (δ : ℝ) :
    strongTypicalMass (n := n) p δ =
      @iidEventMass α _ n p (fun w : Fin n → α => StrongTypical p w δ)
        (Classical.decPred _) := by
  classical
  unfold strongTypicalMass iidEventMass StrongTypicalWord StrongTypicalWord.codeword
  rw [← Finset.sum_subtype
    (s := (Finset.univ.filter fun w : Fin n → α => StrongTypical p w δ))
    (h := by intro w; simp)
    (f := fun w : Fin n → α => iidProductMass p w)]
  rw [Finset.sum_filter]

/-- The pruned i.i.d. distribution on the strongly typical subtype.  The
normalizing mass is explicit because the HSW proof obtains positivity from the
high-probability typical-set estimate. -/
def prunedStrongTypicalDistribution [Fintype α] [DecidableEq α] {n : ℕ}
    (p : QIT.FiniteDistribution α) (δ : ℝ)
    (hmass : 0 < strongTypicalMass (n := n) p δ) :
    QIT.FiniteDistribution (StrongTypicalWord p n δ) where
  prob x := iidProductMass p (StrongTypicalWord.codeword p δ x) /
    strongTypicalMass (n := n) p δ
  sum_eq_one := by
    classical
    have hmass_ne : strongTypicalMass (n := n) p δ ≠ 0 := ne_of_gt hmass
    calc
      ∑ x : StrongTypicalWord p n δ,
          iidProductMass p (StrongTypicalWord.codeword p δ x) /
            strongTypicalMass (n := n) p δ
          =
        (∑ x : StrongTypicalWord p n δ,
          iidProductMass p (StrongTypicalWord.codeword p δ x)) /
            strongTypicalMass (n := n) p δ := by
            rw [Finset.sum_div]
      _ = strongTypicalMass (n := n) p δ / strongTypicalMass (n := n) p δ := by
            rw [sum_iidProductMass_strongTypicalWord_eq_mass]
      _ = 1 := by
            exact div_self hmass_ne

/-- Pointwise domination of the pruned strongly-typical law by the renormalized
i.i.d. product law.  This is the classical probability kernel behind the HSW
`(1 - ε)⁻¹` pruned-distribution prefactor. -/
theorem prunedStrongTypicalDistribution_prob_le_inv_one_sub
    [Fintype α] [DecidableEq α] {n : ℕ}
    (p : QIT.FiniteDistribution α) {δ pruneε : ℝ}
    (hmass_pos : 0 < strongTypicalMass (n := n) p δ)
    (hmass_lower : (1 - pruneε : ℝ) ≤ (strongTypicalMass (n := n) p δ : ℝ))
    (hprune : pruneε < 1) (x : StrongTypicalWord p n δ) :
    ((prunedStrongTypicalDistribution p δ hmass_pos).prob x : ℝ) ≤
      (1 - pruneε)⁻¹ *
        ∏ i : Fin n, (p.prob (StrongTypicalWord.codeword p δ x i) : ℝ) := by
  classical
  have hpos : 0 < 1 - pruneε := by linarith
  have hmass_real_pos : 0 < (strongTypicalMass (n := n) p δ : ℝ) := by
    exact_mod_cast hmass_pos
  have hden_le : 1 - pruneε ≤ (strongTypicalMass (n := n) p δ : ℝ) := hmass_lower
  have hinv_le : ((strongTypicalMass (n := n) p δ : ℝ))⁻¹ ≤ (1 - pruneε)⁻¹ :=
    inv_anti₀ hpos hden_le
  have hprod_nonneg :
      0 ≤ ∏ i : Fin n, (p.prob (StrongTypicalWord.codeword p δ x i) : ℝ) := by
    refine Finset.prod_nonneg fun i _ => ?_
    exact NNReal.coe_nonneg _
  calc
    ((prunedStrongTypicalDistribution p δ hmass_pos).prob x : ℝ)
        =
      (∏ i : Fin n, (p.prob (StrongTypicalWord.codeword p δ x i) : ℝ)) *
        ((strongTypicalMass (n := n) p δ : ℝ))⁻¹ := by
        unfold prunedStrongTypicalDistribution iidProductMass
        simp [div_eq_mul_inv]
    _ ≤
      (∏ i : Fin n, (p.prob (StrongTypicalWord.codeword p δ x i) : ℝ)) *
        (1 - pruneε)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv_le hprod_nonneg
    _ =
      (1 - pruneε)⁻¹ *
        ∏ i : Fin n, (p.prob (StrongTypicalWord.codeword p δ x i) : ℝ) := by
        ring

/-- Conditional strong typicality in the form needed for the deterministic
bridge: each empirical pair frequency is close to the empirical input
frequency times the channel law `K(z|x)`.

This is the finite-count form of the conditional-typicality output produced by
the source's conditional LLN step. -/
def StrongConditionallyTypical [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {n : ℕ} (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (zseq : Fin n → β)
    (δ : ℝ) : Prop :=
  ∀ x z, |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)| ≤ δ

/-- Marginal output distribution induced by an input distribution and a
stochastic kernel. -/
def inducedMarginal [Fintype α] [Fintype β]
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β) :
    QIT.FiniteDistribution β where
  prob z := ∑ x, p.prob x * K.prob x z
  sum_eq_one := by
    classical
    calc
      ∑ z : β, ∑ x : α, p.prob x * K.prob x z
          = ∑ x : α, ∑ z : β, p.prob x * K.prob x z := by
              rw [Finset.sum_comm]
      _ = ∑ x : α, p.prob x * ∑ z : β, K.prob x z := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]
      _ = ∑ x : α, p.prob x := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [K.sum_eq_one x, mul_one]
      _ = 1 := p.sum_eq_one

@[simp]
theorem inducedMarginal_prob [Fintype α] [Fintype β]
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β) (z : β) :
    (inducedMarginal p K).prob z = ∑ x, p.prob x * K.prob x z := rfl

/-- Conditional product mass of an output word `zseq` given a fixed input word
`xseq` through the memoryless kernel `K`. -/
def conditionalProductMass [Fintype β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (zseq : Fin n → β) :
    ℝ≥0 :=
  ∏ i : Fin n, K.prob (xseq i) (zseq i)

/-- Finite event mass under the conditional product law. -/
def conditionalEventMass [Fintype β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (event : (Fin n → β) → Prop)
    [DecidablePred event] : ℝ≥0 :=
  ∑ zseq : Fin n → β, if event zseq then conditionalProductMass K xseq zseq else 0

theorem conditionalProductMass_sum_eq_one [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) :
    ∑ zseq : Fin n → β, conditionalProductMass K xseq zseq = 1 := by
  classical
  unfold conditionalProductMass
  calc
    ∑ zseq : Fin n → β, ∏ i : Fin n, K.prob (xseq i) (zseq i)
        = ∑ zseq ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset β)),
            ∏ i : Fin n, K.prob (xseq i) (zseq i) := by
              rw [Fintype.piFinset_univ]
      _ = ∏ i : Fin n, ∑ z ∈ (Finset.univ : Finset β), K.prob (xseq i) z := by
              rw [Finset.sum_prod_piFinset]
      _ = ∏ i : Fin n, (1 : ℝ≥0) := by
                  refine Finset.prod_congr rfl fun i _ => ?_
                  simpa using K.sum_eq_one (xseq i)
      _ = 1 := by simp

@[simp]
theorem wordCount_unit {n : ℕ} (xseq : Fin n → Unit) :
    wordCount xseq () = n := by
  classical
  unfold wordCount
  simp

theorem wordFreq_unit {n : ℕ} (xseq : Fin n → Unit) (hn : 0 < n) :
    wordFreq xseq () = 1 := by
  unfold wordFreq
  rw [wordCount_unit]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn_ne]

@[simp]
theorem pairCount_unit_left [DecidableEq β] {n : ℕ}
    (xseq : Fin n → Unit) (zseq : Fin n → β) (z : β) :
    pairCount xseq zseq () z = wordCount zseq z := by
  classical
  unfold pairCount wordCount
  simp

theorem pairFreq_unit_left [DecidableEq β] {n : ℕ}
    (xseq : Fin n → Unit) (zseq : Fin n → β) (z : β) :
    pairFreq xseq zseq () z = wordFreq zseq z := by
  unfold pairFreq wordFreq
  rw [pairCount_unit_left]

theorem conditionalProductMass_distributionKernel_eq_iidProductMass
    [Fintype β] {n : ℕ} (p : QIT.FiniteDistribution β)
    (xseq : Fin n → Unit) (zseq : Fin n → β) :
    conditionalProductMass (distributionKernel p) xseq zseq =
      iidProductMass p zseq := by
  unfold conditionalProductMass iidProductMass distributionKernel
  simp

theorem strongConditionallyTypical_distributionKernel_iff_strongTypical
    [Fintype β] [DecidableEq β] {n : ℕ} (p : QIT.FiniteDistribution β)
    (xseq : Fin n → Unit) (zseq : Fin n → β) {δ : ℝ} (hn : 0 < n) :
    StrongConditionallyTypical (distributionKernel p) xseq zseq δ ↔
      StrongTypical p zseq δ := by
  constructor
  · intro h z
    have hz := h () z
    simpa [pairFreq_unit_left, wordFreq_unit xseq hn] using hz
  · intro h x z
    cases x
    simpa [pairFreq_unit_left, wordFreq_unit xseq hn] using h z

theorem conditionalProductMass_expect_coordinate [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (i : Fin n) (f : β → ℝ) :
    ∑ zseq : Fin n → β, (conditionalProductMass K xseq zseq : ℝ) * f (zseq i) =
      ∑ z : β, (K.prob (xseq i) z : ℝ) * f z := by
  classical
  unfold conditionalProductMass
  calc
    ∑ zseq : Fin n → β, ((∏ j : Fin n, K.prob (xseq j) (zseq j) : ℝ≥0) : ℝ) *
        f (zseq i)
        =
      ∑ zseq ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset β)),
        ∏ j : Fin n,
          ((K.prob (xseq j) (zseq j) : ℝ) *
            if j = i then f (zseq j) else 1) := by
        rw [Fintype.piFinset_univ]
        refine Finset.sum_congr rfl fun zseq _ => ?_
        rw [Finset.prod_mul_distrib]
        rw [Finset.prod_ite_eq']
        simp
    _ =
      ∏ j : Fin n, ∑ z ∈ (Finset.univ : Finset β),
        ((K.prob (xseq j) z : ℝ) * if j = i then f z else 1) := by
        exact Finset.sum_prod_piFinset
          (s := (Finset.univ : Finset β))
          (g := fun j z => ((K.prob (xseq j) z : ℝ) * if j = i then f z else 1))
    _ =
      ∏ j : Fin n, ∑ z : β,
        ((K.prob (xseq j) z : ℝ) * if j = i then f z else 1) := by
        simp
    _ = ∑ z : β, (K.prob (xseq i) z : ℝ) * f z := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hj
          have hsum : ∑ z : β, (K.prob (xseq j) z : ℝ) = 1 := by
            exact_mod_cast K.sum_eq_one (xseq j)
          simp [hj, hsum]
        · simp

theorem conditionalProductMass_expect_two_coordinates [Fintype β] [DecidableEq β]
    {n : ℕ} (K : QIT.StochasticKernel α β) (xseq : Fin n → α)
    {i j : Fin n} (hij : i ≠ j) (f g : β → ℝ) :
    ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) * (f (zseq i) * g (zseq j)) =
      (∑ z : β, (K.prob (xseq i) z : ℝ) * f z) *
        (∑ z : β, (K.prob (xseq j) z : ℝ) * g z) := by
  classical
  unfold conditionalProductMass
  calc
    ∑ zseq : Fin n → β,
        ((∏ l : Fin n, K.prob (xseq l) (zseq l) : ℝ≥0) : ℝ) *
          (f (zseq i) * g (zseq j))
        =
      ∑ zseq ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset β)),
        ∏ l : Fin n,
          (((K.prob (xseq l) (zseq l) : ℝ) *
              (if l = i then f (zseq l) else 1)) *
            (if l = j then g (zseq l) else 1)) := by
        rw [Fintype.piFinset_univ]
        refine Finset.sum_congr rfl fun zseq _ => ?_
        rw [Finset.prod_mul_distrib]
        rw [Finset.prod_mul_distrib]
        rw [Finset.prod_ite_eq']
        rw [Finset.prod_ite_eq']
        simp [mul_assoc, mul_left_comm, mul_comm]
    _ =
      ∏ l : Fin n, ∑ z ∈ (Finset.univ : Finset β),
        (((K.prob (xseq l) z : ℝ) *
            (if l = i then f z else 1)) *
          (if l = j then g z else 1)) := by
        exact Finset.sum_prod_piFinset
          (s := (Finset.univ : Finset β))
          (g := fun l z =>
            (((K.prob (xseq l) z : ℝ) * (if l = i then f z else 1)) *
              (if l = j then g z else 1)))
    _ =
      ∏ l : Fin n, ∑ z : β,
        (((K.prob (xseq l) z : ℝ) *
            (if l = i then f z else 1)) *
          (if l = j then g z else 1)) := by
        simp
    _ =
      (∑ z : β, (K.prob (xseq i) z : ℝ) * f z) *
        (∑ z : β, (K.prob (xseq j) z : ℝ) * g z) := by
        let F : Fin n → ℝ := fun l =>
          ∑ z : β,
            (((K.prob (xseq l) z : ℝ) *
                (if l = i then f z else 1)) *
              (if l = j then g z else 1))
        change (∏ l : Fin n, F l) =
          (∑ z : β, (K.prob (xseq i) z : ℝ) * f z) *
            (∑ z : β, (K.prob (xseq j) z : ℝ) * g z)
        have hFi : F i = ∑ z : β, (K.prob (xseq i) z : ℝ) * f z := by
          simp [F, hij]
        have hFj : F j = ∑ z : β, (K.prob (xseq j) z : ℝ) * g z := by
          simp [F, hij.symm, mul_assoc]
        have hFrest : ∀ l ∈ (Finset.univ.erase i).erase j, F l = 1 := by
          intro l hl
          have hli : l ≠ i := by
            exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hl)).1
          have hlj : l ≠ j := by
            exact (Finset.mem_erase.mp hl).1
          have hsum : ∑ z : β, (K.prob (xseq l) z : ℝ) = 1 := by
            exact_mod_cast K.sum_eq_one (xseq l)
          simp [F, hli, hlj, hsum]
        rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i)]
        rw [Finset.sdiff_singleton_eq_erase]
        have hjmem : j ∈ Finset.univ.erase i := by
          simp [hij.symm]
        rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hjmem]
        rw [Finset.sdiff_singleton_eq_erase]
        rw [Finset.prod_eq_one hFrest]
        rw [hFi, hFj]
        ring

theorem conditionalEventMass_le_one [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α)
    (event : (Fin n → β) → Prop) [DecidablePred event] :
    conditionalEventMass K xseq event ≤ 1 := by
  classical
  unfold conditionalEventMass
  calc
    ∑ zseq : Fin n → β, (if event zseq then conditionalProductMass K xseq zseq else 0)
        ≤ ∑ zseq : Fin n → β, conditionalProductMass K xseq zseq := by
            refine Finset.sum_le_sum fun zseq _ => ?_
            by_cases hz : event zseq <;> simp [hz]
    _ = 1 := conditionalProductMass_sum_eq_one K xseq

theorem conditionalEventMass_add_compl_eq_one [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α)
    (event : (Fin n → β) → Prop) [DecidablePred event] :
    (conditionalEventMass K xseq event : ℝ) +
      (conditionalEventMass K xseq (fun zseq => ¬ event zseq) : ℝ) = 1 := by
  classical
  unfold conditionalEventMass
  rw [NNReal.coe_sum, NNReal.coe_sum]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ zseq : Fin n → β,
        (((if event zseq then conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ) +
          ((if ¬ event zseq then conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ))
        =
      ∑ zseq : Fin n → β, (conditionalProductMass K xseq zseq : ℝ) := by
        refine Finset.sum_congr rfl fun zseq _ => ?_
        by_cases hz : event zseq <;> simp [hz]
    _ = 1 := by
        exact_mod_cast conditionalProductMass_sum_eq_one K xseq

/-- Conditional-typical event mass for the finite conditional product law. -/
def conditionalTypicalMass [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (δ : ℝ) : ℝ≥0 :=
  by
    classical
    exact conditionalEventMass K xseq
      (fun zseq => StrongConditionallyTypical K xseq zseq δ)

/-- Complementary mass of the conditionally non-typical event. -/
def conditionalNontypicalMass [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {n : ℕ} (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (δ : ℝ) : ℝ≥0 :=
  by
    classical
    exact conditionalEventMass K xseq
      (fun zseq => ¬ StrongConditionallyTypical K xseq zseq δ)

theorem conditionalTypicalMass_distributionKernel_eq_strongTypicalMass
    [Fintype β] [DecidableEq β] {n : ℕ} (p : QIT.FiniteDistribution β)
    (xseq : Fin n → Unit) (δ : ℝ) (hn : 0 < n) :
    conditionalTypicalMass (distributionKernel p) xseq δ =
      strongTypicalMass (n := n) p δ := by
  classical
  rw [strongTypicalMass_eq_iidEventMass]
  unfold conditionalTypicalMass conditionalEventMass iidEventMass
  refine Finset.sum_congr rfl fun zseq _ => ?_
  rw [conditionalProductMass_distributionKernel_eq_iidProductMass]
  have hiff :=
    strongConditionallyTypical_distributionKernel_iff_strongTypical
      p xseq zseq (δ := δ) hn
  by_cases htyp : StrongTypical p zseq δ
  · have hcond : StrongConditionallyTypical (distributionKernel p) xseq zseq δ :=
      hiff.mpr htyp
    simp [htyp, hcond]
  · have hcond : ¬ StrongConditionallyTypical (distributionKernel p) xseq zseq δ := by
      intro h'
      exact htyp (hiff.mp h')
    simp [htyp, hcond]

/-- Centered coordinate indicator for the pair `(x,z)` under the conditional
product law.  Coordinates whose input symbol is not `x` contribute zero; the
remaining coordinates are Bernoulli indicators centered at `K(z|x)`. -/
def centeredPairIndicator [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β)
    (i : Fin n) (zseq : Fin n → β) : ℝ :=
  if xseq i = x then
    (if zseq i = z then (1 : ℝ) else 0) - (K.prob x z : ℝ)
  else 0

theorem sum_pairIndicator_eq_pairCount
    [DecidableEq α] [DecidableEq β] {n : ℕ}
    (xseq : Fin n → α) (zseq : Fin n → β) (x : α) (z : β) :
    (∑ i : Fin n, if xseq i = x ∧ zseq i = z then (1 : ℝ) else 0) =
      (pairCount xseq zseq x z : ℝ) := by
  classical
  unfold pairCount
  rw [Finset.sum_boole]

theorem sum_inputIndicator_eq_wordCount
    [DecidableEq α] {n : ℕ} (xseq : Fin n → α) (x : α) :
    (∑ i : Fin n, if xseq i = x then (1 : ℝ) else 0) =
      (wordCount xseq x : ℝ) := by
  classical
  unfold wordCount
  rw [Finset.sum_boole]

theorem wordCount_le_length [DecidableEq α] {n : ℕ} (xseq : Fin n → α) (x : α) :
    wordCount xseq x ≤ n := by
  classical
  unfold wordCount
  simpa using
    Finset.card_le_card
      (Finset.filter_subset (fun i : Fin n => xseq i = x) Finset.univ)

theorem wordCount_real_le_length [DecidableEq α] {n : ℕ} (xseq : Fin n → α) (x : α) :
    (wordCount xseq x : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast wordCount_le_length xseq x

/-- Sum a symbol observable along a finite word by grouping coordinates with
the same symbol. -/
theorem sum_eq_sum_wordCount_mul [Fintype α] [DecidableEq α] {n : ℕ}
    (xseq : Fin n → α) (f : α → ℝ) :
    (∑ i : Fin n, f (xseq i)) =
      ∑ x : α, (wordCount xseq x : ℝ) * f x := by
  classical
  calc
    (∑ i : Fin n, f (xseq i)) =
        ∑ i : Fin n, ∑ x : α, if xseq i = x then f x else 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single (xseq i)]
          · simp
          · intro x _ hx
            simp [hx.symm]
          · intro h
            exact (h (Finset.mem_univ (xseq i))).elim
    _ = ∑ x : α, ∑ i : Fin n, if xseq i = x then f x else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x : α, (wordCount xseq x : ℝ) * f x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          calc
            (∑ i : Fin n, if xseq i = x then f x else 0) =
                ∑ i : Fin n, (if xseq i = x then (1 : ℝ) else 0) * f x := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  by_cases hi : xseq i = x <;> simp [hi]
            _ = (∑ i : Fin n, if xseq i = x then (1 : ℝ) else 0) * f x := by
                  rw [Finset.sum_mul]
            _ = (wordCount xseq x : ℝ) * f x := by
                  unfold wordCount
                  simp [Finset.sum_boole]

/-- Strong typicality controls the empirical average of any finite real
observable.

If every symbol frequency is within `δ` of `p`, then the deviation of the
observable sum from its distributional expectation is bounded by
`n δ ∑x |f x|`. -/
theorem strongTypical_sum_observable_deviation_le [Fintype α] [DecidableEq α] {n : ℕ}
    (p : QIT.FiniteDistribution α) (xseq : Fin n → α) {δ : ℝ}
    (hn : 0 < n) (hδ : 0 ≤ δ) (hx : StrongTypical p xseq δ) (f : α → ℝ) :
    |(∑ i : Fin n, f (xseq i)) -
        (n : ℝ) * ∑ x : α, (p.prob x : ℝ) * f x| ≤
      (n : ℝ) * δ * ∑ x : α, |f x| := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hcount : ∀ x : α, (wordCount xseq x : ℝ) = (n : ℝ) * wordFreq xseq x := by
    intro x
    unfold wordFreq
    field_simp [hnR]
  have hrewrite :
      (∑ i : Fin n, f (xseq i)) -
          (n : ℝ) * ∑ x : α, (p.prob x : ℝ) * f x =
        (n : ℝ) * ∑ x : α, (wordFreq xseq x - (p.prob x : ℝ)) * f x := by
    calc
      (∑ i : Fin n, f (xseq i)) -
          (n : ℝ) * ∑ x : α, (p.prob x : ℝ) * f x =
          (∑ x : α, (wordCount xseq x : ℝ) * f x) -
            (n : ℝ) * ∑ x : α, (p.prob x : ℝ) * f x := by
            rw [sum_eq_sum_wordCount_mul xseq f]
      _ = (∑ x : α, ((n : ℝ) * wordFreq xseq x) * f x) -
            (n : ℝ) * ∑ x : α, (p.prob x : ℝ) * f x := by
            refine congrArg₂ Sub.sub ?_ rfl
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hcount x]
      _ = (n : ℝ) *
            (∑ x : α, wordFreq xseq x * f x -
              ∑ x : α, (p.prob x : ℝ) * f x) := by
            have hleft :
                (∑ x : α, ((n : ℝ) * wordFreq xseq x) * f x) =
                  (n : ℝ) * ∑ x : α, wordFreq xseq x * f x := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => ?_
              ring
            rw [hleft]
            ring
      _ = (n : ℝ) * ∑ x : α, (wordFreq xseq x - (p.prob x : ℝ)) * f x := by
            rw [← Finset.sum_sub_distrib]
            refine congrArg ((n : ℝ) * ·) ?_
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
  rw [hrewrite]
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    |(n : ℝ) * ∑ x : α, (wordFreq xseq x - (p.prob x : ℝ)) * f x|
        = (n : ℝ) * |∑ x : α, (wordFreq xseq x - (p.prob x : ℝ)) * f x| := by
          rw [abs_mul, abs_of_nonneg hn_nonneg]
    _ ≤ (n : ℝ) *
          ∑ x : α, |(wordFreq xseq x - (p.prob x : ℝ)) * f x| :=
          mul_le_mul_of_nonneg_left
            (Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun x : α => (wordFreq xseq x - (p.prob x : ℝ)) * f x))
            hn_nonneg
    _ ≤ (n : ℝ) * ∑ x : α, δ * |f x| := by
          refine mul_le_mul_of_nonneg_left ?_ hn_nonneg
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hx x) le_rfl (abs_nonneg _) hδ
    _ = (n : ℝ) * δ * ∑ x : α, |f x| := by
          have hδsum : (∑ x : α, δ * |f x|) = δ * ∑ x : α, |f x| := by
            rw [Finset.mul_sum]
          rw [hδsum]
          ring

theorem sum_centeredPairIndicator_eq_deviation_numer
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (zseq : Fin n → β)
    (x : α) (z : β) :
    (∑ i : Fin n, centeredPairIndicator K xseq x z i zseq) =
      (pairCount xseq zseq x z : ℝ) -
        (wordCount xseq x : ℝ) * (K.prob x z : ℝ) := by
  classical
  unfold centeredPairIndicator
  calc
    (∑ i : Fin n,
        if xseq i = x then
          (if zseq i = z then (1 : ℝ) else 0) - (K.prob x z : ℝ)
        else 0)
        =
          (∑ i : Fin n, if xseq i = x ∧ zseq i = z then (1 : ℝ) else 0) -
            (∑ i : Fin n, if xseq i = x then (K.prob x z : ℝ) else 0) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hx : xseq i = x
            · by_cases hz : zseq i = z <;> simp [hx, hz]
            · simp [hx]
    _ =
          (pairCount xseq zseq x z : ℝ) -
            (wordCount xseq x : ℝ) * (K.prob x z : ℝ) := by
            rw [sum_pairIndicator_eq_pairCount]
            have hconst :
                (∑ i : Fin n, if xseq i = x then (K.prob x z : ℝ) else 0) =
                  (∑ i : Fin n, if xseq i = x then (1 : ℝ) else 0) *
                    (K.prob x z : ℝ) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases hx : xseq i = x <;> simp [hx]
            rw [hconst]
            have hword := sum_inputIndicator_eq_wordCount xseq x
            rw [hword]

theorem pairFreq_deviation_eq_centeredPairIndicator_average
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (zseq : Fin n → β)
    (x : α) (z : β) :
    pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ) =
      (∑ i : Fin n, centeredPairIndicator K xseq x z i zseq) / (n : ℝ) := by
  classical
  unfold pairFreq wordFreq
  rw [sum_centeredPairIndicator_eq_deviation_numer K xseq zseq x z]
  ring

theorem centeredPairIndicator_expect_eq_zero
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β)
    (i : Fin n) :
    ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) *
          centeredPairIndicator K xseq x z i zseq = 0 := by
  classical
  by_cases hx : xseq i = x
  · have hcoord := conditionalProductMass_expect_coordinate
      K xseq i (fun y : β => (if y = z then (1 : ℝ) else 0) - (K.prob x z : ℝ))
    calc
      ∑ zseq : Fin n → β,
          (conditionalProductMass K xseq zseq : ℝ) *
            centeredPairIndicator K xseq x z i zseq
          =
        ∑ y : β, (K.prob (xseq i) y : ℝ) *
          ((if y = z then (1 : ℝ) else 0) - (K.prob x z : ℝ)) := by
          simpa [centeredPairIndicator, hx] using hcoord
      _ =
        ∑ y : β, (K.prob x y : ℝ) *
          ((if y = z then (1 : ℝ) else 0) - (K.prob x z : ℝ)) := by
          simp [hx]
      _ = 0 := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          have hindicator :
              ∑ y : β, (K.prob x y : ℝ) * (if y = z then (1 : ℝ) else 0) =
                (K.prob x z : ℝ) := by
            rw [Finset.sum_eq_single z]
            · simp
            · intro y _ hy
              simp [hy]
            · intro hz
              exact (hz (Finset.mem_univ z)).elim
          have hconst :
              ∑ y : β, (K.prob x y : ℝ) * (K.prob x z : ℝ) =
                (K.prob x z : ℝ) := by
            rw [← Finset.sum_mul]
            have hsum : ∑ y : β, (K.prob x y : ℝ) = 1 := by
              exact_mod_cast K.sum_eq_one x
            rw [hsum, one_mul]
          rw [hindicator, hconst, sub_self]
  · refine Finset.sum_eq_zero fun zseq _ => ?_
    simp [centeredPairIndicator, hx]

theorem centeredPairIndicator_cross_expect_eq_zero
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β)
    {i j : Fin n} (hij : i ≠ j) :
    ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) *
          (centeredPairIndicator K xseq x z i zseq *
            centeredPairIndicator K xseq x z j zseq) = 0 := by
  classical
  let fi : β → ℝ := fun y =>
    if xseq i = x then (if y = z then (1 : ℝ) else 0) - (K.prob x z : ℝ) else 0
  let gj : β → ℝ := fun y =>
    if xseq j = x then (if y = z then (1 : ℝ) else 0) - (K.prob x z : ℝ) else 0
  have htwo := conditionalProductMass_expect_two_coordinates
    (K := K) (xseq := xseq) (hij := hij) (f := fi) (g := gj)
  have hi_zero :
      ∑ y : β, (K.prob (xseq i) y : ℝ) * fi y = 0 := by
    have hcoord := conditionalProductMass_expect_coordinate K xseq i fi
    have hcenter := centeredPairIndicator_expect_eq_zero K xseq x z i
    calc
      ∑ y : β, (K.prob (xseq i) y : ℝ) * fi y
          =
        ∑ zseq : Fin n → β, (conditionalProductMass K xseq zseq : ℝ) * fi (zseq i) := hcoord.symm
      _ =
        ∑ zseq : Fin n → β,
          (conditionalProductMass K xseq zseq : ℝ) *
            centeredPairIndicator K xseq x z i zseq := by
          refine Finset.sum_congr rfl fun zseq _ => ?_
          simp [fi, centeredPairIndicator]
      _ = 0 := hcenter
  have hj_zero :
      ∑ y : β, (K.prob (xseq j) y : ℝ) * gj y = 0 := by
    have hcoord := conditionalProductMass_expect_coordinate K xseq j gj
    have hcenter := centeredPairIndicator_expect_eq_zero K xseq x z j
    calc
      ∑ y : β, (K.prob (xseq j) y : ℝ) * gj y
          =
        ∑ zseq : Fin n → β, (conditionalProductMass K xseq zseq : ℝ) * gj (zseq j) := hcoord.symm
      _ =
        ∑ zseq : Fin n → β,
          (conditionalProductMass K xseq zseq : ℝ) *
            centeredPairIndicator K xseq x z j zseq := by
          refine Finset.sum_congr rfl fun zseq _ => ?_
          simp [gj, centeredPairIndicator]
      _ = 0 := hcenter
  calc
    ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) *
          (centeredPairIndicator K xseq x z i zseq *
            centeredPairIndicator K xseq x z j zseq)
        =
      ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) * (fi (zseq i) * gj (zseq j)) := by
        refine Finset.sum_congr rfl fun zseq _ => ?_
        simp [fi, gj, centeredPairIndicator]
    _ =
      (∑ y : β, (K.prob (xseq i) y : ℝ) * fi y) *
        (∑ y : β, (K.prob (xseq j) y : ℝ) * gj y) := htwo
    _ = 0 := by rw [hi_zero, zero_mul]

theorem centeredPairIndicator_sq_le_inputIndicator
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β)
    (i : Fin n) (zseq : Fin n → β) :
    (centeredPairIndicator K xseq x z i zseq) ^ 2 ≤
      if xseq i = x then (1 : ℝ) else 0 := by
  classical
  by_cases hx : xseq i = x
  · have hq0 : 0 ≤ (K.prob x z : ℝ) := by positivity
    have hq1 : (K.prob x z : ℝ) ≤ 1 := by
      exact_mod_cast K.prob_le_one x z
    have habs :
        |(if zseq i = z then (1 : ℝ) else 0) - (K.prob x z : ℝ)| ≤ 1 := by
      by_cases hz : zseq i = z
      · simp [hz]
        rw [abs_le]
        constructor <;> nlinarith
      · simp [hz]
        exact hq1
    have hsq : ((if zseq i = z then (1 : ℝ) else 0) - (K.prob x z : ℝ)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact habs
    simpa [centeredPairIndicator, hx] using hsq
  · simp [centeredPairIndicator, hx]

theorem centeredPairIndicator_sq_expect_le_inputIndicator
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β)
    (i : Fin n) :
    ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) *
          (centeredPairIndicator K xseq x z i zseq) ^ 2
      ≤ if xseq i = x then (1 : ℝ) else 0 := by
  classical
  calc
    ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) *
          (centeredPairIndicator K xseq x z i zseq) ^ 2
        ≤
      ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) *
          (if xseq i = x then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun zseq _ => ?_
        exact mul_le_mul_of_nonneg_left
          (centeredPairIndicator_sq_le_inputIndicator K xseq x z i zseq)
          (by positivity)
    _ =
        (∑ zseq : Fin n → β, (conditionalProductMass K xseq zseq : ℝ)) *
          (if xseq i = x then (1 : ℝ) else 0) := by
        rw [Finset.sum_mul]
    _ = if xseq i = x then (1 : ℝ) else 0 := by
        have hsum : ∑ zseq : Fin n → β, (conditionalProductMass K xseq zseq : ℝ) = 1 := by
          exact_mod_cast conditionalProductMass_sum_eq_one K xseq
        rw [hsum, one_mul]

theorem centeredPairIndicator_sum_sq_expect_le_wordCount
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β) :
    ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) *
          (∑ i : Fin n, centeredPairIndicator K xseq x z i zseq) ^ 2
      ≤ (wordCount xseq x : ℝ) := by
  classical
  let c : Fin n → (Fin n → β) → ℝ :=
    fun i zseq => centeredPairIndicator K xseq x z i zseq
  have hexpand :
      ∑ zseq : Fin n → β,
          (conditionalProductMass K xseq zseq : ℝ) *
            (∑ i : Fin n, c i zseq) ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, ∑ zseq : Fin n → β,
          (conditionalProductMass K xseq zseq : ℝ) * (c i zseq * c j zseq) := by
    calc
      ∑ zseq : Fin n → β,
          (conditionalProductMass K xseq zseq : ℝ) *
            (∑ i : Fin n, c i zseq) ^ 2
          =
        ∑ zseq : Fin n → β,
          (conditionalProductMass K xseq zseq : ℝ) *
            ((∑ i : Fin n, c i zseq) * (∑ j : Fin n, c j zseq)) := by
          refine Finset.sum_congr rfl fun zseq _ => ?_
          ring
      _ =
        ∑ zseq : Fin n → β,
          ∑ i : Fin n, ∑ j : Fin n,
            (conditionalProductMass K xseq zseq : ℝ) * (c i zseq * c j zseq) := by
          refine Finset.sum_congr rfl fun zseq _ => ?_
          let m : ℝ := (conditionalProductMass K xseq zseq : ℝ)
          have hdist_left : m * (∑ i : Fin n, c i zseq) =
              ∑ i : Fin n, m * c i zseq := by
            rw [Finset.mul_sum]
          calc
            m * ((∑ i : Fin n, c i zseq) * (∑ j : Fin n, c j zseq))
                =
              (m * (∑ i : Fin n, c i zseq)) * (∑ j : Fin n, c j zseq) := by
                ring
            _ =
              (∑ i : Fin n, m * c i zseq) * (∑ j : Fin n, c j zseq) := by
                rw [hdist_left]
            _ =
              ∑ i : Fin n, (m * c i zseq) * (∑ j : Fin n, c j zseq) := by
                rw [Finset.sum_mul]
            _ =
              ∑ i : Fin n, ∑ j : Fin n, (m * c i zseq) * c j zseq := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.mul_sum]
            _ =
              ∑ i : Fin n, ∑ j : Fin n, m * (c i zseq * c j zseq) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                refine Finset.sum_congr rfl fun j _ => ?_
                ring
      _ =
        ∑ i : Fin n, ∑ j : Fin n, ∑ zseq : Fin n → β,
          (conditionalProductMass K xseq zseq : ℝ) * (c i zseq * c j zseq) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
  rw [hexpand]
  calc
    ∑ i : Fin n, ∑ j : Fin n, ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) * (c i zseq * c j zseq)
        =
      ∑ i : Fin n, ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) * (c i zseq) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · refine Finset.sum_congr rfl fun zseq _ => ?_
          ring
        · intro j _ hji
          have hij : i ≠ j := by exact hji.symm
          simpa [c, mul_comm, mul_left_comm, mul_assoc] using
            centeredPairIndicator_cross_expect_eq_zero
              (K := K) (xseq := xseq) (x := x) (z := z) (hij := hij)
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
    _ ≤ ∑ i : Fin n, if xseq i = x then (1 : ℝ) else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [c] using centeredPairIndicator_sq_expect_le_inputIndicator K xseq x z i
    _ = (wordCount xseq x : ℝ) := by
        exact sum_inputIndicator_eq_wordCount xseq x

/-- Second moment of one pair-frequency deviation under the conditional product
law `Z^n | X^n = x^n`. -/
def pairDeviationSecondMoment [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β) : ℝ :=
  ∑ zseq : Fin n → β,
    (conditionalProductMass K xseq zseq : ℝ) *
      (pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)) ^ 2

/-- Mass of the event where one pair-frequency deviation is at least `δ`. -/
def pairDeviationBadMass [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β) (δ : ℝ) :
    ℝ≥0 :=
  by
    classical
    exact conditionalEventMass K xseq
      (fun zseq =>
        δ ≤ |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)|)

theorem pairDeviationSecondMoment_nonneg
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β) :
    0 ≤ pairDeviationSecondMoment K xseq x z := by
  classical
  unfold pairDeviationSecondMoment
  refine Finset.sum_nonneg fun zseq _ => ?_
  exact mul_nonneg (by positivity) (sq_nonneg _)

theorem pairDeviationSecondMoment_le_wordCount_div_sq
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β)
    (hn : 0 < n) :
    pairDeviationSecondMoment K xseq x z ≤
      (wordCount xseq x : ℝ) / (n : ℝ) ^ 2 := by
  classical
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold pairDeviationSecondMoment
  calc
    ∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) *
          (pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)) ^ 2
        =
      (∑ zseq : Fin n → β,
        (conditionalProductMass K xseq zseq : ℝ) *
          (∑ i : Fin n, centeredPairIndicator K xseq x z i zseq) ^ 2) /
        (n : ℝ) ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun zseq _ => ?_
        rw [pairFreq_deviation_eq_centeredPairIndicator_average K xseq zseq x z]
        field_simp [hn_ne]
    _ ≤ (wordCount xseq x : ℝ) / (n : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right
          (centeredPairIndicator_sum_sq_expect_le_wordCount K xseq x z)
          (sq_nonneg (n : ℝ))

/-- Finite Chebyshev/Markov bridge for one pair-frequency deviation.  This is
pure finite-sum probability: bad-event mass times `δ²` is bounded by the second
moment of the deviation. -/
theorem pairDeviationBadMass_mul_sq_le_secondMoment
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β)
    {δ : ℝ} (hδ : 0 < δ) :
    (pairDeviationBadMass K xseq x z δ : ℝ) * δ ^ 2 ≤
      pairDeviationSecondMoment K xseq x z := by
  classical
  unfold pairDeviationBadMass conditionalEventMass pairDeviationSecondMoment
  rw [NNReal.coe_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun zseq _ => ?_
  set d : ℝ := pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)
  change ((if δ ≤ |d| then conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ) *
      δ ^ 2 ≤ (conditionalProductMass K xseq zseq : ℝ) * d ^ 2
  by_cases hbad : δ ≤ |d|
  · have hsq : δ ^ 2 ≤ d ^ 2 := by
      have hδabs : |δ| ≤ |d| := by
        rw [abs_of_pos hδ]
        exact hbad
      simpa [sq_abs] using sq_le_sq.mpr hδabs
    have hmass_nonneg : 0 ≤ (conditionalProductMass K xseq zseq : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsq hmass_nonneg
    simpa [hbad, mul_assoc, mul_comm, mul_left_comm] using hmul
  · simpa [hbad] using
      mul_nonneg (by positivity : 0 ≤ (conditionalProductMass K xseq zseq : ℝ)) (sq_nonneg d)

theorem pairDeviationBadMass_le_one_div_length_mul_sq
    [Fintype β] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (x : α) (z : β)
    {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    (pairDeviationBadMass K xseq x z δ : ℝ) ≤
      1 / ((n : ℝ) * δ ^ 2) := by
  classical
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hδsq_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hbad_mul := pairDeviationBadMass_mul_sq_le_secondMoment K xseq x z hδ
  have hmom := pairDeviationSecondMoment_le_wordCount_div_sq K xseq x z hn
  have hbad_div :
      (pairDeviationBadMass K xseq x z δ : ℝ) ≤
        ((wordCount xseq x : ℝ) / (n : ℝ) ^ 2) / δ ^ 2 := by
    rw [le_div_iff₀ hδsq_pos]
    exact le_trans hbad_mul hmom
  have hword :
      (wordCount xseq x : ℝ) / (n : ℝ) ^ 2 ≤
        (n : ℝ) / (n : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_right
      (wordCount_real_le_length xseq x) (sq_nonneg (n : ℝ))
  have hword_div :
      ((wordCount xseq x : ℝ) / (n : ℝ) ^ 2) / δ ^ 2 ≤
        ((n : ℝ) / (n : ℝ) ^ 2) / δ ^ 2 := by
    exact div_le_div_of_nonneg_right hword (le_of_lt hδsq_pos)
  have halg : ((n : ℝ) / (n : ℝ) ^ 2) / δ ^ 2 =
      1 / ((n : ℝ) * δ ^ 2) := by
    field_simp [hn_ne, ne_of_gt hδsq_pos]
  exact le_trans hbad_div (by simpa [halg] using hword_div)

theorem pairDeviationBadMass_sum_le_card_bound
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α)
    {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    ∑ x : α, ∑ z : β, (pairDeviationBadMass K xseq x z δ : ℝ) ≤
      (Fintype.card α : ℝ) * (Fintype.card β : ℝ) /
        ((n : ℝ) * δ ^ 2) := by
  classical
  calc
    ∑ x : α, ∑ z : β, (pairDeviationBadMass K xseq x z δ : ℝ)
        ≤ ∑ x : α, ∑ z : β, 1 / ((n : ℝ) * δ ^ 2) := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine Finset.sum_le_sum fun z _ => ?_
          exact pairDeviationBadMass_le_one_div_length_mul_sq K xseq x z hn hδ
    _ = (Fintype.card α : ℝ) * (Fintype.card β : ℝ) /
        ((n : ℝ) * δ ^ 2) := by
          rw [Finset.sum_const, Finset.sum_const]
          simp [Finset.card_univ]
          ring

theorem conditionalNontypicalMass_le_pairDeviationBadMass_sum
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (δ : ℝ) :
    (conditionalNontypicalMass K xseq δ : ℝ)
      ≤ ∑ x : α, ∑ z : β, (pairDeviationBadMass K xseq x z δ : ℝ) := by
  classical
  unfold conditionalNontypicalMass pairDeviationBadMass conditionalEventMass
  simp_rw [NNReal.coe_sum]
  calc
    ∑ zseq : Fin n → β,
        ((if ¬ StrongConditionallyTypical K xseq zseq δ then
            conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ)
        ≤
      ∑ zseq : Fin n → β, ∑ x : α, ∑ z : β,
        ((if δ ≤
              |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)| then
            conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ) := by
        refine Finset.sum_le_sum fun zseq _ => ?_
        by_cases htyp : StrongConditionallyTypical K xseq zseq δ
        · simp [htyp]
          exact Finset.sum_nonneg fun x _ =>
            Finset.sum_nonneg fun z _ => by
              by_cases hbad : δ ≤
                  |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)| <;>
                simp [hbad]
        · have hx_exists : ∃ x : α, ¬ ∀ z : β,
              |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)| ≤ δ := by
            simpa [StrongConditionallyTypical] using not_forall.mp htyp
          rcases hx_exists with ⟨x0, hx0⟩
          have hz_exists : ∃ z : β,
              ¬ |pairFreq xseq zseq x0 z - wordFreq xseq x0 * (K.prob x0 z : ℝ)| ≤ δ :=
            not_forall.mp hx0
          rcases hz_exists with ⟨z0, hz0⟩
          have hbad : δ ≤
              |pairFreq xseq zseq x0 z0 - wordFreq xseq x0 * (K.prob x0 z0 : ℝ)| := by
            exact le_of_lt (lt_of_not_ge hz0)
          have hinner :
              (conditionalProductMass K xseq zseq : ℝ) ≤
                ∑ z : β,
                  ((if δ ≤
                        |pairFreq xseq zseq x0 z - wordFreq xseq x0 * (K.prob x0 z : ℝ)| then
                      conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ) := by
            calc
              (conditionalProductMass K xseq zseq : ℝ)
                  =
                ((if δ ≤
                      |pairFreq xseq zseq x0 z0 -
                        wordFreq xseq x0 * (K.prob x0 z0 : ℝ)| then
                    conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ) := by
                    simp [hbad]
              _ ≤
                ∑ z : β,
                  ((if δ ≤
                        |pairFreq xseq zseq x0 z - wordFreq xseq x0 * (K.prob x0 z : ℝ)| then
                      conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ) := by
                    exact Finset.single_le_sum
                      (s := (Finset.univ : Finset β))
                      (f := fun z : β =>
                        ((if δ ≤
                              |pairFreq xseq zseq x0 z -
                                wordFreq xseq x0 * (K.prob x0 z : ℝ)| then
                            conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ))
                      (fun z _ => by
                        by_cases hbadz : δ ≤
                            |pairFreq xseq zseq x0 z -
                              wordFreq xseq x0 * (K.prob x0 z : ℝ)| <;>
                          simp [hbadz])
                      (Finset.mem_univ z0)
          have houter :
              (∑ z : β,
                  ((if δ ≤
                        |pairFreq xseq zseq x0 z - wordFreq xseq x0 * (K.prob x0 z : ℝ)| then
                      conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ))
                ≤
                ∑ x : α, ∑ z : β,
                  ((if δ ≤
                        |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)| then
                      conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ) := by
            exact Finset.single_le_sum
              (s := (Finset.univ : Finset α))
              (f := fun x : α =>
                ∑ z : β,
                  ((if δ ≤
                        |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)| then
                      conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ))
              (fun x _ => Finset.sum_nonneg fun z _ => by
                by_cases hbadz : δ ≤
                    |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)| <;>
                  simp [hbadz])
              (Finset.mem_univ x0)
          simpa [htyp] using le_trans hinner houter
    _ =
      ∑ x : α, ∑ z : β, ∑ zseq : Fin n → β,
        ((if δ ≤
              |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)| then
            conditionalProductMass K xseq zseq else 0 : ℝ≥0) : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]

theorem conditionalTypicalMass_ge_one_sub_pairDeviationBadMass_sum
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) (δ : ℝ) :
    1 - (∑ x : α, ∑ z : β, (pairDeviationBadMass K xseq x z δ : ℝ)) ≤
      (conditionalTypicalMass K xseq δ : ℝ) := by
  classical
  have hpart_event := conditionalEventMass_add_compl_eq_one
    K xseq (fun zseq => StrongConditionallyTypical K xseq zseq δ)
  have hpart :
      (conditionalTypicalMass K xseq δ : ℝ) +
        (conditionalNontypicalMass K xseq δ : ℝ) = 1 := by
    unfold conditionalTypicalMass conditionalNontypicalMass
    exact hpart_event
  have hbad := conditionalNontypicalMass_le_pairDeviationBadMass_sum K xseq δ
  nlinarith

theorem conditionalTypicalMass_ge_one_sub_card_bound
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α)
    {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    1 - ((Fintype.card α : ℝ) * (Fintype.card β : ℝ) /
        ((n : ℝ) * δ ^ 2)) ≤
      (conditionalTypicalMass K xseq δ : ℝ) := by
  classical
  have hbad := conditionalTypicalMass_ge_one_sub_pairDeviationBadMass_sum K xseq δ
  have hsum := pairDeviationBadMass_sum_le_card_bound K xseq hn hδ
  nlinarith

/-- Finite Chebyshev/union-bound lower bound for the ordinary i.i.d. strongly
typical set.

This is obtained as the one-point-input special case of
`conditionalTypicalMass_ge_one_sub_card_bound`, so the probability argument is
shared with the conditional typicality route used in HSW pack-1. -/
theorem strongTypicalMass_ge_one_sub_card_bound
    [Fintype α] [DecidableEq α] {n : ℕ}
    (p : QIT.FiniteDistribution α) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    1 - ((Fintype.card α : ℝ) / ((n : ℝ) * δ ^ 2)) ≤
      (strongTypicalMass (n := n) p δ : ℝ) := by
  let xseq : Fin n → Unit := fun _ => ()
  have hcond :=
    conditionalTypicalMass_ge_one_sub_card_bound
      (K := distributionKernel p) (xseq := xseq) hn hδ
  rw [conditionalTypicalMass_distributionKernel_eq_strongTypicalMass p xseq δ hn] at hcond
  simpa using hcond

theorem conditionalTypicalMass_ge_one_sub_epsilon_of_card_bound
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α)
    {δ ε : ℝ} (hn : 0 < n) (hδ : 0 < δ)
    (hlarge :
      (Fintype.card α : ℝ) * (Fintype.card β : ℝ) /
          ((n : ℝ) * δ ^ 2) ≤ ε) :
    1 - ε ≤ (conditionalTypicalMass K xseq δ : ℝ) := by
  have hmass := conditionalTypicalMass_ge_one_sub_card_bound K xseq hn hδ
  nlinarith

/-- Marginal-typical event mass of `Z^n | X^n = x^n`, with typicality tested
against the induced output marginal `p_Z`. -/
def marginalTypicalMass [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (xseq : Fin n → α) (δ : ℝ) : ℝ≥0 :=
  by
    classical
    exact conditionalEventMass K xseq
      (fun zseq => StrongTypical (inducedMarginal p K) zseq δ)

theorem wordCount_real_eq_sum_pairCount_real
    [Fintype α] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (xseq : Fin n → α) (zseq : Fin n → β) (z : β) :
    (wordCount zseq z : ℝ) = ∑ x : α, (pairCount xseq zseq x z : ℝ) := by
  classical
  unfold wordCount pairCount
  rw [Finset.natCast_card_filter]
  simp_rw [Finset.natCast_card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hz : zseq i = z
  · simp [hz]
  · simp [hz]

theorem wordFreq_eq_sum_pairFreq
    [Fintype α] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (xseq : Fin n → α) (zseq : Fin n → β) (z : β) :
    wordFreq zseq z = ∑ x : α, pairFreq xseq zseq x z := by
  classical
  unfold wordFreq pairFreq
  rw [wordCount_real_eq_sum_pairCount_real xseq zseq z]
  rw [Finset.sum_div]

theorem finset_abs_sum_le_sum_abs {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    |∑ i, f i| ≤ ∑ i, |f i| := by
  classical
  simpa using Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := f)

/-- Strong input typicality plus conditional strong typicality implies marginal
output strong typicality, with the explicit finite-alphabet slack
`|α| * (δx + δc)`.

This is the deterministic `conditional + marginal -> marginal` bridge used in
Wilde's proof after the conditional LLN step. -/
theorem strongTypical_inducedMarginal_of_strongConditionallyTypical
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (xseq : Fin n → α) (zseq : Fin n → β) {δx δc : ℝ}
    (hδx : 0 ≤ δx) (_hδc : 0 ≤ δc)
    (hx : StrongTypical p xseq δx)
    (hcond : StrongConditionallyTypical K xseq zseq δc) :
    StrongTypical (inducedMarginal p K) zseq
      ((Fintype.card α : ℝ) * (δx + δc)) := by
  classical
  intro z
  have hrewrite :
      wordFreq zseq z - ((inducedMarginal p K).prob z : ℝ) =
        ∑ x : α,
          (pairFreq xseq zseq x z - (p.prob x : ℝ) * (K.prob x z : ℝ)) := by
    rw [inducedMarginal_prob]
    rw [wordFreq_eq_sum_pairFreq xseq zseq z]
    simp only [NNReal.coe_sum, NNReal.coe_mul]
    rw [← Finset.sum_sub_distrib]
  rw [hrewrite]
  refine le_trans (finset_abs_sum_le_sum_abs (fun x : α =>
      pairFreq xseq zseq x z - (p.prob x : ℝ) * (K.prob x z : ℝ))) ?_
  calc
    ∑ x : α, |pairFreq xseq zseq x z - (p.prob x : ℝ) * (K.prob x z : ℝ)|
        ≤ ∑ x : α,
            (δc + δx) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have hsplit :
              pairFreq xseq zseq x z - (p.prob x : ℝ) * (K.prob x z : ℝ) =
                (pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)) +
                (wordFreq xseq x - (p.prob x : ℝ)) * (K.prob x z : ℝ) := by
            ring
          rw [hsplit]
          have h1 := hcond x z
          have h2abs : |(wordFreq xseq x - (p.prob x : ℝ)) * (K.prob x z : ℝ)| ≤ δx := by
            rw [abs_mul]
            have hKnonneg : 0 ≤ (K.prob x z : ℝ) := by positivity
            have hKle : (K.prob x z : ℝ) ≤ 1 := by
              exact_mod_cast K.prob_le_one x z
            have hxabs := hx x
            calc
              |wordFreq xseq x - (p.prob x : ℝ)| * |(K.prob x z : ℝ)|
                  = |wordFreq xseq x - (p.prob x : ℝ)| * (K.prob x z : ℝ) := by
                      rw [abs_of_nonneg hKnonneg]
              _ ≤ δx * 1 := mul_le_mul hxabs hKle hKnonneg hδx
              _ = δx := by ring
          calc
            |(pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)) +
                (wordFreq xseq x - (p.prob x : ℝ)) * (K.prob x z : ℝ)|
                ≤ |pairFreq xseq zseq x z - wordFreq xseq x * (K.prob x z : ℝ)| +
                    |(wordFreq xseq x - (p.prob x : ℝ)) * (K.prob x z : ℝ)| :=
                    abs_add_le _ _
            _ ≤ δc + δx := add_le_add h1 h2abs
            _ = δc + δx := rfl
    _ = (Fintype.card α : ℝ) * (δx + δc) := by
          rw [Finset.sum_const, Finset.card_univ]
          norm_num
          ring

theorem conditionalTypicalMass_le_marginalTypicalMass
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (xseq : Fin n → α) {δx δc : ℝ}
    (hδx : 0 ≤ δx) (hδc : 0 ≤ δc)
    (hx : StrongTypical p xseq δx) :
    conditionalTypicalMass K xseq δc ≤
      marginalTypicalMass p K xseq ((Fintype.card α : ℝ) * (δx + δc)) := by
  classical
  unfold conditionalTypicalMass marginalTypicalMass conditionalEventMass
  refine Finset.sum_le_sum fun zseq _ => ?_
  by_cases hcond : StrongConditionallyTypical K xseq zseq δc
  · have hmarg :
        StrongTypical (inducedMarginal p K) zseq
          ((Fintype.card α : ℝ) * (δx + δc)) :=
      strongTypical_inducedMarginal_of_strongConditionallyTypical
        p K xseq zseq hδx hδc hx hcond
    simp [hcond, hmarg]
  · simp [hcond]

theorem marginalTypicalMass_ge_of_conditionalTypicalMass_ge
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (xseq : Fin n → α) {δx δc η : ℝ}
    (hδx : 0 ≤ δx) (hδc : 0 ≤ δc)
    (hx : StrongTypical p xseq δx)
    (hmass : η ≤ (conditionalTypicalMass K xseq δc : ℝ)) :
    η ≤ (marginalTypicalMass p K xseq ((Fintype.card α : ℝ) * (δx + δc)) : ℝ) := by
  have hle := conditionalTypicalMass_le_marginalTypicalMass
    p K xseq hδx hδc hx
  exact le_trans hmass (by exact_mod_cast hle)

/-- Finite conditional-typicality capture in the form used by Wilde's HSW
pack-1 route.  If the input word is strongly typical and `n` is large enough
for the explicit Chebyshev/union bound, then the conditional product output
is marginally typical with probability at least `1 - ε`.

The tolerance in the marginal typicality test is the deterministic bridge slack
`|α| * (δx + δc)`.  The finite-size condition is written explicitly as
`|α||β| / (n δc²) ≤ ε`; this is a concrete "sufficiently large `n`" hypothesis. -/
theorem marginalTypicalMass_ge_one_sub_epsilon_of_conditionalTypicality
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (xseq : Fin n → α) {δx δc ε : ℝ}
    (hn : 0 < n) (hδx : 0 ≤ δx) (hδc : 0 < δc)
    (hx : StrongTypical p xseq δx)
    (hlarge :
      (Fintype.card α : ℝ) * (Fintype.card β : ℝ) /
          ((n : ℝ) * δc ^ 2) ≤ ε) :
    1 - ε ≤
      (marginalTypicalMass p K xseq ((Fintype.card α : ℝ) * (δx + δc)) : ℝ) := by
  have hcond := conditionalTypicalMass_ge_one_sub_epsilon_of_card_bound
    K xseq hn hδc hlarge
  exact marginalTypicalMass_ge_of_conditionalTypicalMass_ge
    p K xseq hδx (le_of_lt hδc) hx hcond

end ClassicalTypicality

end

end QIT
