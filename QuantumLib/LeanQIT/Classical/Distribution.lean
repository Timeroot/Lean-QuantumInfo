/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumInfo.ClassicalInfo.Distribution
public import Mathlib.Data.NNReal.Basic

/-!
# Nonnegative-real weights and supports of a finite distribution

`ProbDistribution` stores its weights as elements of `Prob`, the reals in
`[0, 1]`, which carry multiplication but not addition. Sums and products of
weights are the basic operations of the classical typicality and coding
arguments, so `ProbDistribution.nnprob` reads the same weights as nonnegative
reals and `ProbDistribution.ofNNReal` builds a distribution from them.

On top of that this file records the support predicate `SupportedBy` used by
the relative-entropy and hypothesis-testing API, for which the interesting
comparison is against a bare weight function rather than another distribution.
-/

@[expose] public section

open scoped BigOperators NNReal

namespace ProbDistribution

universe u

variable {α : Type u} [Fintype α]

/-- The weight a distribution gives a point, as a nonnegative real. -/
def nnprob (p : ProbDistribution α) (x : α) : ℝ≥0 :=
  p x

theorem coe_nnprob (p : ProbDistribution α) (x : α) : (p.nnprob x : ℝ) = p x :=
  rfl

/-- The nonnegative-real weights of a finite distribution sum to one. -/
theorem sum_nnprob (p : ProbDistribution α) : ∑ x, p.nnprob x = 1 := by
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_sum, NNReal.coe_one]
  exact p.normalized

theorem nnprob_le_one (p : ProbDistribution α) (x : α) : p.nnprob x ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnprob, NNReal.coe_one]
  exact Prob.coe_le_one

/-- The distribution with the given nonnegative-real weights. -/
@[reducible]
def ofNNReal (f : α → ℝ≥0) (hf : ∑ x, f x = 1) : ProbDistribution α :=
  mk' (fun x => (f x : ℝ)) (fun x => (f x).coe_nonneg) <| by
    rw [← NNReal.coe_sum, hf, NNReal.coe_one]

@[simp]
theorem nnprob_ofNNReal (f : α → ℝ≥0) (hf : ∑ x, f x = 1) : (ofNNReal f hf).nnprob = f :=
  rfl

@[simp]
theorem ofNNReal_nnprob (p : ProbDistribution α) (hp : ∑ x, p.nnprob x = 1) :
    ofNNReal p.nnprob hp = p :=
  rfl

/-- The support of `r` is contained in the support of the weight function `p`. -/
def SupportedBy (r : ProbDistribution α) (p : α → ℝ≥0) : Prop :=
  ∀ x, r.nnprob x ≠ 0 → p x ≠ 0

@[simp]
theorem supportedBy_self (r : ProbDistribution α) : r.SupportedBy r.nnprob :=
  fun _ hx => hx

/-- Support containment is transitive. -/
theorem SupportedBy.trans {r p : ProbDistribution α} {q : α → ℝ≥0}
    (hrp : r.SupportedBy p.nnprob) (hpq : p.SupportedBy q) :
    r.SupportedBy q :=
  fun x hx => hpq x (hrp x hx)

/-- A finite probability distribution has at least one nonzero mass point. -/
theorem exists_nnprob_ne_zero (r : ProbDistribution α) : ∃ x : α, r.nnprob x ≠ 0 := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  have hsum : ∑ x : α, r.nnprob x = 0 := by simp [h]
  rw [r.sum_nnprob] at hsum
  exact one_ne_zero hsum

/-- A chosen nonzero mass point of a finite distribution. -/
noncomputable def supportPoint (r : ProbDistribution α) : α :=
  Classical.choose r.exists_nnprob_ne_zero

theorem supportPoint_nnprob_ne_zero (r : ProbDistribution α) :
    r.nnprob r.supportPoint ≠ 0 :=
  Classical.choose_spec r.exists_nnprob_ne_zero

/-- The floors of scaled weights have total mass at most the scale. -/
theorem floor_scaled_sum_le (r : ProbDistribution α) (N : ℕ) :
    ∑ x : α, Nat.floor ((N : ℝ) * (r.nnprob x : ℝ)) ≤ N := by
  exact_mod_cast (show
    (∑ x : α, (Nat.floor ((N : ℝ) * (r.nnprob x : ℝ)) : ℝ)) ≤ (N : ℝ) from by
      have hterm : ∀ x : α,
          (Nat.floor ((N : ℝ) * (r.nnprob x : ℝ)) : ℝ) ≤ (N : ℝ) * (r.nnprob x : ℝ) := by
        intro x
        exact Nat.floor_le (mul_nonneg (by positivity) (by positivity))
      calc
        (∑ x : α, (Nat.floor ((N : ℝ) * (r.nnprob x : ℝ)) : ℝ))
            ≤ ∑ x : α, (N : ℝ) * (r.nnprob x : ℝ) := Finset.sum_le_sum fun x _ => hterm x
        _ = (N : ℝ) := by
          rw [← Finset.mul_sum]
          have hsum : ∑ x : α, (r.nnprob x : ℝ) = 1 := by
            exact_mod_cast r.sum_nnprob
          rw [hsum]
          ring)

end ProbDistribution
