/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Binary hypothesis test spectral API: classical layer

This module contains the finite classical-distribution infrastructure, the
relative-entropy family, the classical binary model, and the common-support
variational proof for the classical Chernoff bound.  The API lives at
information layer L2 because its consumers (RenyiLimit and MutualInformationDPI)
are L2, while QIT/Classical is reserved for classical-state infrastructure.
These declarations were relocated from QIT/HypothesisTesting/ChernoffSupport.lean
as part of the L3-to-L2 layering cleanup.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

open scoped ComplexOrder MatrixOrder NNReal ENNReal Topology
open Filter Matrix Polynomial

namespace BinaryHypothesisTest

/-- A finite classical probability distribution. -/
structure ClassicalDistribution (α : Type u) [Fintype α] where
  prob : α → ℝ≥0
  sum_eq_one : ∑ x, prob x = 1

namespace ClassicalDistribution

variable {α : Type u} [Fintype α]

/-- Support containment for finite classical distributions. -/
def SupportedBy (r : ClassicalDistribution α) (p : α → ℝ≥0) : Prop :=
  ∀ x, r.prob x ≠ 0 → p x ≠ 0

@[simp]
theorem supportedBy_self (r : ClassicalDistribution α) :
    r.SupportedBy r.prob := by
  intro x hx
  exact hx

/-- Support containment is transitive. -/
theorem SupportedBy.trans {r p : ClassicalDistribution α} {q : α → ℝ≥0}
    (hrp : r.SupportedBy p.prob) (hpq : p.SupportedBy q) :
    r.SupportedBy q := by
  intro x hx
  exact hpq x (hrp x hx)

/-- A finite probability distribution has at least one nonzero mass point. -/
theorem exists_prob_ne_zero (r : ClassicalDistribution α) :
    ∃ x : α, r.prob x ≠ 0 := by
  by_contra h
  have hall : ∀ x : α, r.prob x = 0 := by
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hsum0 : ∑ x : α, r.prob x = 0 := by
    simp [hall]
  have : (0 : ℝ≥0) = 1 := by
    simpa [hsum0] using r.sum_eq_one
  norm_num at this

/-- A chosen nonzero support point of a finite distribution. -/
noncomputable def supportPoint (r : ClassicalDistribution α) : α :=
  Classical.choose (exists_prob_ne_zero r)

theorem supportPoint_prob_ne_zero (r : ClassicalDistribution α) :
    r.prob r.supportPoint ≠ 0 :=
  Classical.choose_spec (exists_prob_ne_zero r)

/-- The floors of scaled probabilities have total mass at most the scale. -/
theorem floor_scaled_sum_le (r : ClassicalDistribution α) (N : Nat) :
    ∑ x : α, Nat.floor ((N : ℝ) * (r.prob x : ℝ)) ≤ N := by
  exact_mod_cast (show
    (∑ x : α, (Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : ℝ)) ≤ (N : ℝ) from by
      have hterm : ∀ x : α,
          (Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : ℝ) ≤
            (N : ℝ) * (r.prob x : ℝ) := by
        intro x
        exact Nat.floor_le (mul_nonneg (by positivity) (by positivity))
      calc
        (∑ x : α, (Nat.floor ((N : ℝ) * (r.prob x : ℝ)) : ℝ))
            ≤ ∑ x : α, (N : ℝ) * (r.prob x : ℝ) :=
              Finset.sum_le_sum fun x _ => hterm x
        _ = (N : ℝ) := by
          rw [← Finset.mul_sum]
          have hsum : ∑ x : α, (r.prob x : ℝ) = 1 := by
            exact_mod_cast r.sum_eq_one
          rw [hsum]
          ring)
end ClassicalDistribution
/-- One real KL summand, with the standard `0 log 0 = 0` convention on the
first argument.  Unsupported positive mass is handled by the EReal wrapper
below, not by this real-valued expression. -/
def relativeEntropySummandReal {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (x : α) : ℝ :=
  if r.prob x = 0 then
    0
  else
    (r.prob x : ℝ) * Real.log ((r.prob x : ℝ) / (p.prob x : ℝ))

/-- Finite real-valued classical relative entropy on a fixed support. -/
def relativeEntropyReal {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) : ℝ :=
  ∑ x, relativeEntropySummandReal r p x

/-- Support-aware extended-real classical relative entropy.  It is `⊤` when
`r` assigns positive mass outside the support of `p`. -/
def relativeEntropy {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) : EReal := by
  classical
  exact
    if r.SupportedBy p.prob then
      (relativeEntropyReal r p : EReal)
    else
      ⊤

@[simp]
theorem relativeEntropySummandReal_zero_mass {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) {x : α} (hx : r.prob x = 0) :
    relativeEntropySummandReal r p x = 0 := by
  simp [relativeEntropySummandReal, hx]

theorem relativeEntropy_eq_top_of_not_supported {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (h : ¬ r.SupportedBy p.prob) :
    relativeEntropy r p = ⊤ := by
  classical
  simp [relativeEntropy, h]

theorem relativeEntropy_eq_coe_of_supported {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (h : r.SupportedBy p.prob) :
    relativeEntropy r p = (relativeEntropyReal r p : EReal) := by
  classical
  simp [relativeEntropy, h]

/-- Pointwise Gibbs inequality with the `0 log 0 = 0` convention. -/
theorem relativeEntropySummandReal_ge_sub {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (h : r.SupportedBy p.prob) (x : α) :
    (r.prob x : ℝ) - (p.prob x : ℝ) ≤
      relativeEntropySummandReal r p x := by
  by_cases hr0 : r.prob x = 0
  · have hp_nonneg : 0 ≤ (p.prob x : ℝ) := by positivity
    simp [relativeEntropySummandReal, hr0]
  · have hp0 : p.prob x ≠ 0 := h x hr0
    have hrr : 0 < (r.prob x : ℝ) := by
      have hrr_nn : (0 : ℝ≥0) < r.prob x :=
        lt_of_le_of_ne (by positivity) (Ne.symm hr0)
      exact_mod_cast hrr_nn
    have hpp : 0 < (p.prob x : ℝ) := by
      have hpp_nn : (0 : ℝ≥0) < p.prob x :=
        lt_of_le_of_ne (by positivity) (Ne.symm hp0)
      exact_mod_cast hpp_nn
    have hratio : 0 < (r.prob x : ℝ) / (p.prob x : ℝ) :=
      div_pos hrr hpp
    have hlog := Real.one_sub_inv_le_log_of_pos hratio
    have hmul :
        (r.prob x : ℝ) * (1 - (((r.prob x : ℝ) / (p.prob x : ℝ))⁻¹)) ≤
          (r.prob x : ℝ) *
            Real.log ((r.prob x : ℝ) / (p.prob x : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt hrr)
    calc
      (r.prob x : ℝ) - (p.prob x : ℝ)
          = (r.prob x : ℝ) *
              (1 - (((r.prob x : ℝ) / (p.prob x : ℝ))⁻¹)) := by
            field_simp [hrr.ne', hpp.ne']
      _ ≤ (r.prob x : ℝ) *
            Real.log ((r.prob x : ℝ) / (p.prob x : ℝ)) := hmul
      _ = relativeEntropySummandReal r p x := by
            simp [relativeEntropySummandReal, hr0]

/-- Classical relative entropy is nonnegative on a fixed support. -/
theorem relativeEntropyReal_nonneg {α : Type u} [Fintype α]
    (r p : ClassicalDistribution α) (h : r.SupportedBy p.prob) :
    0 ≤ relativeEntropyReal r p := by
  have hterm :
      ∀ x : α,
        (r.prob x : ℝ) - (p.prob x : ℝ) ≤
          relativeEntropySummandReal r p x :=
    relativeEntropySummandReal_ge_sub r p h
  have hsum_lower :
      (∑ x : α, ((r.prob x : ℝ) - (p.prob x : ℝ))) ≤
        ∑ x : α, relativeEntropySummandReal r p x :=
    Finset.sum_le_sum fun x _ => hterm x
  have hsumr : ∑ x : α, (r.prob x : ℝ) = 1 := by
    exact_mod_cast r.sum_eq_one
  have hsump : ∑ x : α, (p.prob x : ℝ) = 1 := by
    exact_mod_cast p.sum_eq_one
  have hzero :
      (∑ x : α, ((r.prob x : ℝ) - (p.prob x : ℝ))) = 0 := by
    rw [Finset.sum_sub_distrib, hsumr, hsump]
    ring
  unfold relativeEntropyReal
  linarith


/-- A finite classical binary discrimination model with two probability vectors
on the same finite alphabet. -/
structure ClassicalBinaryModel (α : Type u) [Fintype α] where
  p : α → ℝ≥0
  q : α → ℝ≥0
  p_sum : ∑ x, p x = 1
  q_sum : ∑ x, q x = 1

namespace ClassicalBinaryModel

variable {α : Type u} [Fintype α]

/-- The `p` side as a finite classical distribution. -/
def pDistribution (M : ClassicalBinaryModel α) : ClassicalDistribution α :=
  { prob := M.p
    sum_eq_one := M.p_sum }

/-- The `q` side as a finite classical distribution. -/
def qDistribution (M : ClassicalBinaryModel α) : ClassicalDistribution α :=
  { prob := M.q
    sum_eq_one := M.q_sum }

@[simp]
theorem pDistribution_prob (M : ClassicalBinaryModel α) :
    M.pDistribution.prob = M.p := rfl

@[simp]
theorem qDistribution_prob (M : ClassicalBinaryModel α) :
    M.qDistribution.prob = M.q := rfl

/-- Equal-prior classical error `sum_x min{p_x/2, q_x/2}`. -/
def equalPriorError (M : ClassicalBinaryModel α) : ℝ≥0 :=
  ∑ x, min ((1 / 2 : ℝ≥0) * M.p x) ((1 / 2 : ℝ≥0) * M.q x)

/-- Equal-prior classical error as an `ℝ≥0∞` quantity. -/
def equalPriorErrorENNReal (M : ClassicalBinaryModel α) : ℝ≥0∞ :=
  (M.equalPriorError : ℝ≥0∞)

/-- IID tensor power of a finite classical binary model. -/
def tensorPower (M : ClassicalBinaryModel α) : (n : Nat) → ClassicalBinaryModel (TensorPower α n)
  | 0 =>
      { p := fun _ => 1
        q := fun _ => 1
        p_sum := by
          change (∑ _x : PUnit, (1 : ℝ≥0)) = 1
          simp
        q_sum := by
          change (∑ _x : PUnit, (1 : ℝ≥0)) = 1
          simp }
  | n + 1 =>
      let Mn := M.tensorPower n
      { p := fun x => M.p x.1 * Mn.p x.2
        q := fun x => M.q x.1 * Mn.q x.2
        p_sum := by
          change (∑ x : Prod α (TensorPower α n), M.p x.1 * Mn.p x.2) = 1
          rw [Fintype.sum_prod_type]
          calc
            (∑ x : α, ∑ xs : TensorPower α n, M.p x * Mn.p xs)
                = ∑ x : α, M.p x * ∑ xs : TensorPower α n, Mn.p xs := by
                  simp [Finset.mul_sum]
            _ = ∑ x : α, M.p x := by simp [Mn.p_sum]
            _ = 1 := M.p_sum
        q_sum := by
          change (∑ x : Prod α (TensorPower α n), M.q x.1 * Mn.q x.2) = 1
          rw [Fintype.sum_prod_type]
          calc
            (∑ x : α, ∑ xs : TensorPower α n, M.q x * Mn.q xs)
                = ∑ x : α, M.q x * ∑ xs : TensorPower α n, Mn.q xs := by
                  simp [Finset.mul_sum]
            _ = ∑ x : α, M.q x := by simp [Mn.q_sum]
            _ = 1 := M.q_sum }

@[simp]
theorem tensorPower_zero_p (M : ClassicalBinaryModel α) (x : TensorPower α 0) :
    (M.tensorPower 0).p x = 1 := by
  cases x
  simp [tensorPower]

@[simp]
theorem tensorPower_zero_q (M : ClassicalBinaryModel α) (x : TensorPower α 0) :
    (M.tensorPower 0).q x = 1 := by
  cases x
  simp [tensorPower]

@[simp]
theorem tensorPower_succ_p (M : ClassicalBinaryModel α) (n : Nat)
    (x : α) (xs : TensorPower α n) :
    (M.tensorPower (n + 1)).p (x, xs) = M.p x * (M.tensorPower n).p xs := by
  simp [tensorPower]

@[simp]
theorem tensorPower_succ_q (M : ClassicalBinaryModel α) (n : Nat)
    (x : α) (xs : TensorPower α n) :
    (M.tensorPower (n + 1)).q (x, xs) = M.q x * (M.tensorPower n).q xs := by
  simp [tensorPower]

/-- Classical Petz/Chernoff coefficient `sum_x p_x^s q_x^(1-s)`. -/
def petzChernoffCoefficient (M : ClassicalBinaryModel α) (s : ℝ) : ℝ≥0 :=
  ∑ x, (M.p x) ^ s * (M.q x) ^ (1 - s)

/-- Classical Chernoff exponent for a fixed `s`, using natural logarithms. -/
def chernoffExponent (M : ClassicalBinaryModel α) (s : ℝ) : EReal :=
  - ENNReal.log (M.petzChernoffCoefficient s : ℝ≥0∞)

/-- Classical Chernoff distance as the supremum of fixed-`s` exponents over
`0 ≤ s ≤ 1`. -/
def chernoffDistance (M : ClassicalBinaryModel α) : EReal :=
  ⨆ s : Set.Icc (0 : ℝ) 1, M.chernoffExponent s.1

/-- The unnormalized tilted Chernoff weight `p_x^s q_x^(1-s)`. -/
noncomputable def tiltedWeight (M : ClassicalBinaryModel α) (s : ℝ) (x : α) : ℝ≥0 :=
  M.p x ^ s * M.q x ^ (1 - s)

/-- Tilted weights sum to the classical Petz/Chernoff coefficient. -/
theorem tiltedWeight_sum (M : ClassicalBinaryModel α) (s : ℝ) :
    ∑ x : α, M.tiltedWeight s x = M.petzChernoffCoefficient s := by
  rfl

/-- The normalized tilted distribution associated with a nonzero Chernoff
coefficient. -/
noncomputable def tiltedDistribution (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.petzChernoffCoefficient s ≠ 0) : ClassicalDistribution α :=
  { prob := fun x => M.tiltedWeight s x / M.petzChernoffCoefficient s
    sum_eq_one := by
      rw [← Finset.sum_div]
      exact div_self hZ }

@[simp]
theorem tiltedDistribution_prob (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.petzChernoffCoefficient s ≠ 0) (x : α) :
    (M.tiltedDistribution s hZ).prob x =
      M.tiltedWeight s x / M.petzChernoffCoefficient s := rfl

/-- Away from the endpoint `s = 0`, the tilted distribution is supported on
the `p` support. -/
theorem tiltedDistribution_supportedBy_p
    (M : ClassicalBinaryModel α) {s : ℝ} (hs : s ≠ 0)
    (hZ : M.petzChernoffCoefficient s ≠ 0) :
    (M.tiltedDistribution s hZ).SupportedBy M.p := by
  intro x hx
  rw [tiltedDistribution_prob] at hx
  have hweight : M.tiltedWeight s x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  unfold tiltedWeight at hweight
  have hp_pow : M.p x ^ s ≠ 0 := by
    intro hp0
    simp [hp0] at hweight
  exact fun hp0 => hp_pow ((NNReal.rpow_eq_zero hs).mpr hp0)

/-- Away from the endpoint `s = 1`, the tilted distribution is supported on
the `q` support. -/
theorem tiltedDistribution_supportedBy_q
    (M : ClassicalBinaryModel α) {s : ℝ} (hs : 1 - s ≠ 0)
    (hZ : M.petzChernoffCoefficient s ≠ 0) :
    (M.tiltedDistribution s hZ).SupportedBy M.q := by
  intro x hx
  rw [tiltedDistribution_prob] at hx
  have hweight : M.tiltedWeight s x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  unfold tiltedWeight at hweight
  have hq_pow : M.q x ^ (1 - s) ≠ 0 := by
    intro hq0
    simp [hq0] at hweight
  exact fun hq0 => hq_pow ((NNReal.rpow_eq_zero hs).mpr hq0)

/-- The finite common support of the two classical distributions.  The direct
classical Chernoff variational proof works on this support so all logarithms
and real powers have strictly positive bases. -/
noncomputable def commonSupport (M : ClassicalBinaryModel α) : Type u :=
  {x : α // M.p x ≠ 0 ∧ M.q x ≠ 0}

noncomputable instance commonSupportFintype
    (M : ClassicalBinaryModel α) : Fintype M.commonSupport := by
  unfold commonSupport
  infer_instance

/-- The common-support Chernoff partition function, using the repository's
orientation `p^s q^(1-s)` from `petzChernoffCoefficient`. -/
noncomputable def chernoffPartition (M : ClassicalBinaryModel α) (s : ℝ) : ℝ :=
  ∑ x : M.commonSupport,
    ((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s))

/-- Nonnegative-real version of the common-support Chernoff partition.  This is
used to normalize the tilted distribution without endpoint support artifacts
from the full alphabet. -/
noncomputable def chernoffPartitionNNReal (M : ClassicalBinaryModel α) (s : ℝ) : ℝ≥0 :=
  ∑ x : M.commonSupport, M.p x.1 ^ s * M.q x.1 ^ (1 - s)

@[simp]
theorem chernoffPartitionNNReal_coe (M : ClassicalBinaryModel α) (s : ℝ) :
    (M.chernoffPartitionNNReal s : ℝ) = M.chernoffPartition s := by
  simp [chernoffPartitionNNReal, chernoffPartition]

/-- A nonempty common support makes the common-support partition strictly
positive for every real Chernoff parameter. -/
theorem chernoffPartitionNNReal_pos_of_commonSupport_nonempty
    (M : ClassicalBinaryModel α) (h : Nonempty M.commonSupport) (s : ℝ) :
    0 < M.chernoffPartitionNNReal s := by
  classical
  rcases h with ⟨x⟩
  unfold chernoffPartitionNNReal
  apply Finset.sum_pos'
  · intro y _hy
    positivity
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    have hp : 0 < M.p x.1 := by
      exact lt_of_le_of_ne (by positivity) (Ne.symm x.2.1)
    have hq : 0 < M.q x.1 := by
      exact lt_of_le_of_ne (by positivity) (Ne.symm x.2.2)
    positivity

/-- On the open interval `(0,1)`, the common-support partition agrees with
the full classical Petz/Chernoff coefficient.  Terms outside common support
vanish because both exponents are nonzero there. -/
theorem chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
    (M : ClassicalBinaryModel α) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    M.chernoffPartitionNNReal s = M.petzChernoffCoefficient s := by
  classical
  let f : α → ℝ≥0 := fun x => M.p x ^ s * M.q x ^ (1 - s)
  have hfilter :
      (∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0, f x) = M.chernoffPartitionNNReal s := by
    unfold chernoffPartitionNNReal commonSupport f
    exact Finset.sum_bij
      (fun x hx => ⟨x, by simpa using (Finset.mem_filter.mp hx).2⟩)
      (by intro x hx; simp)
      (by intro a _ b _ h; simpa using h)
      (by
        intro y _hy
        refine ⟨y.1, ?_, rfl⟩
        simp [y.2])
      (by intro x hx; rfl)
  have hfull_filter :
      (∑ x : α, f x) =
        ∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0, f x := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun x : α => M.p x ≠ 0 ∧ M.q x ≠ 0) (f := f)]
    have hzero :
        (∑ x with ¬(M.p x ≠ 0 ∧ M.q x ≠ 0), f x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxnot : ¬(M.p x ≠ 0 ∧ M.q x ≠ 0) := (Finset.mem_filter.mp hx).2
      unfold f
      by_cases hp : M.p x = 0
      · simp [hp, NNReal.zero_rpow hs0.ne']
      · have hq : M.q x = 0 := by
          by_contra hq
          exact hxnot ⟨hp, hq⟩
        have h1s : 1 - s ≠ 0 := by linarith
        simp [hq, NNReal.zero_rpow h1s]
    rw [hzero, add_zero]
  rw [← hfilter, ← hfull_filter]
  rfl

/-- A positive classical Petz/Chernoff coefficient gives the finite real-log
form of the fixed-`s` exponent. -/
theorem chernoffExponent_eq_coe_neg_log_of_petzChernoffCoefficient_pos
    (M : ClassicalBinaryModel α) (s : ℝ)
    (h : 0 < M.petzChernoffCoefficient s) :
    M.chernoffExponent s =
      ((- Real.log (M.petzChernoffCoefficient s : ℝ) : ℝ) : EReal) := by
  have h0 : (M.petzChernoffCoefficient s : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast h.ne'
  have htop : ((M.petzChernoffCoefficient s : ℝ≥0∞) ≠ ⊤) := by
    simp
  simp [chernoffExponent, ENNReal.log_pos_real h0 htop, EReal.coe_neg]

/-- Interior common-support negative log partitions are bounded by the public
classical Chernoff distance. -/
theorem neg_log_commonPartition_le_chernoffDistance_of_mem_Ioo
    (M : ClassicalBinaryModel α) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    ((-Real.log (M.chernoffPartition s) : ℝ) : EReal) ≤ M.chernoffDistance := by
  have hpart :
      M.chernoffPartitionNNReal s = M.petzChernoffCoefficient s :=
    chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
      (M := M) hs0 hs1
  have hpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hpetzpos : 0 < M.petzChernoffCoefficient s := by
    rwa [← hpart]
  have hcoeff :
      M.chernoffExponent s =
        ((-Real.log (M.chernoffPartition s) : ℝ) : EReal) := by
    rw [chernoffExponent_eq_coe_neg_log_of_petzChernoffCoefficient_pos
      (M := M) (s := s) hpetzpos]
    rw [← hpart]
    simp
  rw [← hcoeff]
  exact le_iSup (fun t : Set.Icc (0 : ℝ) 1 => M.chernoffExponent t.1)
    ⟨s, le_of_lt hs0, le_of_lt hs1⟩

/-- Finite classical Chernoff distance excludes disjoint support. -/
theorem commonSupport_nonempty_of_chernoffDistance_ne_top
    (M : ClassicalBinaryModel α) (hfinite : M.chernoffDistance ≠ ⊤) :
    Nonempty M.commonSupport := by
  classical
  by_contra hnone
  have hcoeff : M.petzChernoffCoefficient (1 / 2 : ℝ) = 0 := by
    unfold petzChernoffCoefficient
    apply Finset.sum_eq_zero
    intro x _hx
    have hnot : ¬ (M.p x ≠ 0 ∧ M.q x ≠ 0) := by
      intro h
      exact hnone ⟨⟨x, h⟩⟩
    have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
    have honehalf : (1 - (1 / 2 : ℝ)) ≠ 0 := by norm_num
    by_cases hp : M.p x = 0
    · rw [hp, NNReal.zero_rpow hhalf, zero_mul]
    · have hq : M.q x = 0 := by
        by_contra hq
        exact hnot ⟨hp, hq⟩
      rw [hq, NNReal.zero_rpow honehalf, mul_zero]
  have hexp : M.chernoffExponent (1 / 2 : ℝ) = ⊤ := by
    unfold chernoffExponent
    rw [hcoeff]
    simp
  have hle : (⊤ : EReal) ≤ M.chernoffDistance := by
    rw [← hexp]
    exact le_iSup
      (fun t : Set.Icc (0 : ℝ) 1 => M.chernoffExponent t.1)
      ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  exact hfinite (le_antisymm le_top hle)

/-- Finite classical Chernoff distance gives a nonzero common-support
partition at every parameter. -/
theorem chernoffPartitionNNReal_ne_zero_of_chernoffDistance_ne_top
    (M : ClassicalBinaryModel α) (hfinite : M.chernoffDistance ≠ ⊤) (s : ℝ) :
    M.chernoffPartitionNNReal s ≠ 0 :=
  ne_of_gt
    (chernoffPartitionNNReal_pos_of_commonSupport_nonempty (M := M)
      (commonSupport_nonempty_of_chernoffDistance_ne_top (M := M) hfinite) s)

/-- Real log-partition for the common-support classical Chernoff function. -/
noncomputable def chernoffLogPartition (M : ClassicalBinaryModel α) (s : ℝ) : ℝ :=
  Real.log (M.chernoffPartition s)

/-- Derivative of the common-support Chernoff partition. -/
noncomputable def chernoffPartitionDeriv (M : ClassicalBinaryModel α) (s : ℝ) : ℝ :=
  ∑ x : M.commonSupport,
    ((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s)) *
      (Real.log (M.p x.1 : ℝ) - Real.log (M.q x.1 : ℝ))

/-- The tilted distribution supported on the common support, normalized by the
common-support partition. -/
noncomputable def commonSupportTiltedDistribution
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) : ClassicalDistribution α :=
  { prob := fun x =>
      if M.p x ≠ 0 ∧ M.q x ≠ 0 then
        M.p x ^ s * M.q x ^ (1 - s) / M.chernoffPartitionNNReal s
      else 0
    sum_eq_one := by
      classical
      rw [← Finset.sum_filter
        (s := Finset.univ)
        (p := fun x : α => M.p x ≠ 0 ∧ M.q x ≠ 0)
        (f := fun x : α => M.p x ^ s * M.q x ^ (1 - s) /
          M.chernoffPartitionNNReal s)]
      rw [← Finset.sum_div]
      have hsum :
          (∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0,
            M.p x ^ s * M.q x ^ (1 - s)) = M.chernoffPartitionNNReal s := by
        unfold chernoffPartitionNNReal commonSupport
        exact Finset.sum_bij (fun x hx => ⟨x, by simpa using (Finset.mem_filter.mp hx).2⟩)
          (by intro x hx; simp)
          (by intro a _ b _ h; simpa using h)
          (by
            intro y _hy
            refine ⟨y.1, ?_, rfl⟩
            simp [y.2])
          (by intro x hx; rfl)
      rw [hsum]
      exact div_self hZ }

@[simp]
theorem commonSupportTiltedDistribution_prob
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) (x : α) :
    (M.commonSupportTiltedDistribution s hZ).prob x =
      if M.p x ≠ 0 ∧ M.q x ≠ 0 then
        M.p x ^ s * M.q x ^ (1 - s) / M.chernoffPartitionNNReal s
      else 0 := rfl

theorem commonSupportTiltedDistribution_prob_toReal_of_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : M.p x ≠ 0 ∧ M.q x ≠ 0) :
    ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) =
      ((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
        M.chernoffPartition s := by
  have hZr : (M.chernoffPartitionNNReal s : ℝ) = M.chernoffPartition s := by
    simp
  simp [commonSupportTiltedDistribution_prob, hx, hZr]

theorem commonSupportTiltedDistribution_prob_toReal_of_not_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : ¬(M.p x ≠ 0 ∧ M.q x ≠ 0)) :
    ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) = 0 := by
  simp [commonSupportTiltedDistribution_prob, hx]

private theorem sum_div_mul_sub_const_eq {ι : Type u} [Fintype ι]
    (W A : ι → ℝ) {Z c : ℝ} (hZ : Z ≠ 0) (hW : (∑ x, W x) = Z) :
    (∑ x, (W x / Z) * (c * A x - Real.log Z)) =
      c * (∑ x, W x * A x) / Z - Real.log Z := by
  calc
    (∑ x, (W x / Z) * (c * A x - Real.log Z))
        = (∑ x, ((c * (W x * A x)) / Z - (Real.log Z * W x) / Z)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          field_simp [hZ]
    _ = (∑ x, (c * (W x * A x)) / Z) -
        (∑ x, (Real.log Z * W x) / Z) := by
          rw [Finset.sum_sub_distrib]
    _ = c * (∑ x, W x * A x) / Z -
        Real.log Z * (∑ x, W x) / Z := by
          congr 2
          · rw [← Finset.sum_div]
            congr 1
            rw [Finset.mul_sum]
          · rw [← Finset.sum_div]
            congr 1
            rw [Finset.mul_sum]
    _ = c * (∑ x, W x * A x) / Z - Real.log Z := by
          rw [hW]
          field_simp [hZ]

/-- Pointwise KL summand of the common-support tilted distribution against
the `p` side. -/
theorem relativeEntropySummandReal_commonSupportTilted_p_of_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : M.p x ≠ 0 ∧ M.q x ≠ 0) :
    relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.pDistribution x =
      (((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        ((1 - s) * (Real.log (M.q x : ℝ) - Real.log (M.p x : ℝ)) -
          Real.log (M.chernoffPartition s)) := by
  classical
  have hp : 0 < (M.p x : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hx.1)
  have hq : 0 < (M.q x : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hx.2)
  have hZpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition s := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hr :
      ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) =
      ((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
        M.chernoffPartition s :=
    commonSupportTiltedDistribution_prob_toReal_of_mem (M := M) (s := s) hZ hx
  have hrpos :
      0 < ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) := by
    rw [hr]
    positivity
  have hrne_nn : (M.commonSupportTiltedDistribution s hZ).prob x ≠ 0 := by
    exact_mod_cast hrpos.ne'
  rw [relativeEntropySummandReal, if_neg hrne_nn]
  rw [hr]
  congr 1
  simp [pDistribution]
  rw [Real.log_div
      (div_ne_zero
        (mul_ne_zero (Real.rpow_pos_of_pos hp s).ne'
          (Real.rpow_pos_of_pos hq (1 - s)).ne')
        hZpos.ne')
      hp.ne',
    Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos hp s).ne'
      (Real.rpow_pos_of_pos hq (1 - s)).ne') hZpos.ne',
    Real.log_mul (Real.rpow_pos_of_pos hp s).ne'
      (Real.rpow_pos_of_pos hq (1 - s)).ne',
    Real.log_rpow hp, Real.log_rpow hq]
  ring

/-- Pointwise KL summand of the common-support tilted distribution against
the `q` side. -/
theorem relativeEntropySummandReal_commonSupportTilted_q_of_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : M.p x ≠ 0 ∧ M.q x ≠ 0) :
    relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.qDistribution x =
      (((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        (s * (Real.log (M.p x : ℝ) - Real.log (M.q x : ℝ)) -
          Real.log (M.chernoffPartition s)) := by
  classical
  have hp : 0 < (M.p x : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hx.1)
  have hq : 0 < (M.q x : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hx.2)
  have hZpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition s := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hr :
      ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) =
      ((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
        M.chernoffPartition s :=
    commonSupportTiltedDistribution_prob_toReal_of_mem (M := M) (s := s) hZ hx
  have hrpos :
      0 < ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) := by
    rw [hr]
    positivity
  have hrne_nn : (M.commonSupportTiltedDistribution s hZ).prob x ≠ 0 := by
    exact_mod_cast hrpos.ne'
  rw [relativeEntropySummandReal, if_neg hrne_nn]
  rw [hr]
  congr 1
  simp [qDistribution]
  rw [Real.log_div
      (div_ne_zero
        (mul_ne_zero (Real.rpow_pos_of_pos hp s).ne'
          (Real.rpow_pos_of_pos hq (1 - s)).ne')
        hZpos.ne')
      hq.ne',
    Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos hp s).ne'
      (Real.rpow_pos_of_pos hq (1 - s)).ne') hZpos.ne',
    Real.log_mul (Real.rpow_pos_of_pos hp s).ne'
      (Real.rpow_pos_of_pos hq (1 - s)).ne',
    Real.log_rpow hp, Real.log_rpow hq]
  ring

/-- Outside the common support, the `p` KL summand of the common-support tilted
distribution is zero. -/
theorem relativeEntropySummandReal_commonSupportTilted_p_of_not_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : ¬(M.p x ≠ 0 ∧ M.q x ≠ 0)) :
    relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.pDistribution x = 0 := by
  have hr :
      ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) = 0 :=
    commonSupportTiltedDistribution_prob_toReal_of_not_mem (M := M) (s := s) hZ hx
  have hrnn : (M.commonSupportTiltedDistribution s hZ).prob x = 0 := by
    exact_mod_cast hr
  rw [relativeEntropySummandReal, if_pos hrnn]

/-- Outside the common support, the `q` KL summand of the common-support tilted
distribution is zero. -/
theorem relativeEntropySummandReal_commonSupportTilted_q_of_not_mem
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : α}
    (hx : ¬(M.p x ≠ 0 ∧ M.q x ≠ 0)) :
    relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.qDistribution x = 0 := by
  have hr :
      ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) = 0 :=
    commonSupportTiltedDistribution_prob_toReal_of_not_mem (M := M) (s := s) hZ hx
  have hrnn : (M.commonSupportTiltedDistribution s hZ).prob x = 0 := by
    exact_mod_cast hr
  rw [relativeEntropySummandReal, if_pos hrnn]

/-- Common-support sum algebra for the tilted KL against `p`. -/
theorem commonSupportTilted_relativeEntropy_p_sum_algebra
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    (∑ x : M.commonSupport,
      (((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        ((1 - s) * (Real.log (M.q x.1 : ℝ) - Real.log (M.p x.1 : ℝ)) -
          Real.log (M.chernoffPartition s))) =
      -Real.log (M.chernoffPartition s) -
        (1 - s) * M.chernoffPartitionDeriv s / M.chernoffPartition s := by
  have hZpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition s := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  unfold chernoffPartition chernoffPartitionDeriv
  let W : M.commonSupport → ℝ := fun x =>
    ((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s))
  let A : M.commonSupport → ℝ := fun x =>
    Real.log (M.q x.1 : ℝ) - Real.log (M.p x.1 : ℝ)
  have halg := sum_div_mul_sub_const_eq
    (W := W) (A := A) (Z := M.chernoffPartition s) (c := 1 - s)
    hZpos.ne' (by simp [W, chernoffPartition])
  have hderiv :
      (∑ x : M.commonSupport, W x * A x) = -M.chernoffPartitionDeriv s := by
    unfold W A chernoffPartitionDeriv
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  change
    (∑ x, (W x / M.chernoffPartition s) *
      ((1 - s) * A x - Real.log (M.chernoffPartition s))) =
      -Real.log (M.chernoffPartition s) -
        (1 - s) * M.chernoffPartitionDeriv s / M.chernoffPartition s
  rw [halg, hderiv]
  ring

/-- Common-support sum algebra for the tilted KL against `q`. -/
theorem commonSupportTilted_relativeEntropy_q_sum_algebra
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    (∑ x : M.commonSupport,
      (((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        (s * (Real.log (M.p x.1 : ℝ) - Real.log (M.q x.1 : ℝ)) -
          Real.log (M.chernoffPartition s))) =
      -Real.log (M.chernoffPartition s) +
        s * M.chernoffPartitionDeriv s / M.chernoffPartition s := by
  have hZpos_nn : 0 < M.chernoffPartitionNNReal s := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition s := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  unfold chernoffPartition chernoffPartitionDeriv
  let W : M.commonSupport → ℝ := fun x =>
    ((M.p x.1 : ℝ) ^ s) * ((M.q x.1 : ℝ) ^ (1 - s))
  let A : M.commonSupport → ℝ := fun x =>
    Real.log (M.p x.1 : ℝ) - Real.log (M.q x.1 : ℝ)
  have halg := sum_div_mul_sub_const_eq
    (W := W) (A := A) (Z := M.chernoffPartition s) (c := s)
    hZpos.ne' (by simp [W, chernoffPartition])
  have hderiv :
      (∑ x : M.commonSupport, W x * A x) = M.chernoffPartitionDeriv s := by
    unfold W A chernoffPartitionDeriv
    rfl
  change
    (∑ x, (W x / M.chernoffPartition s) *
      (s * A x - Real.log (M.chernoffPartition s))) =
      -Real.log (M.chernoffPartition s) +
        s * M.chernoffPartitionDeriv s / M.chernoffPartition s
  rw [halg, hderiv]
  ring

/-- KL identity for the common-support tilted distribution against `p`. -/
theorem relativeEntropyReal_commonSupportTilted_p
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    relativeEntropyReal (M.commonSupportTiltedDistribution s hZ) M.pDistribution =
      -Real.log (M.chernoffPartition s) -
        (1 - s) * M.chernoffPartitionDeriv s / M.chernoffPartition s := by
  classical
  unfold relativeEntropyReal
  have hrestrict :
      (∑ x, relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.pDistribution x) =
        Finset.sum Finset.univ (fun x : α =>
          if M.p x ≠ 0 ∧ M.q x ≠ 0 then
            relativeEntropySummandReal
              (M.commonSupportTiltedDistribution s hZ) M.pDistribution x
          else 0) := by
    apply Finset.sum_congr rfl
    intro x _hxmem
    by_cases hx : M.p x ≠ 0 ∧ M.q x ≠ 0
    · simp [hx]
    · rw [if_neg hx]
      rw [relativeEntropySummandReal_commonSupportTilted_p_of_not_mem (M := M) (s := s) hZ hx]
  rw [hrestrict]
  rw [← Finset.sum_filter
    (s := Finset.univ)
    (p := fun x : α => M.p x ≠ 0 ∧ M.q x ≠ 0)
    (f := fun x : α => relativeEntropySummandReal
      (M.commonSupportTiltedDistribution s hZ) M.pDistribution x)]
  calc
    (∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0,
      relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.pDistribution x)
        =
      ∑ y : M.commonSupport,
        relativeEntropySummandReal
          (M.commonSupportTiltedDistribution s hZ) M.pDistribution y.1 := by
          unfold commonSupport
          exact Finset.sum_bij (fun x hx => ⟨x, by simpa using (Finset.mem_filter.mp hx).2⟩)
            (by intro x hx; simp)
            (by intro a _ b _ h; simpa using h)
            (by
              intro y _hy
              refine ⟨y.1, ?_, rfl⟩
              simp [y.2])
            (by intro x hx; rfl)
    _ =
      ∑ y : M.commonSupport,
        (((M.p y.1 : ℝ) ^ s) * ((M.q y.1 : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        ((1 - s) * (Real.log (M.q y.1 : ℝ) - Real.log (M.p y.1 : ℝ)) -
          Real.log (M.chernoffPartition s)) := by
          apply Finset.sum_congr rfl
          intro y _hy
          exact relativeEntropySummandReal_commonSupportTilted_p_of_mem
            (M := M) (s := s) hZ y.2
    _ = -Real.log (M.chernoffPartition s) -
        (1 - s) * M.chernoffPartitionDeriv s / M.chernoffPartition s :=
          commonSupportTilted_relativeEntropy_p_sum_algebra (M := M) (s := s) hZ

/-- KL identity for the common-support tilted distribution against `q`. -/
theorem relativeEntropyReal_commonSupportTilted_q
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    relativeEntropyReal (M.commonSupportTiltedDistribution s hZ) M.qDistribution =
      -Real.log (M.chernoffPartition s) +
        s * M.chernoffPartitionDeriv s / M.chernoffPartition s := by
  classical
  unfold relativeEntropyReal
  have hrestrict :
      (∑ x, relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.qDistribution x) =
        Finset.sum Finset.univ (fun x : α =>
          if M.p x ≠ 0 ∧ M.q x ≠ 0 then
            relativeEntropySummandReal
              (M.commonSupportTiltedDistribution s hZ) M.qDistribution x
          else 0) := by
    apply Finset.sum_congr rfl
    intro x _hxmem
    by_cases hx : M.p x ≠ 0 ∧ M.q x ≠ 0
    · simp [hx]
    · rw [if_neg hx]
      rw [relativeEntropySummandReal_commonSupportTilted_q_of_not_mem (M := M) (s := s) hZ hx]
  rw [hrestrict]
  rw [← Finset.sum_filter
    (s := Finset.univ)
    (p := fun x : α => M.p x ≠ 0 ∧ M.q x ≠ 0)
    (f := fun x : α => relativeEntropySummandReal
      (M.commonSupportTiltedDistribution s hZ) M.qDistribution x)]
  calc
    (∑ x with M.p x ≠ 0 ∧ M.q x ≠ 0,
      relativeEntropySummandReal
        (M.commonSupportTiltedDistribution s hZ) M.qDistribution x)
        =
      ∑ y : M.commonSupport,
        relativeEntropySummandReal
          (M.commonSupportTiltedDistribution s hZ) M.qDistribution y.1 := by
          unfold commonSupport
          exact Finset.sum_bij (fun x hx => ⟨x, by simpa using (Finset.mem_filter.mp hx).2⟩)
            (by intro x hx; simp)
            (by intro a _ b _ h; simpa using h)
            (by
              intro y _hy
              refine ⟨y.1, ?_, rfl⟩
              simp [y.2])
            (by intro x hx; rfl)
    _ =
      ∑ y : M.commonSupport,
        (((M.p y.1 : ℝ) ^ s) * ((M.q y.1 : ℝ) ^ (1 - s)) /
          M.chernoffPartition s) *
        (s * (Real.log (M.p y.1 : ℝ) - Real.log (M.q y.1 : ℝ)) -
          Real.log (M.chernoffPartition s)) := by
          apply Finset.sum_congr rfl
          intro y _hy
          exact relativeEntropySummandReal_commonSupportTilted_q_of_mem
            (M := M) (s := s) hZ y.2
    _ = -Real.log (M.chernoffPartition s) +
        s * M.chernoffPartitionDeriv s / M.chernoffPartition s :=
          commonSupportTilted_relativeEntropy_q_sum_algebra (M := M) (s := s) hZ

/-- The common-support tilted distribution is supported on `p`. -/
theorem commonSupportTiltedDistribution_supportedBy_p
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    (M.commonSupportTiltedDistribution s hZ).SupportedBy M.p := by
  intro x hx
  rw [commonSupportTiltedDistribution_prob] at hx
  by_contra hp0
  simp [hp0] at hx

/-- The common-support tilted distribution is supported on `q`. -/
theorem commonSupportTiltedDistribution_supportedBy_q
    (M : ClassicalBinaryModel α) (s : ℝ)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    (M.commonSupportTiltedDistribution s hZ).SupportedBy M.q := by
  intro x hx
  rw [commonSupportTiltedDistribution_prob] at hx
  by_contra hq0
  simp [hq0] at hx

/-- The common-support partition is differentiable, with derivative determined
by the orientation `p^s q^(1-s)`. -/
theorem hasDerivAt_chernoffPartition
    (M : ClassicalBinaryModel α) (s : ℝ) :
    HasDerivAt (fun t : ℝ => M.chernoffPartition t)
      (M.chernoffPartitionDeriv s) s := by
  unfold chernoffPartition chernoffPartitionDeriv
  refine HasDerivAt.fun_sum (u := Finset.univ) ?_
  intro i _hi
  let a : ℝ := (M.p i.1 : ℝ)
  let b : ℝ := (M.q i.1 : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (pos_iff_ne_zero.mpr i.2.1)
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast (pos_iff_ne_zero.mpr i.2.2)
  have hpowa :
      HasDerivAt (fun t : ℝ => a ^ t) (Real.log a * a ^ s) s := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id s
    simpa using hid.const_rpow ha
  have hlin : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
    simpa using (hasDerivAt_const (x := s) (c := (1 : ℝ))).sub (hasDerivAt_id s)
  have hpowb :
      HasDerivAt (fun t : ℝ => b ^ (1 - t))
        (-(Real.log b * b ^ (1 - s))) s := by
    simpa using hlin.const_rpow hb
  have hmul := hpowa.mul hpowb
  change HasDerivAt (fun t : ℝ => a ^ t * b ^ (1 - t))
    (a ^ s * b ^ (1 - s) * (Real.log a - Real.log b)) s
  convert hmul using 1
  ring

/-- The common-support Chernoff partition is continuous. -/
theorem continuous_chernoffPartition (M : ClassicalBinaryModel α) :
    Continuous (fun s : ℝ => M.chernoffPartition s) := by
  unfold chernoffPartition
  refine continuous_finsetSum Finset.univ ?_
  intro i _hi
  let a : ℝ := (M.p i.1 : ℝ)
  let b : ℝ := (M.q i.1 : ℝ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast i.2.1
  have hb : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast i.2.2
  exact (Real.continuous_const_rpow ha).mul
    ((Real.continuous_const_rpow hb).comp (continuous_const.sub continuous_id))

/-- The common-support Chernoff partition attains a minimum on `[0,1]`. -/
theorem exists_isMinOn_chernoffPartition_Icc
    (M : ClassicalBinaryModel α) :
    ∃ sStar : Set.Icc (0 : ℝ) 1,
      IsMinOn (fun s : Set.Icc (0 : ℝ) 1 => M.chernoffPartition s.1)
        Set.univ sStar := by
  have hcont : ContinuousOn (fun s : Set.Icc (0 : ℝ) 1 =>
      M.chernoffPartition s.1) Set.univ :=
    ((continuous_chernoffPartition M).comp continuous_subtype_val).continuousOn
  obtain ⟨sStar, _hmem, hmin⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty) hcont
  exact ⟨sStar, hmin⟩

/-- Real-valued version of the common-support partition minimizer on `[0,1]`. -/
theorem exists_isMinOn_chernoffPartition_Icc_real
    (M : ClassicalBinaryModel α) :
    ∃ sStar ∈ Set.Icc (0 : ℝ) 1,
      IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar := by
  have hcont : ContinuousOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) :=
    (continuous_chernoffPartition M).continuousOn
  exact isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) hcont

/-- At a left-endpoint minimum of the common-support partition on `[0,1]`,
the one-sided derivative is nonnegative. -/
theorem chernoffPartitionDeriv_nonneg_at_left_min
    (M : ClassicalBinaryModel α) {sStar : ℝ}
    (hs : sStar = 0)
    (hmin : IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar) :
    0 ≤ M.chernoffPartitionDeriv sStar := by
  subst sStar
  have hdir : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    have hseg : segment ℝ (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [segment_eq_Icc zero_le_one]
    simpa using sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg :
      0 ≤
        (ContinuousLinearMap.toSpanSingleton ℝ (M.chernoffPartitionDeriv 0)) (1 : ℝ) :=
    hmin.localize.hasFDerivWithinAt_nonneg
      ((hasDerivAt_chernoffPartition M 0).hasDerivWithinAt) hdir
  simpa [ContinuousLinearMap.toSpanSingleton_apply] using hnonneg

/-- At a right-endpoint minimum of the common-support partition on `[0,1]`,
the one-sided derivative is nonpositive. -/
theorem chernoffPartitionDeriv_nonpos_at_right_min
    (M : ClassicalBinaryModel α) {sStar : ℝ}
    (hs : sStar = 1)
    (hmin : IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar) :
    M.chernoffPartitionDeriv sStar ≤ 0 := by
  subst sStar
  have hdir : (-1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 1 := by
    simpa using
      (sub_mem_posTangentConeAt_of_segment_subset
        (x := (1 : ℝ)) (y := (0 : ℝ))
        (by rw [segment_symm, segment_eq_Icc zero_le_one]))
  have hnonneg :
      0 ≤
        (ContinuousLinearMap.toSpanSingleton ℝ (M.chernoffPartitionDeriv 1)) (-1 : ℝ) :=
    hmin.localize.hasFDerivWithinAt_nonneg
      ((hasDerivAt_chernoffPartition M 1).hasDerivWithinAt) hdir
  simpa [ContinuousLinearMap.toSpanSingleton_apply] using hnonneg

/-- At an interior minimum of the common-support partition on `[0,1]`,
the derivative vanishes. -/
theorem chernoffPartitionDeriv_eq_zero_at_interior_min
    (M : ClassicalBinaryModel α) {sStar : ℝ}
    (hs0 : 0 < sStar) (hs1 : sStar < 1)
    (hmin : IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar) :
    M.chernoffPartitionDeriv sStar = 0 := by
  have hnhds : Set.Icc (0 : ℝ) 1 ∈ 𝓝 sStar :=
    Icc_mem_nhds hs0 hs1
  exact hmin.isLocalMin hnhds |>.hasDerivAt_eq_zero
    (hasDerivAt_chernoffPartition M sStar)

/-- The left endpoint common-support log partition is bounded by the public
Chernoff distance by approaching it from the open interval. -/
theorem neg_log_commonPartition_left_le_chernoffDistance
    (M : ClassicalBinaryModel α)
    (hZ : M.chernoffPartitionNNReal 0 ≠ 0) :
    ((-Real.log (M.chernoffPartition 0) : ℝ) : EReal) ≤
      M.chernoffDistance := by
  classical
  let sseq : Nat → ℝ := fun n => (((n + 2 : Nat) : ℝ)⁻¹)
  have hZpos_nn : 0 < M.chernoffPartitionNNReal 0 := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition 0 := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hsseq_tend : Tendsto sseq atTop (𝓝 (0 : ℝ)) := by
    simpa [sseq, Function.comp_def, one_div, Nat.cast_add,
      add_comm, add_left_comm, add_assoc] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
  have hpart_tend :
      Tendsto (fun n : Nat => M.chernoffPartition (sseq n))
        atTop (𝓝 (M.chernoffPartition 0)) :=
    (continuous_chernoffPartition M).continuousAt.tendsto.comp hsseq_tend
  have hpart_pos_eventual :
      ∀ᶠ n in atTop, 0 < M.chernoffPartition (sseq n) :=
    hpart_tend.eventually (lt_mem_nhds hZpos)
  have hineq_eventual :
      ∀ᶠ n in atTop,
        ((-Real.log (M.chernoffPartition (sseq n)) : ℝ) : EReal) ≤
          M.chernoffDistance := by
    filter_upwards [hpart_pos_eventual] with n hpos
    have hs0 : 0 < sseq n := by
      have hpos_nat : (0 : ℝ) < (n + 2 : Nat) := by
        exact_mod_cast Nat.succ_pos (n + 1)
      exact inv_pos.mpr hpos_nat
    have hs1 : sseq n < 1 := by
      have hlt : (1 : ℝ) < (n + 2 : Nat) := by
        have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
        norm_num
        linarith
      simpa [sseq] using inv_lt_one_of_one_lt₀ hlt
    have hZseq : M.chernoffPartitionNNReal (sseq n) ≠ 0 := by
      have hpos_nn : 0 < M.chernoffPartitionNNReal (sseq n) := by
        rw [← chernoffPartitionNNReal_coe] at hpos
        exact_mod_cast hpos
      exact ne_of_gt hpos_nn
    exact neg_log_commonPartition_le_chernoffDistance_of_mem_Ioo
      (M := M) hs0 hs1 hZseq
  have hlog_tend :
      Tendsto (fun n : Nat => -Real.log (M.chernoffPartition (sseq n)))
        atTop (𝓝 (-Real.log (M.chernoffPartition 0))) := by
    have hcont :
        ContinuousAt (fun x : ℝ => -Real.log x) (M.chernoffPartition 0) :=
      (Real.continuousAt_log hZpos.ne').neg
    exact hcont.tendsto.comp hpart_tend
  exact le_of_tendsto (EReal.tendsto_coe.mpr hlog_tend) hineq_eventual

/-- The right endpoint common-support log partition is bounded by the public
Chernoff distance by approaching it from the open interval. -/
theorem neg_log_commonPartition_right_le_chernoffDistance
    (M : ClassicalBinaryModel α)
    (hZ : M.chernoffPartitionNNReal 1 ≠ 0) :
    ((-Real.log (M.chernoffPartition 1) : ℝ) : EReal) ≤
      M.chernoffDistance := by
  classical
  let sseq : Nat → ℝ := fun n => (1 : ℝ) - (((n + 2 : Nat) : ℝ)⁻¹)
  have hZpos_nn : 0 < M.chernoffPartitionNNReal 1 := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition 1 := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hinv_tend :
      Tendsto (fun n : Nat => (((n + 2 : Nat) : ℝ)⁻¹))
        atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def, one_div, Nat.cast_add,
      add_comm, add_left_comm, add_assoc] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
  have hsseq_tend : Tendsto sseq atTop (𝓝 (1 : ℝ)) := by
    simpa [sseq] using tendsto_const_nhds.sub hinv_tend
  have hpart_tend :
      Tendsto (fun n : Nat => M.chernoffPartition (sseq n))
        atTop (𝓝 (M.chernoffPartition 1)) :=
    (continuous_chernoffPartition M).continuousAt.tendsto.comp hsseq_tend
  have hpart_pos_eventual :
      ∀ᶠ n in atTop, 0 < M.chernoffPartition (sseq n) :=
    hpart_tend.eventually (lt_mem_nhds hZpos)
  have hineq_eventual :
      ∀ᶠ n in atTop,
        ((-Real.log (M.chernoffPartition (sseq n)) : ℝ) : EReal) ≤
          M.chernoffDistance := by
    filter_upwards [hpart_pos_eventual] with n hpos
    have hinv_pos : 0 < (((n + 2 : Nat) : ℝ)⁻¹) := by
      have hpos_nat : (0 : ℝ) < (n + 2 : Nat) := by
        exact_mod_cast Nat.succ_pos (n + 1)
      exact inv_pos.mpr hpos_nat
    have hinv_lt_one : (((n + 2 : Nat) : ℝ)⁻¹) < 1 := by
      have hlt : (1 : ℝ) < (n + 2 : Nat) := by
        have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
        norm_num
        linarith
      exact inv_lt_one_of_one_lt₀ hlt
    have hs0 : 0 < sseq n := by
      dsimp [sseq]
      linarith
    have hs1 : sseq n < 1 := by
      dsimp [sseq]
      linarith
    have hZseq : M.chernoffPartitionNNReal (sseq n) ≠ 0 := by
      have hpos_nn : 0 < M.chernoffPartitionNNReal (sseq n) := by
        rw [← chernoffPartitionNNReal_coe] at hpos
        exact_mod_cast hpos
      exact ne_of_gt hpos_nn
    exact neg_log_commonPartition_le_chernoffDistance_of_mem_Ioo
      (M := M) hs0 hs1 hZseq
  have hlog_tend :
      Tendsto (fun n : Nat => -Real.log (M.chernoffPartition (sseq n)))
        atTop (𝓝 (-Real.log (M.chernoffPartition 1))) := by
    have hcont :
        ContinuousAt (fun x : ℝ => -Real.log x) (M.chernoffPartition 1) :=
      (Real.continuousAt_log hZpos.ne').neg
    exact hcont.tendsto.comp hpart_tend
  exact le_of_tendsto (EReal.tendsto_coe.mpr hlog_tend) hineq_eventual

/-- Any nonzero common-support log partition on `[0,1]` is bounded by the
public classical Chernoff distance.  Endpoint cases are obtained as limits from
the open interval because the full Petz coefficient has endpoint artifacts
from `0^0`. -/
theorem neg_log_commonPartition_le_chernoffDistance
    (M : ClassicalBinaryModel α) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    ((-Real.log (M.chernoffPartition s) : ℝ) : EReal) ≤
      M.chernoffDistance := by
  rcases lt_or_eq_of_le hs.1 with hs0 | hs0eq
  · rcases lt_or_eq_of_le hs.2 with hs1 | hs1eq
    · exact neg_log_commonPartition_le_chernoffDistance_of_mem_Ioo
        (M := M) hs0 hs1 hZ
    · subst s
      exact neg_log_commonPartition_right_le_chernoffDistance (M := M) hZ
  · subst s
    exact neg_log_commonPartition_left_le_chernoffDistance (M := M) hZ

/-- IID tensor powers multiply classical Petz/Chernoff coefficients. -/
theorem tensorPower_petzChernoffCoefficient
    (M : ClassicalBinaryModel α) (s : ℝ) (n : Nat) :
    (M.tensorPower n).petzChernoffCoefficient s =
      M.petzChernoffCoefficient s ^ n := by
  induction n with
  | zero =>
      change
        (∑ _x : PUnit, (1 : ℝ≥0) ^ s * (1 : ℝ≥0) ^ (1 - s)) =
          M.petzChernoffCoefficient s ^ 0
      simp
  | succ n ih =>
      change
        (∑ x : Prod α (TensorPower α n),
            ((M.p x.1 * (M.tensorPower n).p x.2) ^ s) *
              ((M.q x.1 * (M.tensorPower n).q x.2) ^ (1 - s))) =
          M.petzChernoffCoefficient s ^ (n + 1)
      rw [Fintype.sum_prod_type]
      calc
        (∑ x : α, ∑ xs : TensorPower α n,
            ((M.p x * (M.tensorPower n).p xs) ^ s) *
              ((M.q x * (M.tensorPower n).q xs) ^ (1 - s)))
            = ∑ x : α, ∑ xs : TensorPower α n,
                (M.p x ^ s * M.q x ^ (1 - s)) *
                  ((M.tensorPower n).p xs ^ s *
                    (M.tensorPower n).q xs ^ (1 - s)) := by
              simp [NNReal.mul_rpow, mul_assoc, mul_left_comm]
        _ = ∑ x : α,
              (M.p x ^ s * M.q x ^ (1 - s)) *
                (∑ xs : TensorPower α n,
                  (M.tensorPower n).p xs ^ s *
                    (M.tensorPower n).q xs ^ (1 - s)) := by
              simp [Finset.mul_sum]
        _ =
            (∑ x : α, M.p x ^ s * M.q x ^ (1 - s)) *
              (∑ xs : TensorPower α n,
                (M.tensorPower n).p xs ^ s *
                  (M.tensorPower n).q xs ^ (1 - s)) := by
              rw [Finset.sum_mul]
        _ = M.petzChernoffCoefficient s * (M.tensorPower n).petzChernoffCoefficient s := by
              rfl
        _ = M.petzChernoffCoefficient s * M.petzChernoffCoefficient s ^ n := by
              rw [ih]
        _ = M.petzChernoffCoefficient s ^ (n + 1) := by
              rw [pow_succ]
              rw [mul_comm]

variable [DecidableEq α]

def distributionKLMax
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α) : EReal :=
  max (relativeEntropy r M.pDistribution) (relativeEntropy r M.qDistribution)

omit [DecidableEq α] in
/-- On common support, the support-aware KL maximum is the real KL maximum
embedded into `EReal`. -/
theorem distributionKLMax_eq_coe_real_of_supported
    (M : ClassicalBinaryModel α) (r : ClassicalDistribution α)
    (hp : r.SupportedBy M.p) (hq : r.SupportedBy M.q) :
    M.distributionKLMax r =
      ((max (relativeEntropyReal r M.pDistribution)
          (relativeEntropyReal r M.qDistribution) : ℝ) : EReal) := by
  classical
  have hp' : r.SupportedBy M.pDistribution.prob := by
    simpa [pDistribution] using hp
  have hq' : r.SupportedBy M.qDistribution.prob := by
    simpa [qDistribution] using hq
  unfold distributionKLMax
  rw [relativeEntropy_eq_coe_of_supported _ _ hp',
    relativeEntropy_eq_coe_of_supported _ _ hq']
  by_cases hle :
      relativeEntropyReal r M.pDistribution ≤
        relativeEntropyReal r M.qDistribution
  · rw [max_eq_right hle, max_eq_right (EReal.coe_le_coe_iff.mpr hle)]
  · have hge :
        relativeEntropyReal r M.qDistribution ≤
          relativeEntropyReal r M.pDistribution := le_of_not_ge hle
    rw [max_eq_left hge, max_eq_left (EReal.coe_le_coe_iff.mpr hge)]

omit [DecidableEq α] in
/-- A common-support tilted distribution at a common-support partition
minimizer has KL maximum bounded by the negative log of the partition. -/
theorem commonSupportTilted_distributionKLMax_le_neg_log_partition_at_min
    (M : ClassicalBinaryModel α) [DecidableEq α] {sStar : ℝ}
    (hs : sStar ∈ Set.Icc (0 : ℝ) 1)
    (hmin : IsMinOn (fun s : ℝ => M.chernoffPartition s) (Set.Icc 0 1) sStar)
    (hZ : M.chernoffPartitionNNReal sStar ≠ 0) :
    M.distributionKLMax (M.commonSupportTiltedDistribution sStar hZ) ≤
      ((-Real.log (M.chernoffPartition sStar) : ℝ) : EReal) := by
  classical
  have hZpos_nn : 0 < M.chernoffPartitionNNReal sStar := by
    exact lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition sStar := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have hs0 : 0 ≤ sStar := hs.1
  have hs1 : sStar ≤ 1 := hs.2
  have hdist :
      M.distributionKLMax (M.commonSupportTiltedDistribution sStar hZ) =
        ((max
            (relativeEntropyReal (M.commonSupportTiltedDistribution sStar hZ) M.pDistribution)
            (relativeEntropyReal (M.commonSupportTiltedDistribution sStar hZ) M.qDistribution)
          : ℝ) : EReal) :=
    distributionKLMax_eq_coe_real_of_supported (M := M)
      (r := M.commonSupportTiltedDistribution sStar hZ)
      (commonSupportTiltedDistribution_supportedBy_p M sStar hZ)
      (commonSupportTiltedDistribution_supportedBy_q M sStar hZ)
  rw [hdist, EReal.coe_le_coe_iff]
  refine max_le ?_ ?_
  · rw [relativeEntropyReal_commonSupportTilted_p (M := M) (s := sStar) hZ]
    rcases lt_or_eq_of_le hs0 with hs0lt | hs0eq
    · rcases lt_or_eq_of_le hs1 with hs1lt | hs1eq
      · have hD :
            M.chernoffPartitionDeriv sStar = 0 :=
          chernoffPartitionDeriv_eq_zero_at_interior_min (M := M)
            hs0lt hs1lt hmin
        rw [hD]
        have hzero :
            (1 - sStar) * 0 / M.chernoffPartition sStar = 0 := by ring
        rw [hzero]
        simp
      · have hD :
            M.chernoffPartitionDeriv sStar ≤ 0 :=
          chernoffPartitionDeriv_nonpos_at_right_min (M := M) hs1eq hmin
        have hcoeff : 0 ≤ (1 - sStar) := by linarith
        have hterm :
            0 ≤ (1 - sStar) * M.chernoffPartitionDeriv sStar /
              M.chernoffPartition sStar := by
          have hm : 0 ≤ (1 - sStar) * M.chernoffPartitionDeriv sStar := by
            nlinarith [hcoeff, hD]
          exact div_nonneg hm hZpos.le
        nlinarith
    · subst sStar
      have hD :
          0 ≤ M.chernoffPartitionDeriv 0 :=
        chernoffPartitionDeriv_nonneg_at_left_min (M := M) rfl hmin
      have hterm :
          0 ≤ (1 - (0 : ℝ)) * M.chernoffPartitionDeriv 0 /
            M.chernoffPartition 0 := by
        have hm : 0 ≤ (1 - (0 : ℝ)) * M.chernoffPartitionDeriv 0 := by
          nlinarith
        exact div_nonneg hm hZpos.le
      nlinarith
  · rw [relativeEntropyReal_commonSupportTilted_q (M := M) (s := sStar) hZ]
    rcases lt_or_eq_of_le hs0 with hs0lt | hs0eq
    · rcases lt_or_eq_of_le hs1 with hs1lt | hs1eq
      · have hD :
            M.chernoffPartitionDeriv sStar = 0 :=
          chernoffPartitionDeriv_eq_zero_at_interior_min (M := M)
            hs0lt hs1lt hmin
        rw [hD]
        have hzero :
            sStar * 0 / M.chernoffPartition sStar = 0 := by ring
        rw [hzero]
        simp
      · have hD :
            M.chernoffPartitionDeriv sStar ≤ 0 :=
          chernoffPartitionDeriv_nonpos_at_right_min (M := M) hs1eq hmin
        have hterm :
            sStar * M.chernoffPartitionDeriv sStar /
              M.chernoffPartition sStar ≤ 0 := by
          have hm : sStar * M.chernoffPartitionDeriv sStar ≤ 0 := by
            nlinarith [hs0, hD]
          exact div_nonpos_of_nonpos_of_nonneg hm hZpos.le
        nlinarith
    · subst sStar
      have hzero :
          (0 : ℝ) * M.chernoffPartitionDeriv 0 /
            M.chernoffPartition 0 = 0 := by ring
      rw [hzero]
      simp

omit [DecidableEq α] in
/-- Direct tilted-distribution variational witness for the classical Chernoff
bound.  In the finite-distance case the common support is nonempty, so the
common-support tilted distribution at a partition minimizer is well-defined and
has KL maximum at most the public Chernoff distance. -/
theorem exists_distribution_klMax_le_chernoffDistance
    (M : ClassicalBinaryModel α) [DecidableEq α]
    (hfinite : M.chernoffDistance ≠ ⊤) :
    ∃ r : ClassicalDistribution α,
      r.SupportedBy M.p ∧
      r.SupportedBy M.q ∧
      M.distributionKLMax r ≤ M.chernoffDistance := by
  classical
  obtain ⟨sStar, hs, hmin⟩ := exists_isMinOn_chernoffPartition_Icc_real M
  let hZ : M.chernoffPartitionNNReal sStar ≠ 0 :=
    chernoffPartitionNNReal_ne_zero_of_chernoffDistance_ne_top
      (M := M) hfinite sStar
  refine ⟨M.commonSupportTiltedDistribution sStar hZ,
    commonSupportTiltedDistribution_supportedBy_p M sStar hZ,
    commonSupportTiltedDistribution_supportedBy_q M sStar hZ, ?_⟩
  exact
    (commonSupportTilted_distributionKLMax_le_neg_log_partition_at_min
      (M := M) hs hmin hZ).trans
      (neg_log_commonPartition_le_chernoffDistance (M := M) hs hZ)


end ClassicalBinaryModel

end BinaryHypothesisTest

end

end QIT
