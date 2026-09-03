/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.HSW
public import QIT.Information.Entropy.Entropy
public import QIT.Information.CQChannel
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.HypothesisTesting.ComparatorTest
public import QIT.Information.Entropy.MutualInformationDPI
public import QIT.States.MaximallyEntangled
public import QIT.States.MaximallyMixed
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Randomness-distribution relaxation for classical codes

The HSW converse reduces an `n`-use reliable classical-communication code to a
randomness-distribution task: a shared-randomness state
`Φ̄_{M M'} = (1/|M|) Σ_m |m m⟩⟨m m|` whose mutual information
`I(M ; M')_{Φ̄} = log |M|` equals the code's rate, plus an error criterion
inherited from the code's reliability.

This module provides:
- `maximallyCorrelated` — the classically correlated shared-randomness state
  `Φ̄_{MM'}` (proved). It is a diagonal classical mixture, not a coherent
  quantum maximally entangled state.
- `mutualInformation_maximallyCorrelated_statement` — `I(M;M')_{Φ̄} = log₂ |M|` (proved)
- `uniformProb` / `uniformEnsemble` / `cqChannelOutputState` — the cq state
  `τ_{MBⁿ} = (1/|M|) Σ_m |m⟩⟨m|_M ⊗ N^{⊗n}(C.encoder m)` induced by a uniform
  message distribution and an `HSWClassicalCode`
- `cqChannelOutputState_marginalB_eq_average` — the quantum marginal of `τ_{MBⁿ}`
  is the uniform average of the channel output states (proved)
- `uniformDecodedMessageState` — the classical joint state of a uniform
  transmitted message and Bob's decoded message (proved to be the local
  measurement of `cqChannelOutputState`)
- `hswCode_randomnessDistribution_statement` — the source-range Fano lower
  bound `(1-ε)·log₂|M| + xlog2 ε + xlog2 (1-ε) ≤ I(M;Bⁿ)_{τ}` for all codes
  with maximal error at most `ε`, explicitly assuming `0 ≤ ε ≤ 1`
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u uIn uOut

noncomputable section

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable (N : Channel a b)

/-- Sum over `x` of `if x = anchor then c else 0` is `c` (the single matching
term). -/
private theorem sum_if_eq_right {α : Type u} [Fintype α] [DecidableEq α]
    (anchor : α) (c : ℂ) :
    ∑ x : α, (if x = anchor then c else 0) = c := by
  simp only [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-- Sum over `x` of `if anchor = x then c else 0` is `c` (the single matching
term). -/
private theorem sum_if_eq_left {α : Type u} [Fintype α] [DecidableEq α]
    (anchor : α) (c : ℂ) :
    ∑ x : α, (if anchor = x then c else 0) = c := by
  simp only [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- The maximally-correlated (randomness-distribution) state on a message pair
`M × M'`: `Φ̄ = (1/|M|) Σ_m |m,m⟩⟨m,m|`, the diagonal density matrix that is
`|M|⁻¹` on each `|m,m⟩`-correlated diagonal entry and zero elsewhere. It has
`|M|` equal eigenvalues `1/|M|`, so `I(M;M')_{Φ̄} = log₂ |M|`. -/
noncomputable def maximallyCorrelated (M : Type u) [Fintype M] [DecidableEq M]
    [Nonempty M] : State (Prod M M) where
  matrix :=
    Matrix.diagonal fun (ij : Prod M M) =>
      if ij.1 = ij.2 then ((Fintype.card M : ℝ)⁻¹ : ℂ) else 0
  pos := by
    refine Matrix.PosSemidef.diagonal ?_
    intro (ij : Prod M M)
    dsimp only
    split_ifs <;> positivity
  trace_eq_one := by
    have hk : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
    rw [Matrix.trace_diagonal, Fintype.sum_prod_type]
    simp only [sum_if_eq_left, Finset.sum_const, nsmul_eq_mul]
    have key : ((Fintype.card M : ℝ)) * ((Fintype.card M : ℝ)⁻¹) = (1 : ℝ) :=
      mul_inv_cancel₀ (ne_of_gt hk)
    exact_mod_cast key

@[simp]
theorem maximallyCorrelated_matrix (M : Type u) [Fintype M] [DecidableEq M]
    [Nonempty M] :
    (maximallyCorrelated M).matrix =
      Matrix.diagonal fun (ij : Prod M M) =>
        if ij.1 = ij.2 then ((Fintype.card M : ℝ)⁻¹ : ℂ) else 0 := by
  rfl

/-- Each marginal of the maximally-correlated state is the maximally mixed
state: `Φ̄.marginalA.matrix = Φ̄.marginalB.matrix` is the diagonal matrix with
every diagonal entry `1/|M|` (equivalently `(1/|M|) · 1`). -/
theorem maximallyCorrelated_marginalA_matrix (M : Type u) [Fintype M]
    [DecidableEq M] [Nonempty M] :
    (maximallyCorrelated M).marginalA.matrix =
      Matrix.diagonal fun (_ : M) => ((Fintype.card M : ℝ)⁻¹ : ℂ) := by
  ext i i'
  set c : ℂ := ((Fintype.card M : ℝ)⁻¹ : ℂ)
  have hmarg : (maximallyCorrelated M).marginalA.matrix i i' =
      ∑ j : M, (maximallyCorrelated M).matrix (i, j) (i', j) := by
    show partialTraceB _ i i' = _
    rfl
  have hsum : ∑ j : M, (maximallyCorrelated M).matrix (i, j) (i', j) =
      (if i = i' then c else 0) := by
    rw [maximallyCorrelated_matrix]
    by_cases h : i = i'
    · subst h
      have hentry : ∀ j : M,
          (Matrix.diagonal fun (ij : Prod M M) => if ij.1 = ij.2 then c else 0) (i, j) (i, j) =
            (if i = j then c else 0) := fun j => by
        rw [Matrix.diagonal_apply, if_pos rfl]
      rw [Finset.sum_congr rfl (fun j _ => hentry j), sum_if_eq_left, if_pos rfl]
    · have h0 : ∀ j : M,
          (Matrix.diagonal fun (ij : Prod M M) => if ij.1 = ij.2 then c else 0) (i, j) (i', j)
            = 0 := by
        intro j
        rw [Matrix.diagonal_apply]
        by_cases heq : (i, j) = (i', j)
        · rw [if_pos heq]
          exact (h (congrArg Prod.fst heq)).elim
        · rw [if_neg heq]
      rw [Finset.sum_congr rfl (fun j _ => h0 j), Finset.sum_const_zero, if_neg h]
  rw [hmarg, hsum, Matrix.diagonal_apply]

theorem maximallyCorrelated_marginalB_matrix (M : Type u) [Fintype M]
    [DecidableEq M] [Nonempty M] :
    (maximallyCorrelated M).marginalB.matrix =
      Matrix.diagonal fun (_ : M) => ((Fintype.card M : ℝ)⁻¹ : ℂ) := by
  ext j j'
  set c : ℂ := ((Fintype.card M : ℝ)⁻¹ : ℂ)
  have hmarg : (maximallyCorrelated M).marginalB.matrix j j' =
      ∑ i : M, (maximallyCorrelated M).matrix (i, j) (i, j') := by
    show partialTraceA _ j j' = _
    rfl
  have hsum : ∑ i : M, (maximallyCorrelated M).matrix (i, j) (i, j') =
      (if j = j' then c else 0) := by
    rw [maximallyCorrelated_matrix]
    by_cases h : j = j'
    · subst h
      have hentry : ∀ i : M,
          (Matrix.diagonal fun (ij : Prod M M) => if ij.1 = ij.2 then c else 0) (i, j) (i, j) =
            (if i = j then c else 0) := fun i => by
        rw [Matrix.diagonal_apply, if_pos rfl]
      rw [Finset.sum_congr rfl (fun i _ => hentry i), sum_if_eq_right, if_pos rfl]
    · have h0 : ∀ i : M,
          (Matrix.diagonal fun (ij : Prod M M) => if ij.1 = ij.2 then c else 0) (i, j) (i, j')
            = 0 := by
        intro i
        rw [Matrix.diagonal_apply]
        by_cases heq : (i, j) = (i, j')
        · rw [if_pos heq]
          exact (h (congrArg Prod.snd heq)).elim
        · rw [if_neg heq]
      rw [Finset.sum_congr rfl (fun i _ => h0 i), Finset.sum_const_zero, if_neg h]
  rw [hmarg, hsum, Matrix.diagonal_apply]

/-- The first marginal of the classically correlated shared-randomness state is
the canonical maximally mixed state. -/
theorem maximallyCorrelated_marginalA (M : Type u) [Fintype M]
    [DecidableEq M] [Nonempty M] :
    (maximallyCorrelated M).marginalA = State.maximallyMixed M := by
  apply State.ext
  rw [maximallyCorrelated_marginalA_matrix, State.maximallyMixed_matrix]
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- The second marginal of the classically correlated shared-randomness state is
the canonical maximally mixed state. -/
theorem maximallyCorrelated_marginalB (M : Type u) [Fintype M]
    [DecidableEq M] [Nonempty M] :
    (maximallyCorrelated M).marginalB = State.maximallyMixed M := by
  apply State.ext
  rw [maximallyCorrelated_marginalB_matrix, State.maximallyMixed_matrix]
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- On `Bool`, the classically correlated shared-randomness state is not the
canonical coherent maximally entangled two-qubit state. -/
theorem maximallyCorrelated_bool_ne_maximallyEntangled :
    maximallyCorrelated Bool ≠ State.maximallyEntangled (Equiv.refl Bool) := by
  intro h
  have hentry := congrArg (fun ρ => ρ.matrix (false, false) (true, true)) h
  simp [maximallyCorrelated, State.maximallyEntangled, PureVector.maximallyEntangled,
    PureVector.state, rankOneMatrix_apply] at hentry

/-- `xlog2 x * Real.log 2 = x * Real.log x` for `0 ≤ x` (the `0 log 0` convention
absorbs the zero case). Scaling by `Real.log 2 ≠ 0` eliminates the base-2
division in `log2`. -/
private lemma xlog2_mul_log2_self {x : ℝ} (hx : 0 ≤ x) :
    xlog2 x * Real.log 2 = x * Real.log x := by
  by_cases hzx : x = 0
  · simp [xlog2, hzx, Real.log_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    simp only [xlog2, if_neg hzx, log2]
    field_simp

/-- Product rule for `xlog2` on nonnegative real inputs. -/
private lemma xlog2_mul_of_nonneg {x y : ℝ} (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    xlog2 (x * y) = y * xlog2 x + x * xlog2 y := by
  by_cases hx0 : x = 0
  · simp [hx0, xlog2]
  by_cases hy0 : y = 0
  · simp [hy0, xlog2]
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  simp only [xlog2, if_neg hx0, if_neg hy0, if_neg hxy0, log2]
  rw [Real.log_mul hx0 hy0]
  ring

/-- Binary entropy in bits, written with the repository's `xlog2` convention. -/
def binaryEntropyBits (p : ℝ) : ℝ :=
  -xlog2 p - xlog2 (1 - p)

/-- The local bits convention agrees with mathlib's natural-log binary entropy
after division by `log 2` on the probability interval. -/
theorem binaryEntropyBits_eq_binEntropy_div_log_two {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryEntropyBits p = Real.binEntropy p / Real.log 2 := by
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hmul :
      binaryEntropyBits p * Real.log 2 = Real.binEntropy p := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    calc
      binaryEntropyBits p * Real.log 2 =
          -(xlog2 p * Real.log 2) - xlog2 (1 - p) * Real.log 2 := by
            unfold binaryEntropyBits
            ring
      _ = -(p * Real.log p) - (1 - p) * Real.log (1 - p) := by
            rw [xlog2_mul_log2_self hp0, xlog2_mul_log2_self (sub_nonneg.mpr hp1)]
      _ = p.negMulLog + (1 - p).negMulLog := by
            simp [Real.negMulLog]
            ring
  calc
    binaryEntropyBits p = binaryEntropyBits p * Real.log 2 / Real.log 2 := by
      field_simp [hlog2_ne]
    _ = Real.binEntropy p / Real.log 2 := by rw [hmul]

/-- Jensen's inequality for binary entropy in bits over a finite probability
mass. -/
theorem binaryEntropyBits_weighted_sum_le
    {ι : Type u} [Fintype ι] {w t : ι → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i : ι, w i = 1)
    (ht_nonneg : ∀ i, 0 ≤ t i)
    (ht_le_one : ∀ i, t i ≤ 1) :
    ∑ i : ι, w i * binaryEntropyBits (t i) ≤
      binaryEntropyBits (∑ i : ι, w i * t i) := by
  classical
  have hlog_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), t i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i _
    exact ⟨ht_nonneg i, ht_le_one i⟩
  have hjensen :
      ∑ i : ι, w i * Real.binEntropy (t i) ≤
        Real.binEntropy (∑ i : ι, w i * t i) := by
    have hj :=
      Real.strictConcave_binEntropy.concaveOn.le_map_sum
        (t := (Finset.univ : Finset ι)) (w := w) (p := t)
        (by intro i _; exact hw_nonneg i) (by simpa using hw_sum) hmem
    simpa [smul_eq_mul] using hj
  have havg_nonneg : 0 ≤ ∑ i : ι, w i * t i := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw_nonneg i) (ht_nonneg i)
  have havg_le_one : (∑ i : ι, w i * t i) ≤ 1 := by
    calc
      (∑ i : ι, w i * t i) ≤ ∑ i : ι, w i * 1 := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact mul_le_mul_of_nonneg_left (ht_le_one i) (hw_nonneg i)
      _ = 1 := by
        simp [hw_sum]
  have hleft :
      ∑ i : ι, w i * binaryEntropyBits (t i) =
        (∑ i : ι, w i * Real.binEntropy (t i)) / Real.log 2 := by
    calc
      ∑ i : ι, w i * binaryEntropyBits (t i) =
          ∑ i : ι, w i * (Real.binEntropy (t i) / Real.log 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [binaryEntropyBits_eq_binEntropy_div_log_two (ht_nonneg i) (ht_le_one i)]
      _ = ∑ i : ι, (w i * Real.binEntropy (t i)) / Real.log 2 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
      _ = (∑ i : ι, w i * Real.binEntropy (t i)) / Real.log 2 := by
            rw [Finset.sum_div]
  have hright :
      binaryEntropyBits (∑ i : ι, w i * t i) =
        Real.binEntropy (∑ i : ι, w i * t i) / Real.log 2 :=
    binaryEntropyBits_eq_binEntropy_div_log_two havg_nonneg havg_le_one
  rw [hleft, hright]
  exact div_le_div_of_nonneg_right hjensen hlog_pos.le

/-- The natural-log Fano scalar expression
`p log |M| + h(p)`, where `h` is binary entropy in natural units. -/
noncomputable def fanoEntropyNats (M : Type u) [Fintype M] (p : ℝ) : ℝ :=
  p * Real.log (Fintype.card M : ℝ) + Real.binEntropy p

/-- The Fano scalar expression in bits is its natural-log version divided by
`log 2`. -/
theorem fanoEntropyRhs_eq_nats_div_log_two
    (M : Type u) [Fintype M] [Nonempty M] {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε * log2 (Fintype.card M : ℝ) - xlog2 ε - xlog2 (1 - ε) =
      fanoEntropyNats M ε / Real.log 2 := by
  have hbin := binaryEntropyBits_eq_binEntropy_div_log_two hε0 hε1
  calc
    ε * log2 (Fintype.card M : ℝ) - xlog2 ε - xlog2 (1 - ε) =
        ε * log2 (Fintype.card M : ℝ) + binaryEntropyBits ε := by
          unfold binaryEntropyBits
          ring
    _ = ε * (Real.log (Fintype.card M : ℝ) / Real.log 2) +
        Real.binEntropy ε / Real.log 2 := by
          rw [hbin]
          rfl
    _ = (ε * Real.log (Fintype.card M : ℝ) + Real.binEntropy ε) / Real.log 2 := by
          ring
    _ = fanoEntropyNats M ε / Real.log 2 := by
          rfl

/-- Derivative of the natural-log Fano scalar on the open interval `(0,1)`. -/
theorem fanoEntropyNats_deriv
    (M : Type u) [Fintype M] {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    deriv (fanoEntropyNats M) p =
      Real.log (Fintype.card M : ℝ) + (Real.log (1 - p) - Real.log p) := by
  unfold fanoEntropyNats
  rw [deriv_fun_add]
  · rw [deriv_mul_const]
    · have hid : deriv (fun p : ℝ => p) p = 1 := by simp
      rw [hid, one_mul, Real.deriv_binEntropy]
    · exact differentiableAt_id
  · exact differentiableAt_id.mul_const _
  · exact Real.differentiableAt_binEntropy hp0 hp1

/-- The natural-log Fano scalar is continuous on the probability interval. -/
theorem fanoEntropyNats_continuousOn
    (M : Type u) [Fintype M] :
    ContinuousOn (fanoEntropyNats M) (Set.Icc (0 : ℝ) 1) := by
  unfold fanoEntropyNats
  exact ((continuous_id.mul continuous_const).add Real.binEntropy_continuous).continuousOn

/-- The natural-log Fano scalar is strictly increasing up to the usual Fano
threshold `1 - 1/(|M|+1)`. -/
theorem fanoEntropyNats_strictMonoOn_threshold
    (M : Type u) [Fintype M] [Nonempty M] :
    StrictMonoOn (fanoEntropyNats M)
      (Set.Icc (0 : ℝ) (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ))) := by
  have hcard_nat : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
  have hcard_pos : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast hcard_nat
  have hq_pos : (0 : ℝ) < ((Fintype.card M + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card M + 1)
  apply strictMonoOn_of_deriv_pos
    (convex_Icc (0 : ℝ) (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)))
    ?_ ?_
  · exact (fanoEntropyNats_continuousOn M).mono (by
      intro x hx
      exact ⟨hx.1, by
        have hthreshold_le_one :
            1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) ≤ 1 := by
          have hq_inv_nonneg : 0 ≤ 1 / ((Fintype.card M + 1 : ℕ) : ℝ) :=
            div_nonneg zero_le_one hq_pos.le
          linarith
        exact hx.2.trans hthreshold_le_one⟩)
  · intro p hp
    simp only [interior_Icc] at hp
    have hp0 : 0 < p := hp.1
    have hp_threshold : p < 1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) := by
      simpa [one_div] using hp.2
    have hp1 : p < 1 := by
      have hthreshold_le_one :
          1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) ≤ 1 := by
        have hq_inv_nonneg : 0 ≤ 1 / ((Fintype.card M + 1 : ℕ) : ℝ) :=
          div_nonneg zero_le_one hq_pos.le
        linarith
      exact hp_threshold.trans_le hthreshold_le_one
    rw [fanoEntropyNats_deriv M (ne_of_gt hp0) (ne_of_lt hp1)]
    have hprod_pos : 0 < (Fintype.card M : ℝ) * (1 - p) :=
      mul_pos hcard_pos (by linarith)
    have hp_lt_prod : p < (Fintype.card M : ℝ) * (1 - p) := by
      have hpq : p * ((Fintype.card M + 1 : ℕ) : ℝ) < (Fintype.card M : ℝ) := by
        have h := mul_lt_mul_of_pos_right hp_threshold hq_pos
        have hcalc :
            (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)) *
                ((Fintype.card M + 1 : ℕ) : ℝ) =
              (Fintype.card M : ℝ) := by
          field_simp [ne_of_gt hq_pos]
          norm_num
        rw [hcalc] at h
        exact h
      have hq_cast :
          ((Fintype.card M + 1 : ℕ) : ℝ) = (Fintype.card M : ℝ) + 1 := by
        norm_num
      nlinarith
    calc
      0 < Real.log ((Fintype.card M : ℝ) * (1 - p)) - Real.log p := by
        rw [sub_pos]
        exact Real.strictMonoOn_log (Set.mem_Ioi.mpr hp0) (Set.mem_Ioi.mpr hprod_pos)
          hp_lt_prod
      _ = Real.log (Fintype.card M : ℝ) + (Real.log (1 - p) - Real.log p) := by
        rw [Real.log_mul hcard_pos.ne' (by linarith : 1 - p ≠ 0)]
        ring

/-- The natural-log Fano scalar is strictly decreasing after the Fano
threshold. -/
theorem fanoEntropyNats_strictAntiOn_threshold
    (M : Type u) [Fintype M] [Nonempty M] :
    StrictAntiOn (fanoEntropyNats M)
      (Set.Icc (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)) 1) := by
  have hcard_nat : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
  have hcard_pos : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast hcard_nat
  have hq_pos : (0 : ℝ) < ((Fintype.card M + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card M + 1)
  apply strictAntiOn_of_deriv_neg
    (convex_Icc (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)) 1) ?_ ?_
  · exact (fanoEntropyNats_continuousOn M).mono (by
      intro x hx
      exact ⟨by
        have hthreshold_nonneg :
            0 ≤ 1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) := by
          have hq_nat : 1 ≤ Fintype.card M + 1 := by omega
          have hq_real : (1 : ℝ) ≤ ((Fintype.card M + 1 : ℕ) : ℝ) := by
            exact_mod_cast hq_nat
          have hinv_le_one : 1 / ((Fintype.card M + 1 : ℕ) : ℝ) ≤ 1 := by
            rw [one_div]
            exact inv_le_one_of_one_le₀ hq_real
          linarith
        exact hthreshold_nonneg.trans hx.1, hx.2⟩)
  · intro p hp
    simp only [interior_Icc] at hp
    have hthreshold_lt_p : 1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) < p := by
      simpa [one_div] using hp.1
    have hp1 : p < 1 := hp.2
    have hp0 : 0 < p := by
      have hthreshold_nonneg :
          0 ≤ 1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) := by
        have hq_nat : 1 ≤ Fintype.card M + 1 := by omega
        have hq_real : (1 : ℝ) ≤ ((Fintype.card M + 1 : ℕ) : ℝ) := by
          exact_mod_cast hq_nat
        have hinv_le_one : 1 / ((Fintype.card M + 1 : ℕ) : ℝ) ≤ 1 := by
          rw [one_div]
          exact inv_le_one_of_one_le₀ hq_real
        linarith
      exact hthreshold_nonneg.trans_lt hthreshold_lt_p
    rw [fanoEntropyNats_deriv M (ne_of_gt hp0) (ne_of_lt hp1)]
    have hprod_pos : 0 < (Fintype.card M : ℝ) * (1 - p) :=
      mul_pos hcard_pos (by linarith)
    have hprod_lt_p : (Fintype.card M : ℝ) * (1 - p) < p := by
      have hdp : (Fintype.card M : ℝ) < p * ((Fintype.card M + 1 : ℕ) : ℝ) := by
        have h := mul_lt_mul_of_pos_right hthreshold_lt_p hq_pos
        have hcalc :
            (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)) *
                ((Fintype.card M + 1 : ℕ) : ℝ) =
              (Fintype.card M : ℝ) := by
          field_simp [ne_of_gt hq_pos]
          norm_num
        rw [hcalc] at h
        exact h
      have hq_cast :
          ((Fintype.card M + 1 : ℕ) : ℝ) = (Fintype.card M : ℝ) + 1 := by
        norm_num
      nlinarith
    calc
      Real.log (Fintype.card M : ℝ) + (Real.log (1 - p) - Real.log p) =
          Real.log ((Fintype.card M : ℝ) * (1 - p)) - Real.log p := by
        rw [Real.log_mul hcard_pos.ne' (by linarith : 1 - p ≠ 0)]
        ring
      _ < 0 := by
        rw [sub_neg]
        exact Real.strictMonoOn_log (Set.mem_Ioi.mpr hprod_pos) (Set.mem_Ioi.mpr hp0)
          hprod_lt_p

/-- On the increasing side of the Fano entropy curve, the Fano scalar
expression is monotone in the error parameter. -/
theorem fanoEntropyRhs_mono_of_le_threshold
    (M : Type u) [Fintype M] [Nonempty M] {e ε : ℝ}
    (he0 : 0 ≤ e) (heε : e ≤ ε) (hε0 : 0 ≤ ε)
    (hε_threshold : ε ≤ 1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)) :
    e * log2 (Fintype.card M : ℝ) - xlog2 e - xlog2 (1 - e) ≤
      ε * log2 (Fintype.card M : ℝ) - xlog2 ε - xlog2 (1 - ε) := by
  have hcard_nat : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
  have hq : 2 ≤ Fintype.card M + 1 := by omega
  have hthreshold_le_one :
      1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) ≤ 1 := by
    have hq_pos : (0 : ℝ) < ((Fintype.card M + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < Fintype.card M + 1)
    have hq_inv_nonneg : 0 ≤ 1 / ((Fintype.card M + 1 : ℕ) : ℝ) :=
      div_nonneg zero_le_one hq_pos.le
    linarith
  have he1 : e ≤ 1 := heε.trans (hε_threshold.trans hthreshold_le_one)
  have hε1 : ε ≤ 1 := hε_threshold.trans hthreshold_le_one
  rw [fanoEntropyRhs_eq_nats_div_log_two M he0 he1,
    fanoEntropyRhs_eq_nats_div_log_two M hε0 hε1]
  have hmono := (fanoEntropyNats_strictMonoOn_threshold M).monotoneOn
  have he_mem :
      e ∈ Set.Icc (0 : ℝ) (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)) :=
    ⟨he0, heε.trans hε_threshold⟩
  have hε_mem :
      ε ∈ Set.Icc (0 : ℝ) (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)) :=
    ⟨hε0, hε_threshold⟩
  exact div_le_div_of_nonneg_right (hmono he_mem hε_mem heε)
    (le_of_lt (Real.log_pos one_lt_two))

/-- On the decreasing side of the Fano entropy curve, the Fano scalar
expression stays above its endpoint value `log₂ |M|`. -/
theorem log_card_le_fanoEntropyRhs_of_threshold_le
    (M : Type u) [Fintype M] [Nonempty M] {ε : ℝ}
    (hε_threshold : 1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) ≤ ε) (hε1 : ε ≤ 1) :
    log2 (Fintype.card M : ℝ) ≤
      ε * log2 (Fintype.card M : ℝ) - xlog2 ε - xlog2 (1 - ε) := by
  have hcard_nat : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
  have hq : 2 ≤ Fintype.card M + 1 := by omega
  have hthreshold_nonneg :
      0 ≤ 1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) := by
    have hq_nat : 1 ≤ Fintype.card M + 1 := by omega
    have hq_real : (1 : ℝ) ≤ ((Fintype.card M + 1 : ℕ) : ℝ) := by exact_mod_cast hq_nat
    have hq_pos : (0 : ℝ) < ((Fintype.card M + 1 : ℕ) : ℝ) := by positivity
    have hinv_le_one : 1 / ((Fintype.card M + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [one_div]
      exact inv_le_one_of_one_le₀ hq_real
    linarith
  have hε0 : 0 ≤ ε := hthreshold_nonneg.trans hε_threshold
  rw [fanoEntropyRhs_eq_nats_div_log_two M hε0 hε1]
  have hanti := (fanoEntropyNats_strictAntiOn_threshold M).antitoneOn
  have hε_mem :
      ε ∈ Set.Icc (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)) 1 :=
    ⟨hε_threshold, hε1⟩
  have hone_mem :
      (1 : ℝ) ∈ Set.Icc (1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)) 1 :=
    ⟨by linarith, le_rfl⟩
  have hnats_endpoint :
      fanoEntropyNats M 1 ≤ fanoEntropyNats M ε :=
    hanti hε_mem hone_mem hε1
  have hendpoint :
      fanoEntropyNats M 1 / Real.log 2 =
        log2 (Fintype.card M : ℝ) := by
    unfold fanoEntropyNats log2
    simp
  rw [← hendpoint]
  exact div_le_div_of_nonneg_right hnats_endpoint (le_of_lt (Real.log_pos one_lt_two))

/-- Scaling identity for binary entropy in bits:
`r h₂(e/r) = -xlog₂ e - xlog₂(r-e) + xlog₂ r`.  This is the
algebraic heart of the fiberwise Fano proof. -/
theorem mul_binaryEntropyBits_div_eq
    {e r : ℝ} (he : 0 ≤ e) (her : e ≤ r) (hr : 0 < r) :
    r * binaryEntropyBits (e / r) =
      -xlog2 e - xlog2 (r - e) + xlog2 r := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hfrac_nonneg : 0 ≤ e / r := div_nonneg he hr.le
  have hfrac_le_one : e / r ≤ 1 := (div_le_one hr).mpr her
  have hcompl_nonneg : 0 ≤ 1 - e / r := sub_nonneg.mpr hfrac_le_one
  have he_eq : e = r * (e / r) := by
    field_simp [hrne]
  have hsucc_eq : r - e = r * (1 - e / r) := by
    field_simp [hrne]
  have hx_e : xlog2 e = (e / r) * xlog2 r + r * xlog2 (e / r) := by
    calc
      xlog2 e = xlog2 (r * (e / r)) := congrArg xlog2 he_eq
      _ = (e / r) * xlog2 r + r * xlog2 (e / r) :=
            xlog2_mul_of_nonneg hr.le hfrac_nonneg
  have hx_succ :
      xlog2 (r - e) = (1 - e / r) * xlog2 r + r * xlog2 (1 - e / r) := by
    calc
      xlog2 (r - e) = xlog2 (r * (1 - e / r)) := congrArg xlog2 hsucc_eq
      _ = (1 - e / r) * xlog2 r + r * xlog2 (1 - e / r) :=
            xlog2_mul_of_nonneg hr.le hcompl_nonneg
  unfold binaryEntropyBits
  rw [hx_e, hx_succ]
  ring

/-- `|M| · xlog2(|M|⁻¹) = -log₂|M|`, the entropy of the uniform distribution
on `M`. Proved by scaling both sides by `Real.log 2 ≠ 0`, which turns the
`log2` divisions into `Real.log` atoms clean for `field_simp`. -/
private lemma card_mul_xlog2_inv (M : Type u) [Fintype M] [Nonempty M] :
    ((Fintype.card M : ℝ)) * xlog2 ((Fintype.card M : ℝ)⁻¹) = -log2 (Fintype.card M) := by
  have hk : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  have hkne : (Fintype.card M : ℝ) ≠ 0 := ne_of_gt hk
  have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  suffices h : ((Fintype.card M : ℝ)) * xlog2 ((Fintype.card M : ℝ)⁻¹) * Real.log 2 =
      (-log2 (Fintype.card M)) * Real.log 2 by
    exact mul_right_cancel₀ hlog2ne h
  rw [mul_assoc, xlog2_mul_log2_self (inv_nonneg.mpr hk.le)]
  rw [← mul_assoc, mul_inv_cancel₀ hkne, one_mul, Real.log_inv]
  show -Real.log ((Fintype.card M : ℝ)) = (-log2 (Fintype.card M)) * Real.log 2
  unfold log2
  field_simp

/-- Sum of `xlog2 (|M|⁻¹)` over `M` equals `-log₂ |M|`. -/
private lemma sum_xlog2_inv_card (M : Type u) [Fintype M] [Nonempty M] :
    ∑ _m : M, xlog2 ((Fintype.card M : ℝ)⁻¹) = -log2 (Fintype.card M) := by
  have hsum : ∑ m : M, xlog2 ((Fintype.card M : ℝ)⁻¹) =
      ((Fintype.card M : ℝ)) * xlog2 ((Fintype.card M : ℝ)⁻¹) := by
    rw [Finset.sum_const, nsmul_eq_mul]; rfl
  rw [hsum, card_mul_xlog2_inv M]

/-- `xlog2 (if c then a else 0) = if c then xlog2 a else 0` (the zero case uses
`0 log 0 := 0`). -/
private lemma xlog2_ite {c : Prop} [Decidable c] {a : ℝ} :
    xlog2 (if c then a else 0) = if c then xlog2 a else 0 := by
  by_cases hc : c
  · simp [hc]
  · simp [hc, xlog2]

/-- Sum of `xlog2` of the maximally-correlated diagonal over `M × M`. -/
private lemma sum_xlog2_diag_prod (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] :
    ∑ (ij : Prod M M), xlog2 (if ij.1 = ij.2 then ((Fintype.card M : ℝ)⁻¹) else 0) =
      -log2 (Fintype.card M) := by
  rw [show ∑ (ij : Prod M M), xlog2 (if ij.1 = ij.2 then _ else 0) =
        ∑ (ij : Prod M M), (if ij.1 = ij.2 then xlog2 ((Fintype.card M : ℝ)⁻¹) else 0) from by
        simp only [xlog2_ite]]
  rw [Fintype.sum_prod_type]
  show ∑ i : M, ∑ j : M, (if i = j then xlog2 ((Fintype.card M : ℝ)⁻¹) else 0) =
      -log2 (Fintype.card M)
  have hinner : ∀ i : M,
      ∑ j : M, (if i = j then xlog2 ((Fintype.card M : ℝ)⁻¹) else 0) =
        xlog2 ((Fintype.card M : ℝ)⁻¹) := by
    intro i
    simp only [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  simp only [hinner, sum_xlog2_inv_card]

/-- Mutual information of the maximally-correlated state `Φ̄` equals the rate:
`I(M ; M')_{Φ̄} = log₂ |M|`. This is the randomness-distribution reduction's
shared-randomness identity — the maximally-correlated state carries
`log₂ |M|` bits of (perfectly correlated) mutual information. -/
theorem mutualInformation_maximallyCorrelated_statement
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] :
    mutualInformation (maximallyCorrelated M) = log2 (Fintype.card M) := by
  have hA : State.vonNeumann (maximallyCorrelated M).marginalA =
      log2 (Fintype.card M) := by
    rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal (maximallyCorrelated M).marginalA
        (fun (_ : M) => (Fintype.card M : ℝ)⁻¹)
        (by push_cast; exact maximallyCorrelated_marginalA_matrix M), sum_xlog2_inv_card]
    ring
  have hB : State.vonNeumann (maximallyCorrelated M).marginalB =
      log2 (Fintype.card M) := by
    rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal (maximallyCorrelated M).marginalB
        (fun (_ : M) => (Fintype.card M : ℝ)⁻¹)
        (by push_cast; exact maximallyCorrelated_marginalB_matrix M), sum_xlog2_inv_card]
    ring
  have hΦ : State.vonNeumann (maximallyCorrelated M) = log2 (Fintype.card M) := by
    rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal (maximallyCorrelated M)
        (fun (ij : Prod M M) => if ij.1 = ij.2 then (Fintype.card M : ℝ)⁻¹ else 0)
        (by ext (a b : Prod M M)
            by_cases hab : a = b
            · subst hab
              simp only [maximallyCorrelated_matrix, Matrix.diagonal_apply, if_true]
              by_cases hdiag : a.1 = a.2 <;> simp [hdiag]
            · simp only [hab, maximallyCorrelated_matrix, Matrix.diagonal_apply, if_false]),
        sum_xlog2_diag_prod]
    ring
  show State.vonNeumann (maximallyCorrelated M).marginalA +
      State.vonNeumann (maximallyCorrelated M).marginalB -
      State.vonNeumann (maximallyCorrelated M) = log2 (Fintype.card M)
  rw [hA, hB, hΦ]
  ring

/-- Uniform probability distribution on `M`: `uniformProbs M m = 1/|M|`. -/
def uniformProbs (M : Type u) [Fintype M] [Nonempty M] (_m : M) : ℝ≥0 :=
  (Fintype.card M : ℝ≥0)⁻¹

/-- The uniform probabilities over `M` sum to one. -/
theorem uniformProbs_sum_eq_one (M : Type u) [Fintype M] [Nonempty M] :
    (∑ m : M, uniformProbs M m) = 1 := by
  have hcard_ne_zero : (Fintype.card M : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := M)).ne'
  apply NNReal.eq
  simp [uniformProbs, Finset.sum_const, nsmul_eq_mul]

/-- Uniform ensemble over `M` with states `ρ m`. Each message is equally likely. -/
noncomputable def uniformEnsemble
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    {a : Type uIn} [Fintype a] [DecidableEq a]
    (ρ : M → State a) : Ensemble M a :=
  Ensemble.mk (uniformProbs M) (uniformProbs_sum_eq_one M) ρ

/-- The cq channel output state `τ_{MBⁿ}` induced by a uniform message
distribution and the `n`-use channel encoding:

`τ_{MBⁿ} = (1/|M|) Σ_m |m⟩⟨m|_M ⊗ N^{⊗n}(C.encoder m)`.

This is the shared-randomness state that feeds the randomness-distribution
converse: the encoder is sampled uniformly, so the classical register `M` is
maximally mixed, and the quantum register `Bⁿ` carries the channel output
conditioned on the message. -/
noncomputable def cqChannelOutputState
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) : State (Prod M (TensorPower b n)) :=
  (uniformEnsemble M C.outputState).cqState

/-- The quantum marginal of `cqChannelOutputState` is the uniform average of the
channel output states: `τ_{Bⁿ} = (1/|M|) Σ_m N^{⊗n}(C.encoder m)`. -/
theorem cqChannelOutputState_marginalB_eq_average
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    (cqChannelOutputState N n M C).marginalB =
      (uniformEnsemble M C.outputState).averageState := by
  simp [cqChannelOutputState, Ensemble.cqState_marginalB_eq_averageState]

/-! ## Decoded classical message pair -/

/-- Joint probability distribution of the transmitted message and Bob's decoded
message when the transmitted message is uniform and the decoder POVM is applied
to the channel output. -/
def uniformDecodedMessageProb
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    Prod M M → ℝ≥0 :=
  fun p => uniformMessageProb (M := M) p.1 * C.decoder.prob (C.outputState p.1) p.2

/-- The transmitted/decoded-message joint probabilities sum to one. -/
theorem uniformDecodedMessageProb_sum
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    ∑ p : Prod M M, uniformDecodedMessageProb N n M C p = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ m : M, ∑ mhat : M,
        uniformMessageProb (M := M) m * C.decoder.prob (C.outputState m) mhat) =
        ∑ m : M, uniformMessageProb (M := M) m *
          (∑ mhat : M, C.decoder.prob (C.outputState m) mhat) := by
          refine Finset.sum_congr rfl ?_
          intro m _
          rw [Finset.mul_sum]
    _ = ∑ m : M, uniformMessageProb (M := M) m := by
          refine Finset.sum_congr rfl ?_
          intro m _
          rw [C.decoder.sum_prob, mul_one]
    _ = 1 := uniformMessageProb_sum (M := M)

/-- Joint classical state of the transmitted message and Bob's decoded message. -/
def uniformDecodedMessageState
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) : State (Prod M M) :=
  Classical.diagonalState (uniformDecodedMessageProb N n M C)
    (uniformDecodedMessageProb_sum N n M C)

/-- The decoded classical message-pair state is obtained by measuring the
quantum output register of the cq channel output state with Bob's decoder. -/
theorem uniformDecodedMessageState_eq_measure_cqChannelOutputState
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    uniformDecodedMessageState N n M C =
      ((Channel.idChannel M).prod (Channel.measure C.decoder)).applyState
        (cqChannelOutputState N n M C) := by
  apply State.ext
  ext p q
  rcases p with ⟨m, mhat⟩
  rcases q with ⟨m', mhat'⟩
  change (uniformDecodedMessageState N n M C).matrix (m, mhat) (m', mhat') =
    (((Channel.idChannel M).prod (Channel.measure C.decoder)).applyState
      (uniformEnsemble M C.outputState).cqState).matrix (m, mhat) (m', mhat')
  rw [applyState_id_prod_cqState_matrix (uniformEnsemble M C.outputState)
    (Channel.measure C.decoder)]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  by_cases hm : m = m'
  · subst m'
    by_cases hhat : mhat = mhat'
    · subst mhat'
      have hmeas :
          ((Channel.measure C.decoder).applyState (C.outputState m)).matrix mhat mhat =
            (C.decoder.prob (C.outputState m) mhat : ℂ) := by
        rw [← Classical.measuredState_eq_measure_applyState]
        simp
      rw [Finset.sum_eq_single m]
      · simp [uniformDecodedMessageState, Classical.diagonalState,
          uniformDecodedMessageProb, uniformEnsemble, uniformProbs, uniformMessageProb,
          Matrix.kronecker, hmeas]
      · intro x _ hx
        simp [Matrix.kronecker, hx]
      · simp
    · have hmeas :
          ((Channel.measure C.decoder).applyState (C.outputState m)).matrix mhat mhat' = 0 := by
        rw [← Classical.measuredState_eq_measure_applyState]
        exact Classical.measuredState_apply_ne C.decoder (C.outputState m) hhat
      rw [Finset.sum_eq_single m]
      · simp [uniformDecodedMessageState, Classical.diagonalState,
          uniformDecodedMessageProb, uniformEnsemble, uniformProbs, uniformMessageProb,
          Matrix.kronecker, hhat, hmeas]
      · intro x _ hx
        simp [Matrix.kronecker, hx]
      · simp
  · rw [Finset.sum_eq_zero]
    · simp [uniformDecodedMessageState, Classical.diagonalState,
        uniformDecodedMessageProb, hm]
    · intro x _
      by_cases hx : x = m
      · subst x
        simp [Matrix.kronecker, hm]
      · simp [Matrix.kronecker, hx]

/-- Decoding is a right-local channel, so it cannot increase mutual
information. -/
theorem mutualInformation_uniformDecodedMessageState_le_cqChannelOutputState
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    mutualInformation (uniformDecodedMessageState N n M C) ≤
      mutualInformation (cqChannelOutputState N n M C) := by
  rw [uniformDecodedMessageState_eq_measure_cqChannelOutputState N n M C]
  simpa using
    mutualInformation_dataProcessing_local_channels_ge
      (cqChannelOutputState N n M C)
      (Channel.idChannel M)
      (Channel.measure C.decoder)

/-- The transmitted-message marginal of the decoded classical pair is uniform. -/
theorem uniformDecodedMessageState_marginalA
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    (uniformDecodedMessageState N n M C).marginalA = uniformMessageState (M := M) := by
  apply State.ext
  ext m m'
  by_cases h : m = m'
  · subst m'
    simp only [State.marginalA_matrix, partialTraceB, uniformDecodedMessageState,
      Classical.diagonalState_matrix, uniformDecodedMessageProb, uniformMessageState_matrix,
      Matrix.diagonal_apply_eq]
    have hsum :
        ∑ x : M, uniformMessageProb (M := M) m *
            C.decoder.prob (C.outputState m) x =
          uniformMessageProb (M := M) m := by
      rw [← Finset.mul_sum, C.decoder.sum_prob, mul_one]
    exact_mod_cast hsum
  · simp [State.marginalA, partialTraceB, uniformDecodedMessageState,
      Classical.diagonalState, uniformDecodedMessageProb, uniformMessageState, h]

/-- The equality-comparator accept probability is the uniform average decoding
success probability. -/
theorem uniformDecodedMessageState_comparator_accept
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    effectAcceptProbability (uniformDecodedMessageState N n M C) (comparatorEffect (M := M)) =
      ∑ m : M, (uniformMessageProb (M := M) m : ℝ) * C.successProbability m := by
  unfold effectAcceptProbability HSWClassicalCode.successProbability
  calc
    (∑ p : Prod M M,
        (∑ q : Prod M M,
          (uniformDecodedMessageState N n M C).matrix p q * comparatorEffect (M := M) q p)).re =
        (∑ p : Prod M M,
          (uniformDecodedMessageState N n M C).matrix p p *
            comparatorEffect (M := M) p p).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.sum_eq_single_of_mem p (Finset.mem_univ p) (by
            intro q _ hq
            have hzero : comparatorEffect (M := M) q p = 0 := by
              unfold comparatorEffect
              exact Matrix.diagonal_apply_ne _ hq
            rw [hzero, mul_zero])
    _ = (∑ p : Prod M M,
          (if p.1 = p.2 then
            (uniformMessageProb (M := M) p.1 : ℂ) *
              (C.decoder.prob (C.outputState p.1) p.2 : ℂ)
          else 0)).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro p _
          by_cases h : p.1 = p.2
          · simp [uniformDecodedMessageState, Classical.diagonalState,
              uniformDecodedMessageProb, comparatorEffect, h]
          · simp [uniformDecodedMessageState, Classical.diagonalState,
              uniformDecodedMessageProb, comparatorEffect, h]
    _ = (∑ m : M,
          (uniformMessageProb (M := M) m : ℂ) *
            (C.decoder.prob (C.outputState m) m : ℂ)).re := by
          congr 1
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro m _
          simp
    _ = ∑ m : M, (uniformMessageProb (M := M) m : ℝ) *
          (C.decoder.prob (C.outputState m) m : ℝ) := by
          simp
    _ = ∑ m : M, (uniformMessageProb (M := M) m : ℝ) *
          C.successProbability m := by
          simp [HSWClassicalCode.successProbability]

/-- Maximal-error reliability implies that the comparator accepts the
transmitted/decoded-message pair with probability at least `1 - ε`. -/
theorem comparator_accept_ge_of_maxErrorAtMost
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) {ε : ℝ}
    (hC : C.maxErrorAtMost ε) :
    1 - ε ≤
      effectAcceptProbability (uniformDecodedMessageState N n M C) (comparatorEffect (M := M)) := by
  rw [uniformDecodedMessageState_comparator_accept]
  have hsumReal :
      ∑ m : M, (uniformMessageProb (M := M) m : ℝ) = 1 := by
    exact_mod_cast (uniformMessageProb_sum (M := M))
  calc
    1 - ε = (∑ m : M, (uniformMessageProb (M := M) m : ℝ)) * (1 - ε) := by
      rw [hsumReal, one_mul]
    _ = ∑ m : M, (uniformMessageProb (M := M) m : ℝ) * (1 - ε) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ m : M, (uniformMessageProb (M := M) m : ℝ) * C.successProbability m := by
      refine Finset.sum_le_sum ?_
      intro m _
      have hsucc : 1 - ε ≤ C.successProbability m := by
        have hm := hC m
        unfold HSWClassicalCode.error at hm
        linarith
      exact mul_le_mul_of_nonneg_left hsucc (NNReal.coe_nonneg _)

/-! ## Source-facing Fano interface -/

/-- Shannon entropy in bits of an explicit finite classical probability mass
function, using the repository convention `0 log 0 = 0`. -/
def classicalEntropy {α : Type u} [Fintype α] (p : α → ℝ≥0) : ℝ :=
  -∑ x : α, xlog2 (p x : ℝ)

/-- The von Neumann entropy of a diagonal classical state is the corresponding
finite Shannon entropy. -/
theorem diagonalState_vonNeumann_eq_classicalEntropy
    {α : Type u} [Fintype α] [DecidableEq α]
    (p : α → ℝ≥0) (hp : ∑ x : α, p x = 1) :
    State.vonNeumann (Classical.diagonalState p hp) = classicalEntropy p := by
  unfold classicalEntropy
  exact State.vonNeumann_eq_neg_sum_xlog2_of_diagonal (Classical.diagonalState p hp)
    (fun x => (p x : ℝ)) (by
      ext i j
      rw [Classical.diagonalState_matrix, Matrix.diagonal_apply])

/-- Entropy of the uniform distribution on a finite nonempty register. -/
theorem classicalEntropy_uniformMessageProb
    (M : Type u) [Fintype M] [Nonempty M] :
    classicalEntropy (uniformMessageProb (M := M)) = log2 (Fintype.card M : ℝ) := by
  unfold classicalEntropy uniformMessageProb
  rw [show (∑ x : M, xlog2 (((Fintype.card M : ℝ≥0)⁻¹ : ℝ≥0) : ℝ)) =
      ∑ x : M, xlog2 ((Fintype.card M : ℝ)⁻¹) by
        simp [NNReal.coe_inv]]
  rw [sum_xlog2_inv_card]
  ring

/-- Finite classical entropy is bounded by the logarithm of the alphabet size. -/
theorem classicalEntropy_le_log_card
    {α : Type u} [Fintype α] [DecidableEq α]
    (p : α → ℝ≥0) (hp : ∑ x : α, p x = 1) :
    classicalEntropy p ≤ log2 (Fintype.card α : ℝ) := by
  have hS :=
    State.vonNeumann_le_log_card (Classical.diagonalState p hp)
  rwa [diagonalState_vonNeumann_eq_classicalEntropy p hp] at hS

/-- Normalize a positive-mass finite subdistribution. -/
def normalizedSubprob {α : Type u} [Fintype α] (q : α → ℝ≥0) (r : ℝ≥0) :
    α → ℝ≥0 :=
  fun x => q x / r

theorem normalizedSubprob_sum
    {α : Type u} [Fintype α] (q : α → ℝ≥0) {r : ℝ≥0}
    (hsum : ∑ x : α, q x = r) (hr : r ≠ 0) :
    ∑ x : α, normalizedSubprob q r x = 1 := by
  unfold normalizedSubprob
  rw [← Finset.sum_div, hsum, div_self hr]

/-- Entropy of a positive-mass subdistribution, rewritten through its
normalized distribution. -/
theorem classicalEntropy_eq_total_normalizedEntropy
    {α : Type u} [Fintype α] (q : α → ℝ≥0) {r : ℝ≥0}
    (hsum : ∑ x : α, q x = r) (hr : r ≠ 0) :
    classicalEntropy q =
      -xlog2 (r : ℝ) + (r : ℝ) * classicalEntropy (normalizedSubprob q r) := by
  let qnorm : α → ℝ := fun x => ((normalizedSubprob q r x : ℝ≥0) : ℝ)
  have hsum_norm_real :
      ∑ x : α, qnorm x = 1 := by
    simpa [qnorm] using (show
      ∑ x : α, ((normalizedSubprob q r x : ℝ≥0) : ℝ) = 1 by
        exact_mod_cast normalizedSubprob_sum q hsum hr)
  unfold classicalEntropy
  have hterm : ∀ x : α,
      xlog2 (q x : ℝ) =
        qnorm x * xlog2 (r : ℝ) + (r : ℝ) * xlog2 (qnorm x) := by
    intro x
    have hq :
        (q x : ℝ) = (r : ℝ) * qnorm x := by
      simp only [qnorm, normalizedSubprob, NNReal.coe_div]
      field_simp [show (r : ℝ) ≠ 0 by exact_mod_cast hr]
    rw [hq]
    exact xlog2_mul_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  calc
    -(∑ x : α, xlog2 (q x : ℝ)) =
        -(∑ x : α, (qnorm x * xlog2 (r : ℝ) + (r : ℝ) * xlog2 (qnorm x))) := by
          congr 1
          exact Finset.sum_congr rfl fun x _ => hterm x
    _ = -xlog2 (r : ℝ) + (r : ℝ) * (-(∑ x : α, xlog2 (qnorm x))) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsum_norm_real]
          ring

/-- Entropy upper bound for a positive-mass finite subdistribution. -/
theorem classicalEntropy_subprob_le_total_log_card
    {α : Type u} [Fintype α] [DecidableEq α] (q : α → ℝ≥0) {r : ℝ≥0}
    (hsum : ∑ x : α, q x = r) (hrpos : 0 < (r : ℝ)) :
    classicalEntropy q ≤ -xlog2 (r : ℝ) + (r : ℝ) * log2 (Fintype.card α : ℝ) := by
  have hr : r ≠ 0 := by
    exact_mod_cast (ne_of_gt hrpos)
  rw [classicalEntropy_eq_total_normalizedEntropy q hsum hr]
  have hnorm :
      classicalEntropy (normalizedSubprob q r) ≤ log2 (Fintype.card α : ℝ) :=
    classicalEntropy_le_log_card (normalizedSubprob q r)
      (normalizedSubprob_sum q hsum hr)
  have hmul :=
    mul_le_mul_of_nonneg_left hnorm (le_of_lt hrpos)
  simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmul (-xlog2 (r : ℝ))

/-- A finite nonnegative subdistribution with zero total mass has zero Shannon
entropy under the repository's `0 log 0 = 0` convention. -/
theorem classicalEntropy_eq_zero_of_sum_zero
    {α : Type u} [Fintype α] (q : α → ℝ≥0)
    (hsum : ∑ x : α, q x = 0) :
    classicalEntropy q = 0 := by
  have hq : ∀ x : α, q x = 0 := by
    intro x
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => (bot_le : (0 : ℝ≥0) ≤ q y))).mp hsum x
      (Finset.mem_univ x)
  unfold classicalEntropy
  simp [hq, xlog2]

/-- First marginal of a classical decoded-pair law. -/
def decodedPairMarginalAProb
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0) : M → ℝ≥0 :=
  fun m => ∑ mhat : M, p (m, mhat)

/-- Second marginal of a classical decoded-pair law. -/
def decodedPairMarginalBProb
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0) : M → ℝ≥0 :=
  fun mhat => ∑ m : M, p (m, mhat)

theorem decodedPairMarginalAProb_sum
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0)
    (hp : ∑ pair : Prod M M, p pair = 1) :
    ∑ m : M, decodedPairMarginalAProb M p m = 1 := by
  unfold decodedPairMarginalAProb
  rw [← hp]
  rw [Fintype.sum_prod_type]

theorem decodedPairMarginalBProb_sum
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0)
    (hp : ∑ pair : Prod M M, p pair = 1) :
    ∑ mhat : M, decodedPairMarginalBProb M p mhat = 1 := by
  unfold decodedPairMarginalBProb
  rw [← hp]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The first marginal of a diagonal decoded-pair state is the diagonal state
of the first classical marginal. -/
theorem diagonalDecodedPair_marginalA_matrix
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0)
    (hp : ∑ pair : Prod M M, p pair = 1) :
    (Classical.diagonalState p hp).marginalA.matrix =
      Matrix.diagonal fun m : M => (decodedPairMarginalAProb M p m : ℂ) := by
  ext m m'
  rw [State.marginalA_matrix]
  show partialTraceB (Classical.diagonalState p hp).matrix m m' =
    (Matrix.diagonal fun m : M => (decodedPairMarginalAProb M p m : ℂ)) m m'
  by_cases h : m = m'
  · subst m'
    simp [partialTraceB, decodedPairMarginalAProb]
  · simp [partialTraceB, decodedPairMarginalAProb, h]

/-- The second marginal of a diagonal decoded-pair state is the diagonal state
of the second classical marginal. -/
theorem diagonalDecodedPair_marginalB_matrix
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0)
    (hp : ∑ pair : Prod M M, p pair = 1) :
    (Classical.diagonalState p hp).marginalB.matrix =
      Matrix.diagonal fun mhat : M => (decodedPairMarginalBProb M p mhat : ℂ) := by
  ext mhat mhat'
  rw [State.marginalB_matrix]
  show partialTraceA (Classical.diagonalState p hp).matrix mhat mhat' =
    (Matrix.diagonal fun mhat : M => (decodedPairMarginalBProb M p mhat : ℂ)) mhat mhat'
  by_cases h : mhat = mhat'
  · subst mhat'
    simp [partialTraceA, decodedPairMarginalBProb]
  · simp [partialTraceA, decodedPairMarginalBProb, h]

/-- Mutual information of a finite diagonal decoded-pair law is the classical
expression `H(A) + H(B) - H(AB)`. -/
theorem diagonalDecodedPair_mutualInformation_eq_classicalEntropy
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0)
    (hp : ∑ pair : Prod M M, p pair = 1) :
    mutualInformation (Classical.diagonalState p hp) =
      classicalEntropy (decodedPairMarginalAProb M p) +
        classicalEntropy (decodedPairMarginalBProb M p) -
        classicalEntropy p := by
  unfold mutualInformation
  have hA :
      State.vonNeumann (Classical.diagonalState p hp).marginalA =
        classicalEntropy (decodedPairMarginalAProb M p) := by
    unfold classicalEntropy
    exact State.vonNeumann_eq_neg_sum_xlog2_of_diagonal
      (Classical.diagonalState p hp).marginalA
      (fun m : M => (decodedPairMarginalAProb M p m : ℝ))
      (diagonalDecodedPair_marginalA_matrix M p hp)
  have hB :
      State.vonNeumann (Classical.diagonalState p hp).marginalB =
        classicalEntropy (decodedPairMarginalBProb M p) := by
    unfold classicalEntropy
    exact State.vonNeumann_eq_neg_sum_xlog2_of_diagonal
      (Classical.diagonalState p hp).marginalB
      (fun m : M => (decodedPairMarginalBProb M p m : ℝ))
      (diagonalDecodedPair_marginalB_matrix M p hp)
  have hAB :
      State.vonNeumann (Classical.diagonalState p hp) = classicalEntropy p :=
    diagonalState_vonNeumann_eq_classicalEntropy p hp
  rw [hA, hB, hAB]

/-- Conditional entropy of the first decoded-pair register given the second,
written purely as finite classical entropies. -/
def decodedPairConditionalEntropy
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0) : ℝ :=
  classicalEntropy p - classicalEntropy (decodedPairMarginalBProb M p)

/-- The unnormalized posterior fiber `m ↦ p(m, \hat m)` of a decoded-pair
law at a fixed decoded value `\hat m`. -/
def decodedPairFiberProb
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0) (mhat : M) : M → ℝ≥0 :=
  fun m => p (m, mhat)

theorem decodedPairFiberProb_sum
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0) (mhat : M) :
    ∑ m : M, decodedPairFiberProb M p mhat m = decodedPairMarginalBProb M p mhat := by
  rfl

/-- Classical entropy of a decoded-pair joint law decomposes as the sum of
the entropies of its unnormalized posterior fibers. -/
theorem classicalEntropy_decodedPair_eq_sum_fiber
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0) :
    classicalEntropy p =
      ∑ mhat : M, classicalEntropy (decodedPairFiberProb M p mhat) := by
  unfold classicalEntropy decodedPairFiberProb
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [Finset.sum_neg_distrib]

/-- Conditional entropy of a decoded-pair law as a sum of unnormalized
posterior-fiber contributions. -/
theorem decodedPairConditionalEntropy_eq_sum_fiber
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0) :
    decodedPairConditionalEntropy M p =
      ∑ mhat : M,
        (classicalEntropy (decodedPairFiberProb M p mhat) +
          xlog2 (decodedPairMarginalBProb M p mhat : ℝ)) := by
  unfold decodedPairConditionalEntropy
  rw [classicalEntropy_decodedPair_eq_sum_fiber]
  unfold classicalEntropy
  rw [Finset.sum_add_distrib]
  ring

/-- A conditional-entropy form of decoded-pair Fano immediately gives the
mutual-information lower bound used by the HSW randomness-distribution
reduction.  The remaining mathematical core is therefore the purely classical
finite inequality
`H(M | \hat M) ≤ ε log₂ |M| - xlog₂ ε - xlog₂(1-ε)`. -/
theorem decodedMessageFano_of_conditionalEntropy_le
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (p : Prod M M → ℝ≥0) (hp : ∑ pair : Prod M M, p pair = 1) (ε : ℝ)
    (hmarg : decodedPairMarginalAProb M p = uniformMessageProb (M := M))
    (hcond :
      decodedPairConditionalEntropy M p ≤
        ε * log2 (Fintype.card M : ℝ) - xlog2 ε - xlog2 (1 - ε)) :
    (1 - ε) * log2 (Fintype.card M : ℝ) + xlog2 ε + xlog2 (1 - ε) ≤
      mutualInformation (Classical.diagonalState p hp) := by
  rw [diagonalDecodedPair_mutualInformation_eq_classicalEntropy M p hp]
  have hA :
      classicalEntropy (decodedPairMarginalAProb M p) =
        log2 (Fintype.card M : ℝ) := by
    rw [hmarg]
    exact classicalEntropy_uniformMessageProb M
  unfold decodedPairConditionalEntropy at hcond
  rw [hA]
  linarith

/-- Equality-success probability of a classical decoded-pair law. -/
def decodedPairSuccessProb
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) : ℝ≥0 :=
  ∑ m : M, p (m, m)

/-- Error probability of a classical decoded-pair law. -/
def decodedPairErrorProb
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) : ℝ≥0 :=
  ∑ pair : Prod M M, if pair.1 = pair.2 then 0 else p pair

/-- Correct mass in the posterior fiber indexed by a decoded value `\hat m`. -/
def decodedPairFiberCorrectProb
    (M : Type u) [Fintype M] (p : Prod M M → ℝ≥0) (mhat : M) : ℝ≥0 :=
  p (mhat, mhat)

/-- Error mass in the posterior fiber indexed by a decoded value `\hat m`. -/
def decodedPairFiberErrorProb
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M) :
    ℝ≥0 :=
  ∑ m : M, if m = mhat then 0 else p (m, mhat)

/-- The wrong-message subdistribution inside the posterior fiber indexed by
`\hat m`, extended by zero at the correct message. -/
def decodedPairFiberWrongProb
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M) :
    M → ℝ≥0 :=
  fun m => if m = mhat then 0 else p (m, mhat)

theorem decodedPairFiberWrongProb_sum
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M) :
    ∑ m : M, decodedPairFiberWrongProb M p mhat m =
      decodedPairFiberErrorProb M p mhat := by
  rfl

/-- A fiber's Shannon entropy splits into the correct-message atom and the
wrong-message subdistribution. -/
theorem classicalEntropy_decodedPairFiber_eq_correct_wrong
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M) :
    classicalEntropy (decodedPairFiberProb M p mhat) =
      -xlog2 (decodedPairFiberCorrectProb M p mhat : ℝ) +
        classicalEntropy (decodedPairFiberWrongProb M p mhat) := by
  unfold classicalEntropy decodedPairFiberProb decodedPairFiberCorrectProb
    decodedPairFiberWrongProb
  have hsplit :
      ∑ m : M, xlog2 (p (m, mhat) : ℝ) =
        xlog2 (p (mhat, mhat) : ℝ) +
          ∑ m : M, xlog2 ((if m = mhat then 0 else p (m, mhat) : ℝ≥0) : ℝ) := by
    calc
      ∑ m : M, xlog2 (p (m, mhat) : ℝ) =
          ∑ m : M,
            ((if m = mhat then xlog2 (p (m, mhat) : ℝ) else 0) +
              if m = mhat then 0 else xlog2 (p (m, mhat) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro m _
            by_cases hm : m = mhat <;> simp [hm]
      _ =
          ∑ m : M, (if m = mhat then xlog2 (p (m, mhat) : ℝ) else 0) +
            ∑ m : M, (if m = mhat then 0 else xlog2 (p (m, mhat) : ℝ)) := by
            rw [Finset.sum_add_distrib]
      _ =
          xlog2 (p (mhat, mhat) : ℝ) +
            ∑ m : M, xlog2 ((if m = mhat then 0 else p (m, mhat) : ℝ≥0) : ℝ) := by
            congr 1
            · rw [Finset.sum_ite_eq']
              simp
            · refine Finset.sum_congr rfl ?_
              intro m _
              by_cases hm : m = mhat <;> simp [hm, xlog2]
  rw [hsplit]
  ring

/-- Entropy of the wrong-message subdistribution in one decoded fiber is bounded
by its total error mass times `log₂ |M|`, plus the binary split term for that
mass. -/
theorem classicalEntropy_decodedPairFiberWrong_le
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M) :
    classicalEntropy (decodedPairFiberWrongProb M p mhat) ≤
      -xlog2 (decodedPairFiberErrorProb M p mhat : ℝ) +
        (decodedPairFiberErrorProb M p mhat : ℝ) * log2 (Fintype.card M : ℝ) := by
  by_cases herr : decodedPairFiberErrorProb M p mhat = 0
  · have hsum :
        ∑ m : M, decodedPairFiberWrongProb M p mhat m = 0 := by
        rw [decodedPairFiberWrongProb_sum, herr]
    rw [classicalEntropy_eq_zero_of_sum_zero (decodedPairFiberWrongProb M p mhat) hsum,
      herr]
    simp [xlog2]
  · have herrpos : 0 < ((decodedPairFiberErrorProb M p mhat : ℝ≥0) : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr herr)
    exact classicalEntropy_subprob_le_total_log_card (decodedPairFiberWrongProb M p mhat)
      (decodedPairFiberWrongProb_sum M p mhat) herrpos

/-- A posterior fiber splits into its correct mass and its error mass. -/
theorem decodedPairFiberCorrect_add_errorProb
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M) :
    decodedPairFiberCorrectProb M p mhat + decodedPairFiberErrorProb M p mhat =
      decodedPairMarginalBProb M p mhat := by
  unfold decodedPairFiberCorrectProb decodedPairFiberErrorProb decodedPairMarginalBProb
  calc
    p (mhat, mhat) + ∑ m : M, (if m = mhat then 0 else p (m, mhat)) =
        (∑ m : M, if m = mhat then p (m, mhat) else 0) +
          ∑ m : M, (if m = mhat then 0 else p (m, mhat)) := by
          congr 1
          rw [Finset.sum_ite_eq']
          simp
    _ = ∑ m : M,
          ((if m = mhat then p (m, mhat) else 0) +
            if m = mhat then 0 else p (m, mhat)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ m : M, p (m, mhat) := by
          refine Finset.sum_congr rfl ?_
          intro m _
          by_cases hm : m = mhat <;> simp [hm]

/-- The error mass in one decoded fiber is bounded by the total mass of that
fiber. -/
theorem decodedPairFiberErrorProb_le_marginalB
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M) :
    (decodedPairFiberErrorProb M p mhat : ℝ) ≤
      (decodedPairMarginalBProb M p mhat : ℝ) := by
  have hsplit :
      (decodedPairFiberCorrectProb M p mhat : ℝ) +
          (decodedPairFiberErrorProb M p mhat : ℝ) =
        (decodedPairMarginalBProb M p mhat : ℝ) := by
    exact_mod_cast decodedPairFiberCorrect_add_errorProb M p mhat
  nlinarith [NNReal.coe_nonneg (decodedPairFiberCorrectProb M p mhat)]

/-- If a decoded fiber has zero total mass, then its correct and error masses
are both zero. -/
theorem decodedPairFiberCorrect_eq_zero_of_marginalB_eq_zero
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M)
    (hmarg : decodedPairMarginalBProb M p mhat = 0) :
    decodedPairFiberCorrectProb M p mhat = 0 := by
  have hsplit := decodedPairFiberCorrect_add_errorProb M p mhat
  rw [hmarg] at hsplit
  apply le_antisymm
  · calc
      decodedPairFiberCorrectProb M p mhat ≤
          decodedPairFiberCorrectProb M p mhat + decodedPairFiberErrorProb M p mhat :=
            le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ decodedPairFiberErrorProb M p mhat)
      _ = 0 := hsplit
  · exact bot_le

/-- If a decoded fiber has zero total mass, then its error mass is zero. -/
theorem decodedPairFiberError_eq_zero_of_marginalB_eq_zero
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M)
    (hmarg : decodedPairMarginalBProb M p mhat = 0) :
    decodedPairFiberErrorProb M p mhat = 0 := by
  have hsplit := decodedPairFiberCorrect_add_errorProb M p mhat
  rw [hmarg] at hsplit
  apply le_antisymm
  · calc
      decodedPairFiberErrorProb M p mhat ≤
          decodedPairFiberCorrectProb M p mhat + decodedPairFiberErrorProb M p mhat :=
            le_add_of_nonneg_left (bot_le : (0 : ℝ≥0) ≤ decodedPairFiberCorrectProb M p mhat)
      _ = 0 := hsplit
  · exact bot_le

/-- Fiberwise Fano bound.  For a fixed decoded value `\hat m`, the contribution
to `H(M|\hat M)` is controlled by the fiber error rate and the number of
messages. -/
theorem decodedPairFiberConditionalEntropy_le
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M) :
    classicalEntropy (decodedPairFiberProb M p mhat) +
        xlog2 (decodedPairMarginalBProb M p mhat : ℝ) ≤
      (decodedPairMarginalBProb M p mhat : ℝ) *
          binaryEntropyBits
            ((decodedPairFiberErrorProb M p mhat : ℝ) /
              (decodedPairMarginalBProb M p mhat : ℝ)) +
        (decodedPairFiberErrorProb M p mhat : ℝ) *
          log2 (Fintype.card M : ℝ) := by
  by_cases hmarg : decodedPairMarginalBProb M p mhat = 0
  · have hcorr := decodedPairFiberCorrect_eq_zero_of_marginalB_eq_zero M p mhat hmarg
    have herr := decodedPairFiberError_eq_zero_of_marginalB_eq_zero M p mhat hmarg
    have hfiber_zero :
        ∑ m : M, decodedPairFiberProb M p mhat m = 0 := by
      rw [decodedPairFiberProb_sum, hmarg]
    rw [classicalEntropy_eq_zero_of_sum_zero (decodedPairFiberProb M p mhat) hfiber_zero,
      hmarg, herr]
    simp [xlog2]
  · have hmarg_pos : 0 < ((decodedPairMarginalBProb M p mhat : ℝ≥0) : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hmarg)
    have herr_nonneg : 0 ≤ (decodedPairFiberErrorProb M p mhat : ℝ) :=
      NNReal.coe_nonneg _
    have herr_le_marg :
        (decodedPairFiberErrorProb M p mhat : ℝ) ≤
          (decodedPairMarginalBProb M p mhat : ℝ) :=
      decodedPairFiberErrorProb_le_marginalB M p mhat
    have hcorr_eq :
        (decodedPairFiberCorrectProb M p mhat : ℝ) =
          (decodedPairMarginalBProb M p mhat : ℝ) -
            (decodedPairFiberErrorProb M p mhat : ℝ) := by
      have hsplit :
          (decodedPairFiberCorrectProb M p mhat : ℝ) +
              (decodedPairFiberErrorProb M p mhat : ℝ) =
            (decodedPairMarginalBProb M p mhat : ℝ) := by
        exact_mod_cast decodedPairFiberCorrect_add_errorProb M p mhat
      linarith
    have hfiber :=
      classicalEntropy_decodedPairFiber_eq_correct_wrong M p mhat
    have hwrong :=
      classicalEntropy_decodedPairFiberWrong_le M p mhat
    have hbase :
        classicalEntropy (decodedPairFiberProb M p mhat) +
            xlog2 (decodedPairMarginalBProb M p mhat : ℝ) ≤
          -xlog2 (decodedPairFiberCorrectProb M p mhat : ℝ) -
              xlog2 (decodedPairFiberErrorProb M p mhat : ℝ) +
              xlog2 (decodedPairMarginalBProb M p mhat : ℝ) +
            (decodedPairFiberErrorProb M p mhat : ℝ) *
              log2 (Fintype.card M : ℝ) := by
      rw [hfiber]
      linarith
    have hbinary :
        (decodedPairMarginalBProb M p mhat : ℝ) *
            binaryEntropyBits
              ((decodedPairFiberErrorProb M p mhat : ℝ) /
                (decodedPairMarginalBProb M p mhat : ℝ)) =
          -xlog2 (decodedPairFiberErrorProb M p mhat : ℝ) -
              xlog2
                ((decodedPairMarginalBProb M p mhat : ℝ) -
                  (decodedPairFiberErrorProb M p mhat : ℝ)) +
            xlog2 (decodedPairMarginalBProb M p mhat : ℝ) :=
      mul_binaryEntropyBits_div_eq herr_nonneg herr_le_marg hmarg_pos
    rw [hcorr_eq] at hbase
    rw [hbinary]
    (convert hbase using 1; ring)

/-- A single decoded fiber contributes at most its total mass times `log₂ |M|`
to the conditional entropy. -/
theorem decodedPairFiberConditionalEntropy_le_log_card
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) (mhat : M) :
    classicalEntropy (decodedPairFiberProb M p mhat) +
        xlog2 (decodedPairMarginalBProb M p mhat : ℝ) ≤
      (decodedPairMarginalBProb M p mhat : ℝ) * log2 (Fintype.card M : ℝ) := by
  by_cases hmarg : decodedPairMarginalBProb M p mhat = 0
  · have hfiber_zero :
        ∑ m : M, decodedPairFiberProb M p mhat m = 0 := by
      rw [decodedPairFiberProb_sum, hmarg]
    rw [classicalEntropy_eq_zero_of_sum_zero (decodedPairFiberProb M p mhat) hfiber_zero,
      hmarg]
    simp [xlog2]
  · have hmarg_pos : 0 < ((decodedPairMarginalBProb M p mhat : ℝ≥0) : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hmarg)
    have hfiber :=
      classicalEntropy_subprob_le_total_log_card (decodedPairFiberProb M p mhat)
        (decodedPairFiberProb_sum M p mhat) hmarg_pos
    linarith

/-- Total decoded-pair error is the sum of posterior-fiber error masses. -/
theorem decodedPairErrorProb_eq_sum_fiberError
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) :
    decodedPairErrorProb M p =
      ∑ mhat : M, decodedPairFiberErrorProb M p mhat := by
  unfold decodedPairErrorProb decodedPairFiberErrorProb
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- The decoded-pair error probability is the decoded-marginal weighted average
of the posterior fiber error rates.  Zero-mass decoded fibers contribute zero. -/
theorem decodedPairErrorProb_eq_sum_marginalB_mul_errorRate
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) :
    (decodedPairErrorProb M p : ℝ) =
      ∑ mhat : M,
        (decodedPairMarginalBProb M p mhat : ℝ) *
          ((decodedPairFiberErrorProb M p mhat : ℝ) /
            (decodedPairMarginalBProb M p mhat : ℝ)) := by
  calc
    (decodedPairErrorProb M p : ℝ) =
        ∑ mhat : M, (decodedPairFiberErrorProb M p mhat : ℝ) := by
          exact_mod_cast decodedPairErrorProb_eq_sum_fiberError M p
    _ =
        ∑ mhat : M,
          (decodedPairMarginalBProb M p mhat : ℝ) *
            ((decodedPairFiberErrorProb M p mhat : ℝ) /
              (decodedPairMarginalBProb M p mhat : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro mhat _
          by_cases hmarg : decodedPairMarginalBProb M p mhat = 0
          · have herr := decodedPairFiberError_eq_zero_of_marginalB_eq_zero M p mhat hmarg
            simp [hmarg, herr]
          · have hmarg_ne : (decodedPairMarginalBProb M p mhat : ℝ) ≠ 0 := by
              exact_mod_cast hmarg
            field_simp [hmarg_ne]

/-- Weighted Jensen step for decoded-pair posterior binary entropies. -/
theorem decodedPair_weighted_binaryEntropyBits_le
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0)
    (hp : ∑ pair : Prod M M, p pair = 1) :
    ∑ mhat : M,
        (decodedPairMarginalBProb M p mhat : ℝ) *
          binaryEntropyBits
            ((decodedPairFiberErrorProb M p mhat : ℝ) /
              (decodedPairMarginalBProb M p mhat : ℝ)) ≤
      binaryEntropyBits (decodedPairErrorProb M p : ℝ) := by
  classical
  let w : M → ℝ := fun mhat => (decodedPairMarginalBProb M p mhat : ℝ)
  let t : M → ℝ := fun mhat =>
    (decodedPairFiberErrorProb M p mhat : ℝ) /
      (decodedPairMarginalBProb M p mhat : ℝ)
  have hw_nonneg : ∀ mhat : M, 0 ≤ w mhat := by
    intro mhat
    exact NNReal.coe_nonneg _
  have hw_sum : ∑ mhat : M, w mhat = 1 := by
    have hw_sum_real :
        ∑ mhat : M, (decodedPairMarginalBProb M p mhat : ℝ) = 1 := by
      exact_mod_cast decodedPairMarginalBProb_sum M p hp
    simpa [w] using hw_sum_real
  have ht_nonneg : ∀ mhat : M, 0 ≤ t mhat := by
    intro mhat
    exact div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  have ht_le_one : ∀ mhat : M, t mhat ≤ 1 := by
    intro mhat
    by_cases hmarg : decodedPairMarginalBProb M p mhat = 0
    · have herr := decodedPairFiberError_eq_zero_of_marginalB_eq_zero M p mhat hmarg
      simp [t, hmarg, herr]
    · have hmarg_pos : 0 < (decodedPairMarginalBProb M p mhat : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr hmarg)
      have herr_le_marg :=
        decodedPairFiberErrorProb_le_marginalB M p mhat
      simpa [t] using (div_le_one hmarg_pos).mpr herr_le_marg
  have hj := binaryEntropyBits_weighted_sum_le
    (w := w) (t := t) hw_nonneg hw_sum ht_nonneg ht_le_one
  have hmean :
      ∑ mhat : M, w mhat * t mhat = (decodedPairErrorProb M p : ℝ) := by
    rw [← decodedPairErrorProb_eq_sum_marginalB_mul_errorRate M p]
  simpa [w, t, hmean] using hj

/-- Decoded-pair Fano conditional-entropy bound at the actual decoded error
probability. -/
theorem decodedPairConditionalEntropy_le_actualError
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0)
    (hp : ∑ pair : Prod M M, p pair = 1) :
    decodedPairConditionalEntropy M p ≤
      (decodedPairErrorProb M p : ℝ) * log2 (Fintype.card M : ℝ) -
        xlog2 (decodedPairErrorProb M p : ℝ) -
        xlog2 (1 - (decodedPairErrorProb M p : ℝ)) := by
  have hfiber_sum := decodedPairConditionalEntropy_eq_sum_fiber M p
  have hfiber_bound :
      ∑ mhat : M,
          (classicalEntropy (decodedPairFiberProb M p mhat) +
            xlog2 (decodedPairMarginalBProb M p mhat : ℝ)) ≤
        ∑ mhat : M,
          ((decodedPairMarginalBProb M p mhat : ℝ) *
              binaryEntropyBits
                ((decodedPairFiberErrorProb M p mhat : ℝ) /
                  (decodedPairMarginalBProb M p mhat : ℝ)) +
            (decodedPairFiberErrorProb M p mhat : ℝ) *
              log2 (Fintype.card M : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro mhat _
    exact decodedPairFiberConditionalEntropy_le M p mhat
  have hbin := decodedPair_weighted_binaryEntropyBits_le M p hp
  have herr_sum :
      ∑ mhat : M,
          (decodedPairFiberErrorProb M p mhat : ℝ) *
            log2 (Fintype.card M : ℝ) =
        (decodedPairErrorProb M p : ℝ) * log2 (Fintype.card M : ℝ) := by
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast (decodedPairErrorProb_eq_sum_fiberError M p).symm
  rw [hfiber_sum]
  calc
    ∑ mhat : M,
        (classicalEntropy (decodedPairFiberProb M p mhat) +
          xlog2 (decodedPairMarginalBProb M p mhat : ℝ)) ≤
        ∑ mhat : M,
          ((decodedPairMarginalBProb M p mhat : ℝ) *
              binaryEntropyBits
                ((decodedPairFiberErrorProb M p mhat : ℝ) /
                  (decodedPairMarginalBProb M p mhat : ℝ)) +
            (decodedPairFiberErrorProb M p mhat : ℝ) *
              log2 (Fintype.card M : ℝ)) := hfiber_bound
    _ =
        (∑ mhat : M,
          (decodedPairMarginalBProb M p mhat : ℝ) *
              binaryEntropyBits
                ((decodedPairFiberErrorProb M p mhat : ℝ) /
                  (decodedPairMarginalBProb M p mhat : ℝ))) +
          ∑ mhat : M,
            (decodedPairFiberErrorProb M p mhat : ℝ) *
              log2 (Fintype.card M : ℝ) := by
          rw [Finset.sum_add_distrib]
    _ ≤
        binaryEntropyBits (decodedPairErrorProb M p : ℝ) +
          (decodedPairErrorProb M p : ℝ) * log2 (Fintype.card M : ℝ) := by
          exact add_le_add hbin (le_of_eq herr_sum)
    _ =
        (decodedPairErrorProb M p : ℝ) * log2 (Fintype.card M : ℝ) -
          xlog2 (decodedPairErrorProb M p : ℝ) -
          xlog2 (1 - (decodedPairErrorProb M p : ℝ)) := by
          unfold binaryEntropyBits
          ring

/-- Decoded-pair conditional entropy is bounded by the logarithm of the
transmitted-message alphabet. -/
theorem decodedPairConditionalEntropy_le_log_card
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0)
    (hp : ∑ pair : Prod M M, p pair = 1) :
    decodedPairConditionalEntropy M p ≤ log2 (Fintype.card M : ℝ) := by
  have hfiber_sum := decodedPairConditionalEntropy_eq_sum_fiber M p
  have hfiber_bound :
      ∑ mhat : M,
          (classicalEntropy (decodedPairFiberProb M p mhat) +
            xlog2 (decodedPairMarginalBProb M p mhat : ℝ)) ≤
        ∑ mhat : M,
          (decodedPairMarginalBProb M p mhat : ℝ) * log2 (Fintype.card M : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro mhat _
    exact decodedPairFiberConditionalEntropy_le_log_card M p mhat
  have hmarg_sum :
      ∑ mhat : M,
          (decodedPairMarginalBProb M p mhat : ℝ) * log2 (Fintype.card M : ℝ) =
        log2 (Fintype.card M : ℝ) := by
    rw [← Finset.sum_mul]
    have hsum_real :
        ∑ mhat : M, (decodedPairMarginalBProb M p mhat : ℝ) = 1 := by
      exact_mod_cast decodedPairMarginalBProb_sum M p hp
    rw [hsum_real, one_mul]
  rw [hfiber_sum]
  exact hfiber_bound.trans_eq hmarg_sum

/-- The decoded-pair success probability plus error probability is the total
mass of the joint law. -/
theorem decodedPairSuccessProb_add_errorProb
    (M : Type u) [Fintype M] [DecidableEq M] (p : Prod M M → ℝ≥0) :
    decodedPairSuccessProb M p + decodedPairErrorProb M p = ∑ pair : Prod M M, p pair := by
  classical
  unfold decodedPairSuccessProb decodedPairErrorProb
  calc
    (∑ m : M, p (m, m)) +
        ∑ pair : Prod M M, (if pair.1 = pair.2 then 0 else p pair) =
        (∑ pair : Prod M M, if pair.1 = pair.2 then p pair else 0) +
          ∑ pair : Prod M M, (if pair.1 = pair.2 then 0 else p pair) := by
          congr 1
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro m _
          simp
    _ = ∑ pair : Prod M M,
          ((if pair.1 = pair.2 then p pair else 0) +
            if pair.1 = pair.2 then 0 else p pair) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ pair : Prod M M, p pair := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          by_cases hpair : pair.1 = pair.2 <;> simp [hpair]

/-- The uniform decoded-message law has uniform transmitted-message marginal. -/
theorem uniformDecodedMessageProb_marginalA
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    decodedPairMarginalAProb M (uniformDecodedMessageProb N n M C) =
      uniformMessageProb (M := M) := by
  funext m
  unfold decodedPairMarginalAProb uniformDecodedMessageProb
  calc
    ∑ mhat : M, uniformMessageProb (m, mhat).1 *
        C.decoder.prob (C.outputState (m, mhat).1) (m, mhat).2 =
        uniformMessageProb (M := M) m *
          ∑ mhat : M, C.decoder.prob (C.outputState m) mhat := by
          rw [Finset.mul_sum]
    _ = uniformMessageProb (M := M) m := by
          rw [C.decoder.sum_prob, mul_one]

/-- The uniform decoded-message law's success probability is the uniform average
decoder success probability. -/
theorem uniformDecodedMessageProb_success
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) :
    (decodedPairSuccessProb M (uniformDecodedMessageProb N n M C) : ℝ) =
      ∑ m : M, (uniformMessageProb (M := M) m : ℝ) * C.successProbability m := by
  unfold decodedPairSuccessProb uniformDecodedMessageProb HSWClassicalCode.successProbability
  simp

/-- Maximal-error reliability bounds the classical decoded-pair error
probability by `ε`. -/
theorem uniformDecodedMessageProb_error_le_of_maxErrorAtMost
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (C : HSWClassicalCode N n M) {ε : ℝ}
    (hC : C.maxErrorAtMost ε) :
    (decodedPairErrorProb M (uniformDecodedMessageProb N n M C) : ℝ) ≤ ε := by
  have hsum :
      (decodedPairSuccessProb M (uniformDecodedMessageProb N n M C) : ℝ) +
          decodedPairErrorProb M (uniformDecodedMessageProb N n M C) =
        (1 : ℝ) := by
    exact_mod_cast
      (decodedPairSuccessProb_add_errorProb M (uniformDecodedMessageProb N n M C) |>.trans
        (uniformDecodedMessageProb_sum N n M C))
  have hsucc :
      1 - ε ≤
        (decodedPairSuccessProb M (uniformDecodedMessageProb N n M C) : ℝ) := by
    rw [uniformDecodedMessageProb_success]
    have hsumReal :
        ∑ m : M, (uniformMessageProb (M := M) m : ℝ) = 1 := by
      exact_mod_cast (uniformMessageProb_sum (M := M))
    calc
      1 - ε = (∑ m : M, (uniformMessageProb (M := M) m : ℝ)) * (1 - ε) := by
        rw [hsumReal, one_mul]
      _ = ∑ m : M, (uniformMessageProb (M := M) m : ℝ) * (1 - ε) := by
        rw [Finset.sum_mul]
      _ ≤ ∑ m : M, (uniformMessageProb (M := M) m : ℝ) * C.successProbability m := by
        refine Finset.sum_le_sum ?_
        intro m _
        have hsuccm : 1 - ε ≤ C.successProbability m := by
          have hm := hC m
          unfold HSWClassicalCode.error at hm
          linarith
        exact mul_le_mul_of_nonneg_left hsuccm (NNReal.coe_nonneg _)
  linarith

/-- Classical decoded-pair Fano lower bound.

This is the only remaining genuinely classical information-theoretic
ingredient in the HSW randomness-distribution reduction.  It is deliberately
stated for an explicit finite classical joint law `p(m, \hat m)`, matching
Wilde's theorem `thm-cie:fano`, rather than for an arbitrary quantum state.
The source probability range `0 ≤ ε ≤ 1` and the classical decoded-pair
assumptions are explicit. -/
def decodedMessageFano_statement
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] : Prop :=
  ∀ (p : Prod M M → ℝ≥0) (hp : ∑ pair : Prod M M, p pair = 1) (ε : ℝ),
    decodedPairMarginalAProb M p = uniformMessageProb (M := M) →
    (decodedPairErrorProb M p : ℝ) ≤ ε →
    0 ≤ ε → ε ≤ 1 →
    (1 - ε) * log2 (Fintype.card M : ℝ) + xlog2 ε + xlog2 (1 - ε) ≤
      mutualInformation (Classical.diagonalState p hp)

/-- Wilde's classical Fano inequality (`thm-cie:fano`) specialized to the
decoded-pair law used in the HSW converse.  If a uniform message `M` is decoded
as `\hat M` with error at most `ε`, then
`I(M;\hat M) ≥ (1-ε) log₂ |M| + xlog₂ ε + xlog₂(1-ε)`.

The proof first bounds `H(M|\hat M)` by the actual decoded error.  The scalar
Fano expression is then monotone up to the usual threshold
`1 - 1/(|M|+1)` and bounded below by `log₂ |M|` after the threshold. -/
theorem decodedMessageFano
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] :
    decodedMessageFano_statement M := by
  intro p hp ε hmarg herr hε0 hε1
  refine decodedMessageFano_of_conditionalEntropy_le M p hp ε hmarg ?_
  let e : ℝ := (decodedPairErrorProb M p : ℝ)
  have he0 : 0 ≤ e := NNReal.coe_nonneg _
  by_cases hsmall : ε ≤ 1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ)
  · have hactual :
        decodedPairConditionalEntropy M p ≤
          e * log2 (Fintype.card M : ℝ) - xlog2 e - xlog2 (1 - e) := by
        simpa [e] using decodedPairConditionalEntropy_le_actualError M p hp
    have hscalar :
        e * log2 (Fintype.card M : ℝ) - xlog2 e - xlog2 (1 - e) ≤
          ε * log2 (Fintype.card M : ℝ) - xlog2 ε - xlog2 (1 - ε) := by
      exact fanoEntropyRhs_mono_of_le_threshold M he0 (by simpa [e] using herr) hε0
        hsmall
    exact hactual.trans hscalar
  · have hthreshold_le :
        1 - 1 / ((Fintype.card M + 1 : ℕ) : ℝ) ≤ ε :=
      le_of_lt (not_le.mp hsmall)
    have hlog :
        decodedPairConditionalEntropy M p ≤ log2 (Fintype.card M : ℝ) :=
      decodedPairConditionalEntropy_le_log_card M p hp
    have hscalar :
        log2 (Fintype.card M : ℝ) ≤
          ε * log2 (Fintype.card M : ℝ) - xlog2 ε - xlog2 (1 - ε) :=
      log_card_le_fanoEntropyRhs_of_threshold_le M hthreshold_le hε1
    exact hlog.trans hscalar

/-- Randomness-distribution (Fano) reduction for classical codes: every `n`-use
reliable `HSWClassicalCode` for `N` (`maxErrorAtMost ε`) satisfies

`(1-ε)·log₂|M| + xlog2 ε + xlog2 (1-ε) ≤ I(M;Bⁿ)_{τ}`

where `τ = τ_{MBⁿ}` is the cq channel output state.  The left-hand side is the
Fano lower bound on the mutual information of a uniformly distributed message
recovered with error at most `ε`.  The source Fano range `0 ≤ ε ≤ 1` is explicit
in the theorem interface, because `HSWClassicalCode.maxErrorAtMost ε` alone is
only an order predicate on code errors and does not assert that `ε` is a
probability.  The right-hand side is the quantum mutual information of the
shared-randomness state.  Together with
`mutualInformation_maximallyCorrelated_statement` (which says
`I(M;M')_{Φ̄} = log₂ |M|`), this theorem reduces the HSW converse to the AFW /
data-processing / cq-Holevo chain. -/
def hswCode_randomnessDistribution_statement
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] (ε : ℝ) : Prop :=
  ∀ (C : HSWClassicalCode N n M), C.maxErrorAtMost ε →
    0 ≤ ε → ε ≤ 1 →
    (1 - ε) * log2 (Fintype.card M : ℝ) + xlog2 ε + xlog2 (1 - ε) ≤
    mutualInformation (cqChannelOutputState N n M C)

/-- The classical decoded-pair Fano inequality, plus decoder data processing,
directly inhabits the HSW randomness-distribution target. -/
theorem hswCode_randomnessDistribution_of_decodedMessageFano
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] (ε : ℝ)
    (hFano : decodedMessageFano_statement M) :
    hswCode_randomnessDistribution_statement N n M ε := by
  intro C hC hε0 hε1
  have hdecoded :
      (1 - ε) * log2 (Fintype.card M : ℝ) + xlog2 ε + xlog2 (1 - ε) ≤
        mutualInformation (uniformDecodedMessageState N n M C) :=
    hFano (uniformDecodedMessageProb N n M C) (uniformDecodedMessageProb_sum N n M C) ε
      (uniformDecodedMessageProb_marginalA N n M C)
      (uniformDecodedMessageProb_error_le_of_maxErrorAtMost N n M C hC) hε0 hε1
  exact hdecoded.trans (mutualInformation_uniformDecodedMessageState_le_cqChannelOutputState N n M C)

/-- Unconditional HSW randomness-distribution/Fano reduction, obtained by
applying the decoded-pair Fano inequality to the uniform decoded-message law. -/
theorem hswCode_randomnessDistribution
    (n : ℕ) (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] (ε : ℝ) :
    hswCode_randomnessDistribution_statement N n M ε :=
  hswCode_randomnessDistribution_of_decodedMessageFano N n M ε (decodedMessageFano M)

end

end QIT
