/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.Classical.HSWDirect.Rates

/-!
# Reshaping HSW codes, and the bridge to a direct-coding witness

A block code for `N^⊗k` used `t` times is not literally a code for `N` used `t * k` times, and a
code of length `m` is not literally a code of length `m + r`; both are codes for a reindexed system.
This module supplies the three reshapings the achievability argument performs, each as a
`HSWClassicalCode` constructor together with the effect on the rate and on the maximal error:

* `castLength`, transporting along an equality of block lengths, which changes neither;
* `flattenBlock`, turning a length-`t` code for `N^⊗k` into a length-`t * k` code for `N` by
  relabelling along `TensorPower.blockFlattenEquiv`, dividing the rate by `k`;
* `padRight`, extending a length-`m` code to length `m + r` by appending a fixed tail state along
  `TensorPower.appendEquiv`, scaling the rate by `m / (m + r)`.

The error-preservation statements come in pairs.  The `_of_outputState` versions take the
channel-output compatibility as a hypothesis and are pure decoding-probability bookkeeping; the
plain versions discharge that hypothesis from the transport laws in
`HSWDirect.TensorPower`.  Composing the last two gives
`flattenBlock_padRight_rate_ge_of_ratio`, which is what converts exact-multiple block codes into
codes at every sufficiently large length.

The final section is a bridge rather than a construction: given a completed spectral
packing-hypotheses bundle, an input-codeword lift, and a rate estimate,
`HSWPackingHypothesesSpectral.toAverageErrorPackingWitness` assembles the average-error witness, and
`exists_directCodingWitness_expurgated` expurgates it to a maximal-error one at the cost of `1 / n`
in rate and a factor two in error.  No random coding, typicality estimate, or block-channel lift is
hidden in either statement.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe uIn uOut uEnsemble uMessage uAux

noncomputable section

namespace HSWClassicalCode

variable {a : Type uIn} {b : Type uOut} {M : Type uMessage}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype M] [DecidableEq M] [Nonempty M]
variable {N : CPTPMap a b} {t k : ℕ}

/-- Transport an HSW code across an equality of block lengths. -/
def castLength {n n' : ℕ} (h : n = n') (C : HSWClassicalCode N n M) :
    HSWClassicalCode N n' M :=
  h ▸ C

@[simp]
theorem castLength_rate {n n' : ℕ} (h : n = n') (C : HSWClassicalCode N n M) :
    (C.castLength h).rate = C.rate := by
  cases h
  rfl

theorem castLength_maxErrorAtMost {n n' : ℕ} (h : n = n')
    (C : HSWClassicalCode N n M) {ε : ℝ} (hC : C.maxErrorAtMost ε) :
    (C.castLength h).maxErrorAtMost ε := by
  cases h
  exact hC

/-- Flatten an exact-multiple block-channel HSW code.

A code for `(N^{⊗ k})` used `t` times has input type
`(A^k)^t` and output type `(B^k)^t`.  This constructor relabels those systems
to `A^{t*k}` and `B^{t*k}`.  The separate theorem
`flattenBlock_maxErrorAtMost_of_outputState` records the still-substantive
channel-action compatibility needed to preserve decoding probabilities. -/
def flattenBlock (C : HSWClassicalCode (N.tensorPower k) t M) :
    HSWClassicalCode N (t * k) M where
  encoder m := (C.encoder m).reindex (TensorPower.blockFlattenEquiv a t k)
  decoder := C.decoder.reindex (TensorPower.blockFlattenEquiv b t k)

/-- Exact-multiple block flattening divides the block-channel code rate by the
inner block size `k`. -/
theorem flattenBlock_rate_eq_div (C : HSWClassicalCode (N.tensorPower k) t M)
    (ht : 0 < t) (hk : 0 < k) :
    C.flattenBlock.rate = C.rate / (k : ℝ) := by
  have ht_ne : t ≠ 0 := Nat.ne_of_gt ht
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have htk_ne : t * k ≠ 0 := Nat.mul_ne_zero ht_ne hk_ne
  have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  unfold flattenBlock HSWClassicalCode.rate messageRate
  rw [if_neg htk_ne, if_neg ht_ne]
  field_simp [ne_of_gt ht_pos, ne_of_gt hk_pos]
  rw [Nat.cast_mul]
  ring

/-- Rate lower bound form of `flattenBlock_rate_eq_div`. -/
theorem flattenBlock_rate_ge_of_mul_le_rate
    (C : HSWClassicalCode (N.tensorPower k) t M)
    {R : ℝ} (ht : 0 < t) (hk : 0 < k) (hR : (k : ℝ) * R ≤ C.rate) :
    R ≤ C.flattenBlock.rate := by
  rw [C.flattenBlock_rate_eq_div ht hk]
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  exact (le_div_iff₀ hk_pos).mpr (by simpa [mul_comm] using hR)

/-- If the flattened channel output is the reindexed block-channel output, then
flattening preserves each message success probability.

The hypothesis is intentionally explicit: proving it requires the recursive
matrix identity relating `(N^{⊗ k})^{⊗ t}` and `N^{⊗ (t*k)}` under
`TensorPower.blockFlattenEquiv`, which is a separate block-transport proof
dependency. -/
theorem flattenBlock_successProbability_of_outputState
    (C : HSWClassicalCode (N.tensorPower k) t M)
    (houtput : ∀ m : M,
      C.flattenBlock.outputState m =
        (C.outputState m).reindex (TensorPower.blockFlattenEquiv b t k))
    (m : M) :
    C.flattenBlock.successProbability m = C.successProbability m := by
  unfold HSWClassicalCode.successProbability
  rw [houtput m]
  exact POVM.prob_reindex_state C.decoder (C.outputState m)
    (TensorPower.blockFlattenEquiv b t k) m

/-- Under the explicit output-state compatibility, exact-multiple block
flattening preserves maximal-error reliability. -/
theorem flattenBlock_maxErrorAtMost_of_outputState
    (C : HSWClassicalCode (N.tensorPower k) t M)
    {ε : ℝ}
    (houtput : ∀ m : M,
      C.flattenBlock.outputState m =
        (C.outputState m).reindex (TensorPower.blockFlattenEquiv b t k))
    (hC : C.maxErrorAtMost ε) :
    C.flattenBlock.maxErrorAtMost ε := by
  intro m
  unfold HSWClassicalCode.error
  rw [C.flattenBlock_successProbability_of_outputState houtput m]
  exact hC m

/-- Exact-multiple block flattening has the expected reindexed output state. -/
theorem flattenBlock_outputState
    (C : HSWClassicalCode (N.tensorPower k) t M) (m : M) :
    C.flattenBlock.outputState m =
      (C.outputState m).reindex (TensorPower.blockFlattenEquiv b t k) := by
  unfold HSWClassicalCode.outputState HSWClassicalCode.flattenBlock
  exact CPTPOp.tensorPower_blockFlatten_applyState N t k (C.encoder m)

/-- Exact-multiple block flattening preserves each message success probability. -/
theorem flattenBlock_successProbability
    (C : HSWClassicalCode (N.tensorPower k) t M) (m : M) :
    C.flattenBlock.successProbability m = C.successProbability m :=
  C.flattenBlock_successProbability_of_outputState C.flattenBlock_outputState m

/-- Exact-multiple block flattening preserves maximal-error reliability. -/
theorem flattenBlock_maxErrorAtMost
    (C : HSWClassicalCode (N.tensorPower k) t M) {ε : ℝ}
    (hC : C.maxErrorAtMost ε) :
    C.flattenBlock.maxErrorAtMost ε :=
  C.flattenBlock_maxErrorAtMost_of_outputState C.flattenBlock_outputState hC

/-- Pad an HSW code on the right by a fixed tail input state, with the decoder
ignoring the tail output register.

This is the code-level primitive needed to convert exact-multiple block codes
into codes at arbitrary sufficiently large lengths.  The preservation theorems
below take the channel-output product identity for `N^{⊗ (m+r)}` as an explicit
hypothesis. -/
def padRight {m r : ℕ} (C : HSWClassicalCode N m M)
    (tail : MState (TensorPower a r)) : HSWClassicalCode N (m + r) M where
  encoder msg :=
    ((C.encoder msg).prod tail).reindex (TensorPower.appendEquiv a m r)
  decoder :=
    (C.decoder.tensorRightIdentity (TensorPower b r)).reindex
      (TensorPower.appendEquiv b m r)

/-- Under the explicit product-output compatibility, right padding preserves
each message success probability. -/
theorem padRight_successProbability_of_outputState {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : MState (TensorPower a r))
    (houtput : ∀ msg : M,
      (C.padRight tail).outputState msg =
        ((C.outputState msg).prod ((N.tensorPower r) tail)).reindex
          (TensorPower.appendEquiv b m r))
    (msg : M) :
    (C.padRight tail).successProbability msg = C.successProbability msg := by
  unfold HSWClassicalCode.successProbability
  rw [houtput msg]
  change
    (((C.decoder.tensorRightIdentity (TensorPower b r)).reindex
        (TensorPower.appendEquiv b m r)).prob
      (((C.outputState msg).prod ((N.tensorPower r) tail)).reindex
        (TensorPower.appendEquiv b m r)) msg : ℝ) =
      (C.decoder.prob (C.outputState msg) msg : ℝ)
  rw [POVM.prob_reindex_state]
  exact POVM.tensorRightIdentity_prob_prod C.decoder (C.outputState msg)
    ((N.tensorPower r) tail) msg

/-- Under the explicit product-output compatibility, right padding preserves
maximal-error reliability. -/
theorem padRight_maxErrorAtMost_of_outputState {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : MState (TensorPower a r)) {ε : ℝ}
    (houtput : ∀ msg : M,
      (C.padRight tail).outputState msg =
        ((C.outputState msg).prod ((N.tensorPower r) tail)).reindex
          (TensorPower.appendEquiv b m r))
    (hC : C.maxErrorAtMost ε) :
    (C.padRight tail).maxErrorAtMost ε := by
  intro msg
  unfold HSWClassicalCode.error
  rw [C.padRight_successProbability_of_outputState tail houtput msg]
  exact hC msg

/-- Right padding has the expected product output under the tensor-power
append transport. -/
theorem padRight_outputState {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : MState (TensorPower a r)) (msg : M) :
    (C.padRight tail).outputState msg =
      ((C.outputState msg).prod ((N.tensorPower r) tail)).reindex
        (TensorPower.appendEquiv b m r) := by
  unfold HSWClassicalCode.outputState HSWClassicalCode.padRight
  exact CPTPOp.tensorPower_append_applyState_prod N m r (C.encoder msg) tail

/-- Right padding preserves each message success probability. -/
theorem padRight_successProbability {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : MState (TensorPower a r)) (msg : M) :
    (C.padRight tail).successProbability msg = C.successProbability msg :=
  C.padRight_successProbability_of_outputState tail (C.padRight_outputState tail) msg

/-- Right padding preserves maximal-error reliability. -/
theorem padRight_maxErrorAtMost {m r : ℕ}
    (C : HSWClassicalCode N m M) (tail : MState (TensorPower a r)) {ε : ℝ}
    (hC : C.maxErrorAtMost ε) :
    (C.padRight tail).maxErrorAtMost ε :=
  C.padRight_maxErrorAtMost_of_outputState tail (C.padRight_outputState tail) hC

/-- Rate lower bound for the exact-multiple flattening followed by right
padding.  The hypothesis `hratio` is the explicit large-block arithmetic that
absorbs the padding loss. -/
theorem flattenBlock_padRight_rate_ge_of_ratio
    {r : ℕ} (C : HSWClassicalCode (N.tensorPower k) t M)
    (tail : MState (TensorPower a r)) {A B : ℝ} (ht : 0 < t) (hk : 0 < k)
    (hbase : A ≤ C.rate / (k : ℝ))
    (hratio : B ≤ A * (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ))) :
    B ≤ (C.flattenBlock.padRight tail).rate := by
  change B ≤ messageRate M (t * k + r)
  exact messageRate.block_pad_ge_of_ratio (M := M) ht hk hbase hratio

end HSWClassicalCode

namespace HSWPackingHypothesesSpectral

/-- A completed HSW spectral packing-hypotheses bundle yields the deterministic
average-error packing witness consumed by the HSW direct-achievability
assembly layer.

This theorem is only a bridge: the caller must already supply the source-shaped
packing hypotheses, the input-codeword lift `φ`, the channel-output agreement,
and the message-cardinality/rate estimate.  No random-coding existence,
typicality estimate, or block-channel lift is hidden in this statement. -/
theorem toAverageErrorPackingWitness
    {a : Type uIn} {b : Type uOut} {ι : Type uEnsemble}
    {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype ι] [DecidableEq ι] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype M] [DecidableEq M] [Nonempty M]
    (N : CPTPMap a b) (E₀ : MEnsemble a ι) {n : ℕ} {typicalitySlack rateSlack : ℝ}
    {Eout : MEnsemble (TensorPower b n) 𝒳}
    (H : HSWPackingHypothesesSpectral Eout typicalitySlack)
    (φ : 𝒳 → MState (TensorPower a n))
    (houtput : ∀ x, (N.tensorPower n) (φ x) = Eout.states x)
    (hrate : messageRate M n ≥ N.hswHolevoRate E₀ - rateSlack) :
    Nonempty
      (HSWAverageErrorPackingWitness N E₀ n rateSlack
        (2 * (H.ε + 2 * Real.sqrt H.ε) +
          4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D)) M) :=
  PackingLemma.hswAverageErrorPackingWitness_of_packing
    N E₀ n rateSlack Eout H.P H.P_posSemidef H.P_idempotent H.P_le_one
    H.Px H.Px_projector φ houtput H.d H.D H.ε H.hD_pos H.hε_nonneg
    H.h1 H.h2 H.h3 H.h4 hrate

/-- A completed HSW spectral packing-hypotheses bundle, together with a positive
packing-error bound, expurgates to the maximal-error direct-coding witness used
by operational achievability.

The additional `1/n` rate slack and the factor-two error loss are exactly the
average-to-maximal expurgation losses formalized in `HSW.lean`.  The positivity
assumption on the displayed packing-error expression is the side condition
required by that expurgation step. -/
theorem exists_directCodingWitness_expurgated
    {a : Type uIn} {b : Type uOut} {ι : Type uEnsemble}
    {𝒳 : Type uAux} {M : Type uMessage}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype ι] [DecidableEq ι] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype M] [DecidableEq M] [Nonempty M]
    (N : CPTPMap a b) (E₀ : MEnsemble a ι) {n : ℕ} {typicalitySlack rateSlack : ℝ}
    {Eout : MEnsemble (TensorPower b n) 𝒳}
    (H : HSWPackingHypothesesSpectral Eout typicalitySlack)
    (φ : 𝒳 → MState (TensorPower a n))
    (houtput : ∀ x, (N.tensorPower n) (φ x) = Eout.states x)
    (hrate : messageRate M n ≥ N.hswHolevoRate E₀ - rateSlack)
    (hn : 0 < n)
    (hpackingError_pos :
      0 < 2 * (H.ε + 2 * Real.sqrt H.ε) +
        4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D)) :
    ∃ (M' : Type uMessage), ∃ (_ : Fintype M'), ∃ (_ : DecidableEq M'),
      ∃ (_ : Nonempty M'),
      Nonempty
        (HSWDirectCodingWitness N E₀ n (rateSlack + (1 : ℝ) / (n : ℝ))
          (2 * (2 * (H.ε + 2 * Real.sqrt H.ε) +
            4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D))) M') := by
  let packingError : ℝ :=
    2 * (H.ε + 2 * Real.sqrt H.ε) +
      4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D)
  have havg :
      Nonempty (HSWAverageErrorPackingWitness N E₀ n rateSlack packingError M) := by
    simpa [packingError] using
      H.toAverageErrorPackingWitness N E₀ φ houtput hrate
  rcases havg with ⟨W⟩
  have hpos : 0 < packingError := by
    simpa [packingError] using hpackingError_pos
  simpa [packingError] using W.exists_directCodingWitness_expurgated hn hpos

end HSWPackingHypothesesSpectral

end

end QIT
