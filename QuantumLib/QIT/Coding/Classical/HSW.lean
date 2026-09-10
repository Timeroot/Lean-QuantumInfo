/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.Holevo
public import QuantumLib.QIT.Classical.Bridge
public import QuantumLib.QIT.Core.Channel
public import QuantumLib.QIT.Core.POVMProbability
public import QuantumLib.QIT.Util.SDP.HermitianPSDTraceDuality
public import QuantumLib.QIT.Coding.Rate
public import QuantumLib.QIT.Information.Entropy.Log2Lemmas
import QuantumLib.QIT.Util.TensorPower

/-!
# HSW coding theorem: classical capacity

Definition of the classical capacity of a quantum channel via the operational
supremum of achievable rates, the regularized Holevo information interface,
and the source-shaped direct-achievability interface.

The achievability theorems here are stated relative to an explicit HSW coding
witness: a random code together with a packing-lemma decoder and the typical and
conditionally typical projector estimates that bound its error.  Such witnesses
are built in `QuantumLib.QIT.Coding.Classical.PackingLemma` and
`QuantumLib.QIT.Coding.Classical.HSWDirect`; the matching upper bound is in
`QuantumLib.QIT.Coding.Classical.HSWConverse`.  The capacity equality follows
Wilde's HSW theorem statement [Wilde2011Qst, qit-notes.tex:33588-33632], with
the direct route in [Wilde2011Qst, qit-notes.tex:33634-33808].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

universe uIn uOut uEnsemble uMessage uAux

namespace QIT

noncomputable section

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The singleton ensemble concentrated on a given state. -/
private def singletonEnsemble (ρ : MState a) : MEnsemble a PUnit.{uEnsemble + 1} :=
  .ofProbs (fun _ => 1) (by simp) (fun _ => ρ)

end
end QIT

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

variable (N : CPTPMap a b)

/-- Output ensemble obtained by sending every member of an input ensemble
through the channel. -/
def outputEnsemble {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E : MEnsemble a ι) : MEnsemble b ι :=
  .ofProbs E.probs E.weights_sum (fun i => N (E.states i))

/-- Relabeling the classical index commutes with applying a channel to an ensemble. -/
@[simp]
theorem outputEnsemble_relabelIndex
    {ι : Type uEnsemble} {κ : Type uAux}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (E : MEnsemble a ι) (e : κ ≃ ι) :
    N.outputEnsemble (E.relabelIndex e) = (N.outputEnsemble E).relabelIndex e :=
  rfl

/-- Single-letter HSW Holevo rate for an input ensemble and channel. -/
def hswHolevoRate {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E : MEnsemble a ι) : ℝ :=
  (N.outputEnsemble E).holevoInformation

/-- All single-letter Holevo information values realized by finite input
ensembles for channel `N`. -/
def holevoInformationValues : Set ℝ :=
  {r : ℝ | ∃ (ι : Type uEnsemble) (instF : Fintype ι) (instD : DecidableEq ι),
    letI : Fintype ι := instF
    letI : DecidableEq ι := instD
    ∃ E : MEnsemble a ι, r = N.hswHolevoRate E}

/-- Channel Holevo information as the supremum over finite input ensembles. -/
def holevoInformation : ℝ :=
  sSup (CPTPOp.holevoInformationValues.{uIn, uOut, uEnsemble} N)

/-- The finite-ensemble Holevo value set is bounded above by the output
dimension bound. -/
theorem mem_holevoInformationValues_le_log_card {r : ℝ}
    (hr : r ∈ (CPTPOp.holevoInformationValues.{uIn, uOut, uEnsemble} N)) :
    r ≤ log2 (Fintype.card b) := by
  rcases hr with ⟨ι, hιF, hιD, E, rfl⟩
  let : Fintype ι := hιF
  let : DecidableEq ι := hιD
  exact MEnsemble.holevo_le_log_card (N.outputEnsemble E)

/-- The finite-ensemble Holevo value set is bounded above, so its supremum is the
channel Holevo information rather than a junk value. -/
theorem holevoInformationValues_bddAbove :
    BddAbove (CPTPOp.holevoInformationValues.{uIn, uOut, uEnsemble} N) := by
  exact ⟨log2 (Fintype.card b), fun _ hr => N.mem_holevoInformationValues_le_log_card hr⟩

/-- The finite-ensemble Holevo value set is nonempty when the channel input
system admits a state. -/
theorem holevoInformationValues_nonempty [Nonempty a] :
    (CPTPOp.holevoInformationValues.{uIn, uOut, uEnsemble} N).Nonempty := by
  let E : MEnsemble a PUnit.{uEnsemble + 1} :=
    singletonEnsemble (Classical.basisState (Classical.choice (inferInstance : Nonempty a)))
  exact ⟨N.hswHolevoRate E, ⟨PUnit.{uEnsemble + 1}, inferInstance, inferInstance, E, rfl⟩⟩

/-- Approximate the channel Holevo supremum from below by a concrete finite
input ensemble. -/
theorem exists_hswHolevoRate_gt_of_lt_holevoInformation
    (hne : (CPTPOp.holevoInformationValues.{uIn, uOut, uEnsemble} N).Nonempty) {R : ℝ}
    (hR : R < (CPTPOp.holevoInformation.{uIn, uOut, uEnsemble} N)) :
    ∃ (ι : Type uEnsemble), ∃ (_ : Fintype ι), ∃ (_ : DecidableEq ι),
      ∃ E : MEnsemble a ι, R < N.hswHolevoRate E := by
  rw [holevoInformation] at hR
  obtain ⟨r, hr, hRr⟩ := (lt_csSup_iff N.holevoInformationValues_bddAbove hne).mp hR
  rcases hr with ⟨ι, hιF, hιD, E, rfl⟩
  exact ⟨ι, hιF, hιD, E, hRr⟩

/-- Holevo information of the `n`-use tensor-power channel. -/
def blockHolevoInformation (n : ℕ) : ℝ :=
  (CPTPOp.holevoInformation.{uIn, uOut, uEnsemble} (N.tensorPower n))

/-- Approximate a positive block Holevo rate from below by a concrete ensemble
for the block channel. -/
theorem exists_block_hswHolevoRate_div_gt_of_lt_blockHolevoInformation_div
    {k : ℕ} (hk : 0 < k)
    (hne : (CPTPOp.holevoInformationValues.{uIn, uOut, uEnsemble} (N.tensorPower k)).Nonempty)
    {R : ℝ} (hR : R < (CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k / (k : ℝ)) :
    ∃ (ι : Type uEnsemble), ∃ (_ : Fintype ι), ∃ (_ : DecidableEq ι),
      ∃ E : MEnsemble (QIT.TensorPower a k) ι,
        R < (N.tensorPower k).hswHolevoRate E / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hRmul : R * (k : ℝ) < (CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k := by
    calc
      R * (k : ℝ) <
          ((CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k / (k : ℝ)) * (k : ℝ) :=
        mul_lt_mul_of_pos_right hR hkR
      _ = (CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k := by
        field_simp [ne_of_gt hkR]
  obtain ⟨ι, hιF, hιD, E, hgt⟩ :=
    (N.tensorPower k).exists_hswHolevoRate_gt_of_lt_holevoInformation hne
      (by simpa [blockHolevoInformation] using hRmul)
  refine ⟨ι, hιF, hιD, E, ?_⟩
  calc
    R = (R * (k : ℝ)) / (k : ℝ) := by field_simp [ne_of_gt hkR]
    _ < (N.tensorPower k).hswHolevoRate E / (k : ℝ) :=
        div_lt_div_of_pos_right hgt hkR

/-- Regularized Holevo block-rate values `χ(N^⊗n) / n` for positive block
lengths.  This uses a supremum-safe interface instead of assuming the
source-style limit exists before it is proved. -/
def regularizedHolevoRateValues : Set ℝ :=
  {R : ℝ | ∃ n : ℕ, 0 < n ∧
    R = (CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ)}

/-- Regularized Holevo information as the supremum of positive block rates. -/
def regularizedHolevoInformation : ℝ :=
  sSup (CPTPOp.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N)

/-- The regularized Holevo block-rate set is nonempty when the channel input
system is nonempty. -/
theorem regularizedHolevoRateValues_nonempty [Nonempty a] :
    (CPTPOp.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N).Nonempty := by
  refine ⟨(CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) 1 / (1 : ℝ), ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  simp

/-- The regularized Holevo block-rate set is bounded above by the single-use
output dimension bound, for nonempty finite input and output systems. -/
theorem regularizedHolevoRateValues_bddAbove [Nonempty a] [Nonempty b] :
    BddAbove (CPTPOp.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N) := by
  refine ⟨log2 (Fintype.card b), ?_⟩
  intro r hr
  rcases hr with ⟨n, hn, rfl⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound :
      (CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n ≤
        log2 (Fintype.card (QIT.TensorPower b n)) := by
    have : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty (α := a) n
    unfold blockHolevoInformation CPTPOp.holevoInformation
    exact csSup_le
      (N.tensorPower n).holevoInformationValues_nonempty
      (fun r hr => (N.tensorPower n).mem_holevoInformationValues_le_log_card hr)
  calc
    (CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ)
        ≤ log2 (Fintype.card (QIT.TensorPower b n)) / (n : ℝ) :=
          div_le_div_of_nonneg_right hbound (le_of_lt hnR)
    _ = log2 (Fintype.card b) := by
      rw [tensorPower_card_real (a := b) n, log2_pow]
      field_simp [ne_of_gt hnR]

end CPTPOp

end

namespace QIT

noncomputable section

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A finite HSW classical communication code for `n` uses of channel `N`.

The encoder assigns one input state on `A^n` to each message; the decoder is a
POVM on the output system `B^n` with the same message labels as outcomes. -/
structure HSWClassicalCode (N : CPTPMap a b) (n : ℕ)
    (M : Type uMessage) [Fintype M] [DecidableEq M] [Nonempty M] where
  /-- The input state on `A^n` that carries each message. -/
  encoder : M → MState (TensorPower a n)
  /-- The decoding POVM on `B^n`, with outcomes labelled by messages. -/
  decoder : POVM M (TensorPower b n)

namespace HSWClassicalCode

variable {N : CPTPMap a b} {n : ℕ}
variable {M : Type uMessage} [Fintype M] [DecidableEq M] [Nonempty M]

/-- Channel output state for a selected message. -/
def outputState (C : HSWClassicalCode N n M) (m : M) : MState (TensorPower b n) :=
  (N.tensorPower n) (C.encoder m)

/-- Born-rule probability that the decoder returns the transmitted message. -/
def successProbability (C : HSWClassicalCode N n M) (m : M) : ℝ :=
  (C.decoder.prob (C.outputState m) m : ℝ)

/-- Message-wise error probability. -/
def error (C : HSWClassicalCode N n M) (m : M) : ℝ :=
  1 - C.successProbability m

/-- Maximal message error bounded by `ε`. -/
def maxErrorAtMost (C : HSWClassicalCode N n M) (ε : ℝ) : Prop :=
  ∀ m : M, C.error m ≤ ε

/-- Classical communication rate of the message set. -/
def rate (_C : HSWClassicalCode N n M) : ℝ :=
  messageRate M n

end HSWClassicalCode

/-! ### Packing-lemma interfaces

The code/decoder performance layer appearing in Wilde's packing lemma
[Wilde2011Qst, qit-notes.tex:29363-29415]: message-indexed output states, a
POVM with the same message labels, average success/error, and maximal error.
The random-code construction and typical-projector estimates that supply such a
decoder are in `QuantumLib.QIT.Coding.Classical.PackingLemma`. -/

namespace PackingLemma

variable {out : Type uOut}
variable [Fintype out] [DecidableEq out]
variable {M : Type uMessage} [Fintype M] [DecidableEq M] [Nonempty M]

/-- A finite message-indexed family of output states together with a decoder
POVM. -/
structure DecoderCode (M : Type uMessage) (out : Type uOut)
    [Fintype M] [DecidableEq M] [Nonempty M] [Fintype out] [DecidableEq out] where
  /-- The output state associated with each message. -/
  states : M → MState out
  /-- The decoding POVM, with outcomes labelled by messages. -/
  decoder : POVM M out

namespace DecoderCode

/-- Probability that the packing decoder returns the transmitted message. -/
def successProbability (C : DecoderCode M out) (m : M) : ℝ :=
  (C.decoder.prob (C.states m) m : ℝ)

/-- Message-wise error probability for the packing decoder. -/
def error (C : DecoderCode M out) (m : M) : ℝ :=
  1 - C.successProbability m

/-- Maximal message error bounded by `ε`. -/
def maxErrorAtMost (C : DecoderCode M out) (ε : ℝ) : Prop :=
  ∀ m : M, C.error m ≤ ε

/-- Uniform average success probability over the message set. -/
def averageSuccessProbability (C : DecoderCode M out) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ m : M, C.successProbability m

/-- Uniform average error probability over the message set. -/
def averageError (C : DecoderCode M out) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ m : M, C.error m

/-- Average message error bounded by `ε`. -/
def averageErrorAtMost (C : DecoderCode M out) (ε : ℝ) : Prop :=
  C.averageError ≤ ε

/-- The maximal-error condition unfolds to the source-style message-wise
decoder inequality.  This theorem is not a simp rule because arithmetic
normalization can obscure the direct bridge to `HSWClassicalCode.maxErrorAtMost`. -/
theorem maxErrorAtMost_iff (C : DecoderCode M out) (ε : ℝ) :
    C.maxErrorAtMost ε ↔ ∀ m : M, 1 - C.successProbability m ≤ ε := by
  rfl

/-- The average-error condition unfolds to the source-style uniform average
over message errors. -/
theorem averageErrorAtMost_iff (C : DecoderCode M out) (ε : ℝ) :
    C.averageErrorAtMost ε ↔
      (Fintype.card M : ℝ)⁻¹ * ∑ m : M, (1 - C.successProbability m) ≤ ε := by
  rfl

/-- Per-message error of a `DecoderCode` is the complement of the per-message
success probability. -/
theorem error_eq (C : DecoderCode M out) (m : M) : C.error m = 1 - C.successProbability m := by
  rfl

/-! ### Expurgation (average error → maximal error)

Markov's inequality on the average message error: a `DecoderCode` with average
error at most `ε` (and nonnegative per-message errors) has a survivor set of at
least half its messages (`2 · |S| ≥ |M|`), each with per-message error at most
`2 · ε`. Restricting the code to `S` therefore yields a code on at least half
the message set with maximal error at most `2 · ε` (at a cost of at most one
bit of rate). The nonnegativity hypothesis holds for POVM-decoder codes, whose
per-message success probability is at most one.
Source: [Wilde2011Qst, qit-notes.tex:33634-33808]. -/

theorem exists_goodSubset_of_averageErrorAtMost
    (C : DecoderCode M out) {ε : ℝ} (havg : C.averageErrorAtMost ε) (hε : 0 < ε)
    (herr_nonneg : ∀ m : M, 0 ≤ C.error m) :
    ∃ S : Finset M, 2 * S.card ≥ Fintype.card M ∧ ∀ m ∈ S, C.error m ≤ 2 * ε := by
  classical
  set good : Finset M := Finset.filter (fun m => C.error m ≤ 2 * ε) Finset.univ with hgood_def
  refine ⟨good, ?_, fun m hm => (Finset.mem_filter.mp hm).2⟩
  -- Markov: bad = {m | error > 2ε} satisfies 2·|bad| ≤ |M|, so 2·|good| ≥ |M|.
  set bad : Finset M := Finset.filter (fun m => 2 * ε < C.error m) Finset.univ with hbad_def
  have hcardM_pos : (0 : ℝ) < Fintype.card M := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty M›
  have hsum_le : (∑ m, C.error m) ≤ (Fintype.card M : ℝ) * ε := by
    have ha : (Fintype.card M : ℝ)⁻¹ * ∑ m, C.error m ≤ ε := havg
    rw [← inv_mul_le_iff₀ hcardM_pos]
    exact ha
  -- each bad message has error ≥ 2ε; summing, ∑_bad (2ε) ≤ ∑_bad error.
  have hbad_term : ∑ m ∈ bad, (2 * ε : ℝ) ≤ ∑ m ∈ bad, C.error m :=
    Finset.sum_le_sum fun m hm => le_of_lt (Finset.mem_filter.mp hm).2
  have hbad_le_univ : ∑ m ∈ bad, C.error m ≤ ∑ m, C.error m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intros m _ _
    exact herr_nonneg m
  have hbad_bound : ∑ m ∈ bad, (2 * ε : ℝ) ≤ (Fintype.card M : ℝ) * ε :=
    hbad_term.trans (hbad_le_univ.trans hsum_le)
  have hbad_const : (bad.card : ℝ) * (2 * ε) = ∑ m ∈ bad, (2 * ε : ℝ) := by
    simp [Finset.sum_const]
  have h2bad_le : 2 * bad.card ≤ Fintype.card M := by
    have h1 : (bad.card : ℝ) * (2 * ε) ≤ (Fintype.card M : ℝ) * ε := by
      rw [hbad_const]
      exact hbad_bound
    have h2 : (2 : ℝ) * bad.card ≤ (Fintype.card M : ℝ) := by nlinarith [h1, hε]
    exact_mod_cast h2
  -- good and bad partition univ (every real is `≤ 2ε` or `> 2ε`), so
  -- |good| + |bad| = |M|; with 2·|bad| ≤ |M| this gives 2·|good| ≥ |M|.
  have h_disj : Disjoint good bad := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    refine Finset.eq_empty_of_forall_notMem (fun m hm => ?_)
    simp only [hgood_def, hbad_def, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and] at hm
    obtain ⟨hle, hlt⟩ := hm
    linarith
  have h_union : good ∪ bad = (Finset.univ : Finset M) := by
    apply Finset.eq_univ_of_forall
    intro m
    simp only [hgood_def, hbad_def, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases h : C.error m ≤ 2 * ε
    · left
      exact h
    · right
      push Not at h
      exact h
  have hpart : good.card + bad.card = Fintype.card M := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union, Finset.card_univ]
  omega
end DecoderCode

end PackingLemma

namespace HSWClassicalCode

variable {N : CPTPMap a b} {n : ℕ}
variable {M : Type uMessage} [Fintype M] [DecidableEq M] [Nonempty M]

/-- The output-state/decoder layer of an HSW classical code, exactly the object
to which the packing lemma is applied. -/
def toPackingDecoderCode (C : HSWClassicalCode N n M) :
    PackingLemma.DecoderCode M (TensorPower b n) where
  states := C.outputState
  decoder := C.decoder

@[simp]
theorem toPackingDecoderCode_successProbability (C : HSWClassicalCode N n M)
    (m : M) :
    C.toPackingDecoderCode.successProbability m = C.successProbability m := by
  rfl

@[simp]
theorem toPackingDecoderCode_error (C : HSWClassicalCode N n M) (m : M) :
    C.toPackingDecoderCode.error m = C.error m := by
  rfl

@[simp]
theorem toPackingDecoderCode_maxErrorAtMost (C : HSWClassicalCode N n M)
    (ε : ℝ) :
    C.toPackingDecoderCode.maxErrorAtMost ε ↔ C.maxErrorAtMost ε := by
  rfl

/-- Message-wise error probabilities of an HSW code are nonnegative. -/
theorem error_nonneg (C : HSWClassicalCode N n M) (m : M) :
    0 ≤ C.error m := by
  unfold error successProbability
  have hle := C.decoder.prob_le_one (C.outputState m) m
  linarith

/-- HSW-code expurgation at the subset level: from average error at most `ε`,
there is a survivor set of at least half the original messages, each with
message-wise error at most `2ε`.  Constructing the restricted POVM on that
survivor set is a separate code-transport step; this theorem is the counting
heart of Wilde's average-to-maximal-error conversion. -/
theorem exists_goodSubset_of_averageErrorAtMost (C : HSWClassicalCode N n M)
    {ε : ℝ} (havg : C.toPackingDecoderCode.averageErrorAtMost ε) (hε : 0 < ε) :
    ∃ S : Finset M, 2 * S.card ≥ Fintype.card M ∧ ∀ m ∈ S, C.error m ≤ 2 * ε := by
  have hsubset :=
    PackingLemma.DecoderCode.exists_goodSubset_of_averageErrorAtMost
      C.toPackingDecoderCode havg hε (fun m => C.error_nonneg m)
  simpa [toPackingDecoderCode_error] using hsubset

/-- Restrict an HSW code to a nonempty survivor set.  The decoder keeps the
original effects on survivor messages and folds all discarded-message effects
into one distinguished survivor, so the result is again a POVM. -/
noncomputable def restrictToFinset (C : HSWClassicalCode N n M)
    (S : Finset M) [Nonempty {m : M // m ∈ S}] :
    HSWClassicalCode N n {m : M // m ∈ S} where
  encoder m := C.encoder m.1
  decoder := by
    classical
    let m0 : {m : M // m ∈ S} := (inferInstance : Nonempty {m : M // m ∈ S}).some
    let discarded : CMatrix (TensorPower b n) := ∑ m ∈ Sᶜ, C.decoder.effects m
    let effects' : {m : M // m ∈ S} → CMatrix (TensorPower b n) := fun m =>
      C.decoder.effects m.1 + if m = m0 then discarded else (0 : CMatrix (TensorPower b n))
    have hdiscarded_pos : discarded.PosSemidef :=
      Matrix.posSemidef_sum Sᶜ fun m _ => C.decoder.pos m
    have hpos : ∀ m, (effects' m).PosSemidef := by
      intro m
      have hmain : (C.decoder.effects m.1).PosSemidef := C.decoder.pos m.1
      by_cases hm : m = m0
      · have : effects' m = C.decoder.effects m.1 + discarded := by
          simp [effects', hm]
        rw [this]
        exact hmain.add hdiscarded_pos
      · have : effects' m = C.decoder.effects m.1 := by
          simp [effects', hm]
        rw [this]
        exact hmain
    have hsum_survivors :
        (∑ m : {m : M // m ∈ S}, C.decoder.effects m.1) =
          ∑ m ∈ S, C.decoder.effects m := by
      exact (Finset.sum_subtype S (fun m => Iff.rfl) C.decoder.effects).symm
    have hsum_extra :
        (∑ m : {m : M // m ∈ S},
          (if m = m0 then discarded else (0 : CMatrix (TensorPower b n)))) = discarded := by
      calc
        (∑ m : {m : M // m ∈ S},
          (if m = m0 then discarded else (0 : CMatrix (TensorPower b n)))) =
            (if m0 = m0 then discarded else (0 : CMatrix (TensorPower b n))) :=
              Finset.sum_eq_single
                (s := (Finset.univ : Finset {m : M // m ∈ S}))
                (f := fun m : {m : M // m ∈ S} =>
                  if m = m0 then discarded else (0 : CMatrix (TensorPower b n)))
                m0
                (fun m _ hm => by
                  change (if m = m0 then discarded else (0 : CMatrix (TensorPower b n))) = 0
                  rw [if_neg hm])
                (fun hm => False.elim (hm (Finset.mem_univ m0)))
        _ = discarded := by simp
    have hsum : (∑ m, effects' m) = 1 := by
      simp only [effects', Finset.sum_add_distrib]
      rw [hsum_survivors, hsum_extra]
      have hpartition := Finset.sum_compl_add_sum S C.decoder.effects
      rw [C.decoder.sum_eq_one] at hpartition
      change (∑ m ∈ S, C.decoder.effects m) + discarded = 1
      rw [show discarded = ∑ m ∈ Sᶜ, C.decoder.effects m from rfl]
      rw [add_comm]
      exact hpartition
    exact .ofMatrices effects' hpos hsum

@[simp]
theorem restrictToFinset_encoder (C : HSWClassicalCode N n M)
    (S : Finset M) [Nonempty {m : M // m ∈ S}] (m : {m : M // m ∈ S}) :
    (C.restrictToFinset S).encoder m = C.encoder m.1 := by
  rfl

/-- Restricting to a survivor set does not increase any survivor's message-wise
error; the distinguished survivor may only gain extra decoder effect. -/
theorem restrictToFinset_error_le (C : HSWClassicalCode N n M)
    (S : Finset M) [Nonempty {m : M // m ∈ S}] (m : {m : M // m ∈ S}) :
    (C.restrictToFinset S).error m ≤ C.error m.1 := by
  classical
  unfold error successProbability outputState restrictToFinset
  simp only
  let m0 : {m : M // m ∈ S} := (inferInstance : Nonempty {m : M // m ∈ S}).some
  let discarded : CMatrix (TensorPower b n) := ∑ m ∈ Sᶜ, C.decoder.effects m
  have hdiscarded_pos : discarded.PosSemidef :=
    Matrix.posSemidef_sum Sᶜ fun m _ => C.decoder.pos m
  rw [POVM.prob_eq_trace_re, POVM.prob_eq_trace_re]
  simp only [POVM.effects_ofMatrices]
  by_cases hm : m = m0
  · have hsplit :
        C.decoder.effects m.1 +
            (if m = m0 then discarded else (0 : CMatrix (TensorPower b n))) =
          C.decoder.effects m.1 + discarded := by
        simp [hm]
    rw [hsplit, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    have hnonneg :
        0 ≤ (((C.outputState m.1).m * discarded).trace).re :=
      cMatrix_trace_mul_posSemidef_re_nonneg (C.outputState m.1).psd hdiscarded_pos
    have hnonneg' :
        0 ≤ ((((N.tensorPower n) (C.encoder m.1)).m *
          discarded).trace).re := by
      simpa [outputState] using hnonneg
    linarith
  · have hsplit :
        C.decoder.effects m.1 +
            (if m = m0 then discarded else (0 : CMatrix (TensorPower b n))) =
          C.decoder.effects m.1 := by
        simp [hm]
    rw [hsplit]

/-- Expurgate an HSW code with small average error to a maximal-error code on a
survivor message set of at least half the original cardinality. -/
theorem exists_expurgatedCode_of_averageErrorAtMost (C : HSWClassicalCode N n M)
    {ε : ℝ} (havg : C.toPackingDecoderCode.averageErrorAtMost ε) (hε : 0 < ε) :
    ∃ (M' : Type uMessage), ∃ (_ : Fintype M'), ∃ (_ : DecidableEq M'), ∃ (_ : Nonempty M'),
      ∃ C' : HSWClassicalCode N n M',
        2 * Fintype.card M' ≥ Fintype.card M ∧ C'.maxErrorAtMost (2 * ε) := by
  obtain ⟨S, hcard, hgood⟩ := C.exists_goodSubset_of_averageErrorAtMost havg hε
  have hSpos : 0 < S.card := by
    have hMpos : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
    omega
  have hSnonempty : S.Nonempty := Finset.card_pos.mp hSpos
  let M' := {m : M // m ∈ S}
  let : Fintype M' := inferInstance
  let : DecidableEq M' := inferInstance
  let : Nonempty M' := ⟨⟨hSnonempty.choose, hSnonempty.choose_spec⟩⟩
  let C' : HSWClassicalCode N n M' := C.restrictToFinset S
  refine ⟨M', inferInstance, inferInstance, inferInstance, C', ?_, ?_⟩
  · have hcard_eq : Fintype.card M' = S.card := by
      rw [Fintype.card_subtype]
      simp
    rw [hcard_eq]
    exact hcard
  · intro m
    exact (C.restrictToFinset_error_le S m).trans (hgood m.1 m.2)

/-- Expurgation with the standard HSW rate accounting: after discarding at most
half the messages, the maximal-error code has rate at least the original
average-error code rate minus `1/n`. -/
theorem exists_expurgatedCode_of_averageErrorAtMost_rate (C : HSWClassicalCode N n M)
    {ε : ℝ} (hn : 0 < n) (havg : C.toPackingDecoderCode.averageErrorAtMost ε)
    (hε : 0 < ε) :
    ∃ (M' : Type uMessage), ∃ (_ : Fintype M'), ∃ (_ : DecidableEq M'), ∃ (_ : Nonempty M'),
      ∃ C' : HSWClassicalCode N n M',
        C'.rate ≥ C.rate - (1 : ℝ) / (n : ℝ) ∧ C'.maxErrorAtMost (2 * ε) := by
  obtain ⟨M', hM'fin, hM'dec, hM'nonempty, C', hcard, herr⟩ :=
    C.exists_expurgatedCode_of_averageErrorAtMost havg hε
  let : Fintype M' := hM'fin
  let : DecidableEq M' := hM'dec
  let : Nonempty M' := hM'nonempty
  refine ⟨M', inferInstance, inferInstance, inferInstance, C', ?_, herr⟩
  exact messageRate.ge_sub_inv_of_two_card_ge (M := M) (M' := M') hn hcard

end HSWClassicalCode

end
end QIT

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

variable (N : CPTPMap a b)

/-- Direct achievability of a classical communication rate for a channel.

For every rate slack `δ > 0` and error tolerance `ε > 0`, all sufficiently
large block lengths have a finite message code with rate at least `R - δ` and
maximal message error at most `ε`. -/
def IsAchievableClassicalRate (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
      ∃ (M : Type uMessage), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
        ∃ C : HSWClassicalCode N n M, C.rate ≥ R - δ ∧ C.maxErrorAtMost ε

/-- `B` upper-bounds all operationally achievable classical rates for channel
`N`. -/
def IsClassicalRateUpperBound (B : ℝ) : Prop :=
  ∀ R : ℝ, (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R → R ≤ B

/-- Operational classical capacity as the supremum of achievable rates. -/
def classicalCapacity : ℝ :=
  sSup {R : ℝ | (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R}

/-- The full Holevo--Schumacher--Westmoreland capacity formula: the operational
classical capacity equals the regularized Holevo information. -/
def hswCapacityFormula : Prop :=
  (CPTPOp.classicalCapacity.{uIn, uOut, uMessage} N) =
    (CPTPOp.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uMessage} N)

end CPTPOp

end

namespace QIT

noncomputable section

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Source-shaped witness for one block of the HSW direct coding proof.

The witness packages the already-constructed code and the two estimates
delivered by the packing lemma and typical/conditionally typical projectors:
rate at least the Holevo rate minus `δ`, and maximal error at most `ε`. -/
structure HSWDirectCodingWitness {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (N : CPTPMap a b) (E : MEnsemble a ι) (n : ℕ) (δ ε : ℝ)
    (M : Type uMessage) [Fintype M] [DecidableEq M] [Nonempty M] where
  /-- The underlying HSW code. -/
  code : HSWClassicalCode N n M
  /-- The code's rate is within `δ` of the Holevo rate of `E`. -/
  rate_ge : code.rate ≥ N.hswHolevoRate E - δ
  /-- Every message is decoded with error at most `ε`. -/
  maxError_le : code.maxErrorAtMost ε

/-- HSW packing-lemma witness at the average-error stage.

Wilde's random-coding/packing analysis first yields a deterministic code with
small *average* error.  The separate expurgation theorem below converts this
into the maximal-error witness consumed by the operational achievability
definition, with the standard one-bit cardinality loss. -/
structure HSWAverageErrorPackingWitness {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (N : CPTPMap a b) (E : MEnsemble a ι) (n : ℕ) (δ ε : ℝ)
    (M : Type uMessage) [Fintype M] [DecidableEq M] [Nonempty M] where
  /-- The underlying HSW code. -/
  code : HSWClassicalCode N n M
  /-- The code's rate is within `δ` of the Holevo rate of `E`. -/
  rate_ge : code.rate ≥ N.hswHolevoRate E - δ
  /-- The average decoding error at the packing layer is at most `ε`. -/
  packing_average_error_le : code.toPackingDecoderCode.averageErrorAtMost ε

namespace HSWDirectCodingWitness

variable {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
variable {N : CPTPMap a b} {E : MEnsemble a ι} {n : ℕ} {δ ε δ' ε' : ℝ}
variable {M : Type uMessage} [Fintype M] [DecidableEq M] [Nonempty M]

/-- Direct-coding witnesses are monotone in the allowed rate slack and maximal
error tolerance. -/
def weaken (W : HSWDirectCodingWitness N E n δ ε M)
    (hδ : δ ≤ δ') (hε : ε ≤ ε') :
    HSWDirectCodingWitness N E n δ' ε' M where
  code := W.code
  rate_ge := by linarith [W.rate_ge]
  maxError_le := fun m => le_trans (W.maxError_le m) hε

end HSWDirectCodingWitness

namespace HSWAverageErrorPackingWitness

variable {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
variable {N : CPTPMap a b} {E : MEnsemble a ι} {n : ℕ} {δ ε δ' ε' : ℝ}
variable {M : Type uMessage} [Fintype M] [DecidableEq M] [Nonempty M]

/-- Average-error packing witnesses are monotone in the allowed rate slack and
average-error tolerance. -/
def weaken (W : HSWAverageErrorPackingWitness N E n δ ε M)
    (hδ : δ ≤ δ') (hε : ε ≤ ε') :
    HSWAverageErrorPackingWitness N E n δ' ε' M where
  code := W.code
  rate_ge := by linarith [W.rate_ge]
  packing_average_error_le := le_trans W.packing_average_error_le hε

end HSWAverageErrorPackingWitness

/-- HSW-specific packing-lemma witness after the average-random-code and
derandomization/expurgation steps have produced a deterministic decoder with
maximal error control.

The field `packing_max_error_le` is stated at the output-state packing layer;
`toDirectCodingWitness` below turns it into the direct-coding witness consumed
by the existing HSW achievability interface. -/
structure HSWPackingLemmaWitness {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (N : CPTPMap a b) (E : MEnsemble a ι) (n : ℕ) (δ ε : ℝ)
    (M : Type uMessage) [Fintype M] [DecidableEq M] [Nonempty M] where
  /-- The underlying HSW code. -/
  code : HSWClassicalCode N n M
  /-- The code's rate is within `δ` of the Holevo rate of `E`. -/
  rate_ge : code.rate ≥ N.hswHolevoRate E - δ
  /-- The maximal decoding error at the packing layer is at most `ε`. -/
  packing_max_error_le : code.toPackingDecoderCode.maxErrorAtMost ε

namespace HSWPackingLemmaWitness

variable {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
variable {N : CPTPMap a b} {E : MEnsemble a ι} {n : ℕ} {δ ε : ℝ}
variable {M : Type uMessage} [Fintype M] [DecidableEq M] [Nonempty M]

/-- A completed packing-lemma decoder witness is exactly the HSW direct-coding
witness required by the operational achievability theorem. -/
def toDirectCodingWitness (W : HSWPackingLemmaWitness N E n δ ε M) :
    HSWDirectCodingWitness N E n δ ε M where
  code := W.code
  rate_ge := W.rate_ge
  maxError_le := by
    exact (HSWClassicalCode.toPackingDecoderCode_maxErrorAtMost W.code ε).mp
      W.packing_max_error_le

end HSWPackingLemmaWitness

namespace HSWAverageErrorPackingWitness

variable {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
variable {N : CPTPMap a b} {E : MEnsemble a ι} {n : ℕ} {δ ε : ℝ}
variable {M : Type uMessage} [Fintype M] [DecidableEq M] [Nonempty M]

/-- Average-error packing witnesses expurgate to maximal-error direct witnesses.

The rate slack increases by `1/n` because keeping at least half the messages
costs at most one bit; the error tolerance doubles by Markov expurgation. -/
theorem exists_directCodingWitness_expurgated
    (W : HSWAverageErrorPackingWitness N E n δ ε M) (hn : 0 < n) (hε : 0 < ε) :
    ∃ (M' : Type uMessage), ∃ (_ : Fintype M'), ∃ (_ : DecidableEq M'), ∃ (_ : Nonempty M'),
      Nonempty (HSWDirectCodingWitness N E n (δ + (1 : ℝ) / (n : ℝ)) (2 * ε) M') := by
  obtain ⟨M', hM'fin, hM'dec, hM'nonempty, C', hrate, herr⟩ :=
    W.code.exists_expurgatedCode_of_averageErrorAtMost_rate hn
      W.packing_average_error_le hε
  let : Fintype M' := hM'fin
  let : DecidableEq M' := hM'dec
  let : Nonempty M' := hM'nonempty
  refine ⟨M', inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨{ code := C', rate_ge := ?_, maxError_le := herr }⟩
  linarith [W.rate_ge, hrate]

end HSWAverageErrorPackingWitness

end
end QIT

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

variable (N : CPTPMap a b)

/-- Achievability is downward closed in the rate: a code family for rate `S`
also achieves every smaller rate `R`. -/
theorem IsAchievableClassicalRate.mono {R S : ℝ}
    (hS : (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) S) (hRS : R ≤ S) :
    (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R := by
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := hS δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty, C, hrate, herr⟩ := hN0 n hn
  refine ⟨M, hMfin, hMdec, hMnonempty, C, ?_, herr⟩
  linarith

/-- HSW direct achievability from a family of direct-coding witnesses.

This is the direct-coding half of the HSW theorem at the level currently
formalized in Lean: the random-coding, packing-lemma, and typical-subspace
arguments supply the witness family; this theorem records the reusable
interface from those estimates to operational achievability. -/
theorem hsw_direct_achievable_of_directCodingWitness
    {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι] (E : MEnsemble a ι)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∃ (M : Type uMessage), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
            ∃ (_ : Nonempty M), Nonempty (HSWDirectCodingWitness N E n δ ε M)) :
    (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) (N.hswHolevoRate E) := by
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty, ⟨witness⟩⟩ := hN0 n hn
  let : Fintype M := hMfin
  let : DecidableEq M := hMdec
  let : Nonempty M := hMnonempty
  exact ⟨M, inferInstance, inferInstance, inferInstance, witness.code,
    witness.rate_ge, witness.maxError_le⟩

end CPTPOp

end

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

variable (N : CPTPMap a b)

/-- A packing-lemma witness supplies the direct-coding witness expected by the
single-ensemble HSW achievability theorem. -/
theorem hswDirectCodingWitness_nonempty_of_packingWitness
    {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E : MEnsemble a ι) {n : ℕ} {δ ε : ℝ}
    {M : Type uMessage} [Fintype M] [DecidableEq M] [Nonempty M]
    (W : HSWPackingLemmaWitness N E n δ ε M) :
    Nonempty (HSWDirectCodingWitness N E n δ ε M) :=
  ⟨W.toDirectCodingWitness⟩

/-- Direct-witness assembly from the average-error packing stage.

This is the precise interface used by the HSW direct proof before expurgation:
for every target slack, sufficiently large block lengths must provide an
average-error packing witness with half the rate slack and half the error
tolerance, while `1/n` is small enough to absorb the expurgation cardinality
loss. -/
theorem hsw_directWitnessAssembly_from_averageErrorPacking
    {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι] (E : MEnsemble a ι)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∃ (M : Type uMessage), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
              ∃ (_ : Nonempty M),
                Nonempty (HSWAverageErrorPackingWitness N E n (δ / 2) (ε / 2) M)) :
    (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) (N.hswHolevoRate E) := by
  refine N.hsw_direct_achievable_of_directCodingWitness E ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hnN0
  obtain ⟨hn_pos, hinv, M, hMfin, hMdec, hMnonempty, ⟨W⟩⟩ := hN0 n hnN0
  let : Fintype M := hMfin
  let : DecidableEq M := hMdec
  let : Nonempty M := hMnonempty
  have hε_half : 0 < ε / 2 := by linarith
  obtain ⟨M', hM'fin, hM'dec, hM'nonempty, ⟨W'⟩⟩ :=
    W.exists_directCodingWitness_expurgated hn_pos hε_half
  let : Fintype M' := hM'fin
  let : DecidableEq M' := hM'dec
  let : Nonempty M' := hM'nonempty
  refine ⟨M', inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨{ code := W'.code, rate_ge := ?_, maxError_le := ?_ }⟩
  · have hslack : δ / 2 + (1 : ℝ) / (n : ℝ) ≤ δ := by linarith
    linarith [W'.rate_ge]
  · intro m
    have herr := W'.maxError_le m
    linarith

/-- If every finite-ensemble Holevo rate is operationally achievable, then
every rate strictly below the channel's one-shot Holevo information is
operationally achievable.

This is the `sSup` approximation step at the one-block channel level.  It does
not construct codes; the hypothesis supplies the ensemble-specific direct
coding theorem. -/
theorem hsw_holevoInformation_direct_of_ensembleWitnesses [Nonempty a]
    (h :
      ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
        ∀ E : MEnsemble a ι,
          (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) (N.hswHolevoRate E)) :
    ∀ R : ℝ, R < (CPTPOp.holevoInformation.{uIn, uOut, uEnsemble} N) →
      (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R := by
  intro R hR
  rw [holevoInformation] at hR
  obtain ⟨r, hrmem, hRr⟩ :=
    (lt_csSup_iff N.holevoInformationValues_bddAbove
      N.holevoInformationValues_nonempty).mp hR
  rcases hrmem with ⟨ι, hιF, hιD, E, rfl⟩
  let : Fintype ι := hιF
  let : DecidableEq ι := hιD
  exact CPTPOp.IsAchievableClassicalRate.mono N
    (h ι inferInstance inferInstance E) (le_of_lt hRr)

/-- Regularized direct-achievability squeeze from block-rate witnesses.

This theorem isolates the final order-theoretic step of the HSW direct proof:
if every positive block Holevo rate `χ(N^⊗n)/n` is operationally achievable and
the regularized supremum is approximated from below by such block rates, then
every rate below the regularized Holevo information is achievable.  The
substantive coding theorem must supply the two hypotheses; no converse input is
used here. -/
theorem hsw_regularized_direct_of_blockRateWitnesses
    (happrox : ∀ R : ℝ, R < (CPTPOp.regularizedHolevoInformation.{uIn, uOut, uEnsemble} N) →
      ∃ n : ℕ, 0 < n ∧
        R < (CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ))
    (hblock : ∀ n : ℕ, 0 < n →
      (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N)
        ((CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ))) :
    ∀ R : ℝ, R < (CPTPOp.regularizedHolevoInformation.{uIn, uOut, uEnsemble} N) →
      (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R := by
  intro R hR
  obtain ⟨n, hn, hlt⟩ := happrox R hR
  exact CPTPOp.IsAchievableClassicalRate.mono N (hblock n hn) (le_of_lt hlt)

/-- Regularized direct-achievability squeeze using the standard `sSup`
approximation theorem.  The only analytic side conditions are the usual
nonemptiness and boundedness of the block-rate set. -/
theorem hsw_regularized_direct_of_blockRateWitnesses_bdd
    (hne : (CPTPOp.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N).Nonempty)
    (hbdd : BddAbove (CPTPOp.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N))
    (hblock : ∀ n : ℕ, 0 < n →
      (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N)
        ((CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ))) :
    ∀ R : ℝ, R < (CPTPOp.regularizedHolevoInformation.{uIn, uOut, uEnsemble} N) →
      (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockRateWitnesses ?_ hblock
  intro R hR
  rw [regularizedHolevoInformation] at hR
  obtain ⟨r, hrmem, hRr⟩ := (lt_csSup_iff hbdd hne).mp hR
  rcases hrmem with ⟨n, hn, rfl⟩
  exact ⟨n, hn, hRr⟩

/-- Regularized direct-achievability squeeze in strict-rate form.

Operational achievability is naturally open in the rate.  It is therefore
enough to prove that every rate strictly below each positive block Holevo rate
is achievable; the `sSup` approximation then yields every rate strictly below
the regularized Holevo information. -/
theorem hsw_regularized_direct_of_strictBlockRateWitnesses_bdd
    (hne : (CPTPOp.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N).Nonempty)
    (hbdd : BddAbove (CPTPOp.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N))
    (hblock : ∀ n : ℕ, 0 < n → ∀ R : ℝ,
      R < (CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ) →
        (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R) :
    ∀ R : ℝ, R < (CPTPOp.regularizedHolevoInformation.{uIn, uOut, uEnsemble} N) →
      (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R := by
  intro R hR
  rw [regularizedHolevoInformation] at hR
  obtain ⟨r, hrmem, hRr⟩ := (lt_csSup_iff hbdd hne).mp hR
  rcases hrmem with ⟨n, hn, rfl⟩
  exact hblock n hn R hRr

/-- Regularized direct-achievability squeeze in strict-rate form, with the
standard nonempty finite-system side conditions discharged. -/
theorem hsw_regularized_direct_of_strictBlockRateWitnesses [Nonempty a] [Nonempty b]
    (hblock : ∀ n : ℕ, 0 < n → ∀ R : ℝ,
      R < (CPTPOp.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ) →
        (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R) :
    ∀ R : ℝ, R < (CPTPOp.regularizedHolevoInformation.{uIn, uOut, uEnsemble} N) →
      (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R :=
  N.hsw_regularized_direct_of_strictBlockRateWitnesses_bdd
    N.regularizedHolevoRateValues_nonempty
    N.regularizedHolevoRateValues_bddAbove
    hblock

/-- Regularized HSW direct-achievability from block-channel ensemble witnesses
and an explicit block-code transport theorem.

This theorem separates the two inputs of the direct proof:

* `hblockEnsemble` proves ensemble-specific HSW direct coding for every block
  channel `N^⊗n`;
* `htransport` turns a code for the block channel `N^⊗n` at rate `S` into a
  code for the original channel `N` at normalized rate `S/n`.

Given those two inputs, the `sSup` regularized-Holevo step follows. -/
theorem hsw_regularized_direct_of_blockChannelEnsembleWitnesses [Nonempty a] [Nonempty b]
    (htransport :
      ∀ n : ℕ, 0 < n → ∀ S : ℝ,
        (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} (N.tensorPower n)) S →
          (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) (S / (n : ℝ)))
    (hblockEnsemble :
      ∀ n : ℕ, 0 < n →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E : MEnsemble (QIT.TensorPower a n) ι,
            (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} (N.tensorPower n))
              ((N.tensorPower n).hswHolevoRate E)) :
    ∀ R : ℝ, R < (CPTPOp.regularizedHolevoInformation.{uIn, uOut, uEnsemble} N) →
      (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_strictBlockRateWitnesses ?_
  intro n hn R hR
  have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn
  let blockN : CPTPMap (QIT.TensorPower a n) (QIT.TensorPower b n) := N.tensorPower n
  have hblockRate :
      (n : ℝ) * R < (CPTPOp.holevoInformation.{uIn, uOut, uEnsemble} blockN) := by
    have hmul := mul_lt_mul_of_pos_left hR hnR_pos
    dsimp [blockN]
    unfold blockHolevoInformation at hmul
    calc
      (n : ℝ) * R <
          (n : ℝ) *
            ((CPTPOp.holevoInformation.{uIn, uOut, uEnsemble} (N.tensorPower n)) / (n : ℝ)) := hmul
      _ = (CPTPOp.holevoInformation.{uIn, uOut, uEnsemble} (N.tensorPower n)) := by
        field_simp [ne_of_gt hnR_pos]
  have : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty (α := a) n
  have hblockAch :
      (CPTPOp.IsAchievableClassicalRate.{uIn, uOut, uMessage} blockN) ((n : ℝ) * R) := by
    dsimp [blockN]
    exact (N.tensorPower n).hsw_holevoInformation_direct_of_ensembleWitnesses
      (fun ι hιF hιD E => hblockEnsemble n hn ι hιF hιD E)
      ((n : ℝ) * R) hblockRate
  have hnorm := htransport n hn ((n : ℝ) * R) hblockAch
  convert hnorm using 1
  field_simp [ne_of_gt hnR_pos]

end CPTPOp

end
