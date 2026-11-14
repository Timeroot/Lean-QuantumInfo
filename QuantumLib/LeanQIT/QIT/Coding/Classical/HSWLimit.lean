/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.HSWDirect
public import QIT.Coding.Classical.HSWConverse
import QIT.Util.TensorPower

/-!
# HSW capacity formula and regularized Holevo limit

This module is the final assembly layer for the classical-capacity category.
It combines the proved HSW direct and converse theorems and records the
source-facing regularized Holevo limit interface from Wilde's HSW theorem
[Wilde2011Qst, qit-notes.tex:33588-33632].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal
open Filter

namespace QIT

universe uLabel uLabel2 uSystem uSystem2 uIn uOut uEnsemble uCode uAux

noncomputable section

/-- Product-probability averaging of a separated sum. -/
private theorem sum_product_mul_add {ι : Type uLabel} {κ : Type uLabel2} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) (s : ι → ℝ) (t : κ → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    (∑ x : Prod ι κ, p x.1 * q x.2 * (s x.1 + t x.2)) =
      (∑ i, p i * s i) + (∑ j, q j * t j) := by
  rw [Fintype.sum_prod_type]
  calc
    ∑ i : ι, ∑ j : κ, p i * q j * (s i + t j)
        = ∑ i : ι, ∑ j : κ, ((p i * s i) * q j + p i * (q j * t j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ i, ((p i * s i) * ∑ j, q j + p i * ∑ j, q j * t j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = ∑ i, (p i * s i + p i * ∑ j, q j * t j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hq]
          ring
    _ = (∑ i, p i * s i) + ∑ i, p i * ∑ j, q j * t j := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i, p i * s i) + (∑ j, q j * t j) := by
          rw [← Finset.sum_mul, hp]
          ring

/-- Product-probability averaging of a separated product over `ℂ`. -/
private theorem sum_product_mul_mul_complex {ι : Type uLabel} {κ : Type uLabel2}
    [Fintype ι] [Fintype κ]
    (p : ι → ℂ) (q : κ → ℂ) (s : ι → ℂ) (t : κ → ℂ) :
    (∑ x : Prod ι κ, (p x.1 * q x.2) * (s x.1 * t x.2)) =
      (∑ i, p i * s i) * (∑ j, q j * t j) := by
  rw [Fintype.sum_prod_type]
  calc
    ∑ i : ι, ∑ j : κ, (p i * q j) * (s i * t j)
        = ∑ i : ι, ∑ j : κ, (p i * s i) * (q j * t j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ i : ι, (p i * s i) * ∑ j : κ, q j * t j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = (∑ i : ι, p i * s i) * (∑ j : κ, q j * t j) := by
          rw [Finset.sum_mul]

namespace Ensemble

variable {ι : Type uLabel} {κ : Type uLabel2} {a : Type uSystem} {b : Type uSystem2}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq ι] in
/-- Local extensionality for finite ensembles.  The normalization proof is propositionally
irrelevant once the probability weights and state family agree. -/
private theorem ensemble_ext {E F : Ensemble ι a}
    (hprobs : ∀ i, E.probs i = F.probs i)
    (hstates : ∀ i, E.states i = F.states i) :
    E = F := by
  cases E with
  | mk probs weights states =>
      cases F with
      | mk probs' weights' states' =>
          have hp : probs = probs' := funext hprobs
          have hs : states = states' := funext hstates
          cases hp
          cases hs
          simp

/-- Relabel the Hilbert-space basis of every state in an ensemble. -/
def reindexStates (E : Ensemble ι a) (e : a ≃ b) : Ensemble ι b where
  probs := E.probs
  weights_sum := E.weights_sum
  states := fun i => (E.states i).reindex e

omit [DecidableEq ι] in
/-- The average state of a relabeled ensemble is the relabeled average state. -/
theorem reindexStates_averageState (E : Ensemble ι a) (e : a ≃ b) :
    (E.reindexStates e).averageState = E.averageState.reindex e := by
  apply State.ext
  ext x y
  simp [reindexStates, Ensemble.averageState_matrix, State.reindex_matrix,
    Matrix.sum_apply, Matrix.smul_apply]

omit [DecidableEq ι] in
/-- Holevo information is invariant under a common basis relabeling. -/
theorem reindexStates_holevoInformation (E : Ensemble ι a) (e : a ≃ b) :
    (E.reindexStates e).holevoInformation = E.holevoInformation := by
  rw [Ensemble.holevoInformation_def, Ensemble.holevoInformation_def,
    reindexStates_averageState, State.vonNeumann_reindex]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [reindexStates, State.vonNeumann_reindex]

/-- Product of two finite ensembles. -/
def prod (E : Ensemble ι a) (F : Ensemble κ b) : Ensemble (Prod ι κ) (Prod a b) where
  probs := fun x => E.probs x.1 * F.probs x.2
  weights_sum := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ i : ι, ∑ j : κ, E.probs i * F.probs j
          = ∑ i : ι, E.probs i * ∑ j : κ, F.probs j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ i : ι, E.probs i * 1 := by
            rw [F.weights_sum]
      _ = ∑ i : ι, E.probs i := by simp
      _ = 1 := E.weights_sum
  states := fun x => (E.states x.1).prod (F.states x.2)

omit [DecidableEq ι] [DecidableEq κ] in
/-- The average state of a product ensemble is the product of average states. -/
theorem prod_averageState (E : Ensemble ι a) (F : Ensemble κ b) :
    (E.prod F).averageState = E.averageState.prod F.averageState := by
  apply State.ext
  ext x y
  simp only [Ensemble.averageState_matrix, prod, State.prod, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  change
    (∑ z : Prod ι κ,
        (((E.probs z.1 * F.probs z.2 : ℝ≥0) : ℂ) *
          ((E.states z.1).matrix x.1 y.1 * (F.states z.2).matrix x.2 y.2))) =
      (∑ i : ι, ((E.probs i : ℝ≥0) : ℂ) * (E.states i).matrix x.1 y.1) *
        (∑ j : κ, ((F.probs j : ℝ≥0) : ℂ) * (F.states j).matrix x.2 y.2)
  simpa [NNReal.coe_mul] using
    sum_product_mul_mul_complex
      (p := fun i : ι => ((E.probs i : ℝ≥0) : ℂ))
      (q := fun j : κ => ((F.probs j : ℝ≥0) : ℂ))
      (s := fun i : ι => (E.states i).matrix x.1 y.1)
      (t := fun j : κ => (F.states j).matrix x.2 y.2)

omit [DecidableEq ι] [DecidableEq κ] in
/-- Holevo information is additive on product ensembles. -/
theorem prod_holevoInformation (E : Ensemble ι a) (F : Ensemble κ b) :
    (E.prod F).holevoInformation = E.holevoInformation + F.holevoInformation := by
  rw [Ensemble.holevoInformation_def, Ensemble.holevoInformation_def,
    Ensemble.holevoInformation_def, prod_averageState, State.vonNeumann_prod]
  have hsum :
      (∑ x : Prod ι κ,
          ((E.probs x.1 * F.probs x.2).toReal) *
            State.vonNeumann ((E.states x.1).prod (F.states x.2))) =
        (∑ i : ι, (E.probs i).toReal * State.vonNeumann (E.states i)) +
          (∑ j : κ, (F.probs j).toReal * State.vonNeumann (F.states j)) := by
    have hE : ∑ i : ι, ((E.probs i : ℝ≥0) : ℝ) = 1 := by
      exact_mod_cast E.weights_sum
    have hF : ∑ j : κ, ((F.probs j : ℝ≥0) : ℝ) = 1 := by
      exact_mod_cast F.weights_sum
    simpa [NNReal.coe_mul, State.vonNeumann_prod] using
      sum_product_mul_add
        (p := fun i : ι => ((E.probs i : ℝ≥0) : ℝ))
        (q := fun j : κ => ((F.probs j : ℝ≥0) : ℝ))
        (s := fun i : ι => State.vonNeumann (E.states i))
        (t := fun j : κ => State.vonNeumann (F.states j)) hE hF
  change
    E.averageState.vonNeumann + F.averageState.vonNeumann -
        (∑ x : Prod ι κ,
          ((E.probs x.1 * F.probs x.2).toReal) *
            State.vonNeumann ((E.states x.1).prod (F.states x.2))) =
      E.averageState.vonNeumann - ∑ i, (E.probs i).toReal *
          State.vonNeumann (E.states i) +
        (F.averageState.vonNeumann - ∑ j, (F.probs j).toReal *
          State.vonNeumann (F.states j))
  rw [hsum]
  ring

omit [DecidableEq ι] in
/-- A coarse lower bound for Holevo information, using only entropy nonnegativity and the
dimension upper bound.  This avoids depending on entropy concavity in the HSW limit layer. -/
theorem neg_log_card_le_holevoInformation (E : Ensemble ι a) :
    -log2 (Fintype.card a : ℝ) ≤ E.holevoInformation := by
  have hweights : ∑ i : ι, (E.probs i).toReal = 1 := by
    exact_mod_cast E.weights_sum
  have hsum_le :
      (∑ i : ι, (E.probs i).toReal * State.vonNeumann (E.states i)) ≤
        log2 (Fintype.card a : ℝ) := by
    calc
      (∑ i : ι, (E.probs i).toReal * State.vonNeumann (E.states i))
          ≤ ∑ i : ι, (E.probs i).toReal * log2 (Fintype.card a : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left
              (State.vonNeumann_le_log_card (E.states i)) (NNReal.coe_nonneg _)
      _ = (∑ i : ι, (E.probs i).toReal) * log2 (Fintype.card a : ℝ) := by
            rw [Finset.sum_mul]
      _ = log2 (Fintype.card a : ℝ) := by
            rw [hweights]
            ring
  have havg_nonneg : 0 ≤ State.vonNeumann E.averageState :=
    State.vonNeumann_nonneg E.averageState
  rw [Ensemble.holevoInformation_def]
  linarith

end Ensemble

namespace Channel

set_option maxHeartbeats 4000000

variable {a : Type uIn} {b : Type uOut}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private theorem tensorPower_card_real (α : Type uAux) [Fintype α] (n : ℕ) :
    (Fintype.card (QIT.TensorPower α n) : ℝ) = (Fintype.card α : ℝ) ^ n := by
  exact_mod_cast tensorPower_card (a := α) n

private theorem log2_pow_nat (x : ℝ) (n : ℕ) :
    log2 (x ^ n) = (n : ℝ) * log2 x := by
  unfold log2
  rw [Real.log_pow]
  ring

private theorem log2_card_nonneg (α : Type uAux) [Fintype α] [Nonempty α] :
    0 ≤ log2 (Fintype.card α : ℝ) := by
  have hcard_pos_nat : 0 < Fintype.card α := Fintype.card_pos_iff.mpr inferInstance
  have hcard_one : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hcard_pos_nat
  unfold log2
  exact div_nonneg (Real.log_nonneg hcard_one) (le_of_lt (Real.log_pos one_lt_two))

/-- Appending two block input ensembles and then applying the appended tensor-power channel
is the same output ensemble as applying each block channel separately and then appending the
two output blocks. -/
theorem outputEnsemble_append_prod_reindex (N : Channel a b) (m r : ℕ)
    {ι κ : Type uEnsemble} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (E : Ensemble ι (QIT.TensorPower a m)) (F : Ensemble κ (QIT.TensorPower a r)) :
    (N.tensorPower (m + r)).outputEnsemble
        ((E.prod F).reindexStates (TensorPower.appendEquiv a m r)) =
      (((N.tensorPower m).outputEnsemble E).prod
          ((N.tensorPower r).outputEnsemble F)).reindexStates
        (TensorPower.appendEquiv b m r) := by
  apply Ensemble.ensemble_ext
  · intro x
    rfl
  · intro x
    exact tensorPower_append_applyState_prod N m r (E.states x.1) (F.states x.2)

/-- Holevo information is superadditive under channel tensor powers at the level of concrete
product block ensembles. -/
theorem hswHolevoRate_append_prod_reindex (N : Channel a b) (m r : ℕ)
    {ι κ : Type uEnsemble} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (E : Ensemble ι (QIT.TensorPower a m)) (F : Ensemble κ (QIT.TensorPower a r)) :
    (N.tensorPower (m + r)).hswHolevoRate
        ((E.prod F).reindexStates (TensorPower.appendEquiv a m r)) =
      (N.tensorPower m).hswHolevoRate E + (N.tensorPower r).hswHolevoRate F := by
  unfold hswHolevoRate
  rw [outputEnsemble_append_prod_reindex]
  rw [Ensemble.reindexStates_holevoInformation, Ensemble.prod_holevoInformation]

/-- Holevo block information is superadditive under tensor powers.  The proof uses concrete
near-optimal ensembles for the two block channels and the product-ensemble append bridge, so it
does not assume an optimizer exists. -/
theorem blockHolevoInformation_superadditive [Nonempty a] (N : Channel a b) (m r : ℕ) :
    (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) m + (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) r ≤
      (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) (m + r) := by
  rw [le_iff_forall_pos_lt_add]
  intro η hη
  letI : Nonempty (QIT.TensorPower a m) := tensorPower_nonempty_of_nonempty (α := a) m
  letI : Nonempty (QIT.TensorPower a r) := tensorPower_nonempty_of_nonempty (α := a) r
  letI : Nonempty (QIT.TensorPower a (m + r)) :=
    tensorPower_nonempty_of_nonempty (α := a) (m + r)
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨ι, hιF, hιD, E, hE⟩ :=
    (N.tensorPower m).exists_hswHolevoRate_gt_of_lt_holevoInformation
      (N.tensorPower m).holevoInformationValues_nonempty
      (R := (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) m - η / 4) (by
        dsimp [Channel.blockHolevoInformation]
        linarith)
  obtain ⟨κ, hκF, hκD, F, hF⟩ :=
    (N.tensorPower r).exists_hswHolevoRate_gt_of_lt_holevoInformation
      (N.tensorPower r).holevoInformationValues_nonempty
      (R := (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) r - η / 4) (by
        dsimp [Channel.blockHolevoInformation]
        linarith)
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  letI : Fintype κ := hκF
  letI : DecidableEq κ := hκD
  let G : Ensemble (Prod ι κ) (QIT.TensorPower a (m + r)) :=
    (E.prod F).reindexStates (TensorPower.appendEquiv a m r)
  have hGmem :
      (N.tensorPower (m + r)).hswHolevoRate G ∈
        (Channel.holevoInformationValues.{uIn, uOut, uEnsemble} (N.tensorPower (m + r))) := by
    refine ⟨Prod ι κ, inferInstance, inferInstance, G, rfl⟩
  have hGle :
      (N.tensorPower (m + r)).hswHolevoRate G ≤
        (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) (m + r) := by
    unfold blockHolevoInformation Channel.holevoInformation
    exact le_csSup (N.tensorPower (m + r)).holevoInformationValues_bddAbove hGmem
  have hG :
      (N.tensorPower (m + r)).hswHolevoRate G =
        (N.tensorPower m).hswHolevoRate E + (N.tensorPower r).hswHolevoRate F := by
    dsimp [G]
    exact hswHolevoRate_append_prod_reindex N m r E F
  have happrox :
      (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) m +
          (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) r - η / 2 <
        (N.tensorPower m).hswHolevoRate E + (N.tensorPower r).hswHolevoRate F := by
    linarith
  linarith

/-- Coarse lower bound on block Holevo information.  It is intentionally weaker than
nonnegativity, but it is self-contained and sufficient for the Fekete-limit remainder term. -/
theorem neg_block_log_card_le_blockHolevoInformation [Nonempty a] [Nonempty b]
    (N : Channel a b) (n : ℕ) :
    -((n : ℝ) * log2 (Fintype.card b : ℝ)) ≤ (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n := by
  letI : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty (α := a) n
  have hne :
      (Channel.holevoInformationValues.{uIn, uOut, uEnsemble} (N.tensorPower n)).Nonempty :=
    (N.tensorPower n).holevoInformationValues_nonempty
  obtain ⟨r, hr⟩ := hne
  have hr_lower : -log2 (Fintype.card (QIT.TensorPower b n) : ℝ) ≤ r := by
    rcases hr with ⟨ι, hιF, hιD, E, rfl⟩
    letI : Fintype ι := hιF
    letI : DecidableEq ι := hιD
    exact Ensemble.neg_log_card_le_holevoInformation ((N.tensorPower n).outputEnsemble E)
  have hr_le : r ≤ (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n := by
    unfold blockHolevoInformation Channel.holevoInformation
    exact le_csSup (N.tensorPower n).holevoInformationValues_bddAbove hr
  have hlog :
      log2 (Fintype.card (QIT.TensorPower b n) : ℝ) =
        (n : ℝ) * log2 (Fintype.card b : ℝ) := by
    rw [tensorPower_card_real, log2_pow_nat]
  linarith

private theorem nat_mul_blockHolevoInformation_le_block [Nonempty a] [Nonempty b]
    (N : Channel a b) (q k : ℕ) :
    (q : ℝ) * (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k ≤
      (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) (q * k) := by
  induction q with
  | zero =>
      have h0 := neg_block_log_card_le_blockHolevoInformation N 0
      simpa using h0
  | succ q ih =>
      calc
        ((q + 1 : ℕ) : ℝ) * (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k
            = (q : ℝ) * (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k +
              (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k := by
              norm_num [Nat.cast_add, Nat.cast_one]
              ring
        _ ≤ (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) (q * k) +
              (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k :=
              add_le_add ih le_rfl
        _ ≤ (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) (q * k + k) :=
              blockHolevoInformation_superadditive N (q * k) k
        _ = (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) ((q + 1) * k) := by
              rw [Nat.succ_mul]

/-- Epsilon form of the source-style regularized Holevo limit.  This is the finite-dimensional
Fekete argument specialized to the HSW block-Holevo sequence. -/
theorem regularizedHolevoInformation_limit [Nonempty a] [Nonempty b] (N : Channel a b) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
        |(Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ) -
            (Channel.regularizedHolevoInformation.{uIn, uOut, uEnsemble} N)| < ε := by
  intro ε hε
  let s : ℝ := (Channel.regularizedHolevoInformation.{uIn, uOut, uEnsemble} N)
  let B : ℝ := log2 (Fintype.card b : ℝ)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact log2_card_nonneg b
  have hs_le_B : s ≤ B := by
    dsimp [s, B]
    unfold regularizedHolevoInformation
    exact csSup_le N.regularizedHolevoRateValues_nonempty
      (fun r hr => by
        rcases hr with ⟨n, hn, rfl⟩
        exact blockHolevoRate_le_log_card.{uIn, uOut, uEnsemble, uEnsemble} N hn)
  have hs_ne : (Channel.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N).Nonempty :=
    N.regularizedHolevoRateValues_nonempty
  have hs_bdd : BddAbove (Channel.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N) :=
    N.regularizedHolevoRateValues_bddAbove
  have hnear_lt_s : s - ε / 4 < s := by linarith
  have hnear_lt_sSup :
      s - ε / 4 < sSup (Channel.regularizedHolevoRateValues.{uIn, uOut, uEnsemble} N) := by
    dsimp [s]
    unfold regularizedHolevoInformation
    linarith
  obtain ⟨rk, hrk, hrk_gt⟩ :=
    (lt_csSup_iff hs_bdd hs_ne).mp hnear_lt_sSup
  rcases hrk with ⟨k, hk, hrk_eq⟩
  subst rk
  have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨Nbig, hNbig⟩ :=
    exists_nat_gt (max ((k : ℝ) + 1) (8 * (k : ℝ) * B / ε))
  refine ⟨Nbig, ?_⟩
  intro n hn_ge
  have hNbig_le_n : (Nbig : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hk1_lt_Nbig : (k : ℝ) + 1 < (Nbig : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hNbig
  have hbound_lt_Nbig : 8 * (k : ℝ) * B / ε < (Nbig : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hNbig
  have hk_lt_n_real : (k : ℝ) < (n : ℝ) := by linarith
  have hn_pos_nat : 0 < n := by exact_mod_cast (lt_of_le_of_lt (show (0 : ℝ) ≤ k by
    exact_mod_cast Nat.zero_le k) hk_lt_n_real)
  have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hbound_lt_n : 8 * (k : ℝ) * B / ε < (n : ℝ) := by linarith
  let q : ℕ := n / k
  let t : ℕ := n % k
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Nat.div_pos (by exact_mod_cast le_of_lt hk_lt_n_real) hk
  have hqR_pos : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have ht_lt_k : t < k := by
    dsimp [t]
    exact Nat.mod_lt n hk
  have ht_le_k_real : (t : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_of_lt ht_lt_k
  have hdecomp_nat : q * k + t = n := by
    dsimp [q, t]
    simpa [Nat.mul_comm] using Nat.div_add_mod n k
  have hdecomp_real : (q : ℝ) * (k : ℝ) + (t : ℝ) = (n : ℝ) := by
    exact_mod_cast hdecomp_nat
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR_pos
  have hAk_near :
      (s - ε / 4) * (k : ℝ) < (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k := by
    have hrate_near :
        s - ε / 4 < (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k / (k : ℝ) := by
      simpa [s] using hrk_gt
    have hmul := mul_lt_mul_of_pos_right hrate_near hkR_pos
    have hdiv : ((Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k / (k : ℝ)) * (k : ℝ) =
        (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k := by
      field_simp [hk_ne]
    nlinarith
  have hqAk_near :
      (q : ℝ) * ((s - ε / 4) * (k : ℝ)) <
        (q : ℝ) * (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k :=
    mul_lt_mul_of_pos_left hAk_near hqR_pos
  have hqk : (q : ℝ) * (k : ℝ) = (n : ℝ) - (t : ℝ) := by
    linarith
  have hterm_le : s - ε / 4 + B ≤ 2 * B := by
    linarith
  have hloss_le :
      (t : ℝ) * (s - ε / 4 + B) ≤ 2 * (k : ℝ) * B := by
    have h1 :
        (t : ℝ) * (s - ε / 4 + B) ≤ (t : ℝ) * (2 * B) :=
      mul_le_mul_of_nonneg_left hterm_le (by positivity)
    have h2 : (t : ℝ) * (2 * B) ≤ (k : ℝ) * (2 * B) :=
      mul_le_mul_of_nonneg_right ht_le_k_real (by positivity)
    linarith
  have hpenalty_lt : 2 * (k : ℝ) * B < (n : ℝ) * (ε / 4) := by
    have hmul := mul_lt_mul_of_pos_right hbound_lt_n hε
    have hmain : 8 * (k : ℝ) * B < (n : ℝ) * ε := by
      field_simp [ne_of_gt hε] at hmul
      linarith
    linarith
  have hloss_lt :
      (t : ℝ) * (s - ε / 4 + B) < (n : ℝ) * (ε / 4) :=
    lt_of_le_of_lt hloss_le hpenalty_lt
  have hmain_lower :
      (n : ℝ) * (s - ε) <
        (q : ℝ) * (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k - (t : ℝ) * B := by
    nlinarith [hqAk_near, hqk, hloss_lt, hnR_pos]
  have hq_block :
      (q : ℝ) * (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k ≤
        (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) (q * k) :=
    nat_mul_blockHolevoInformation_le_block N q k
  have ht_block :
      -(t : ℝ) * B ≤ (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) t := by
    simpa [B] using neg_block_log_card_le_blockHolevoInformation N t
  have hblock_lower :
      (q : ℝ) * (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k - (t : ℝ) * B ≤
        (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n := by
    calc
      (q : ℝ) * (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) k - (t : ℝ) * B
          ≤ (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) (q * k) +
            (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) t := by
            linarith
      _ ≤ (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) (q * k + t) :=
            blockHolevoInformation_superadditive N (q * k) t
      _ = (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n := by rw [hdecomp_nat]
  have hrate_lower :
      s - ε < (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ) := by
    have hnmain : (n : ℝ) * (s - ε) < (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n :=
      lt_of_lt_of_le hmain_lower hblock_lower
    exact (lt_div_iff₀ hnR_pos).2 (by simpa [mul_comm] using hnmain)
  have hrate_upper :
      (Channel.blockHolevoInformation.{uIn, uOut, uEnsemble} N) n / (n : ℝ) ≤ s := by
    dsimp [s]
    exact blockHolevoRate_le_regularizedHolevoInformation.{
      uIn, uOut, uEnsemble, uEnsemble} N hn_pos_nat
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- Full operational HSW capacity equality in the repository's supremum-safe
regularized-Holevo interface. -/
theorem classicalCapacity_eq_regularizedHolevoInformation [Nonempty a] [Nonempty b]
    (N : Channel a b) :
    (Channel.classicalCapacity.{uIn, uOut, uCode} N) = (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) := by
  have hconv :
      (Channel.IsClassicalRateUpperBound.{uIn, uOut, uCode} N)
        (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) :=
    hsw_regularizedHolevoInformation_converse.{uIn, uOut, uEnsemble, uCode} N
  have hdirect :
      ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) →
        (Channel.IsAchievableClassicalRate.{uIn, uOut, uCode} N) R :=
    hsw_regularizedHolevoInformation_direct.{
      uIn, uOut, max uEnsemble uCode, uCode} N
  have hnonempty :
      ({R : ℝ | (Channel.IsAchievableClassicalRate.{uIn, uOut, uCode} N) R} : Set ℝ).Nonempty := by
    refine ⟨(Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) - 1, ?_⟩
    exact hdirect ((Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) - 1) (by linarith)
  have hbounded : BddAbove {R : ℝ | (Channel.IsAchievableClassicalRate.{uIn, uOut, uCode} N) R} := by
    exact ⟨(Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N), fun R hR => hconv R hR⟩
  apply le_antisymm
  · unfold classicalCapacity
    exact csSup_le hnonempty fun R hR => hconv R hR
  · rw [le_iff_forall_pos_lt_add]
    intro η hη
    have hAch :
        (Channel.IsAchievableClassicalRate.{uIn, uOut, uCode} N)
          ((Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) - η / 2) :=
      hdirect ((Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) - η / 2) (by linarith)
    have hle :
        (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) - η / 2 ≤
          (Channel.classicalCapacity.{uIn, uOut, uCode} N) := by
      unfold classicalCapacity
      exact le_csSup hbounded hAch
    linarith

/-- The named HSW capacity proposition is now proved. -/
theorem hswCapacityFormula_proved [Nonempty a] [Nonempty b]
    (N : Channel a b) :
    (Channel.hswCapacityFormula.{uIn, uOut, uEnsemble, uCode} N) := by
  exact classicalCapacity_eq_regularizedHolevoInformation N

/-- Full source-shaped HSW theorem in the repository's operational/supremum interface plus
the proved epsilon-limit form of the regularized Holevo expression. -/
theorem hswClassicalCapacityTheorem_proved [Nonempty a] [Nonempty b]
    (N : Channel a b) :
    (Channel.classicalCapacity.{uIn, uOut, uCode} N) = (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          |(Channel.blockHolevoInformation.{uIn, uOut, max uEnsemble uCode} N) n / (n : ℝ) -
            (Channel.regularizedHolevoInformation.{uIn, uOut, max uEnsemble uCode} N)| < ε) := by
  exact ⟨classicalCapacity_eq_regularizedHolevoInformation N,
    regularizedHolevoInformation_limit.{uIn, uOut, max uEnsemble uCode} N⟩

end Channel

end

end QIT
