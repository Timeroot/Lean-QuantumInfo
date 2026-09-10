/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.Log2Lemmas

/-!
# Message rate of a block code

The register rate `log₂ |M| / n` of a code that carries a message set `M`
across `n` channel uses, with the degenerate `n = 0` case set to zero.  The
classical and entanglement-assisted coding layers share this definition, and
the expurgation bounds below are what their direct-coding arguments consume.
-/

@[expose] public section

universe uMessage

namespace QIT

noncomputable section

/-- Register rate of an `n`-use classical message code.  The degenerate
`n = 0` convention is set to zero; asymptotic statements consume this only for
sufficiently large block lengths. -/
def messageRate (M : Type uMessage) [Fintype M] (n : ℕ) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card M : ℝ) / (n : ℝ)

namespace messageRate

/-- If the message set size is at least `2^(n R)`, then the message rate is
at least `R`. -/
theorem lowerBound_le_of_rpow_two_mul_le_card
    {M : Type uMessage} [Fintype M] {n : ℕ} {R : ℝ} (hn : 0 < n)
    (hcard : Real.rpow 2 ((n : ℝ) * R) ≤ (Fintype.card M : ℝ)) :
    R ≤ messageRate M n := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow_pos : 0 < Real.rpow 2 ((n : ℝ) * R) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hlog := log2_mono_of_pos hpow_pos hcard
  rw [log2_rpow_two] at hlog
  unfold messageRate
  rw [if_neg hn_ne]
  calc
    R = ((n : ℝ) * R) / (n : ℝ) := by field_simp [ne_of_gt hn_pos]
    _ ≤ log2 (Fintype.card M : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog (le_of_lt hn_pos)

/-- Keeping at least half the messages costs at most one bit before dividing
by the block length. -/
theorem log_card_subtype_ge_sub_one
    {M M' : Type uMessage} [Fintype M] [Nonempty M] [Fintype M'] [Nonempty M']
    (hcard : 2 * Fintype.card M' ≥ Fintype.card M) :
    log2 (Fintype.card M : ℝ) - 1 ≤ log2 (Fintype.card M' : ℝ) := by
  have hMpos_nat : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
  have hM'pos_nat : 0 < Fintype.card M' := Fintype.card_pos_iff.mpr inferInstance
  have hMpos : (0 : ℝ) < Fintype.card M := by exact_mod_cast hMpos_nat
  have hM'ne : (Fintype.card M' : ℝ) ≠ 0 := by exact_mod_cast hM'pos_nat.ne'
  have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
  have hcard_real : (Fintype.card M : ℝ) ≤ 2 * (Fintype.card M' : ℝ) := by
    exact_mod_cast hcard
  have hlog := log2_mono_of_pos hMpos hcard_real
  rw [log2_mul htwo_ne hM'ne, log2_two] at hlog
  linarith

/-- Expurgating to a survivor set of at least half the messages loses at most
`1 / n` bits per channel use. -/
theorem ge_sub_inv_of_two_card_ge
    {M M' : Type uMessage} [Fintype M] [Nonempty M] [Fintype M'] [Nonempty M']
    {n : ℕ} (hn : 0 < n) (hcard : 2 * Fintype.card M' ≥ Fintype.card M) :
    messageRate M n - (1 : ℝ) / (n : ℝ) ≤ messageRate M' n := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := log_card_subtype_ge_sub_one (M := M) (M' := M') hcard
  unfold messageRate
  rw [if_neg hn_ne, if_neg hn_ne]
  calc
    log2 (Fintype.card M : ℝ) / (n : ℝ) - 1 / (n : ℝ) =
        (log2 (Fintype.card M : ℝ) - 1) / (n : ℝ) := by ring
    _ ≤ log2 (Fintype.card M' : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog (le_of_lt hn_pos)

end messageRate

end
end QIT
