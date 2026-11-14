/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.HSWDirect.TensorPower

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

namespace hswMessageRate

theorem nonneg {M : Type u} [Fintype M] [Nonempty M] (n : ℕ) :
    0 ≤ hswMessageRate M n := by
  by_cases hn : n = 0
  · simp [hswMessageRate, hn]
  · have hcard_pos_nat : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
    have hcard_one : (1 : ℝ) ≤ (Fintype.card M : ℝ) := by exact_mod_cast hcard_pos_nat
    have hlog_nonneg : 0 ≤ log2 (Fintype.card M : ℝ) := by
      unfold log2
      exact div_nonneg (Real.log_nonneg hcard_one)
        (le_of_lt (Real.log_pos one_lt_two))
    unfold hswMessageRate
    rw [if_neg hn]
    exact div_nonneg hlog_nonneg (Nat.cast_nonneg n)

theorem block_pad_eq
    {M : Type u} [Fintype M] {t k r : ℕ} (ht : 0 < t) (hk : 0 < k) :
    hswMessageRate M (t * k + r) =
      (hswMessageRate M t / (k : ℝ)) *
        (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) := by
  have ht_ne : t ≠ 0 := Nat.ne_of_gt ht
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have htk_pos : 0 < t * k := Nat.mul_pos ht hk
  have hsum_pos : 0 < t * k + r := Nat.add_pos_left htk_pos r
  have hsum_ne : t * k + r ≠ 0 := Nat.ne_of_gt hsum_pos
  have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum_pos_real : (0 : ℝ) < t * k + r := by exact_mod_cast hsum_pos
  unfold hswMessageRate
  rw [if_neg hsum_ne, if_neg ht_ne]
  rw [Nat.cast_add, Nat.cast_mul]
  field_simp [ne_of_gt ht_pos, ne_of_gt hk_pos, ne_of_gt hsum_pos_real]

theorem block_pad_ge_of_ratio
    {M : Type u} [Fintype M] {t k r : ℕ} {A B : ℝ}
    (ht : 0 < t) (hk : 0 < k)
    (hbase : A ≤ hswMessageRate M t / (k : ℝ))
    (hratio : B ≤ A * (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ))) :
    B ≤ hswMessageRate M (t * k + r) := by
  have hratio_nonneg :
      0 ≤ (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    B ≤ A * (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) := hratio
    _ ≤ (hswMessageRate M t / (k : ℝ)) *
          (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hbase hratio_nonneg
    _ = hswMessageRate M (t * k + r) := by
        rw [block_pad_eq (M := M) ht hk]


/-- The operational message rate exactly exponentiates back to the message
cardinality for positive block lengths. -/
theorem rpow_two_mul_rate_eq_card
    {M : Type u} [Fintype M] [Nonempty M] {n : ℕ} (hn : 0 < n) :
    Real.rpow 2 ((n : ℝ) * hswMessageRate M n) = (Fintype.card M : ℝ) := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard_pos : (0 : ℝ) < Fintype.card M := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  unfold hswMessageRate
  rw [if_neg hn_ne]
  have hmul :
      (n : ℝ) * (log2 (Fintype.card M : ℝ) / (n : ℝ)) =
        log2 (Fintype.card M : ℝ) := by
    field_simp [ne_of_gt hn_pos]
  rw [hmul]
  exact rpow_two_log2_pos hcard_pos

/-- The cross-codeword cardinality factor is bounded by the exponential of the
HSW message rate. -/
theorem card_sub_one_le_rpow_two_mul_rate
    {M : Type u} [Fintype M] [Nonempty M] {n : ℕ} (hn : 0 < n) :
    (Fintype.card M : ℝ) - 1 ≤ Real.rpow 2 ((n : ℝ) * hswMessageRate M n) := by
  rw [rpow_two_mul_rate_eq_card (M := M) hn]
  linarith

/-- Choose a finite nonempty message type whose `n`-use HSW message rate is at
least any prescribed real value.

The construction uses `Fin (max 1 ⌈2^(nR)⌉)`.  This lemma is deliberately
rate-only: the HSW packing-error side condition still has to be discharged from
the separate typical-estimate exponents. -/
theorem exists_finite_message_type_rate_ge {n : ℕ} (hn : 0 < n) (R : ℝ) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      R ≤ hswMessageRate M n := by
  let m : ℕ := max 1 (Nat.ceil (Real.rpow 2 ((n : ℝ) * R)))
  have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hceil_le_m : Nat.ceil (Real.rpow 2 ((n : ℝ) * R)) ≤ m := Nat.le_max_right 1 _
  have hpow_le_m : Real.rpow 2 ((n : ℝ) * R) ≤ (m : ℝ) := by
    exact (Nat.le_ceil (Real.rpow 2 ((n : ℝ) * R))).trans
      (by exact_mod_cast hceil_le_m)
  refine ⟨ULift.{u} (Fin m), inferInstance, inferInstance, ?_, ?_⟩
  · exact ⟨ULift.up ⟨0, hm_pos⟩⟩
  · have hcard : Real.rpow 2 ((n : ℝ) * R) ≤
        (Fintype.card (ULift.{u} (Fin m)) : ℝ) := by
      simpa using hpow_le_m
    exact lowerBound_le_of_rpow_two_mul_le_card (M := ULift.{u} (Fin m)) hn hcard

/-- Choose a finite nonempty message type whose rate is at least `R` while the
cross-codeword cardinality factor is at most `2^(nR)`.

This is the rate/cardinality accounting used in the HSW direct proof after the
packing-error exponent is separated from the code construction. -/
theorem exists_finite_message_type_rate_ge_card_sub_one_le
    {n : ℕ} (hn : 0 < n) (R : ℝ) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      R ≤ hswMessageRate M n ∧
        (Fintype.card M : ℝ) - 1 ≤ Real.rpow 2 ((n : ℝ) * R) := by
  let x : ℝ := Real.rpow 2 ((n : ℝ) * R)
  let m : ℕ := max 1 (Nat.ceil x)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hm_pos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hceil_le_m : Nat.ceil x ≤ m := Nat.le_max_right 1 _
  have hx_le_m : x ≤ (m : ℝ) := by
    exact (Nat.le_ceil x).trans (by exact_mod_cast hceil_le_m)
  have hm_sub_le : (m : ℝ) - 1 ≤ x := by
    by_cases hceil_le_one : Nat.ceil x ≤ 1
    · have hm_eq : m = 1 := by
        dsimp [m]
        exact max_eq_left hceil_le_one
      rw [hm_eq]
      norm_num
      exact hx_pos.le
    · have hceil_one_le : 1 ≤ Nat.ceil x := (Nat.lt_of_not_ge hceil_le_one).le
      have hm_eq : m = Nat.ceil x := by
        dsimp [m]
        exact max_eq_right hceil_one_le
      have hceil_lt : (Nat.ceil x : ℝ) < x + 1 :=
        Nat.ceil_lt_add_one (le_of_lt hx_pos)
      rw [hm_eq]
      linarith
  refine ⟨ULift.{u} (Fin m), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact ⟨ULift.up ⟨0, hm_pos⟩⟩
  · have hcard : Real.rpow 2 ((n : ℝ) * R) ≤
        (Fintype.card (ULift.{u} (Fin m)) : ℝ) := by
      simpa [x] using hx_le_m
    exact lowerBound_le_of_rpow_two_mul_le_card (M := ULift.{u} (Fin m)) hn hcard
  · simpa [x] using hm_sub_le

end hswMessageRate

/-- Combine the two HSW packing-error terms after the message-cardinality
factor has been bounded by an exponential rate estimate. -/
theorem hswPackingError_le_of_rate_cross_bound
    {M : Type u} [Fintype M] {n : ℕ} {R ratio packingε ε : ℝ}
    (hcard : (Fintype.card M : ℝ) - 1 ≤ Real.rpow 2 ((n : ℝ) * R))
    (hratio : 0 ≤ ratio)
    (hself : 2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4)
    (hcross : 4 * Real.rpow 2 ((n : ℝ) * R) * ratio ≤ ε / 4) :
    2 * (packingε + 2 * Real.sqrt packingε) +
        4 * ((Fintype.card M : ℝ) - 1) * ratio ≤ ε / 2 := by
  have hcard_mul :
      ((Fintype.card M : ℝ) - 1) * ratio ≤
        Real.rpow 2 ((n : ℝ) * R) * ratio :=
    mul_le_mul_of_nonneg_right hcard hratio
  have hcross' :
      4 * ((Fintype.card M : ℝ) - 1) * ratio ≤ ε / 4 := by
    calc
      4 * ((Fintype.card M : ℝ) - 1) * ratio
          = 4 * (((Fintype.card M : ℝ) - 1) * ratio) := by ring
      _ ≤ 4 * (Real.rpow 2 ((n : ℝ) * R) * ratio) :=
          mul_le_mul_of_nonneg_left hcard_mul (by norm_num)
      _ = 4 * Real.rpow 2 ((n : ℝ) * R) * ratio := by ring
      _ ≤ ε / 4 := hcross
  linarith

/-- Combine the two HSW packing-error terms after they have been bounded
separately.  This is the local numerical bridge used before the cross term is
eventually discharged from an exponential rate estimate. -/
theorem hswPackingError_le_of_self_cross_bound
    {M : Type u} [Fintype M] {ratio packingε ε : ℝ}
    (hself : 2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4)
    (hcross : 4 * ((Fintype.card M : ℝ) - 1) * ratio ≤ ε / 4) :
    2 * (packingε + 2 * Real.sqrt packingε) +
        4 * ((Fintype.card M : ℝ) - 1) * ratio ≤ ε / 2 := by
  linarith

/-- A concrete small packing-error parameter for the HSW self-error term.

The minimum keeps both `η ≤ ε/32` and `sqrt η ≤ ε/32`, uniformly for all
positive error tolerances. -/
noncomputable def hswSelfPackingEpsilon (ε : ℝ) : ℝ :=
  min (ε / 32) ((ε / 32) ^ 2)

theorem hswSelfPackingEpsilon_pos {ε : ℝ} (hε : 0 < ε) :
    0 < hswSelfPackingEpsilon ε := by
  dsimp [hswSelfPackingEpsilon]
  exact lt_min (by positivity) (sq_pos_of_pos (by positivity))

theorem hswSelfPackingEpsilon_nonneg {ε : ℝ} (hε : 0 < ε) :
    0 ≤ hswSelfPackingEpsilon ε :=
  (hswSelfPackingEpsilon_pos hε).le

theorem hswSelfPackingEpsilon_self_bound {ε : ℝ} (hε : 0 < ε) :
    2 * (hswSelfPackingEpsilon ε + 2 * Real.sqrt (hswSelfPackingEpsilon ε))
        ≤ ε / 4 := by
  have hlinear : hswSelfPackingEpsilon ε ≤ ε / 32 := by
    dsimp [hswSelfPackingEpsilon]
    exact min_le_left _ _
  have hsquare : hswSelfPackingEpsilon ε ≤ (ε / 32) ^ 2 := by
    dsimp [hswSelfPackingEpsilon]
    exact min_le_right _ _
  have hε32_nonneg : 0 ≤ ε / 32 := by positivity
  have hsqrt :
      Real.sqrt (hswSelfPackingEpsilon ε) ≤ ε / 32 := by
    have hs := Real.sqrt_le_sqrt hsquare
    have hsimp : Real.sqrt ((ε / 32) ^ 2) = ε / 32 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hε32_nonneg]
    simpa [hsimp] using hs
  nlinarith

/-- Eventually, an inverse-linear Chebyshev-style ratio is below any positive
threshold.  The denominator is written as `n * δ²` to match the HSW packing
estimates. -/
theorem exists_nat_real_div_mul_sq_le {C η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 → C / ((n : ℝ) * δ ^ 2) ≤ η := by
  let X : ℝ := C / (η * δ ^ 2)
  refine ⟨max 1 (Nat.ceil X), ?_⟩
  intro n hn
  have hceil_le_n : Nat.ceil X ≤ n := (Nat.le_max_right 1 (Nat.ceil X)).trans hn
  have hX_le_n : X ≤ (n : ℝ) :=
    (Nat.le_ceil X).trans (by exact_mod_cast hceil_le_n)
  have hn_one : 1 ≤ n := (Nat.le_max_left 1 (Nat.ceil X)).trans hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_one
  have hδ2_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hcoef_pos : 0 < η * δ ^ 2 := mul_pos hη hδ2_pos
  have hC_le : C ≤ (n : ℝ) * (η * δ ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hX_le_n hcoef_pos.le
    have hX_mul : X * (η * δ ^ 2) = C := by
      dsimp [X]
      field_simp [ne_of_gt hcoef_pos]
    calc
      C = X * (η * δ ^ 2) := hX_mul.symm
      _ ≤ (n : ℝ) * (η * δ ^ 2) := hmul
  have hden_pos : 0 < (n : ℝ) * δ ^ 2 := mul_pos hn_pos hδ2_pos
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- A constant multiple of a nonnegative geometric sequence with ratio below
one is eventually below every positive threshold. -/
theorem exists_nat_const_mul_pow_le {A q η : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 → A * q ^ n ≤ η := by
  by_cases hA : A ≤ 0
  · refine ⟨0, ?_⟩
    intro n _hn
    have hpow_nonneg : 0 ≤ q ^ n := pow_nonneg hq_nonneg n
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hA hpow_nonneg) hη.le
  · have htend :
        Filter.Tendsto (fun n : ℕ => A * q ^ n) Filter.atTop (nhds (A * 0)) :=
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one)
    rw [mul_zero] at htend
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (htend.eventually (Iio_mem_nhds hη))
    exact ⟨N0, fun n hn => le_of_lt (hN0 n hn)⟩

/-- Exponential base-two decay in blocklength is eventually below every
positive threshold. -/
theorem exists_nat_const_mul_rpow_two_neg_mul_le {A c η : ℝ}
    (hc : 0 < c) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
      A * Real.rpow 2 (-(n : ℝ) * c) ≤ η := by
  let q : ℝ := Real.rpow 2 (-c)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-c)
  have hq_lt_one : q < 1 := by
    have hlt : -c < (0 : ℝ) := by linarith
    have hpow_lt :
        Real.rpow 2 (-c) < Real.rpow 2 (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hlt
    simpa using hpow_lt
  obtain ⟨N0, hN0⟩ := exists_nat_const_mul_pow_le (A := A) (q := q) (η := η)
    hq_pos.le hq_lt_one hη
  refine ⟨N0, ?_⟩
  intro n hn
  have hpow :
      q ^ n = Real.rpow 2 (-(n : ℝ) * c) := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  simpa [hpow] using hN0 n hn

/-- Positive slacks can make a finite nonnegative linear error budget
arbitrarily small.  This is the elementary "choose the typicality windows
small enough" step used in the HSW cross-exponent bookkeeping. -/
theorem exists_pos_pair_linear_slack {A B δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ y + x * A + B * (x + y) ≤ δ / 4 := by
  let C : ℝ := 1 + A + B
  have hC_pos : 0 < C := by
    dsimp [C]
    nlinarith
  let x : ℝ := δ / (16 * C)
  let y : ℝ := δ / (16 * C)
  have hx_pos : 0 < x := by
    dsimp [x]
    exact div_pos hδ (mul_pos (by norm_num) hC_pos)
  have hy_pos : 0 < y := by
    dsimp [y]
    exact div_pos hδ (mul_pos (by norm_num) hC_pos)
  have hC_ge_one : 1 ≤ C := by
    dsimp [C]
    nlinarith
  have hA_le_C : A ≤ C := by
    dsimp [C]
    nlinarith
  have hB_le_C : B ≤ C := by
    dsimp [C]
    nlinarith
  have hxC : x * C = δ / 16 := by
    dsimp [x]
    field_simp [ne_of_gt hC_pos]
  have hyC : y * C = δ / 16 := by
    dsimp [y]
    field_simp [ne_of_gt hC_pos]
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hy_le : y ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_left hC_ge_one hy_nonneg
    simpa [mul_one, hyC] using h
  have hxA_le : x * A ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_left hA_le_C hx_nonneg
    simpa [hxC] using h
  have hBx_le : B * x ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_right hB_le_C hx_nonneg
    have hCx : C * x = δ / 16 := by simpa [mul_comm] using hxC
    simpa [hCx] using h
  have hBy_le : B * y ≤ δ / 16 := by
    have h := mul_le_mul_of_nonneg_right hB_le_C hy_nonneg
    have hCy : C * y = δ / 16 := by simpa [mul_comm] using hyC
    simpa [hCy] using h
  refine ⟨x, y, hx_pos, hy_pos, ?_⟩
  have hsplit : B * (x + y) = B * x + B * y := by ring
  rw [hsplit]
  nlinarith

/-- The HSW cross term has a strictly negative exponent once the conditional
dimension slack and source-projector mass slack are chosen below a quarter of
the Holevo-rate gap. -/
theorem hsw_crossExponent_rpow_bound {n : ℕ} {χ avg cond ex ey δ : ℝ}
    (hχ : χ = avg - cond) (hslack : ex + ey ≤ δ / 4) :
    4 * Real.rpow 2 ((n : ℝ) * (χ - δ / 2)) *
          (Real.rpow 2 ((n : ℝ) * (cond + ex)) /
            ((1 - (1 / 2 : ℝ)) *
              Real.rpow 2 ((n : ℝ) * avg - (n : ℝ) * ey))) ≤
        8 * Real.rpow 2 (-(n : ℝ) * (δ / 4)) := by
  let e₁ : ℝ := (n : ℝ) * (χ - δ / 2)
  let e₂ : ℝ := (n : ℝ) * (cond + ex)
  let e₃ : ℝ := (n : ℝ) * avg - (n : ℝ) * ey
  have htwo_pos : 0 < (2 : ℝ) := by norm_num
  have hpow_pos : 0 < Real.rpow 2 e₃ := Real.rpow_pos_of_pos htwo_pos e₃
  have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
  have hdiv_half :
      Real.rpow 2 e₂ / ((1 - (1 / 2 : ℝ)) * Real.rpow 2 e₃) =
        2 * (Real.rpow 2 e₂ / Real.rpow 2 e₃) := by
    rw [hhalf]
    field_simp [ne_of_gt hpow_pos]
  have hpow_combine :
      Real.rpow 2 e₁ * (Real.rpow 2 e₂ / Real.rpow 2 e₃) =
        Real.rpow 2 (e₁ + e₂ - e₃) := by
    rw [div_eq_mul_inv]
    have hinv : (Real.rpow 2 e₃)⁻¹ = Real.rpow 2 (-e₃) :=
      (Real.rpow_neg htwo_pos.le e₃).symm
    rw [hinv]
    rw [← mul_assoc]
    have h12 :
        Real.rpow 2 e₁ * Real.rpow 2 e₂ = Real.rpow 2 (e₁ + e₂) :=
      (Real.rpow_add htwo_pos e₁ e₂).symm
    rw [h12]
    have h123 :
        Real.rpow 2 (e₁ + e₂) * Real.rpow 2 (-e₃) =
          Real.rpow 2 ((e₁ + e₂) + (-e₃)) :=
      (Real.rpow_add htwo_pos (e₁ + e₂) (-e₃)).symm
    rw [h123]
    ring_nf
  have hexp_eq : e₁ + e₂ - e₃ = (n : ℝ) * (ex + ey - δ / 2) := by
    dsimp [e₁, e₂, e₃]
    rw [hχ]
    ring
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hexp_le : e₁ + e₂ - e₃ ≤ -(n : ℝ) * (δ / 4) := by
    rw [hexp_eq]
    nlinarith [mul_le_mul_of_nonneg_left hslack hn_nonneg]
  have hpow_le :
      Real.rpow 2 (e₁ + e₂ - e₃) ≤ Real.rpow 2 (-(n : ℝ) * (δ / 4)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_le
  calc
    4 * Real.rpow 2 ((n : ℝ) * (χ - δ / 2)) *
          (Real.rpow 2 ((n : ℝ) * (cond + ex)) /
            ((1 - (1 / 2 : ℝ)) *
              Real.rpow 2 ((n : ℝ) * avg - (n : ℝ) * ey)))
        = 8 * Real.rpow 2 (e₁ + e₂ - e₃) := by
          change
            4 * Real.rpow 2 e₁ *
                (Real.rpow 2 e₂ / ((1 - (1 / 2 : ℝ)) * Real.rpow 2 e₃)) =
              8 * Real.rpow 2 (e₁ + e₂ - e₃)
          rw [hdiv_half]
          rw [show (4 : ℝ) * Real.rpow 2 e₁ *
                (2 * (Real.rpow 2 e₂ / Real.rpow 2 e₃)) =
              8 * (Real.rpow 2 e₁ * (Real.rpow 2 e₂ / Real.rpow 2 e₃)) by ring]
          rw [hpow_combine]
    _ ≤ 8 * Real.rpow 2 (-(n : ℝ) * (δ / 4)) :=
        mul_le_mul_of_nonneg_left hpow_le (by norm_num)

/-- Concrete HSW cross-exponent bound for an output ensemble.  The slack
budget is exactly the sum of the conditionally-typical dimension slack and the
source-projector product-mass slack. -/
theorem hsw_crossExponentBound_of_typicalitySlack
    {ι : Type u} {out : Type v} [Fintype ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (n : ℕ) (δ δx δc : ℝ)
    (hslack :
      δc + δx * ∑ x, |(E.states x).vonNeumann| +
          ((Fintype.card ι : ℝ) * (δx + δc)) *
            (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
              E.averageState).logTypicalitySlack ≤
        δ / 4) :
    4 * Real.rpow 2 ((n : ℝ) * (E.holevoInformation - δ / 2)) *
          (E.strongTypicalDimensionEnvelope n δx δc /
            ((1 - (1 / 2 : ℝ)) *
              QIT.FiniteDistribution.strongTypicalMassScale
                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution E.averageState)
                n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
        8 * Real.rpow 2 (-(n : ℝ) * (δ / 4)) := by
  let avg : ℝ := E.averageState.vonNeumann
  let cond : ℝ := ∑ x, (E.probs x : ℝ) * (E.states x).vonNeumann
  let ex : ℝ := δc + δx * ∑ x, |(E.states x).vonNeumann|
  let ey : ℝ :=
    ((Fintype.card ι : ℝ) * (δx + δc)) *
      (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
        E.averageState).logTypicalitySlack
  have hχ : E.holevoInformation = avg - cond := by
    dsimp [avg, cond]
    rw [Ensemble.holevoInformation_def]
  have hslack' : ex + ey ≤ δ / 4 := by
    dsimp [ex, ey]
    simpa [add_assoc] using hslack
  have h :=
    hsw_crossExponent_rpow_bound (n := n) (χ := E.holevoInformation) (avg := avg)
      (cond := cond) (ex := ex) (ey := ey) (δ := δ) hχ hslack'
  simpa [Ensemble.strongTypicalDimensionEnvelope, QIT.FiniteDistribution.strongTypicalMassScale,
    HSWPackingHypothesesSpectral.stateEigenvalueDistribution_shannonEntropy, avg, cond, ex, ey,
    add_assoc, mul_assoc] using h

/-- For every finite output ensemble and positive Holevo-rate gap, there are
positive typicality slacks making the HSW cross term uniformly exponentially
small in the blocklength. -/
theorem exists_hsw_crossExponentBound_slacks
    {ι : Type u} {out : Type v} [Fintype ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δx δc : ℝ, 0 < δx ∧ 0 < δc ∧
      ∀ n : ℕ,
        4 * Real.rpow 2 ((n : ℝ) * (E.holevoInformation - δ / 2)) *
            (E.strongTypicalDimensionEnvelope n δx δc /
              ((1 - (1 / 2 : ℝ)) *
                QIT.FiniteDistribution.strongTypicalMassScale
                  (HSWPackingHypothesesSpectral.stateEigenvalueDistribution E.averageState)
                  n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
          8 * Real.rpow 2 (-(n : ℝ) * (δ / 4)) := by
  let A : ℝ := ∑ x, |(E.states x).vonNeumann|
  let L : ℝ :=
    (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
      E.averageState).logTypicalitySlack
  let B : ℝ := (Fintype.card ι : ℝ) * L
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun x _ => abs_nonneg _
  have hL : 0 ≤ L := by
    dsimp [L]
    exact QIT.FiniteDistribution.logTypicalitySlack_nonneg
      (HSWPackingHypothesesSpectral.stateEigenvalueDistribution E.averageState)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le (Fintype.card ι)) hL
  obtain ⟨δx, δc, hδx, hδc, hbudget⟩ :=
    exists_pos_pair_linear_slack (A := A) (B := B) (δ := δ) hA hB hδ
  refine ⟨δx, δc, hδx, hδc, ?_⟩
  intro n
  refine hsw_crossExponentBound_of_typicalitySlack (E := E) (n := n) (δ := δ)
    (δx := δx) (δc := δc) ?_
  dsimp [A, B, L] at hbudget ⊢
  calc
    δc + δx * ∑ x, |(E.states x).vonNeumann| +
          ((Fintype.card ι : ℝ) * (δx + δc)) *
            (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
              E.averageState).logTypicalitySlack =
        δc + δx * ∑ x, |(E.states x).vonNeumann| +
          ((Fintype.card ι : ℝ) *
            (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
              E.averageState).logTypicalitySlack) *
            (δx + δc) := by ring
    _ ≤ δ / 4 := hbudget


end

end QIT
