/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.HSWDirect.WitnessAssembly

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v uEnsemble uMessage uAux uCodebook

noncomputable section

private def hswBasisState (α : Type uAux) [Fintype α] [DecidableEq α] [Nonempty α] :
    State α where
  matrix := Matrix.single (Classical.choice (inferInstance : Nonempty α))
    (Classical.choice (inferInstance : Nonempty α)) (1 : ℂ)
  pos := posSemidef_single (Classical.choice (inferInstance : Nonempty α))
  trace_eq_one := by
    rw [trace_single_one]
    simp

private def tensorPowerBasisState
    (α : Type uAux) [Fintype α] [DecidableEq α] [Nonempty α] :
    (n : ℕ) → State (TensorPower α n)
  | 0 => State.unit
  | n + 1 => (hswBasisState α).prod (tensorPowerBasisState α n)

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Block-channel achievability transports to the original channel with the
standard rate normalization.

For an `S`-rate code family for the block channel `N^{⊗ k}`, this theorem
constructs `S/k`-rate codes for `N`: for a large requested length `ℓ`, write
`ℓ = t*k + r`, use a `t`-use block-channel code, flatten it to `t*k` uses of
`N`, and right-pad the remaining `r` uses with a fixed input state.  The proof
keeps the padding rate loss explicit and absorbs it into the operational
achievability slack. -/
theorem hsw_blockChannelAchievable_transport [Nonempty a]
    (N : Channel a b) (k : ℕ) (hk : 0 < k) (S : ℝ)
    (hS : (Channel.IsAchievableClassicalRate.{u, v, uMessage} (N.tensorPower k)) S) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (S / (k : ℝ)) := by
  intro δ hδ ε hε
  have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hk
  let blockSlack : ℝ := (k : ℝ) * (δ / 4)
  have hblockSlack_pos : 0 < blockSlack := by
    dsimp [blockSlack]
    positivity
  obtain ⟨T0, hT0⟩ := hS blockSlack hblockSlack_pos ε hε
  by_cases htarget_nonpos : S / (k : ℝ) - δ ≤ 0
  · let L : ℕ := max T0 1
    refine ⟨(L + 1) * k, ?_⟩
    intro ℓ hℓ
    let t : ℕ := ℓ / k
    let r : ℕ := ℓ % k
    have hL1_le_t : L + 1 ≤ t := by
      dsimp [t]
      exact (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hℓ)
    have ht_pos : 0 < t := lt_of_lt_of_le (Nat.succ_pos L) hL1_le_t
    have hL_le_t : L ≤ t := (Nat.le_succ L).trans hL1_le_t
    have ht_ge_T0 : t ≥ T0 := (Nat.le_max_left T0 1).trans hL_le_t
    obtain ⟨M, hMfin, hMdec, hMnonempty, C, hrateC, herrC⟩ := hT0 t ht_ge_T0
    letI : Fintype M := hMfin
    letI : DecidableEq M := hMdec
    letI : Nonempty M := hMnonempty
    let tail : State (QIT.TensorPower a r) := tensorPowerBasisState a r
    let Cpad : HSWClassicalCode N (t * k + r) M := C.flattenBlock.padRight tail
    have hlen : t * k + r = ℓ := by
      dsimp [t, r]
      simpa [Nat.mul_comm] using Nat.div_add_mod ℓ k
    let Cfinal : HSWClassicalCode N ℓ M := Cpad.castLength hlen
    have hrate_final : Cfinal.rate ≥ S / (k : ℝ) - δ := by
      have hnonneg : 0 ≤ Cpad.rate := by
        dsimp [Cpad, HSWClassicalCode.rate]
        exact hswMessageRate.nonneg (M := M) (t * k + r)
      simpa [Cfinal] using (show Cpad.rate ≥ S / (k : ℝ) - δ by linarith)
    have herr_pad : Cpad.maxErrorAtMost ε := by
      dsimp [Cpad]
      exact (C.flattenBlock).padRight_maxErrorAtMost tail (C.flattenBlock_maxErrorAtMost herrC)
    have herr_final : Cfinal.maxErrorAtMost ε := by
      dsimp [Cfinal]
      exact Cpad.castLength_maxErrorAtMost hlen herr_pad
    exact ⟨M, inferInstance, inferInstance, inferInstance, Cfinal, hrate_final, herr_final⟩
  · let B : ℝ := S / (k : ℝ) - δ
    have hB_pos : 0 < B := lt_of_not_ge htarget_nonpos
    let X : ℝ := (4 * B) / (3 * δ)
    let L : ℕ := max T0 (Nat.ceil X)
    refine ⟨(L + 1) * k, ?_⟩
    intro ℓ hℓ
    let t : ℕ := ℓ / k
    let r : ℕ := ℓ % k
    have hL1_le_t : L + 1 ≤ t := by
      dsimp [t]
      exact (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hℓ)
    have ht_pos : 0 < t := lt_of_lt_of_le (Nat.succ_pos L) hL1_le_t
    have hL_le_t : L ≤ t := (Nat.le_succ L).trans hL1_le_t
    have ht_ge_T0 : t ≥ T0 := (Nat.le_max_left T0 (Nat.ceil X)).trans hL_le_t
    obtain ⟨M, hMfin, hMdec, hMnonempty, C, hrateC, herrC⟩ := hT0 t ht_ge_T0
    letI : Fintype M := hMfin
    letI : DecidableEq M := hMdec
    letI : Nonempty M := hMnonempty
    let tail : State (QIT.TensorPower a r) := tensorPowerBasisState a r
    let Cpad : HSWClassicalCode N (t * k + r) M := C.flattenBlock.padRight tail
    let A : ℝ := S / (k : ℝ) - δ / 4
    have hbase : A ≤ C.rate / (k : ℝ) := by
      have hdiv :
          (S - blockSlack) / (k : ℝ) ≤ C.rate / (k : ℝ) :=
        div_le_div_of_nonneg_right hrateC hkR_pos.le
      have hslack :
          (S - blockSlack) / (k : ℝ) = S / (k : ℝ) - δ / 4 := by
        dsimp [blockSlack]
        field_simp [ne_of_gt hkR_pos]
      simpa [A, hslack] using hdiv
    have hceil_le_t : Nat.ceil X ≤ t :=
      (Nat.le_max_right T0 (Nat.ceil X)).trans hL_le_t
    have hX_le_t : X ≤ (t : ℝ) := by
      exact (Nat.le_ceil X).trans (by exact_mod_cast hceil_le_t)
    have hcoeff_pos : 0 < (3 * δ / 4 : ℝ) := by positivity
    have hBt : B ≤ (3 * δ / 4) * (t : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hX_le_t (le_of_lt hcoeff_pos)
      have hcalc : (3 * δ / 4 : ℝ) * ((4 * B) / (3 * δ)) = B := by
        field_simp [ne_of_gt hδ]
      simpa [X, hcalc] using hmul
    have hr_le_k : (r : ℝ) ≤ (k : ℝ) := by
      have hr_lt : r < k := by
        dsimp [r]
        exact Nat.mod_lt ℓ hk
      exact_mod_cast le_of_lt hr_lt
    have hpadding_loss :
        B * (r : ℝ) ≤ (3 * δ / 4) * (t : ℝ) * (k : ℝ) := by
      have h1 : B * (r : ℝ) ≤ B * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hr_le_k hB_pos.le
      have h2 : B * (k : ℝ) ≤ ((3 * δ / 4) * (t : ℝ)) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hBt hkR_pos.le
      exact h1.trans h2
    have hden_pos : (0 : ℝ) < ((t * k + r : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_pos_left (Nat.mul_pos ht_pos hk) r
    have hratio :
        B ≤ A * (((t * k : ℕ) : ℝ) / ((t * k + r : ℕ) : ℝ)) := by
      rw [← mul_div_assoc]
      refine (le_div_iff₀ hden_pos).mpr ?_
      norm_num [Nat.cast_add, Nat.cast_mul]
      have hAeq : A = B + 3 * δ / 4 := by
        dsimp [A, B]
        ring
      calc
        B * ((t : ℝ) * (k : ℝ) + (r : ℝ)) =
            B * (r : ℝ) + B * ((t : ℝ) * (k : ℝ)) := by ring
        _ ≤ (3 * δ / 4) * (t : ℝ) * (k : ℝ) +
              B * ((t : ℝ) * (k : ℝ)) :=
            by
              have h := add_le_add_right hpadding_loss (B * ((t : ℝ) * (k : ℝ)))
              simpa [add_comm, add_left_comm, add_assoc] using h
        _ = (B + 3 * δ / 4) * ((t : ℝ) * (k : ℝ)) := by ring
        _ = A * ((t : ℝ) * (k : ℝ)) := by rw [hAeq]
    have hrate_final : Cpad.rate ≥ S / (k : ℝ) - δ := by
      dsimp [B] at hB_pos
      have hB_rate :
          B ≤ Cpad.rate := by
        dsimp [Cpad]
        exact C.flattenBlock_padRight_rate_ge_of_ratio tail ht_pos hk hbase hratio
      simpa [B] using hB_rate
    have herr_final : Cpad.maxErrorAtMost ε := by
      dsimp [Cpad]
      exact (C.flattenBlock).padRight_maxErrorAtMost tail (C.flattenBlock_maxErrorAtMost herrC)
    have hlen : t * k + r = ℓ := by
      dsimp [t, r]
      simpa [Nat.mul_comm] using Nat.div_add_mod ℓ k
    let Cfinal : HSWClassicalCode N ℓ M := Cpad.castLength hlen
    have hrate_final' : Cfinal.rate ≥ S / (k : ℝ) - δ := by
      simpa [Cfinal] using hrate_final
    have herr_final' : Cfinal.maxErrorAtMost ε := by
      dsimp [Cfinal]
      exact Cpad.castLength_maxErrorAtMost hlen herr_final
    exact ⟨M, inferInstance, inferInstance, inferInstance, Cfinal, hrate_final', herr_final'⟩

/-- Regularized HSW direct achievability with the block-channel transport
obligation discharged by `hsw_blockChannelAchievable_transport`.

This is the block-to-regularized bridge: once every positive block channel has
ensemble-specific HSW direct coding at its one-letter Holevo rate, the
regularized direct half for the original channel follows. -/
theorem hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblockEnsemble :
      ∀ n : ℕ, 0 < n →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E : Ensemble ι (QIT.TensorPower a n),
            (Channel.IsAchievableClassicalRate.{u, v, uMessage} (N.tensorPower n))
              ((N.tensorPower n).hswHolevoRate E)) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R :=
  N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses
    (fun n hn S hS => N.hsw_blockChannelAchievable_transport n hn S hS)
    hblockEnsemble

/-- HSW regularized direct achievability from source-shaped spectral packing
families for every block channel.

For every block size `k`, finite input ensemble for `N^{⊗ k}`, slack `δ`, and
target error `ε`, the hypothesis supplies the eventual spectral packing bundle
needed by `hsw_directWitnessAssembly_from_spectralPackingHypotheses` for the
block channel.  The theorem then performs both remaining assembly steps:
ensemble-specific direct coding for each block channel and the
block-to-base rate-normalization transport. -/
theorem hsw_regularized_direct_of_blockSpectralPackingHypotheses
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∃ (M : Type uMessage), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
                    ∃ (_ : Nonempty M),
                      ∃ (𝒳 : Type uCodebook), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                        ∃ (Eout :
                            Ensemble 𝒳 (QIT.TensorPower (QIT.TensorPower b k) n)),
                          ∃ (typicalitySlack : ℝ),
                            ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                              ∃ (φ :
                                  𝒳 → State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                (∀ x,
                                    ((N.tensorPower k).tensorPower n).applyState (φ x) =
                                      Eout.states x) ∧
                                  hswMessageRate M n ≥
                                    (N.tensorPower k).hswHolevoRate E₀ - δ / 2 ∧
                                    2 * (H.ε + 2 * Real.sqrt H.ε) +
                                        4 * ((Fintype.card M : ℝ) - 1) *
                                          (H.d / H.D) ≤
                                      ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_spectralPackingHypotheses E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel spectral packing
estimates, with the finite message set chosen internally at every coding block
length.

This theorem is the strict direct-achievability assembly point closest to the
remaining source proof obligations: the caller supplies the asymptotic HSW
typical/packing estimates for the message type selected by the rate lemma, and
this theorem performs message-size choice, packing/expurgation assembly,
block-channel ensemble coding, and block-to-base rate normalization. -/
theorem hsw_regularized_direct_of_blockSpectralPackingEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (𝒳 : Type uCodebook), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                        ∃ (Eout :
                            Ensemble 𝒳 (QIT.TensorPower (QIT.TensorPower b k) n)),
                          ∃ (typicalitySlack : ℝ),
                            ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                              ∃ (φ :
                                  𝒳 → State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                (∀ x,
                                    ((N.tensorPower k).tensorPower n).applyState (φ x) =
                                      Eout.states x) ∧
                                  2 * (H.ε + 2 * Real.sqrt H.ε) +
                                      4 * ((Fintype.card M : ℝ) - 1) *
                                        (H.d / H.D) ≤
                                    ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_spectralPackingEstimates E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel diagonal
strong-typical packing estimates.

This is the highest direct-achievability assembly point available for the
source-shaped diagonal route formalized in `ConditionalTypicality.lean`.  For
each positive block size `k`, the caller supplies the diagonal/pinched strong
typical estimates for the block channel `N^{⊗ k}`; this theorem then applies
the one-block diagonal assembly theorem and the already-proved
block-to-base-channel rate normalization.

The statement deliberately keeps the diagonal/pinching and asymptotic
typical-estimate family explicit.  It does not identify the diagonal
strong-typical projector with the legacy spectral projector, and it does not
pretend that arbitrary quantum output ensembles have already been reduced to
the pinched classical kernel. -/
theorem hsw_regularized_direct_of_blockDiagonalPackingEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (𝒳 : Type uCodebook), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                              ∃ (Eout :
                                  Ensemble 𝒳 (QIT.TensorPower (QIT.TensorPower b k) n)),
                                ∃ (codewordOf : 𝒳 → Fin n → α),
                                  ∃ (φ :
                                      𝒳 →
                                        State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                    ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                      ∃ (d : ℝ), ∃ (D : ℝ),
                                        ∃ (Px :
                                            𝒳 →
                                              CMatrix
                                                (QIT.TensorPower
                                                  (QIT.TensorPower b k) n)),
                                          0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                            (∀ x,
                                              (Eout.states x).matrix =
                                                (HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                                  K
                                                  (codewordOf x)).matrix) ∧
                                            (∀ x,
                                              ClassicalTypicality.StrongTypical p
                                                (codewordOf x) δx) ∧
                                            (Fintype.card α : ℝ) *
                                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                            (∀ x,
                                              (Px x).PosSemidef ∧ Px x * Px x = Px x ∧
                                                Px x ≤ 1) ∧
                                            (∀ x,
                                              1 - packingε ≤
                                                ((Px x * (Eout.states x).matrix).trace).re) ∧
                                            (∀ x, ((Px x).trace).re ≤ d) ∧
                                            (HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                                  (ClassicalTypicality.inducedMarginal p K)
                                                  n
                                                  ((Fintype.card α : ℝ) * (δx + δc)) *
                                                Eout.averageState.matrix *
                                                HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                                  (ClassicalTypicality.inducedMarginal p K)
                                                  n
                                                  ((Fintype.card α : ℝ) * (δx + δc))
                                                ≤ ((D : ℝ)⁻¹) •
                                                  HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                                    (ClassicalTypicality.inducedMarginal p K)
                                                    n
                                                    ((Fintype.card α : ℝ) * (δx + δc))) ∧
                                            (∀ x,
                                              ((N.tensorPower k).tensorPower n).applyState
                                                  (φ x) =
                                                Eout.states x) ∧
                                            2 * (packingε + 2 * Real.sqrt packingε) +
                                                4 * ((Fintype.card M : ℝ) - 1) * (d / D) ≤
                                              ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_diagonalPackingEstimates E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
strong-typical packing estimates.

This is the regularized direct-achievability entry point for the source-shaped
post-pinching/pruned-distribution route: for every positive block channel
`N^{⊗ k}`, finite input ensemble, and sufficiently large random-coding block
length, the caller supplies the pruned conditional-product estimates.  The
proved pruned pack-4 bridge supplies the projected-average Loewner bound, the
one-block HSW assembly supplies an achievable block-channel Holevo rate, and
the block-transport theorem normalizes the rate back to the original channel.

The theorem still keeps the genuinely asymptotic HSW estimates explicit:
typical-codeword selection, conditionally-typical projectors, marginal-product
mass envelopes, physical output realizations, and final packing-error
inequality are not hidden or replaced by placeholders. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalPackingEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                                    ∃ (Px :
                                        (Fin n → α) →
                                          CMatrix
                                            (QIT.TensorPower
                                              (QIT.TensorPower b k) n)),
                                      0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                        pruneε < 1 ∧
                                        (∀ x : Fin n → α,
                                          Eout.states x =
                                            HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                              K x) ∧
                                        (∀ x : Fin n → α,
                                          ClassicalTypicality.StrongTypical p x δx) ∧
                                        (Fintype.card α : ℝ) *
                                            (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                            ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                        (∀ x : Fin n → α,
                                          (Px x).PosSemidef ∧ Px x * Px x = Px x ∧
                                            Px x ≤ 1) ∧
                                        (∀ x : Fin n → α,
                                          1 - packingε ≤
                                            ((Px x * (Eout.states x).matrix).trace).re) ∧
                                        (∀ x : Fin n → α, ((Px x).trace).re ≤ d) ∧
                                        (∀ zseq : Fin n → QIT.TensorPower b k,
                                          ClassicalTypicality.StrongTypical
                                              (ClassicalTypicality.inducedMarginal p K)
                                              zseq
                                              ((Fintype.card α : ℝ) * (δx + δc)) →
                                            (HSWPackingHypothesesSpectral.marginalProductMass
                                              (ClassicalTypicality.inducedMarginal p K)
                                              zseq : ℝ) ≤ D⁻¹) ∧
                                        (∀ x : Fin n → α,
                                          (Eout.probs x : ℝ) ≤
                                            (1 - pruneε)⁻¹ *
                                              ∏ i, (p.prob (x i) : ℝ)) ∧
                                        (∀ x : Fin n → α,
                                          ((N.tensorPower k).tensorPower n).applyState
                                              (φ x) =
                                            Eout.states x) ∧
                                        2 * (packingε + 2 * Real.sqrt packingε) +
                                            4 * ((Fintype.card M : ℝ) - 1) *
                                              (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalPackingEstimates E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
conditionally-typical projector estimates.

Compared with `hsw_regularized_direct_of_blockPrunedDiagonalPackingEstimates`,
this entry point no longer asks the caller to construct arbitrary per-codeword
projectors.  It instantiates the projectors as the conditionally typical
subspace projectors and consumes the source-shaped second-moment and dimension
estimates instead.  The remaining explicit assumptions are precisely the
unproved asymptotic HSW ingredients that are not part of this bridge:
strong-typical codewords, marginal-product mass envelope, pruned distribution
domination, physical output realization, and the final packing-error
inequality. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalProjectorEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                      pruneε < 1 ∧
                                      (∀ x : Fin n → α,
                                        Eout.states x =
                                          HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                            K x) ∧
                                      (∀ x : Fin n → α,
                                        ClassicalTypicality.StrongTypical p x δx) ∧
                                      (Fintype.card α : ℝ) *
                                          (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                      (∀ x : Fin n → α,
                                        conditionalLogDeviationSecondMoment
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i))) /
                                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                      (∀ x : Fin n → α,
                                        conditionallyTypicalSubspaceDimension
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i)))
                                            δc ≤ d) ∧
                                      (∀ zseq : Fin n → QIT.TensorPower b k,
                                        ClassicalTypicality.StrongTypical
                                            (ClassicalTypicality.inducedMarginal p K)
                                            zseq
                                            ((Fintype.card α : ℝ) * (δx + δc)) →
                                          (HSWPackingHypothesesSpectral.marginalProductMass
                                            (ClassicalTypicality.inducedMarginal p K)
                                            zseq : ℝ) ≤ D⁻¹) ∧
                                      (∀ x : Fin n → α,
                                        (Eout.probs x : ℝ) ≤
                                          (1 - pruneε)⁻¹ *
                                            ∏ i, (p.prob (x i) : ℝ)) ∧
                                      (∀ x : Fin n → α,
                                        ((N.tensorPower k).tensorPower n).applyState
                                            (φ x) =
                                          Eout.states x) ∧
                                      2 * (packingε + 2 * Real.sqrt packingε) +
                                          4 * ((Fintype.card M : ℝ) - 1) *
                                            (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalProjectorEstimates E₀
    (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
conditionally-typical projector estimates with the pack-4 mass bound discharged
by the finite classical entropy envelope.

This is the current source-shaped direct-achievability assembly point for the
diagonal/pruned route: the caller supplies the HSW asymptotic estimates and the
explicit entropy-exponent choice of `D`; the theorem derives the word-level
product-mass envelope, constructs the packing hypotheses, and transports the
block-channel codes back to the original channel. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalProjectorEntropyEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                      pruneε < 1 ∧
                                      (∀ x : Fin n → α,
                                        Eout.states x =
                                          HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                            K x) ∧
                                      (∀ x : Fin n → α,
                                        ClassicalTypicality.StrongTypical p x δx) ∧
                                      (Fintype.card α : ℝ) *
                                          (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                      (∀ x : Fin n → α,
                                        conditionalLogDeviationSecondMoment
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i))) /
                                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                      (∀ x : Fin n → α,
                                        conditionallyTypicalSubspaceDimension
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i)))
                                            δc ≤ d) ∧
                                      Real.rpow 2
                                        (- (n : ℝ) *
                                            (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
                                          (n : ℝ) * ((Fintype.card α : ℝ) * (δx + δc)) *
                                            (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
                                          ≤ D⁻¹ ∧
                                      (∀ x : Fin n → α,
                                        (Eout.probs x : ℝ) ≤
                                          (1 - pruneε)⁻¹ *
                                            ∏ i, (p.prob (x i) : ℝ)) ∧
                                      (∀ x : Fin n → α,
                                        ((N.tensorPower k).tensorPower n).applyState
                                            (φ x) =
                                          Eout.states x) ∧
                                      2 * (packingε + 2 * Real.sqrt packingε) +
                                          4 * ((Fintype.card M : ℝ) - 1) *
                                            (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyEstimates
    E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
projector estimates, with both pack-3 and pack-4 supplied by finite classical
typicality envelopes.

This is stronger than
`hsw_regularized_direct_of_blockPrunedDiagonalProjectorEntropyEstimates`: it no
longer requires a separate conditionally-typical-subspace dimension estimate in
the block-channel hypothesis.  The dimension term in the final packing-error
bound is the named value
`hswConditionalDiagonalDimensionEnvelope p K n δx δc`, derived from codeword
strong typicality. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalProjectorEntropyDimensionEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (D : ℝ), ∃ (pruneε : ℝ),
                                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                      pruneε < 1 ∧
                                      (∀ x : Fin n → α,
                                        Eout.states x =
                                          HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                            K x) ∧
                                      (∀ x : Fin n → α,
                                        ClassicalTypicality.StrongTypical p x δx) ∧
                                      (Fintype.card α : ℝ) *
                                          (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                      (∀ x : Fin n → α,
                                        conditionalLogDeviationSecondMoment
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i))) /
                                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                      Real.rpow 2
                                        (- (n : ℝ) *
                                            (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
                                          (n : ℝ) * ((Fintype.card α : ℝ) * (δx + δc)) *
                                            (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
                                          ≤ D⁻¹ ∧
                                      (∀ x : Fin n → α,
                                        (Eout.probs x : ℝ) ≤
                                          (1 - pruneε)⁻¹ *
                                            ∏ i, (p.prob (x i) : ℝ)) ∧
                                      (∀ x : Fin n → α,
                                        ((N.tensorPower k).tensorPower n).applyState
                                            (φ x) =
                                          Eout.states x) ∧
                                      2 * (packingε + 2 * Real.sqrt packingε) +
                                          4 * ((Fintype.card M : ℝ) - 1) *
                                            (hswConditionalDiagonalDimensionEnvelope
                                                p K n δx δc /
                                              ((1 - pruneε) * D)) ≤ ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyDimensionEstimates
    E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel pruned diagonal
projector estimates with the canonical marginal-product mass scale chosen
internally.

This is the current strongest regularized direct-assembly interface in this
file: the caller supplies the HSW asymptotic random-coding/pruning estimates,
while pack-3's dimension envelope, pack-4's product-mass scale `D`, the
packing/expurgation assembly, and block-to-base rate normalization are all
proved here. -/
theorem hsw_regularized_direct_of_blockPrunedDiagonalProjectorTypicalityScaleEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (Eout :
                                Ensemble (Fin n → α)
                                  (QIT.TensorPower (QIT.TensorPower b k) n)),
                              ∃ (φ :
                                  (Fin n → α) →
                                    State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                                  ∃ (pruneε : ℝ),
                                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                                      pruneε < 1 ∧
                                      (∀ x : Fin n → α,
                                        Eout.states x =
                                          HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                            K x) ∧
                                      (∀ x : Fin n → α,
                                        ClassicalTypicality.StrongTypical p x δx) ∧
                                      (Fintype.card α : ℝ) *
                                          (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                      (∀ x : Fin n → α,
                                        conditionalLogDeviationSecondMoment
                                            (fun i : Fin n =>
                                              Classical.diagonalState
                                                (K.prob (x i)) (K.sum_eq_one (x i))) /
                                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                      (∀ x : Fin n → α,
                                        (Eout.probs x : ℝ) ≤
                                          (1 - pruneε)⁻¹ *
                                            ∏ i, (p.prob (x i) : ℝ)) ∧
                                      (∀ x : Fin n → α,
                                        ((N.tensorPower k).tensorPower n).applyState
                                            (φ x) =
                                          Eout.states x) ∧
                                      2 * (packingε + 2 * Real.sqrt packingε) +
                                          4 * ((Fintype.card M : ℝ) - 1) *
                                            (hswConditionalDiagonalDimensionEnvelope
                                                p K n δx δc /
                                              ((1 - pruneε) *
                                                (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                                  n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                            ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact (N.tensorPower k).hsw_directWitnessAssembly_from_prunedDiagonalProjectorTypicalityScaleEstimates
    E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from block-channel strongly-typical
pruned codebook estimates.

This is the regularized counterpart of
`hsw_directWitnessAssembly_from_strongTypicalCodebookProjectorTypicalityScaleEstimates`.
It removes the impossible full-word assumption
`∀ x : Fin n → α, StrongTypical p x δx` from the block-level interface:
the random-coding index type is the strongly-typical subtype, while the
remaining independent source obligations are kept explicit. -/
theorem hsw_regularized_direct_of_blockStrongTypicalCodebookProjectorTypicalityScaleEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                              ∃ (Eout :
                                  Ensemble
                                    (ClassicalTypicality.StrongTypicalWord p n δx)
                                    (QIT.TensorPower (QIT.TensorPower b k) n)),
                                ∃ (φ :
                                    ClassicalTypicality.StrongTypicalWord p n δx →
                                      State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                  0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                                    (∀ x,
                                      (Eout.states x).matrix =
                                        (HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                          K
                                          (ClassicalTypicality.StrongTypicalWord.codeword
                                            p δx x)).matrix) ∧
                                    (Fintype.card α : ℝ) *
                                        (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                        ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                    (∀ x,
                                      conditionalLogDeviationSecondMoment
                                          (fun i : Fin n =>
                                            Classical.diagonalState
                                              (K.prob
                                                (ClassicalTypicality.StrongTypicalWord.codeword
                                                  p δx x i))
                                              (K.sum_eq_one
                                                (ClassicalTypicality.StrongTypicalWord.codeword
                                                  p δx x i))) /
                                        ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                    (HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                          (ClassicalTypicality.inducedMarginal p K)
                                          n
                                          ((Fintype.card α : ℝ) * (δx + δc)) *
                                        Eout.averageState.matrix *
                                        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                          (ClassicalTypicality.inducedMarginal p K)
                                          n
                                          ((Fintype.card α : ℝ) * (δx + δc))
                                        ≤
                                          (((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                              n ((Fintype.card α : ℝ) * (δx + δc))) : ℝ)⁻¹ •
                                            HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                              (ClassicalTypicality.inducedMarginal p K)
                                              n
                                              ((Fintype.card α : ℝ) * (δx + δc))) ∧
                                    (∀ x,
                                      ((N.tensorPower k).tensorPower n).applyState
                                          (φ x) =
                                        Eout.states x) ∧
                                    2 * (packingε + 2 * Real.sqrt packingε) +
                                        4 * ((Fintype.card M : ℝ) - 1) *
                                          (hswConditionalDiagonalDimensionEnvelope
                                              p K n δx δc /
                                            ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                              n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                          ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_strongTypicalCodebookProjectorTypicalityScaleEstimates
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from canonical pruned strongly-typical
codebook estimates.

This is the strongest currently proved direct-achievability assembly theorem in
this module.  Compared with
`hsw_regularized_direct_of_blockStrongTypicalCodebookProjectorTypicalityScaleEstimates`,
the projected-average pack-4 hypothesis has been eliminated: it is derived from
the canonical pruned i.i.d. distribution on the strongly-typical subtype, and
the resulting effective denominator contains the source's `(1 - pruneε)`
factor. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalCodebookProjectorTypicalityScaleEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                              ∃ (pruneε : ℝ),
                                ∃ (hmass_pos :
                                    0 < ClassicalTypicality.strongTypicalMass
                                      (n := n) p δx),
                                  ∃ (Eout :
                                      Ensemble
                                        (ClassicalTypicality.StrongTypicalWord p n δx)
                                        (QIT.TensorPower (QIT.TensorPower b k) n)),
                                    ∃ (φ :
                                        ClassicalTypicality.StrongTypicalWord p n δx →
                                          State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                      0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                                        pruneε < 1 ∧
                                        (1 - pruneε : ℝ) ≤
                                          (ClassicalTypicality.strongTypicalMass
                                            (n := n) p δx : ℝ) ∧
                                        (∀ x,
                                          Eout.probs x =
                                            (ClassicalTypicality.prunedStrongTypicalDistribution
                                              p δx hmass_pos).prob x) ∧
                                        (∀ x,
                                          Eout.states x =
                                            HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                              K
                                              (ClassicalTypicality.StrongTypicalWord.codeword
                                                p δx x)) ∧
                                        (Fintype.card α : ℝ) *
                                            (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                            ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                        (∀ x,
                                          conditionalLogDeviationSecondMoment
                                              (fun i : Fin n =>
                                                Classical.diagonalState
                                                  (K.prob
                                                    (ClassicalTypicality.StrongTypicalWord.codeword
                                                      p δx x i))
                                                  (K.sum_eq_one
                                                    (ClassicalTypicality.StrongTypicalWord.codeword
                                                      p δx x i))) /
                                            ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                        (∀ x,
                                          ((N.tensorPower k).tensorPower n).applyState
                                              (φ x) =
                                            Eout.states x) ∧
                                        2 * (packingε + 2 * Real.sqrt packingε) +
                                            4 * ((Fintype.card M : ℝ) - 1) *
                                              (hswConditionalDiagonalDimensionEnvelope
                                                  p K n δx δc /
                                                ((1 - pruneε) *
                                                  (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                                    n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                              ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleEstimates
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- HSW regularized direct achievability from canonical pruned strongly-typical
codebook bounds, with the pruned output ensemble constructed internally.

This is the regularized form of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleBounds`.
The block-level hypothesis now contains only the mathematical estimates that
are still genuinely external to this assembly layer: typical-set mass,
conditional log-deviation, physical output realization, and final numerical
packing exponent. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalCodebookProjectorTypicalityScaleBounds
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                        ∃ (p : QIT.FiniteDistribution α),
                          ∃ (K : QIT.StochasticKernel α (QIT.TensorPower b k)),
                            ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                              ∃ (pruneε : ℝ),
                                ∃ (φ :
                                    ClassicalTypicality.StrongTypicalWord p n δx →
                                      State (QIT.TensorPower (QIT.TensorPower a k) n)),
                                  0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                                    pruneε < 1 ∧
                                    (1 - pruneε : ℝ) ≤
                                      (ClassicalTypicality.strongTypicalMass
                                        (n := n) p δx : ℝ) ∧
                                    (Fintype.card α : ℝ) *
                                        (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                        ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                    (∀ x,
                                      conditionalLogDeviationSecondMoment
                                          (fun i : Fin n =>
                                            Classical.diagonalState
                                              (K.prob
                                                (ClassicalTypicality.StrongTypicalWord.codeword
                                                  p δx x i))
                                              (K.sum_eq_one
                                                (ClassicalTypicality.StrongTypicalWord.codeword
                                                  p δx x i))) /
                                        ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                                    (∀ x,
                                      ((N.tensorPower k).tensorPower n).applyState
                                          (φ x) =
                                        HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                          K
                                          (ClassicalTypicality.StrongTypicalWord.codeword
                                            p δx x)) ∧
                                    2 * (packingε + 2 * Real.sqrt packingε) +
                                        4 * ((Fintype.card M : ℝ) - 1) *
                                          (hswConditionalDiagonalDimensionEnvelope
                                              p K n δx δc /
                                            ((1 - pruneε) *
                                              (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                                n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                          ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleBounds
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct-achievability from source-shaped spectral estimates
for the canonical pruned strongly-typical codebook with actual quantum outputs.

This is the regularized/block-channel lift of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSpectralEstimates`.
It removes the older diagonal-output realization hypothesis from the HSW direct
route: for each block ensemble of `N^{⊗ k}`, the random codebook is the
strongly-typical subtype of the induced input law and the encoder is the actual
product input state.  The remaining assumptions are exactly the still-external
asymptotic estimates for pack-1 cross-capture, conditional log-deviation, and
the final packing-error exponent. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSpectralEstimates
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (δx : ℝ), ∃ (δavg : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 ≤ δx ∧ 0 < δavg ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (1 - pruneε : ℝ) ≤
                              (ClassicalTypicality.strongTypicalMass
                                (n := n)
                                ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                δx : ℝ) ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              1 - packingε ≤
                                ((((N.tensorPower k).outputEnsemble E₀).averageState.typicalSubspaceProjector
                                    n δavg) *
                                  (productState fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)).matrix).trace.re) ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) +
                                4 * ((Fintype.card M : ℝ) - 1) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      Real.rpow 2
                                        ((n : ℝ) *
                                            ((N.tensorPower k).outputEnsemble E₀).averageState.vonNeumann -
                                          (n : ℝ) * δavg))) ≤
                                  ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSpectralEstimates
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability from source-projector packing bounds
for the canonical pruned strongly-typical codebook with actual quantum outputs.

This is the block-channel lift of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds`.
It keeps the remaining asymptotic estimates explicit but no longer asks the
caller for the legacy arbitrary spectral projector slack `δavg`: the average
projector is the source-shaped eigenbasis typical projector of the block
average output state, with denominator given by the canonical eigenvalue
strong-typical mass scale. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorBounds
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (1 - pruneε : ℝ) ≤
                              (ClassicalTypicality.strongTypicalMass
                                (n := n)
                                ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                δx : ℝ) ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) +
                                4 * ((Fintype.card M : ℝ) - 1) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 2) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds
    (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability from source-projector packing bounds
with the final packing-error estimate split into self-error and cross-error
components.

This is the block-channel lift of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorComponentBounds`.
It is the preferred staging point for the remaining asymptotic HSW direct
proof: the codebook/source-projector construction has been internalized, and
the caller must now prove only the genuine large-block estimates for typical
mass, conditional log-deviation, self-error, and cross-error. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorComponentBounds
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (1 - pruneε : ℝ) ≤
                              (ClassicalTypicality.strongTypicalMass
                                (n := n)
                                ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                δx : ℝ) ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                            4 * ((Fintype.card M : ℝ) - 1) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 4) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact
    Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorComponentBounds
      (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability from source-projector packing bounds
with the input strongly-typical mass discharged by its finite Chebyshev bound.

Compared with
`hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorComponentBounds`,
the block hypothesis no longer contains the strongly-typical codebook mass
lower bound.  It is replaced by the explicit large-block condition
`|X|/(nδ_x²) ≤ pruneε`. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassBounds
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤
                              pruneε ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                            4 * ((Fintype.card M : ℝ) - 1) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 4) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact
    Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassBounds
      (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability from source-projector packing bounds
with both finite strong-typical mass and source-shaped message-cardinality
rate accounting discharged.

This is the block-channel lift of
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound`.
It is the strongest assembly point in this file: after the caller proves the
remaining source estimates for conditional log-deviation, self-error, and the
cross exponent with the factor `2^{n(χ-δ/2)}`, this theorem performs the
message-set choice, packing/expurgation, block-channel coding, and
block-to-base-channel rate normalization. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      (Fintype.card M : ℝ) - 1 ≤
                        Real.rpow 2
                          ((n : ℝ) * ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤
                              pruneε ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x :
                                ClassicalTypicality.StrongTypicalWord
                                  ((N.tensorPower k).outputEnsemble E₀).indexDistribution
                                  n δx,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    ((N.tensorPower k).outputEnsemble E₀).states
                                      (ClassicalTypicality.StrongTypicalWord.codeword
                                        (((N.tensorPower k).outputEnsemble E₀).indexDistribution)
                                        δx x i)) /
                                ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                            4 * Real.rpow 2
                                  ((n : ℝ) *
                                    ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 4) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine N.hsw_regularized_direct_of_blockChannelEnsembleWitnesses_transport ?_
  intro k hk ι hιF hιD E₀
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  exact
    Channel.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound
      (N.tensorPower k) E₀ (hblock k hk ι inferInstance inferInstance E₀)

/-- Regularized HSW direct achievability with the conditional log-deviation
estimate discharged by the finite ensemble second-moment envelope.

Compared with
`hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound`,
the block hypothesis no longer asks for a pointwise second-moment bound for
every strongly-typical codeword.  The proved non-iid product variance identity
in `ConditionalTypicality.lean` shows that every codeword product has centered
log-deviation second moment bounded by
`n * E.logDeviationSecondMomentEnvelope`; the caller only supplies the resulting
large-block ratio bound.  The older cardinal-dimensional moment condition is
still explicit at this stage and is removed by a later source-estimate layer. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardMomentEnvelope
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      (Fintype.card M : ℝ) - 1 ≤
                        Real.rpow 2
                          ((n : ℝ) * ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                          0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            pruneε < 1 ∧
                            (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤
                              pruneε ∧
                            (Fintype.card ι : ℝ) *
                                (Fintype.card (QIT.TensorPower b k) : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (((N.tensorPower k).outputEnsemble E₀).logDeviationSecondMomentEnvelope /
                                ((n : ℝ) * δc ^ 2) ≤ packingε) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                            4 * Real.rpow 2
                                  ((n : ℝ) *
                                    ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                                  (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                      n δx δc /
                                    ((1 - pruneε) *
                                      QIT.FiniteDistribution.strongTypicalMassScale
                                        (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                          ((N.tensorPower k).outputEnsemble E₀).averageState)
                                        n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                  ε / 4) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound
      ?_
  intro k hk ι hιF hιD E₀ δ hδ ε hε
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  obtain ⟨N0, hN0⟩ := hblock k hk ι inferInstance inferInstance E₀ δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hnN0
  obtain ⟨hn_pos, hn_small, hM⟩ := hN0 n hnN0
  refine ⟨hn_pos, hn_small, ?_⟩
  intro M hMF hMD hMne hrate hcard
  letI : Fintype M := hMF
  letI : DecidableEq M := hMD
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpack_nonneg, hprune_lt,
      hprune_mass, hcardMoment, hmoment, hself, hcross⟩ :=
    hM M inferInstance inferInstance hMne hrate hcard
  refine ⟨δx, δc, packingε, pruneε, hδx, hδc, hpack_nonneg, hprune_lt,
    hprune_mass, hcardMoment, ?_, hself, hcross⟩
  intro x
  exact
    (((N.tensorPower k).outputEnsemble E₀).conditionalLogDeviationSecondMoment_codeword_ratio_le_of_envelope
      (fun i : Fin n =>
        ClassicalTypicality.StrongTypicalWord.codeword
          (((N.tensorPower k).outputEnsemble E₀).indexDistribution) δx x i)
      hn_pos hδc hmoment)

/-- Regularized HSW direct achievability with the self-error parameter fixed
explicitly from the requested error tolerance.

This removes the ad hoc `packingε` and `pruneε` choices from the block
hypothesis.  The caller now proves only the large-block source estimates using
the concrete choices `packingε = hswSelfPackingEpsilon ε` and `pruneε = 1/2`. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardMomentEnvelopeFixedSelfError
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
                0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      (Fintype.card M : ℝ) - 1 ≤
                        Real.rpow 2
                          ((n : ℝ) * ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) →
                      ∃ (δx : ℝ), ∃ (δc : ℝ),
                        0 < δx ∧ 0 < δc ∧
                          (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤
                            (1 / 2 : ℝ) ∧
                          (Fintype.card ι : ℝ) *
                              (Fintype.card (QIT.TensorPower b k) : ℝ) /
                              ((n : ℝ) * δc ^ 2) ≤ hswSelfPackingEpsilon ε ∧
                          (((N.tensorPower k).outputEnsemble E₀).logDeviationSecondMomentEnvelope /
                              ((n : ℝ) * δc ^ 2) ≤ hswSelfPackingEpsilon ε) ∧
                          4 * Real.rpow 2
                                ((n : ℝ) *
                                  ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                                (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                    n δx δc /
                                  ((1 - (1 / 2 : ℝ)) *
                                    QIT.FiniteDistribution.strongTypicalMassScale
                                      (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                        ((N.tensorPower k).outputEnsemble E₀).averageState)
                                      n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                                ε / 4) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardMomentEnvelope
      ?_
  intro k hk ι hιF hιD E₀ δ hδ ε hε
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  obtain ⟨N0, hN0⟩ := hblock k hk ι inferInstance inferInstance E₀ δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hnN0
  obtain ⟨hn_pos, hn_small, hM⟩ := hN0 n hnN0
  refine ⟨hn_pos, hn_small, ?_⟩
  intro M hMF hMD hMne hrate hcard
  letI : Fintype M := hMF
  letI : DecidableEq M := hMD
  obtain ⟨δx, δc, hδx, hδc, hprune_mass, hcardMoment, hmoment, hcross⟩ :=
    hM M inferInstance inferInstance hMne hrate hcard
  refine ⟨δx, δc, hswSelfPackingEpsilon ε, (1 / 2 : ℝ), hδx, hδc,
    hswSelfPackingEpsilon_nonneg hε, ?_, hprune_mass, hcardMoment, hmoment,
    hswSelfPackingEpsilon_self_bound hε, ?_⟩
  · norm_num
  · simpa using hcross

/-- Regularized HSW direct achievability after the inverse-square large-block
estimates have been discharged.

For fixed positive typicality slacks `δx, δc`, the prune-mass, finite
cardinality moment, and log-deviation moment conditions are all of the form
`C/(n δ²) ≤ η`; this theorem proves those eventually from
`exists_nat_real_div_mul_sq_le`.  The only remaining source estimate supplied by
the caller is the final cross exponent, which carries the actual Holevo-rate
gap. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFixedSlackCrossEstimate
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
              ∃ (δx : ℝ), ∃ (δc : ℝ), 0 < δx ∧ 0 < δc ∧
                ∃ Ncross : ℕ, ∀ n : ℕ, n ≥ Ncross →
                  ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M)
                    (_ : Nonempty M),
                    hswMessageRate M n ≥
                        (N.tensorPower k).hswHolevoRate E₀ - δ / 2 →
                      (Fintype.card M : ℝ) - 1 ≤
                        Real.rpow 2
                          ((n : ℝ) * ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) →
                        4 * Real.rpow 2
                              ((n : ℝ) *
                                ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                              (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                                  n δx δc /
                                ((1 - (1 / 2 : ℝ)) *
                                  QIT.FiniteDistribution.strongTypicalMassScale
                                    (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                      ((N.tensorPower k).outputEnsemble E₀).averageState)
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                              ε / 4) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardMomentEnvelopeFixedSelfError
      ?_
  intro k hk ι hιF hιD E₀ δ hδ ε hε
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  obtain ⟨δx, δc, hδx, hδc, Ncross, hcross⟩ :=
    hblock k hk ι inferInstance inferInstance E₀ δ hδ ε hε
  obtain ⟨Nsmall, hNsmall⟩ :=
    exists_nat_real_div_mul_sq_le (C := (1 : ℝ)) (η := δ / 2) (δ := (1 : ℝ))
      (by positivity) (by norm_num)
  obtain ⟨Nprune, hNprune⟩ :=
    exists_nat_real_div_mul_sq_le (C := (Fintype.card ι : ℝ)) (η := (1 / 2 : ℝ))
      (δ := δx) (by norm_num) hδx
  obtain ⟨Ncard, hNcard⟩ :=
    exists_nat_real_div_mul_sq_le
      (C := (Fintype.card ι : ℝ) * (Fintype.card (QIT.TensorPower b k) : ℝ))
      (η := hswSelfPackingEpsilon ε) (δ := δc)
      (hswSelfPackingEpsilon_pos hε) hδc
  obtain ⟨Nmoment, hNmoment⟩ :=
    exists_nat_real_div_mul_sq_le
      (C := ((N.tensorPower k).outputEnsemble E₀).logDeviationSecondMomentEnvelope)
      (η := hswSelfPackingEpsilon ε) (δ := δc)
      (hswSelfPackingEpsilon_pos hε) hδc
  let N0 : ℕ := max 1 (max Nsmall (max Nprune (max Ncard (max Nmoment Ncross))))
  refine ⟨N0, ?_⟩
  intro n hnN0
  have hn_one : 1 ≤ n := by
    dsimp [N0] at hnN0
    omega
  have hn_pos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn_one
  have hn_small_ge : n ≥ Nsmall := by
    dsimp [N0] at hnN0
    omega
  have hn_prune_ge : n ≥ Nprune := by
    dsimp [N0] at hnN0
    omega
  have hn_card_ge : n ≥ Ncard := by
    dsimp [N0] at hnN0
    omega
  have hn_moment_ge : n ≥ Nmoment := by
    dsimp [N0] at hnN0
    omega
  have hn_cross_ge : n ≥ Ncross := by
    dsimp [N0] at hnN0
    omega
  have hsmall : (1 : ℝ) / (n : ℝ) ≤ δ / 2 := by
    have h := hNsmall n hn_small_ge
    simpa using h
  refine ⟨hn_pos, hsmall, ?_⟩
  intro M hMF hMD hMne hrate hcard
  letI : Fintype M := hMF
  letI : DecidableEq M := hMD
  have hprune : (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤ (1 / 2 : ℝ) :=
    hNprune n hn_prune_ge
  have hcardMoment :
      (Fintype.card ι : ℝ) * (Fintype.card (QIT.TensorPower b k) : ℝ) /
          ((n : ℝ) * δc ^ 2) ≤ hswSelfPackingEpsilon ε :=
    hNcard n hn_card_ge
  have hmoment :
      ((N.tensorPower k).outputEnsemble E₀).logDeviationSecondMomentEnvelope /
          ((n : ℝ) * δc ^ 2) ≤ hswSelfPackingEpsilon ε :=
    hNmoment n hn_moment_ge
  refine ⟨δx, δc, hδx, hδc, hprune, hcardMoment, hmoment, ?_⟩
  exact hcross n hn_cross_ge M inferInstance inferInstance hMne hrate hcard

/-- Regularized HSW direct achievability after the cross term has been bounded
by a uniform exponentially decaying source exponent.

This removes the final `Ncross`/`ε` bookkeeping from
`hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFixedSlackCrossEstimate`.
The caller now supplies only fixed positive typicality slacks and the
pointwise source exponent bound
`cross(n) ≤ 8 * 2^{-nδ/4}`.  The proved geometric-decay lemma chooses the
large enough blocklength making this bound at most `ε/4`. -/
theorem hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorCrossExponentBound
    [Nonempty a] [Nonempty b] (N : Channel a b)
    (hblock :
      ∀ k : ℕ, 0 < k →
        ∀ (ι : Type uEnsemble) (_ : Fintype ι) (_ : DecidableEq ι),
          ∀ E₀ : Ensemble ι (QIT.TensorPower a k),
            ∀ δ : ℝ, 0 < δ →
              ∃ (δx : ℝ), ∃ (δc : ℝ), 0 < δx ∧ 0 < δc ∧
                ∀ n : ℕ,
                  4 * Real.rpow 2
                        ((n : ℝ) *
                          ((N.tensorPower k).hswHolevoRate E₀ - δ / 2)) *
                      (((N.tensorPower k).outputEnsemble E₀).strongTypicalDimensionEnvelope
                          n δx δc /
                        ((1 - (1 / 2 : ℝ)) *
                          QIT.FiniteDistribution.strongTypicalMassScale
                            (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                              ((N.tensorPower k).outputEnsemble E₀).averageState)
                            n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                    8 * Real.rpow 2 (-(n : ℝ) * (δ / 4))) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorFixedSlackCrossEstimate
      ?_
  intro k hk ι hιF hιD E₀ δ hδ ε hε
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  obtain ⟨δx, δc, hδx, hδc, hcrossExp⟩ :=
    hblock k hk ι inferInstance inferInstance E₀ δ hδ
  obtain ⟨Ncross, hNcross⟩ :=
    exists_nat_const_mul_rpow_two_neg_mul_le (A := (8 : ℝ)) (c := δ / 4)
      (η := ε / 4) (by positivity) (by positivity)
  refine ⟨δx, δc, hδx, hδc, Ncross, ?_⟩
  intro n hn M hMF hMD hMne hrate hcard
  exact le_trans (hcrossExp n) (hNcross n hn)

/-- HSW direct achievability for the regularized Holevo information.

This is the direct half of Wilde's HSW theorem: every rate strictly below the
regularized Holevo information is operationally achievable.  The proof composes
the source-shaped strongly-typical random-coding construction, packing
lemma/expurgation assembly, block-channel normalization, and the explicit HSW
cross-exponent slack choice.
[Wilde2011Qst, qit-notes.tex:33634-33808] -/
theorem hsw_regularizedHolevoInformation_direct
    [Nonempty a] [Nonempty b] (N : Channel a b) :
    ∀ R : ℝ, R < (Channel.regularizedHolevoInformation.{u, v, uEnsemble} N) →
      (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) R := by
  refine
    N.hsw_regularized_direct_of_blockCanonicalStrongTypicalActualOutputSourceProjectorCrossExponentBound
      ?_
  intro k hk ι hιF hιD E₀ δ hδ
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  simpa [Channel.hswHolevoRate] using
    exists_hsw_crossExponentBound_slacks
      (E := ((N.tensorPower k).outputEnsemble E₀)) hδ

end Channel

end

end QIT
