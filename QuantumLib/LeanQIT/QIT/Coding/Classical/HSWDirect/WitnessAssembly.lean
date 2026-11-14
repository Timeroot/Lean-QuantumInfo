/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Classical.HSWDirect.CodeTransforms

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v uEnsemble uMessage uAux uCodebook

noncomputable section

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- HSW direct-achievability assembly from completed spectral packing bundles.

This is the post-typicality interface for the direct proof.  For every target
rate slack `δ` and target maximal-error tolerance `ε`, the caller must provide,
eventually in the block length `n`,

* positivity of `n` and the expurgation rate-loss bound `1/n ≤ δ/2`;
* a finite message set `M`;
* a finite random-codeword alphabet `𝒳`;
* an output ensemble over `B^n`;
* a completed `HSWPackingHypothesesSpectral` bundle for that output ensemble;
* an input codeword lift whose channel outputs agree with the output ensemble;
* a message-cardinality/rate estimate at slack `δ/2`;
* and the displayed packing-error expression bounded by `ε/2`.

Under exactly those hypotheses, the existing packing lemma, expurgation, and
operational-achievability layer prove that the one-letter Holevo rate
`χ(N,E₀)` is achievable.  The random-code existence and typical-estimate
families remain explicit upstream obligations. -/
theorem hsw_directWitnessAssembly_from_spectralPackingHypotheses
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∃ (M : Type uMessage), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
              ∃ (_ : Nonempty M),
                ∃ (𝒳 : Type uCodebook), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                  ∃ (Eout : Ensemble 𝒳 (QIT.TensorPower b n)),
                    ∃ (typicalitySlack : ℝ),
                      ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                        ∃ (φ : 𝒳 → State (QIT.TensorPower a n)),
                          (∀ x, (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                            hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 ∧
                              2 * (H.ε + 2 * Real.sqrt H.ε) +
                                  4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D) ≤
                                ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_averageErrorPacking E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, M, hMfin, hMdec, hMnonempty,
    𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ,
    houtput, hrate, hpacking_le⟩ := hN0 n hn
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype 𝒳 := h𝒳fin
  letI : DecidableEq 𝒳 := h𝒳dec
  let packingError : ℝ :=
    2 * (H.ε + 2 * Real.sqrt H.ε) +
      4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D)
  have havg :
      Nonempty (HSWAverageErrorPackingWitness N E₀ n (δ / 2) packingError M) := by
    simpa [packingError] using
      H.toAverageErrorPackingWitness N E₀ φ houtput hrate
  refine ⟨hn_pos, hinv_le, M, inferInstance, inferInstance, inferInstance, ?_⟩
  rcases havg with ⟨W⟩
  exact ⟨W.weaken le_rfl (by simpa [packingError] using hpacking_le)⟩

/-- HSW direct-achievability assembly from spectral packing estimates, with the
finite message set chosen internally.

Compared with `hsw_directWitnessAssembly_from_spectralPackingHypotheses`, the
caller no longer supplies the message alphabet or the rate estimate.  For each
large block length, this theorem chooses a finite nonempty message type whose
HSW rate is at least `χ(N,E₀) - δ/2`; the remaining hypothesis is exactly the
source-shaped spectral/typical estimate package for that chosen message set,
including the packing-error bound. -/
theorem hsw_directWitnessAssembly_from_spectralPackingEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (𝒳 : Type uCodebook), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                  ∃ (Eout : Ensemble 𝒳 (QIT.TensorPower b n)),
                    ∃ (typicalitySlack : ℝ),
                      ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                        ∃ (φ : 𝒳 → State (QIT.TensorPower a n)),
                          (∀ x, (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                            2 * (H.ε + 2 * Real.sqrt H.ε) +
                                4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D) ≤
                              ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingHypotheses E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty, hrate⟩ :=
    hswMessageRate.exists_finite_message_type_rate_ge hn_pos
      (N.hswHolevoRate E₀ - δ / 2)
  obtain ⟨𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ, houtput, hpacking_le⟩ :=
    hpack M hMfin hMdec hMnonempty hrate
  exact ⟨hn_pos, hinv_le, M, hMfin, hMdec, hMnonempty,
    𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ, houtput, hrate, hpacking_le⟩

/-- HSW direct-achievability assembly from spectral packing estimates, with the
finite message set chosen internally and its cross-term cardinality bound
exposed to the estimate layer.

This variant is the rate-accounting form used by the asymptotic HSW direct
proof.  The chosen message alphabet satisfies both
`χ(N,E₀)-δ/2 ≤ log₂ |M|/n` and
`|M|-1 ≤ 2^{n(χ(N,E₀)-δ/2)}`.  The second inequality is what lets the final
packing-error bound be proved from a source exponent estimate instead of being
assumed as an opaque all-message-set hypothesis. -/
theorem hsw_directWitnessAssembly_from_spectralPackingEstimatesWithCardBound
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                (Fintype.card M : ℝ) - 1 ≤
                  Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) →
                ∃ (𝒳 : Type uCodebook), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                  ∃ (Eout : Ensemble 𝒳 (QIT.TensorPower b n)),
                    ∃ (typicalitySlack : ℝ),
                      ∃ (H : HSWPackingHypothesesSpectral Eout typicalitySlack),
                        ∃ (φ : 𝒳 → State (QIT.TensorPower a n)),
                          (∀ x, (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                            2 * (H.ε + 2 * Real.sqrt H.ε) +
                                4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D) ≤
                              ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingHypotheses E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty, hrate, hcard⟩ :=
    hswMessageRate.exists_finite_message_type_rate_ge_card_sub_one_le hn_pos
      (N.hswHolevoRate E₀ - δ / 2)
  obtain ⟨𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ, houtput, hpacking_le⟩ :=
    hpack M hMfin hMdec hMnonempty hrate hcard
  exact ⟨hn_pos, hinv_le, M, hMfin, hMdec, hMnonempty,
    𝒳, h𝒳fin, h𝒳dec, Eout, typicalitySlack, H, φ, houtput, hrate, hpacking_le⟩

/-- HSW direct-achievability assembly from the diagonal strong-typical packing
route.

This is the source-shaped version of
`hsw_directWitnessAssembly_from_spectralPackingEstimates` for the currently
formalized pack-1 route.  The caller supplies the diagonal classical channel
`K`, strongly typical codeword map, codeword projectors, and the remaining
pack-2/3/4 estimates in the shape consumed by
`hswPackingHypothesesDiagonal_of_pinchedStrongTypical`.  This theorem then
constructs the generic packing bundle, chooses the finite message set, applies
the packing lemma and expurgation, and proves operational achievability of
`χ(N,E₀)`.

The asymptotic typical/packing estimates remain explicit hypotheses: no
random-coding existence or spectral/strong projector identification is hidden
in this bridge. -/
theorem hsw_directWitnessAssembly_from_diagonalPackingEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (𝒳 : Type uCodebook), ∃ (_ : Fintype 𝒳), ∃ (_ : DecidableEq 𝒳),
                      ∃ (Eout : Ensemble 𝒳 (QIT.TensorPower b n)),
                        ∃ (codewordOf : 𝒳 → Fin n → α),
                          ∃ (φ : 𝒳 → State (QIT.TensorPower a n)),
                            ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                              ∃ (d : ℝ), ∃ (D : ℝ),
                                ∃ (Px : 𝒳 → CMatrix (QIT.TensorPower b n)),
                                  0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                    (∀ x,
                                      (Eout.states x).matrix =
                                        (HSWPackingHypothesesSpectral.conditionalProductDiagonalState K
                                          (codewordOf x)).matrix) ∧
                                    (∀ x,
                                      ClassicalTypicality.StrongTypical p
                                        (codewordOf x) δx) ∧
                                    (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                        ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                    (∀ x,
                                      (Px x).PosSemidef ∧ Px x * Px x = Px x ∧
                                        Px x ≤ 1) ∧
                                    (∀ x,
                                      1 - packingε ≤
                                        ((Px x * (Eout.states x).matrix).trace).re) ∧
                                    (∀ x, ((Px x).trace).re ≤ d) ∧
                                    (HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                          (ClassicalTypicality.inducedMarginal p K) n
                                          ((Fintype.card α : ℝ) * (δx + δc)) *
                                        Eout.averageState.matrix *
                                        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                          (ClassicalTypicality.inducedMarginal p K) n
                                          ((Fintype.card α : ℝ) * (δx + δc))
                                        ≤ ((D : ℝ)⁻¹) •
                                          HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
                                            (ClassicalTypicality.inducedMarginal p K)
                                            n
                                            ((Fintype.card α : ℝ) * (δx + δc))) ∧
                                    (∀ x, (N.tensorPower n).applyState (φ x) =
                                      Eout.states x) ∧
                                    2 * (packingε + 2 * Real.sqrt packingε) +
                                        4 * ((Fintype.card M : ℝ) - 1) * (d / D) ≤
                                      ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, 𝒳, h𝒳fin, h𝒳dec, Eout, codewordOf, φ,
    δx, δc, packingε, d, D, Px, hδx, hδc, hpackingε, hD, hstates, hx, hlarge,
    hPx, h2, h3, h4, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  letI : Fintype 𝒳 := h𝒳fin
  letI : DecidableEq 𝒳 := h𝒳dec
  let H : HSWPackingHypothesesSpectral Eout
      ((Fintype.card α : ℝ) * (δx + δc)) :=
    HSWPackingHypothesesSpectral.hswPackingHypothesesDiagonal_of_pinchedStrongTypical
      p K Eout codewordOf hn_pos hδx hδc hpackingε hD hstates hx hlarge
      Px hPx h2 h3 h4
  refine ⟨𝒳, inferInstance, inferInstance, Eout,
    (Fintype.card α : ℝ) * (δx + δc), H, φ, houtput, ?_⟩
  simpa [H] using hpacking_le

/-- HSW direct-achievability assembly from pruned diagonal packing estimates.

This theorem removes the projected-average pack-4 bound from the caller's
obligations in the diagonal route.  The caller supplies the source-shaped
pruned distribution domination
`p'(xⁿ) ≤ (1 - η)⁻¹ pⁿ(xⁿ)` and the marginal-product mass envelope on the
strong-typical output set.  The proved pruned pack-4 bridge in
`ConditionalTypicality.lean` then constructs the `h4` Loewner bound consumed by
`hsw_directWitnessAssembly_from_diagonalPackingEstimates`.

The remaining inputs are still genuine HSW direct-proof content: a pruned
codeword ensemble, codeword projectors with pack-2/pack-3 estimates, physical
channel-output realizations, and the final packing-error rate inequality. -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalPackingEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
                        ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                          ∃ (d : ℝ), ∃ (D : ℝ), ∃ (pruneε : ℝ),
                            ∃ (Px : (Fin n → α) → CMatrix (QIT.TensorPower b n)),
                              0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ 0 < D ∧
                                pruneε < 1 ∧
                                (∀ x : Fin n → α,
                                  Eout.states x =
                                    HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                      K x) ∧
                                (∀ x : Fin n → α,
                                  ClassicalTypicality.StrongTypical p x δx) ∧
                                (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                    ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                                (∀ x : Fin n → α,
                                  (Px x).PosSemidef ∧ Px x * Px x = Px x ∧
                                    Px x ≤ 1) ∧
                                (∀ x : Fin n → α,
                                  1 - packingε ≤
                                    ((Px x * (Eout.states x).matrix).trace).re) ∧
                                (∀ x : Fin n → α, ((Px x).trace).re ≤ d) ∧
                                (∀ zseq : Fin n → b,
                                  ClassicalTypicality.StrongTypical
                                      (ClassicalTypicality.inducedMarginal p K)
                                      zseq
                                      ((Fintype.card α : ℝ) * (δx + δc)) →
                                    (HSWPackingHypothesesSpectral.marginalProductMass
                                      (ClassicalTypicality.inducedMarginal p K) zseq : ℝ)
                                      ≤ D⁻¹) ∧
                                (∀ x : Fin n → α,
                                  (Eout.probs x : ℝ) ≤
                                    (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                                (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                  Eout.states x) ∧
                                2 * (packingε + 2 * Real.sqrt packingε) +
                                    4 * ((Fintype.card M : ℝ) - 1) *
                                      (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_diagonalPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, d, D, pruneε,
    Px, hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hPx, h2, h3,
    hmass_bound, hdom, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  have hD_eff : 0 < (1 - pruneε) * D := by
    have hpos : 0 < 1 - pruneε := by linarith
    exact mul_pos hpos hD
  refine ⟨α, inferInstance, inferInstance, p, K, (Fin n → α), inferInstance,
    inferInstance, Eout, (fun x => x), φ, δx, δc, packingε, d,
    (1 - pruneε) * D, Px, ?_⟩
  refine ⟨hδx, hδc, hpackingε, hD_eff, ?_, hx, hlarge, hPx, h2, h3, ?_,
    houtput, hpacking_le⟩
  · intro x
    rw [hstates x]
  · exact
      strongTypicalDiagonalProjector_projectedPrunedConditionalProductAverage_le_effectiveD
        p K hprune hD Eout hstates hdom hmass_bound

/-- HSW direct-achievability assembly from source-shaped conditionally-typical
projector estimates.

This is the next specialization after
`hsw_directWitnessAssembly_from_prunedDiagonalPackingEstimates`: instead of
asking the caller to provide arbitrary codeword projectors `Π_x` satisfying
pack-2 and pack-3, it instantiates them as the conditionally typical projectors
of the product output states.  The remaining obligations are the genuine
Wilde HSW estimates: the second-moment capture bound, the
conditionally-typical-subspace dimension bound, the pruned-distribution
domination, the marginal-product mass envelope, physical channel output, and
the final packing-error inequality.
[Wilde2011Qst, qit-notes.tex:33634-33808] -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalProjectorEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
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
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
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
                                        (K.prob (x i)) (K.sum_eq_one (x i))) δc ≤ d) ∧
                              (∀ zseq : Fin n → b,
                                ClassicalTypicality.StrongTypical
                                    (ClassicalTypicality.inducedMarginal p K)
                                    zseq
                                    ((Fintype.card α : ℝ) * (δx + δc)) →
                                  (HSWPackingHypothesesSpectral.marginalProductMass
                                    (ClassicalTypicality.inducedMarginal p K) zseq : ℝ)
                                    ≤ D⁻¹) ∧
                              (∀ x : Fin n → α,
                                (Eout.probs x : ℝ) ≤
                                  (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                              (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_prunedDiagonalPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, d, D, pruneε,
    hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment, hdim,
    hmass_bound, hdom, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let Px : (Fin n → α) → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
      δc
  refine ⟨α, inferInstance, inferInstance, p, K, Eout, φ, δx, δc, packingε,
    d, D, pruneε, Px, ?_⟩
  refine ⟨hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, ?_, ?_, ?_,
    hmass_bound, hdom, houtput, hpacking_le⟩
  · intro x
    dsimp [Px]
    exact ⟨
      conditionallyTypicalSubspaceProjector_posSemidef
        (fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
        δc,
      conditionallyTypicalSubspaceProjector_idempotent
        (fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
        δc,
      conditionallyTypicalSubspaceProjector_le_one
        (fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
        δc⟩
  · intro x
    dsimp [Px]
    rw [hstates x]
    rw [HSWPackingHypothesesSpectral.conditionalProductDiagonalState_matrix_eq_productState_diagonal
      K x]
    have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
      (states := fun i : Fin n => Classical.diagonalState (K.prob (x i)) (K.sum_eq_one (x i)))
      (δ := δc) hn_pos hδc
    have hkey :
        1 - packingε ≤
          1 - conditionalLogDeviationSecondMoment
              (fun i : Fin n => Classical.diagonalState
                (K.prob (x i)) (K.sum_eq_one (x i))) /
            ((n : ℝ) * δc) ^ 2 := by
      linarith [hmoment x]
    exact le_trans hkey hown
  · intro x
    dsimp [Px]
    rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
    exact hdim x

/-- HSW direct-achievability assembly from source-shaped conditionally-typical
projector estimates and the finite classical entropy envelope for pack-4.

Compared with `hsw_directWitnessAssembly_from_prunedDiagonalProjectorEstimates`,
this theorem no longer asks for a word-by-word `hmass_bound`.  It instead
consumes the explicit strong-typical product-mass exponent
`2^{-n H(Z) + n δ L(Z)} ≤ D⁻¹` for the induced output distribution. -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
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
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
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
                                        (K.prob (x i)) (K.sum_eq_one (x i))) δc ≤ d) ∧
                              Real.rpow 2
                                (- (n : ℝ) *
                                    (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
                                  (n : ℝ) * ((Fintype.card α : ℝ) * (δx + δc)) *
                                    (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
                                  ≤ D⁻¹ ∧
                              (∀ x : Fin n → α,
                                (Eout.probs x : ℝ) ≤
                                  (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                              (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (d / ((1 - pruneε) * D)) ≤ ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_prunedDiagonalProjectorEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, d, D, pruneε,
    hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment, hdim,
    hD_entropy, hdom, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  have hδtyp : 0 ≤ (Fintype.card α : ℝ) * (δx + δc) := by
    have hcard : 0 ≤ (Fintype.card α : ℝ) := by exact_mod_cast Nat.zero_le _
    have hsum : 0 ≤ δx + δc := by linarith
    exact mul_nonneg hcard hsum
  refine ⟨α, inferInstance, inferInstance, p, K, Eout, φ, δx, δc, packingε,
    d, D, pruneε, hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment,
    hdim, ?_, hdom, houtput, hpacking_le⟩
  intro zseq hz
  exact HSWPackingHypothesesSpectral.marginalProductMass_le_D_inv_of_entropy_slack
    (ClassicalTypicality.inducedMarginal p K) zseq hn_pos hδtyp hD_entropy hz

/-- HSW direct-achievability assembly with both pack-3 and pack-4 discharged by
finite classical typicality envelopes.

Compared with `hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyEstimates`,
this theorem no longer asks the caller for a separate conditionally-typical
subspace dimension bound.  Strong typicality of every selected codeword supplies
the named diagonal-output dimension envelope
`hswConditionalDiagonalDimensionEnvelope p K n δx δc`. -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyDimensionEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
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
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
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
                                  (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                              (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                      ((1 - pruneε) * D)) ≤ ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, D, pruneε,
    hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment,
    hD_entropy, hdom, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let d := hswConditionalDiagonalDimensionEnvelope p K n δx δc
  refine ⟨α, inferInstance, inferInstance, p, K, Eout, φ, δx, δc, packingε,
    d, D, pruneε, hδx, hδc, hpackingε, hD, hprune, hstates, hx, hlarge, hmoment,
    ?_, hD_entropy, hdom, houtput, ?_⟩
  · intro x
    dsimp [d]
    exact conditionallyTypicalSubspaceProjector_dim_le_hswConditionalDiagonalDimensionEnvelope
      p K x hn_pos hδx hδc (hx x)
  · simpa [d] using hpacking_le

/-- HSW direct-achievability assembly with the canonical marginal-product mass
scale `D = 2^{nH(Z)-nδL(Z)}` chosen internally.

Compared with
`hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyDimensionEstimates`,
this theorem no longer asks the caller to provide `D` or prove the
`2^{-nH+nδL} ≤ D⁻¹` side condition. -/
theorem hsw_directWitnessAssembly_from_prunedDiagonalProjectorTypicalityScaleEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (Eout : Ensemble (Fin n → α) (QIT.TensorPower b n)),
                      ∃ (φ : (Fin n → α) → State (QIT.TensorPower a n)),
                        ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                          ∃ (pruneε : ℝ),
                            0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                              (∀ x : Fin n → α,
                                Eout.states x =
                                  HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                    K x) ∧
                              (∀ x : Fin n → α,
                                ClassicalTypicality.StrongTypical p x δx) ∧
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                  ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                              (∀ x : Fin n → α,
                                conditionalLogDeviationSecondMoment
                                    (fun i : Fin n =>
                                      Classical.diagonalState
                                        (K.prob (x i)) (K.sum_eq_one (x i))) /
                                  ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                              (∀ x : Fin n → α,
                                (Eout.probs x : ℝ) ≤
                                  (1 - pruneε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) ∧
                              (∀ x : Fin n → α, (N.tensorPower n).applyState (φ x) =
                                Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                      ((1 - pruneε) *
                                        (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                          n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                    ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_prunedDiagonalProjectorEntropyDimensionEstimates
    E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, Eout, φ, δx, δc, packingε, pruneε,
    hδx, hδc, hpackingε, hprune, hstates, hx, hlarge, hmoment, hdom, houtput,
    hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let δz : ℝ := (Fintype.card α : ℝ) * (δx + δc)
  let D : ℝ := (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale n δz
  refine ⟨α, inferInstance, inferInstance, p, K, Eout, φ, δx, δc, packingε,
    D, pruneε, hδx, hδc, hpackingε, ?_, hprune, hstates, hx, hlarge, hmoment,
    ?_, hdom, houtput, ?_⟩
  · exact (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale_pos n δz
  · dsimp [D, δz]
    exact le_of_eq
      ((ClassicalTypicality.inducedMarginal p K).rpow_entropy_slack_eq_strongTypicalMassScale_inv
        n ((Fintype.card α : ℝ) * (δx + δc)))
  · simpa [D, δz] using hpacking_le

/-- HSW direct-achievability assembly indexed by the strongly-typical pruned
codebook subtype.

Compared with
`hsw_directWitnessAssembly_from_prunedDiagonalProjectorTypicalityScaleEstimates`,
this theorem no longer asks the caller to prove
`∀ x : Fin n → α, StrongTypical p x δx`, which is not the right pruned-codebook
shape.  Instead, the random-coding index type is the subtype
`ClassicalTypicality.StrongTypicalWord p n δx`, and the codeword map is the
subtype inclusion.  The strong-typicality hypothesis and the pack-3 dimension
envelope are then discharged internally.

The theorem still keeps the genuinely independent HSW obligations explicit:
the diagonal/pinched output realization, the projected-average pack-4 bound for
the pruned ensemble, the uniform conditional log-deviation estimate, the
physical channel-output realization, and the final packing-error inequality. -/
theorem hsw_directWitnessAssembly_from_strongTypicalCodebookProjectorTypicalityScaleEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ),
                      ∃ (Eout :
                          Ensemble (ClassicalTypicality.StrongTypicalWord p n δx)
                            (QIT.TensorPower b n)),
                        ∃ (φ :
                            ClassicalTypicality.StrongTypicalWord p n δx →
                              State (QIT.TensorPower a n)),
                          0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧
                            (∀ x,
                              (Eout.states x).matrix =
                                (HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                  K
                                  (ClassicalTypicality.StrongTypicalWord.codeword p δx x)).matrix) ∧
                            (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
                                ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                            (∀ x,
                              conditionalLogDeviationSecondMoment
                                  (fun i : Fin n =>
                                    Classical.diagonalState
                                      (K.prob
                                        (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
                                      (K.sum_eq_one
                                        (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))) /
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
                              (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                            2 * (packingε + 2 * Real.sqrt packingε) +
                                4 * ((Fintype.card M : ℝ) - 1) *
                                  (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                    ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                      n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                  ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_diagonalPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, δx, δc, packingε, Eout, φ,
    hδx, hδc, hpackingε, hstates, hlarge, hmoment, h4, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  let codewordOf : 𝒳 → Fin n → α := fun x =>
    ClassicalTypicality.StrongTypicalWord.codeword p δx x
  let D : ℝ :=
    (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
      n ((Fintype.card α : ℝ) * (δx + δc))
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
      δc
  refine ⟨α, inferInstance, inferInstance, p, K, 𝒳, inferInstance, inferInstance,
    Eout, codewordOf, φ, δx, δc, packingε,
    hswConditionalDiagonalDimensionEnvelope p K n δx δc, D, Px, ?_⟩
  refine ⟨hδx, hδc, hpackingε, ?_, hstates, ?_, hlarge, ?_, ?_, ?_, ?_,
    houtput, ?_⟩
  · dsimp [D]
    exact (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale_pos
      n ((Fintype.card α : ℝ) * (δx + δc))
  · intro x
    exact ClassicalTypicality.StrongTypicalWord.strongTypical p δx x
  · intro x
    dsimp [Px]
    exact ⟨
      conditionallyTypicalSubspaceProjector_posSemidef
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc,
      conditionallyTypicalSubspaceProjector_idempotent
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc,
      conditionallyTypicalSubspaceProjector_le_one
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc⟩
  · intro x
    dsimp [Px]
    rw [hstates x]
    rw [HSWPackingHypothesesSpectral.conditionalProductDiagonalState_matrix_eq_productState_diagonal
      K (codewordOf x)]
    have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
      (states := fun i : Fin n =>
        Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
      (δ := δc) hn_pos hδc
    have hkey :
        1 - packingε ≤
          1 - conditionalLogDeviationSecondMoment
              (fun i : Fin n =>
                Classical.diagonalState (K.prob (codewordOf x i))
                  (K.sum_eq_one (codewordOf x i))) /
            ((n : ℝ) * δc) ^ 2 := by
      linarith [hmoment x]
    exact le_trans hkey hown
  · intro x
    dsimp [Px]
    rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
    exact conditionallyTypicalSubspaceProjector_dim_le_hswConditionalDiagonalDimensionEnvelope
      p K (codewordOf x) hn_pos hδx hδc
      (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
  · dsimp [D]
    exact h4
  · dsimp [D]
    exact hpacking_le

/-- HSW direct-achievability assembly for the canonical pruned strongly-typical
codebook law.

This strengthens
`hsw_directWitnessAssembly_from_strongTypicalCodebookProjectorTypicalityScaleEstimates`
by deriving the projected-average `pack-4` bound internally from the normalized
i.i.d. law on the strongly-typical subtype.  Consequently the effective
packing denominator is `(1 - pruneε) * strongTypicalMassScale`, matching the
HSW pruning prefactor rather than assuming it away. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                      ∃ (hmass_pos :
                          0 < ClassicalTypicality.strongTypicalMass (n := n) p δx),
                        ∃ (Eout :
                            Ensemble (ClassicalTypicality.StrongTypicalWord p n δx)
                              (QIT.TensorPower b n)),
                          ∃ (φ :
                              ClassicalTypicality.StrongTypicalWord p n δx →
                                State (QIT.TensorPower a n)),
                            0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                              (1 - pruneε : ℝ) ≤
                                (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) ∧
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
                              (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
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
                                (N.tensorPower n).applyState (φ x) = Eout.states x) ∧
                              2 * (packingε + 2 * Real.sqrt packingε) +
                                  4 * ((Fintype.card M : ℝ) - 1) *
                                    (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                      ((1 - pruneε) *
                                        (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                          n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                    ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_diagonalPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, δx, δc, packingε, pruneε, hmass_pos,
    Eout, φ, hδx, hδc, hpackingε, hprune, hmass_lower, hprobs, hstates,
    hlarge, hmoment, houtput, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  let codewordOf : 𝒳 → Fin n → α := fun x =>
    ClassicalTypicality.StrongTypicalWord.codeword p δx x
  let δz : ℝ := (Fintype.card α : ℝ) * (δx + δc)
  let scale : ℝ :=
    (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale n δz
  let D : ℝ := (1 - pruneε) * scale
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
      δc
  refine ⟨α, inferInstance, inferInstance, p, K, 𝒳, inferInstance, inferInstance,
    Eout, codewordOf, φ, δx, δc, packingε,
    hswConditionalDiagonalDimensionEnvelope p K n δx δc, D, Px, ?_⟩
  refine ⟨hδx, hδc, hpackingε, ?_, ?_, ?_, hlarge, ?_, ?_, ?_, ?_,
    houtput, ?_⟩
  · dsimp [D, scale]
    have hprune_pos : 0 < 1 - pruneε := by linarith
    exact mul_pos hprune_pos
      ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale_pos n δz)
  · intro x
    rw [hstates x]
  · intro x
    exact ClassicalTypicality.StrongTypicalWord.strongTypical p δx x
  · intro x
    dsimp [Px]
    exact ⟨
      conditionallyTypicalSubspaceProjector_posSemidef
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc,
      conditionallyTypicalSubspaceProjector_idempotent
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc,
      conditionallyTypicalSubspaceProjector_le_one
        (fun i : Fin n =>
          Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
        δc⟩
  · intro x
    dsimp [Px]
    rw [hstates x]
    rw [HSWPackingHypothesesSpectral.conditionalProductDiagonalState_matrix_eq_productState_diagonal
      K (codewordOf x)]
    have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
      (states := fun i : Fin n =>
        Classical.diagonalState (K.prob (codewordOf x i)) (K.sum_eq_one (codewordOf x i)))
      (δ := δc) hn_pos hδc
    have hkey :
        1 - packingε ≤
          1 - conditionalLogDeviationSecondMoment
              (fun i : Fin n =>
                Classical.diagonalState (K.prob (codewordOf x i))
                  (K.sum_eq_one (codewordOf x i))) /
            ((n : ℝ) * δc) ^ 2 := by
      linarith [hmoment x]
    exact le_trans hkey hown
  · intro x
    dsimp [Px]
    rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
    exact conditionallyTypicalSubspaceProjector_dim_le_hswConditionalDiagonalDimensionEnvelope
      p K (codewordOf x) hn_pos hδx hδc
      (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
  · dsimp [D, scale, δz]
    have hδz : 0 ≤ (Fintype.card α : ℝ) * (δx + δc) := by
      have hcard : 0 ≤ (Fintype.card α : ℝ) := by exact_mod_cast Nat.zero_le _
      have hsum : 0 ≤ δx + δc := by linarith
      exact mul_nonneg hcard hsum
    have hD_entropy :
        Real.rpow 2
          (- (n : ℝ) * (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
            (n : ℝ) * ((Fintype.card α : ℝ) * (δx + δc)) *
              (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
          ≤
            ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
              n ((Fintype.card α : ℝ) * (δx + δc)))⁻¹ := by
      exact le_of_eq
        ((ClassicalTypicality.inducedMarginal p K).rpow_entropy_slack_eq_strongTypicalMassScale_inv
          n ((Fintype.card α : ℝ) * (δx + δc)))
    exact
      strongTypicalDiagonalProjector_projectedPrunedStrongTypicalConditionalProductAverage_le_entropyD
        p K hn_pos hprune hmass_pos hmass_lower
        ((ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale_pos
          n ((Fintype.card α : ℝ) * (δx + δc)))
        hδz hD_entropy Eout hprobs hstates
  · dsimp [D, scale, δz]
    exact hpacking_le

/-- HSW direct-achievability assembly with the canonical pruned output ensemble
constructed internally.

This removes the remaining bookkeeping burden of constructing the pruned
strongly-typical output ensemble from the caller.  The caller supplies only the
typical-set mass lower bound, the conditional spectral log-deviation estimate,
the physical realization of the canonical diagonal product outputs, and the
final packing-error numerical bound. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleBounds
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (α : Type uAux), ∃ (_ : Fintype α), ∃ (_ : DecidableEq α),
                  ∃ (p : QIT.FiniteDistribution α), ∃ (K : QIT.StochasticKernel α b),
                    ∃ (δx : ℝ), ∃ (δc : ℝ), ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                      ∃ (φ :
                          ClassicalTypicality.StrongTypicalWord p n δx →
                            State (QIT.TensorPower a n)),
                        0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                          (1 - pruneε : ℝ) ≤
                            (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) ∧
                          (Fintype.card α : ℝ) * (Fintype.card b : ℝ) /
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
                            (N.tensorPower n).applyState (φ x) =
                              HSWPackingHypothesesSpectral.conditionalProductDiagonalState
                                K
                                (ClassicalTypicality.StrongTypicalWord.codeword p δx x)) ∧
                          2 * (packingε + 2 * Real.sqrt packingε) +
                              4 * ((Fintype.card M : ℝ) - 1) *
                                (hswConditionalDiagonalDimensionEnvelope p K n δx δc /
                                  ((1 - pruneε) *
                                    (ClassicalTypicality.inducedMarginal p K).strongTypicalMassScale
                                      n ((Fintype.card α : ℝ) * (δx + δc)))) ≤
                                ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_canonicalStrongTypicalCodebookProjectorTypicalityScaleEstimates
    E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨α, hαfin, hαdec, p, K, δx, δc, packingε, pruneε, φ,
    hδx, hδc, hpackingε, hprune, hmass_lower, hlarge, hmoment, houtput,
    hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  letI : Fintype α := hαfin
  letI : DecidableEq α := hαdec
  have hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx := by
    have hprune_pos : 0 < 1 - pruneε := by linarith
    have hmass_real_pos :
        0 < (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) :=
      lt_of_lt_of_le hprune_pos hmass_lower
    exact_mod_cast hmass_real_pos
  let Eout : Ensemble (ClassicalTypicality.StrongTypicalWord p n δx)
      (QIT.TensorPower b n) :=
    { probs := (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob
      weights_sum := (ClassicalTypicality.prunedStrongTypicalDistribution
        p δx hmass_pos).sum_eq_one
      states := fun x =>
        HSWPackingHypothesesSpectral.conditionalProductDiagonalState
          K (ClassicalTypicality.StrongTypicalWord.codeword p δx x) }
  refine ⟨α, inferInstance, inferInstance, p, K, δx, δc, packingε, pruneε,
    hmass_pos, Eout, φ, hδx, hδc, hpackingε, hprune, hmass_lower, ?_, ?_,
    hlarge, hmoment, ?_, hpacking_le⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    exact houtput x

/-- HSW direct-achievability assembly with the canonical pruned strongly-typical
codebook and **actual quantum channel outputs**.

The random-code alphabet is the strongly-typical subtype for the output
ensemble's inherited input law.  The input encoder is constructed internally as
the product input state `⊗ᵢ ρ_{xᵢ}`, and the output ensemble is the actual
product output `⊗ᵢ N(ρ_{xᵢ})`.  Therefore this theorem does not assume that a
general quantum output state is diagonal.

The remaining hypotheses are the genuine HSW spectral estimates: pack-1
cross-capture by the average-output typical projector, a uniform conditional
log-deviation bound for pack-2, and the final packing-error exponent.  Pack-3
and pruned pack-4 are discharged internally. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSpectralEstimates
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (δx : ℝ), ∃ (δavg : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 ≤ δx ∧ 0 < δavg ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (1 - pruneε : ℝ) ≤
                        (ClassicalTypicality.strongTypicalMass
                          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        1 - packingε ≤
                          ((((N.outputEnsemble E₀).averageState.typicalSubspaceProjector
                              n δavg) *
                            (productState fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)).matrix).trace).re) ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) +
                          4 * ((Fintype.card M : ℝ) - 1) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                Real.rpow 2
                                  ((n : ℝ) * (N.outputEnsemble E₀).averageState.vonNeumann -
                                    (n : ℝ) * δavg))) ≤
                            ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨δx, δavg, δc, packingε, pruneε, hδx, hδavg, hδc, hpackingε,
    hprune, hmass_lower, hpack1, hmoment, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  let p := (N.outputEnsemble E₀).indexDistribution
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  have hprune_pos : 0 < 1 - pruneε := by linarith
  have hmass_pos_real :
      0 < (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) :=
    lt_of_lt_of_le hprune_pos hmass_lower
  have hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx := by
    exact_mod_cast hmass_pos_real
  let Eout : Ensemble 𝒳 (QIT.TensorPower b n) :=
    { probs := (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob
      weights_sum := (ClassicalTypicality.prunedStrongTypicalDistribution
        p δx hmass_pos).sum_eq_one
      states := fun x =>
        productState fun i : Fin n =>
          (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i) }
  let φ : 𝒳 → State (QIT.TensorPower a n) := fun x =>
    productState fun i : Fin n =>
      E₀.states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)
  let σbar := (N.outputEnsemble E₀).averageState
  let baseD : ℝ := Real.rpow 2 ((n : ℝ) * σbar.vonNeumann - (n : ℝ) * δavg)
  let D : ℝ := (1 - pruneε) * baseD
  let P : CMatrix (QIT.TensorPower b n) := σbar.typicalSubspaceProjector n δavg
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
      δc
  have hbaseD_pos : 0 < baseD := by
    dsimp [baseD]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hD_pos : 0 < D := by
    dsimp [D]
    exact mul_pos hprune_pos hbaseD_pos
  let H : HSWPackingHypothesesSpectral Eout δavg := {
    P := P
    Px := Px
    d := (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc
    D := D
    ε := packingε
    hε_nonneg := hpackingε
    hD_pos := hD_pos
    P_posSemidef := by
      dsimp [P, σbar]
      exact (N.outputEnsemble E₀).averageState.typicalSubspaceProjector_posSemidef n δavg
    P_idempotent := by
      dsimp [P, σbar]
      exact (N.outputEnsemble E₀).averageState.typicalSubspaceProjector_idempotent n δavg
    P_le_one := by
      dsimp [P, σbar]
      exact (N.outputEnsemble E₀).averageState.typicalSubspaceProjector_le_one n δavg
    Px_projector := by
      intro x
      dsimp [Px]
      exact ⟨
        conditionallyTypicalSubspaceProjector_posSemidef
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_idempotent
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_le_one
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc⟩
    h1 := by
      intro x
      dsimp [P, Eout, σbar]
      exact hpack1 x
    h2 := by
      intro x
      dsimp [Px, Eout]
      have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
        (states := fun i : Fin n =>
          (N.outputEnsemble E₀).states
            (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
        (δ := δc) hn_pos hδc
      have hkey :
          1 - packingε ≤
            1 - conditionalLogDeviationSecondMoment
                (fun i : Fin n =>
                  (N.outputEnsemble E₀).states
                    (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) /
              ((n : ℝ) * δc) ^ 2 := by
        linarith [hmoment x]
      exact le_trans hkey hown
    h3 := by
      intro x
      dsimp [Px]
      rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
      exact conditionallyTypicalSubspaceProjector_dim_le_strongTypicalDimensionEnvelope
        (E := N.outputEnsemble E₀)
        (codeword := ClassicalTypicality.StrongTypicalWord.codeword p δx x)
        hn_pos hδx hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
    h4 := by
      have hσbar :
          σbar.matrix =
            ∑ j, (p.prob j) • ((N.outputEnsemble E₀).states j).matrix := by
        dsimp [σbar, p, Ensemble.indexDistribution]
        rfl
      have hpruned :
          Eout.averageState.matrix ≤ ((1 - pruneε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
        exact pack4_prunedStrongTypicalReduction
          (fun j => (N.outputEnsemble E₀).states j) p σbar hσbar hmass_pos
          hmass_lower hprune Eout (by intro x; rfl) (by intro x; rfl)
      have hprojected :
          P * (σbar.tensorPower n).matrix * P ≤ ((baseD : ℝ)⁻¹) • P := by
        have hpack4 :=
          averageState_typicalProjector_projectedAvgState_le
            (n := n) (N.outputEnsemble E₀) δavg
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hpack4
        dsimp [P, σbar, baseD]
        exact_mod_cast hpack4
      have hP_herm : P.IsHermitian := by
        dsimp [P, σbar]
        exact ((N.outputEnsemble E₀).averageState.typicalSubspaceProjector_posSemidef
          n δavg).isHermitian
      have hinv_nonneg : 0 ≤ (1 - pruneε)⁻¹ := inv_nonneg.mpr hprune_pos.le
      have hbase :
          P * Eout.averageState.matrix * P ≤
            (((1 - pruneε)⁻¹ : ℝ) * ((baseD : ℝ)⁻¹)) • P :=
        cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
          hP_herm hinv_nonneg hpruned hprojected
      have hscalar :
          (((1 - pruneε)⁻¹ : ℝ) * ((baseD : ℝ)⁻¹)) = ((D : ℝ)⁻¹) := by
        dsimp [D]
        field_simp [ne_of_gt hprune_pos, ne_of_gt hbaseD_pos]
      simpa [hscalar] using hbase }
  refine ⟨𝒳, inferInstance, inferInstance, Eout, δavg, H, φ, ?_, ?_⟩
  · intro x
    dsimp [φ, Eout, p]
    exact tensorPower_applyState_productState N n
      (fun i : Fin n => E₀.states
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x i))
  · dsimp [H, D, baseD, σbar]
    exact hpacking_le

/-- HSW direct-achievability assembly with the canonical pruned strongly-typical
codebook, actual quantum channel outputs, and the source-shaped average-output
projector.

Compared with
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSpectralEstimates`,
this theorem no longer asks the caller for a legacy spectral average-projector
cross-capture estimate or a separate `δavg`.  The total projector is the
source-shaped eigenbasis strong-typical projector of the average output state,
with slack `(card ι) * (δx + δc)`.  Pack-1 follows from the proved
source-projector capture theorem, and pack-4 follows from the source projector
mass-scale estimate plus the pruned-distribution domination prefactor.

The remaining hypotheses are exactly the still-external asymptotic ingredients
for the HSW direct route: the strongly-typical mass lower bound, the conditional
log-deviation estimate for the conditionally-typical projectors, and the final
packing-error numerical inequality. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (δx : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (1 - pruneε : ℝ) ≤
                        (ClassicalTypicality.strongTypicalMass
                          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) ∧
                      (Fintype.card ι : ℝ) * (Fintype.card b : ℝ) /
                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) +
                          4 * ((Fintype.card M : ℝ) - 1) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                  (N.outputEnsemble E₀).averageState).strongTypicalMassScale
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                            ε / 2) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingEstimates E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε,
    hprune, hmass_lower, hlarge, hmoment, hpacking_le⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  let p := (N.outputEnsemble E₀).indexDistribution
  let δz : ℝ := (Fintype.card ι : ℝ) * (δx + δc)
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  have hprune_pos : 0 < 1 - pruneε := by linarith
  have hmass_pos_real :
      0 < (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) :=
    lt_of_lt_of_le hprune_pos hmass_lower
  have hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx := by
    exact_mod_cast hmass_pos_real
  let Eout : Ensemble 𝒳 (QIT.TensorPower b n) :=
    { probs := (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob
      weights_sum := (ClassicalTypicality.prunedStrongTypicalDistribution
        p δx hmass_pos).sum_eq_one
      states := fun x =>
        productState fun i : Fin n =>
          (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i) }
  let φ : 𝒳 → State (QIT.TensorPower a n) := fun x =>
    productState fun i : Fin n =>
      E₀.states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)
  let σbar := (N.outputEnsemble E₀).averageState
  let scale : ℝ :=
    (HSWPackingHypothesesSpectral.stateEigenvalueDistribution σbar).strongTypicalMassScale
      n δz
  let D : ℝ := (1 - pruneε) * scale
  let P : CMatrix (QIT.TensorPower b n) :=
    HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector σbar n δz
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
      δc
  have hδz : 0 ≤ δz := by
    dsimp [δz]
    have hcard : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Nat.zero_le _
    have hsum : 0 ≤ δx + δc := by linarith
    exact mul_nonneg hcard hsum
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
      σbar).strongTypicalMassScale_pos n δz
  have hD_pos : 0 < D := by
    dsimp [D]
    exact mul_pos hprune_pos hscale_pos
  let H : HSWPackingHypothesesSpectral Eout δz := {
    P := P
    Px := Px
    d := (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc
    D := D
    ε := packingε
    hε_nonneg := hpackingε
    hD_pos := hD_pos
    P_posSemidef := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
        (N.outputEnsemble E₀).averageState n δz
    P_idempotent := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_idempotent
        (N.outputEnsemble E₀).averageState n δz
    P_le_one := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_le_one
        (N.outputEnsemble E₀).averageState n δz
    Px_projector := by
      intro x
      dsimp [Px]
      exact ⟨
        conditionallyTypicalSubspaceProjector_posSemidef
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_idempotent
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_le_one
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc⟩
    h1 := by
      intro x
      dsimp [P, Eout, σbar, p, δz]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_product_capture_of_strongTypical
        (N.outputEnsemble E₀)
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x)
        hn_pos hδx hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical
          (N.outputEnsemble E₀).indexDistribution δx x)
        hlarge
    h2 := by
      intro x
      dsimp [Px, Eout]
      have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
        (states := fun i : Fin n =>
          (N.outputEnsemble E₀).states
            (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
        (δ := δc) hn_pos hδc
      have hkey :
          1 - packingε ≤
            1 - conditionalLogDeviationSecondMoment
                (fun i : Fin n =>
                  (N.outputEnsemble E₀).states
                    (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) /
              ((n : ℝ) * δc) ^ 2 := by
        linarith [hmoment x]
      exact le_trans hkey hown
    h3 := by
      intro x
      dsimp [Px]
      rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
      exact conditionallyTypicalSubspaceProjector_dim_le_strongTypicalDimensionEnvelope
        (E := N.outputEnsemble E₀)
        (codeword := ClassicalTypicality.StrongTypicalWord.codeword p δx x)
        hn_pos hδx hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
    h4 := by
      have hσbar :
          σbar.matrix =
            ∑ j, (p.prob j) • ((N.outputEnsemble E₀).states j).matrix := by
        dsimp [σbar, p, Ensemble.indexDistribution]
        rfl
      have hpruned :
          Eout.averageState.matrix ≤ ((1 - pruneε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
        exact pack4_prunedStrongTypicalReduction
          (fun j => (N.outputEnsemble E₀).states j) p σbar hσbar hmass_pos
          hmass_lower hprune Eout (by intro x; rfl) (by intro x; rfl)
      have hprojected :
          P * (σbar.tensorPower n).matrix * P ≤ ((scale : ℝ)⁻¹) • P := by
        dsimp [P, σbar, scale]
        exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_projectedTensorPower_le_strongTypicalMassScale
          (N.outputEnsemble E₀).averageState hn_pos hδz
      have hP_herm : P.IsHermitian := by
        dsimp [P, σbar]
        exact (HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
          (N.outputEnsemble E₀).averageState n δz).isHermitian
      have hinv_nonneg : 0 ≤ (1 - pruneε)⁻¹ := inv_nonneg.mpr hprune_pos.le
      have hbase :
          P * Eout.averageState.matrix * P ≤
            (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) • P :=
        cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
          hP_herm hinv_nonneg hpruned hprojected
      have hscalar :
          (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) = ((D : ℝ)⁻¹) := by
        dsimp [D]
        field_simp [ne_of_gt hprune_pos, ne_of_gt hscale_pos]
      simpa [hscalar] using hbase }
  refine ⟨𝒳, inferInstance, inferInstance, Eout, δz, H, φ, ?_, ?_⟩
  · intro x
    dsimp [φ, Eout, p]
    exact tensorPower_applyState_productState N n
      (fun i : Fin n => E₀.states
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x i))
  · dsimp [H, D, scale, σbar, δz]
    exact hpacking_le

/-- HSW direct-achievability assembly from the canonical source-projector
route with the final packing-error estimate split into its self-error and
cross-error components.

This theorem is logically equivalent to
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds`
at the assembly layer, but exposes the two asymptotic tasks separately: the
Hayashi-Nagaoka/self term and the cross-codeword packing exponent.  Later HSW
proof leaves discharge these two estimates by different large-block arguments,
so keeping them separated avoids a monolithic opaque numerical hypothesis. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorComponentBounds
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (δx : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 ≤ δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (1 - pruneε : ℝ) ≤
                        (ClassicalTypicality.strongTypicalMass
                          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) ∧
                      (Fintype.card ι : ℝ) * (Fintype.card b : ℝ) /
                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                      4 * ((Fintype.card M : ℝ) - 1) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                  (N.outputEnsemble E₀).averageState).strongTypicalMassScale
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                            ε / 4) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine
    N.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorBounds
      E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε, hprune,
    hmass_lower, hlarge, hmoment, hself, hcross⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  refine ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε, hprune,
    hmass_lower, hlarge, hmoment, ?_⟩
  exact hswPackingError_le_of_self_cross_bound hself hcross

/-- HSW direct-achievability assembly from the canonical source-projector
route, with the strongly-typical codebook mass lower bound discharged by the
finite Chebyshev/union-bound estimate for input strong typicality.

The caller now supplies the explicit large-block condition
`|X|/(n δ_x²) ≤ pruneε`; the theorem proves
`1 - pruneε ≤ P[Xⁿ strongly typical]` internally. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassBounds
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                ∃ (δx : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤ pruneε ∧
                      (Fintype.card ι : ℝ) * (Fintype.card b : ℝ) /
                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                      4 * ((Fintype.card M : ℝ) - 1) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                  (N.outputEnsemble E₀).averageState).strongTypicalMassScale
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                            ε / 4) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine
    N.hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorComponentBounds
      E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε, hprune,
    hmass_large, hlarge, hmoment, hself, hcross⟩ :=
      hpack M hMfin hMdec hMnonempty hrate
  have hmass0 :
      1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) :=
    ClassicalTypicality.strongTypicalMass_ge_one_sub_card_bound
      (p := (N.outputEnsemble E₀).indexDistribution) hn_pos hδx
  have hmass_lower :
      (1 - pruneε : ℝ) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) := by
    have hleft :
        (1 - pruneε : ℝ) ≤
          1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) := by
      linarith
    exact le_trans hleft hmass0
  refine ⟨δx, δc, packingε, pruneε, hδx.le, hδc, hpackingε, hprune,
    hmass_lower, hlarge, hmoment, hself, hcross⟩

/-- HSW direct-achievability assembly from the canonical source-projector
route, with both the strongly-typical codebook mass and the message-cardinality
rate accounting discharged internally.

Compared with
`hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassBounds`,
the final cross-error estimate is stated with the source proof's exponential
rate factor `2^{n(χ-δ/2)}`.  The theorem chooses the message set using
`hswMessageRate.exists_finite_message_type_rate_ge_card_sub_one_le`, then uses
the proved `|M|-1` bound to recover the packing lemma's actual cross term. -/
theorem hsw_directWitnessAssembly_from_canonicalStrongTypicalActualOutputSourceProjectorFiniteMassCardBound
    (N : Channel a b) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type uMessage) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                (Fintype.card M : ℝ) - 1 ≤
                  Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) →
                ∃ (δx : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤ pruneε ∧
                      (Fintype.card ι : ℝ) * (Fintype.card b : ℝ) /
                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                      4 * Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                  (N.outputEnsemble E₀).averageState).strongTypicalMassScale
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                            ε / 4) :
    (Channel.IsAchievableClassicalRate.{u, v, uMessage} N) (N.hswHolevoRate E₀) := by
  refine N.hsw_directWitnessAssembly_from_spectralPackingEstimatesWithCardBound E₀ ?_
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  refine ⟨hn_pos, hinv_le, ?_⟩
  intro M hMfin hMdec hMnonempty hrate hcard
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε, hprune,
    hmass_large, hlarge, hmoment, hself, hcrossCap⟩ :=
      hpack M hMfin hMdec hMnonempty hrate hcard
  let p := (N.outputEnsemble E₀).indexDistribution
  let δz : ℝ := (Fintype.card ι : ℝ) * (δx + δc)
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  have hmass0 :
      1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) :=
    ClassicalTypicality.strongTypicalMass_ge_one_sub_card_bound
      (p := (N.outputEnsemble E₀).indexDistribution) hn_pos hδx
  have hmass_lower :
      (1 - pruneε : ℝ) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) := by
    have hleft :
        (1 - pruneε : ℝ) ≤
          1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) := by
      linarith
    exact le_trans hleft hmass0
  have hprune_pos : 0 < 1 - pruneε := by linarith
  have hmass_pos_real :
      0 < (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) :=
    lt_of_lt_of_le hprune_pos hmass_lower
  have hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx := by
    exact_mod_cast hmass_pos_real
  let Eout : Ensemble 𝒳 (QIT.TensorPower b n) :=
    { probs := (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob
      weights_sum := (ClassicalTypicality.prunedStrongTypicalDistribution
        p δx hmass_pos).sum_eq_one
      states := fun x =>
        productState fun i : Fin n =>
          (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i) }
  let φ : 𝒳 → State (QIT.TensorPower a n) := fun x =>
    productState fun i : Fin n =>
      E₀.states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)
  let σbar := (N.outputEnsemble E₀).averageState
  let scale : ℝ :=
    (HSWPackingHypothesesSpectral.stateEigenvalueDistribution σbar).strongTypicalMassScale
      n δz
  let D : ℝ := (1 - pruneε) * scale
  let P : CMatrix (QIT.TensorPower b n) :=
    HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector σbar n δz
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
      δc
  have hδz : 0 ≤ δz := by
    dsimp [δz]
    have hcardι : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Nat.zero_le _
    have hsum : 0 ≤ δx + δc := by linarith
    exact mul_nonneg hcardι hsum
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
      σbar).strongTypicalMassScale_pos n δz
  have hD_pos : 0 < D := by
    dsimp [D]
    exact mul_pos hprune_pos hscale_pos
  let H : HSWPackingHypothesesSpectral Eout δz := {
    P := P
    Px := Px
    d := (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc
    D := D
    ε := packingε
    hε_nonneg := hpackingε
    hD_pos := hD_pos
    P_posSemidef := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
        (N.outputEnsemble E₀).averageState n δz
    P_idempotent := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_idempotent
        (N.outputEnsemble E₀).averageState n δz
    P_le_one := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_le_one
        (N.outputEnsemble E₀).averageState n δz
    Px_projector := by
      intro x
      dsimp [Px]
      exact ⟨
        conditionallyTypicalSubspaceProjector_posSemidef
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_idempotent
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_le_one
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc⟩
    h1 := by
      intro x
      dsimp [P, Eout, σbar, p, δz]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_product_capture_of_strongTypical
        (N.outputEnsemble E₀)
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x)
        hn_pos hδx.le hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical
          (N.outputEnsemble E₀).indexDistribution δx x)
        hlarge
    h2 := by
      intro x
      dsimp [Px, Eout]
      have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
        (states := fun i : Fin n =>
          (N.outputEnsemble E₀).states
            (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
        (δ := δc) hn_pos hδc
      have hkey :
          1 - packingε ≤
            1 - conditionalLogDeviationSecondMoment
                (fun i : Fin n =>
                  (N.outputEnsemble E₀).states
                    (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) /
              ((n : ℝ) * δc) ^ 2 := by
        linarith [hmoment x]
      exact le_trans hkey hown
    h3 := by
      intro x
      dsimp [Px]
      rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
      exact conditionallyTypicalSubspaceProjector_dim_le_strongTypicalDimensionEnvelope
        (E := N.outputEnsemble E₀)
        (codeword := ClassicalTypicality.StrongTypicalWord.codeword p δx x)
        hn_pos hδx.le hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
    h4 := by
      have hσbar :
          σbar.matrix =
            ∑ j, (p.prob j) • ((N.outputEnsemble E₀).states j).matrix := by
        dsimp [σbar, p, Ensemble.indexDistribution]
        rfl
      have hpruned :
          Eout.averageState.matrix ≤ ((1 - pruneε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
        exact pack4_prunedStrongTypicalReduction
          (fun j => (N.outputEnsemble E₀).states j) p σbar hσbar hmass_pos
          hmass_lower hprune Eout (by intro x; rfl) (by intro x; rfl)
      have hprojected :
          P * (σbar.tensorPower n).matrix * P ≤ ((scale : ℝ)⁻¹) • P := by
        dsimp [P, σbar, scale]
        exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_projectedTensorPower_le_strongTypicalMassScale
          (N.outputEnsemble E₀).averageState hn_pos hδz
      have hP_herm : P.IsHermitian := by
        dsimp [P, σbar]
        exact (HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
          (N.outputEnsemble E₀).averageState n δz).isHermitian
      have hinv_nonneg : 0 ≤ (1 - pruneε)⁻¹ := inv_nonneg.mpr hprune_pos.le
      have hbase :
          P * Eout.averageState.matrix * P ≤
            (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) • P :=
        cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
          hP_herm hinv_nonneg hpruned hprojected
      have hscalar :
          (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) = ((D : ℝ)⁻¹) := by
        dsimp [D]
        field_simp [ne_of_gt hprune_pos, ne_of_gt hscale_pos]
      simpa [hscalar] using hbase }
  refine ⟨𝒳, inferInstance, inferInstance, Eout, δz, H, φ, ?_, ?_⟩
  · intro x
    dsimp [φ, Eout, p]
    exact tensorPower_applyState_productState N n
      (fun i : Fin n => E₀.states
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x i))
  · have hratio_nonneg :
        0 ≤
          (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
            ((1 - pruneε) * scale) := by
      have hd_nonneg :
          0 ≤ (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc := by
        dsimp [Ensemble.strongTypicalDimensionEnvelope]
        exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      exact div_nonneg hd_nonneg hD_pos.le
    have hcross_actual :
        4 * ((Fintype.card M : ℝ) - 1) *
            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
              ((1 - pruneε) * scale)) ≤
          4 * Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) *
            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
              ((1 - pruneε) * scale)) := by
      have hmul := mul_le_mul_of_nonneg_right hcard hratio_nonneg
      nlinarith
    have hcross :
        4 * ((Fintype.card M : ℝ) - 1) *
            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
              ((1 - pruneε) * scale)) ≤ ε / 4 := by
      exact le_trans hcross_actual hcrossCap
    have htotal := hswPackingError_le_of_self_cross_bound hself hcross
    dsimp [H, D, scale, σbar, δz]
    exact htotal

end Channel

end

end QIT
