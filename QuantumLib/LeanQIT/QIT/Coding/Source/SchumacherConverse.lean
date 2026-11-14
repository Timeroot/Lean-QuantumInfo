/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Source.Schumacher
public import QIT.Information.AlickiFannesWinter
public import QIT.Information.Entropy.MutualInformationDPI
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Coding.EntanglementAssisted.Asymptotic.Lower
public import QIT.States.Purification.Canonical
public import QIT.Asymptotic.Typicality
public import QIT.Asymptotic.AEP
public import QIT.Symmetry.SymmetricSubspace

/-!
# Schumacher compression converse

The converse theorem for Schumacher quantum data compression: every achievable
compression rate `R` for an IID quantum source `ρ` satisfies `R ≥ S(ρ)`, where
`S(ρ) = vonNeumann ρ` is the source's von Neumann entropy (its Schumacher rate).

The proof follows Wilde's converse route [Wilde2011Qst, qit-notes.tex:31610-31690]
for the joint (purification) trace-distance error criterion `jointError`.  For
one `(n, R+δ, ε)` compression code `C : SchumacherCompressionCode ρ n W` with
`n ≥ 1` and `0 < ε ≤ 1`, the chain

```
2 log|W| ≥ I(W;Rⁿ)_τ              (dimension bound, right system)
          ≥ I(Âⁿ;Rⁿ)_ω             (mutual-information DPI, decoder on B)
          ≥ I(Aⁿ;Rⁿ)_φ_{RA}^{⊗n} − M(n,ε)   (AFW continuity of H(Rⁿ|·))
          = n I(A;R)_φ             (tensor additivity of mutual information)
          = 2n S(ρ),               (mutual information of a pure bipartite state)
```

where `M(n,ε) = afwContinuityModulus |Aⁿ| ε`, yields
`R + δ ≥ S(ρ) − M(n,ε)/(2n)`.  The block-length-independent bound
`M(n,ε)/(2n) ≤ ε log|A| + (1+ε) h₂(ε/(1+ε))/2` (valid for `n ≥ 1`) sends the
right-hand extra terms to zero as `ε → 0⁺` and `δ → 0⁺`, concluding
`R ≥ S(ρ)`.
-/

@[expose] public section

namespace QIT

open Filter

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace SchumacherCompressionCode

/-- Applying the encoder then the decoder to the system side (with the identity
reference channel in parallel) is the same as applying the composed channel
`D ∘ E` to the system side.

This is the channel-composition identity that identifies the `ω` produced by
the two-step `(id ⊗ D) ∘ (id ⊗ E)` data-processing with the `ω` inside
`jointError`, which is defined via the single composed channel `D ∘ E`. -/
theorem applyState_id_prod_comp_id_prod
    {R : Type u} {A : Type u} {W : Type u} {A' : Type u}
    [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
    [Fintype W] [DecidableEq W] [Fintype A'] [DecidableEq A']
    (φ : State (Prod R A)) (E : Channel A W) (D : Channel W A') :
    ((Channel.idChannel R).prod D).applyState
        (((Channel.idChannel R).prod E).applyState φ) =
      ((Channel.idChannel R).prod (D.comp E)).applyState φ := by
  apply State.ext
  change MatrixMap.kron (Channel.idChannel R).map D.map
      (MatrixMap.kron (Channel.idChannel R).map E.map φ.matrix) =
    MatrixMap.kron (Channel.idChannel R).map (D.comp E).map φ.matrix
  rw [MatrixMap.kron_comp_apply_general,
    Channel.idChannel_map_eq_linearMap_id]
  simp only [LinearMap.id_comp]
  rfl

end SchumacherCompressionCode

namespace State

/-- The single-code Schumacher converse bound (multiplicative form).

For one compression code `C` at block length `n ≥ 1` with joint error at most
`ε`, the Wilde chain gives
`2n S(ρ) ≤ 2n (C.rate) + afwContinuityModulus |Aⁿ| ε`.  The multiplicative
form avoids division by `n` here; the per-copy form is extracted in the final
theorem. -/
theorem schumacher_converse_single_code
    (ρ : State a) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    {W : Type u} [Fintype W] [DecidableEq W]
    (C : SchumacherCompressionCode ρ n W) (herr : C.jointError ≤ ε) :
    2 * (n : ℝ) * ρ.schumacherRate ≤ 2 * (n : ℝ) * C.rate +
      afwContinuityModulus (Fintype.card (TensorPower a n)) ε := by
  -- State the type aliases and the canonical Wilde states.
  let Rn := TensorPower a n
  let ψ : PureVector (Prod a a) := State.canonicalPurification ρ
  let φ : State (Prod Rn Rn) := ψ.state.tensorPowerBipartite n
  let τ : State (Prod Rn W) :=
    ((Channel.idChannel Rn).prod C.encoder).applyState φ
  let N : Channel Rn Rn := C.decoder.comp C.encoder
  let ω : State (Prod Rn Rn) := ((Channel.idChannel Rn).prod N).applyState φ
  -- (1) `C.jointError` is definitionally `ω.normalizedTraceDistance φ`.
  have herr' : ω.normalizedTraceDistance φ ≤ ε := by
    have heq : C.jointError = ω.normalizedTraceDistance φ := rfl
    rw [← heq]; exact herr
  -- (2) The two-step `(id ⊗ D) ∘ (id ⊗ E)` equals the one-step `id ⊗ (D ∘ E)`.
  have hω_two : ((Channel.idChannel Rn).prod C.decoder).applyState τ = ω :=
    SchumacherCompressionCode.applyState_id_prod_comp_id_prod φ C.encoder C.decoder
  -- (3) Step 1: right-system dimension bound `I(W;Rⁿ)_τ ≤ 2 log|W|`.
  have hdim : QIT.mutualInformation τ ≤ 2 * log2 (Fintype.card W) :=
    mutualInformation_le_two_log_card_right τ
  -- (4) Step 2: mutual-information DPI under the decoder on the B marginal.
  have hDPI : QIT.mutualInformation ω ≤ QIT.mutualInformation τ := by
    rw [← hω_two]
    exact mutualInformation_dataProcessing_local_channels_ge τ
      (Channel.idChannel Rn) C.decoder
  -- (5) The Rⁿ marginal is preserved by `(id ⊗ N)`.
  have hmarg : vonNeumann ω.marginalA = vonNeumann φ.marginalA := by
    have hωmarg : ω.marginalA = φ.marginalA := by
      have h1 : (((Channel.idChannel Rn).prod C.decoder).applyState τ).marginalA =
          τ.marginalA :=
        State.marginalA_applyState_id_prod τ C.decoder
      have h2 : (((Channel.idChannel Rn).prod C.encoder).applyState φ).marginalA =
          φ.marginalA :=
        State.marginalA_applyState_id_prod φ C.encoder
      rw [← hω_two, h1, h2]
    exact congrArg State.vonNeumann hωmarg
  -- (6) Step 3: AFW continuity of the conditional entropy.
  have hMIdecomp (σ : State (Prod Rn Rn)) :
      QIT.mutualInformation σ = vonNeumann σ.marginalA - σ.conditionalEntropy := by
    rw [QIT.mutualInformation, State.conditionalEntropy_eq]
    ring
  have hafw : |ω.conditionalEntropy - φ.conditionalEntropy| ≤
      afwContinuityModulus (Fintype.card Rn) ε :=
    State.alickiFannesWinter_conditionalEntropy ω φ ε herr'
  have hafw_bound : QIT.mutualInformation ω ≥ QIT.mutualInformation φ -
      afwContinuityModulus (Fintype.card Rn) ε := by
    rw [hMIdecomp ω, hMIdecomp φ, hmarg]
    linarith [(abs_sub_le_iff.mp hafw).1]
  -- (7) Step 4: tensor additivity of mutual information on the purification.
  have hφ_tensor : QIT.mutualInformation φ =
      (n : ℝ) * QIT.mutualInformation ψ.state :=
    mutualInformation_tensorPowerBipartite ψ.state n
  -- (8) Step 5: mutual information of the pure bipartite purification is 2 S(ρ).
  have hψ_pure : ψ.state.vonNeumann = 0 :=
    pureVector_vonNeumann_eq_zero ψ
  have hψ_marg : ψ.state.marginalA.vonNeumann = ψ.state.marginalB.vonNeumann :=
    pureVector_marginalA_vonNeumann_eq_marginalB ψ
  have hψ_mB : ψ.state.marginalB = ρ := by
    apply State.ext
    exact State.canonicalPurification_purifies ρ
  have hψ_mB_vN : vonNeumann ψ.state.marginalB = vonNeumann ρ :=
    congrArg State.vonNeumann hψ_mB
  have hψ_rate : ρ.schumacherRate = vonNeumann ρ := rfl
  have hφ_pure : QIT.mutualInformation ψ.state = 2 * ρ.schumacherRate := by
    rw [QIT.mutualInformation]
    linarith
  have hφ_val : QIT.mutualInformation φ = 2 * (n : ℝ) * ρ.schumacherRate := by
    rw [hφ_tensor, hφ_pure]; ring
  -- (9) Assemble the Wilde chain.
  have hchain : 2 * log2 (Fintype.card W) ≥
      2 * (n : ℝ) * ρ.schumacherRate -
        afwContinuityModulus (Fintype.card Rn) ε := by linarith
  -- (10) Translate `C.rate = log|W|/n` (n ≥ 1 ⟹ n ≠ 0).
  have hn_ne : n ≠ 0 := by omega
  have hnR_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_ne
  have hrate_mul : 2 * (n : ℝ) * C.rate = 2 * log2 (Fintype.card W) := by
    show 2 * (n : ℝ) * schumacherRegisterRate W n = 2 * log2 (Fintype.card W)
    rw [schumacherRegisterRate, if_neg hn_ne]
    field_simp
  linarith

end State

omit [DecidableEq a] in
/-- Per-copy upper bound on the tensor-power AFW modulus.

For block length `n ≥ 1`, `afwContinuityModulus |Aⁿ| ε / (2n)` is bounded by
`afwContinuityModulus |A| ε / 2`.  This is the block-length-independent
estimate that lets the Schumacher converse limit close: the right-hand side
tends to zero as `ε → 0⁺`. -/
private theorem afwContinuityModulus_tensorPower_div_le
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n) (hε0 : 0 ≤ ε) :
    afwContinuityModulus (Fintype.card (TensorPower a n)) ε / (2 * (n : ℝ)) ≤
      afwContinuityModulus (Fintype.card a) ε / 2 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2nR_pos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have hlog : log2 ((Fintype.card (TensorPower a n) : ℕ) : ℝ) =
      (n : ℝ) * log2 ((Fintype.card a : ℕ) : ℝ) :=
    State.log2_tensorPower_card n
  have hbe : 0 ≤ binaryEntropy (ε / (1 + ε)) :=
    binaryEntropy_afw_argument_nonneg hε0
  have h1pe : 0 ≤ 1 + ε := by linarith
  have hprod : 0 ≤ (1 + ε) * binaryEntropy (ε / (1 + ε)) := mul_nonneg h1pe hbe
  have hge : 0 ≤ ((n : ℝ) - 1) * ((1 + ε) * binaryEntropy (ε / (1 + ε))) :=
    mul_nonneg (by linarith) hprod
  unfold afwContinuityModulus
  rw [hlog, div_le_iff₀ h2nR_pos]
  have hrhs :
      ((2 * ε * log2 ((Fintype.card a : ℕ) : ℝ) +
          (1 + ε) * binaryEntropy (ε / (1 + ε))) / 2) * (2 * (n : ℝ)) =
        2 * (n : ℝ) * (ε * log2 ((Fintype.card a : ℕ) : ℝ)) +
          (n : ℝ) * ((1 + ε) * binaryEntropy (ε / (1 + ε))) := by ring
  rw [hrhs]
  have hcancel : 2 * ε * ((n : ℝ) * log2 ((Fintype.card a : ℕ) : ℝ)) =
      2 * (n : ℝ) * (ε * log2 ((Fintype.card a : ℕ) : ℝ)) := by ring
  rw [hcancel]
  linarith

/-- The Schumacher compression converse.

Every achievable rate `R` for an IID quantum source `ρ` under the joint
(purification) trace-distance error criterion satisfies `S(ρ) ≤ R`
[Wilde2011Qst, qit-notes.tex:31610-31690]. -/
theorem schumacher_converse (ρ : State a) (R : ℝ)
    (hR : ρ.IsAchievableSchumacherRate R) : ρ.schumacherRate ≤ R := by
  by_contra hcontra
  push Not at hcontra
  -- hcontra : R < ρ.schumacherRate
  set η : ℝ := (ρ.schumacherRate - R) / 3 with heta_def
  have hη_pos : 0 < η := by
    rw [heta_def]; exact div_pos (by linarith) (by norm_num)
  -- Pick `ε₀ ∈ (0,1]` with `afwContinuityModulus |A| ε₀ / 2 < η`, using that
  -- the AFW modulus vanishes as `ε → 0⁺`.
  have hlim : Tendsto (fun ε : ℝ => afwContinuityModulus (Fintype.card a) ε / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using
      (tendsto_afwContinuityModulus_nhdsWithin_zero_right (Fintype.card a)).div_const 2
  have hev : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      afwContinuityModulus (Fintype.card a) ε / 2 < η := by
    have hball : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        afwContinuityModulus (Fintype.card a) ε / 2 ∈ Metric.ball (0 : ℝ) η :=
      hlim.eventually (Metric.ball_mem_nhds _ hη_pos)
    filter_upwards [hball] with ε hε
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
    exact lt_of_le_of_lt (le_abs_self _) hε
  -- Extract a radius `δ` from the `nhdsWithin`-eventually statement.
  have hmem : {ε : ℝ | afwContinuityModulus (Fintype.card a) ε / 2 < η} ∈
      nhdsWithin 0 (Set.Ioi 0) := hev
  rw [Metric.mem_nhdsWithin_iff] at hmem
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hmem
  -- Pick `ε₀ = (min δ 1)/2 ∈ (0, min δ 1] ⊆ (0, δ) ∩ (0, 1]`.
  set ε₀ : ℝ := min δ 1 / 2 with hε₀_def
  have hε₀_pos : 0 < ε₀ := div_pos (lt_min hδ_pos (by norm_num)) (by norm_num)
  have hε₀_ltδ : ε₀ < δ := by
    dsimp only [ε₀]
    have hmin : min δ 1 ≤ δ := min_le_left δ 1
    nlinarith
  have hε₀_small : afwContinuityModulus (Fintype.card a) ε₀ / 2 < η := by
    have hε₀_in : ε₀ ∈ Metric.ball (0 : ℝ) δ ∩ Set.Ioi (0 : ℝ) := by
      refine ⟨?_, hε₀_pos⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε₀_pos]
      exact hε₀_ltδ
    exact hδ_sub hε₀_in
  -- Invoke achievability with this `ε₀` and rate slack `η`.
  obtain ⟨N, hN⟩ := hR η hη_pos ε₀ hε₀_pos
  set n : ℕ := max N 1 with hn_def
  have hn : 1 ≤ n := le_max_right N 1
  have hnN : N ≤ n := le_max_left N 1
  obtain ⟨W, hWfin, hWdec, C, hrate, herr⟩ := hN n hnN
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  -- Single-code Wilde chain at block length `n`.
  have hsingle :=
    State.schumacher_converse_single_code ρ ε₀ n hn C herr
  -- Per-copy AFW modulus bound `afwContinuityModulus |Aⁿ| ε₀ / (2n) ≤` the
  -- block-length-independent estimate.
  have hbound :=
    afwContinuityModulus_tensorPower_div_le (a := a) ε₀ n hn (le_of_lt hε₀_pos)
  -- Convert the single-code inequality to the divided form
  -- `S(ρ) ≤ C.rate + afwModulus/(2n)` by dividing by `2n > 0`.
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hn
  have h2nR_pos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have hkey : (ρ.schumacherRate - C.rate) * (2 * (n : ℝ)) ≤
      afwContinuityModulus (Fintype.card (TensorPower a n)) ε₀ := by linarith
  have hdiv : ρ.schumacherRate - C.rate ≤
      afwContinuityModulus (Fintype.card (TensorPower a n)) ε₀ / (2 * (n : ℝ)) :=
    (le_div_iff₀ h2nR_pos).mpr hkey
  -- Chain: `S ≤ C.rate + afwMod/(2n) ≤ (R + η) + afwModulus|A|ε₀/2 < R + 2η`.
  linarith [hdiv, hrate, hbound, hε₀_small, heta_def, hcontra]
