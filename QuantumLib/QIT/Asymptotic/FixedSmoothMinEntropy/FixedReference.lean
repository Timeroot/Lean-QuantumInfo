/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Asymptotic.FixedSmoothMinEntropy.PetzKernel

/-!
# Keeping the conditioning state fixed

`MState.conditionalMinEntropyFixed ρ σ = sup {λ | ρ_AB ≤ 2^(-λ) (I_A ⊗ σ_B)}` is the min-entropy
program with the reference `σ_B` frozen, and `smoothConditionalMinEntropyFixed` smooths the joint
state in purified distance while keeping that same `σ_B` for every witness.  Optimizing over `σ_B`
recovers the usual quantities, so each fixed-reference value is a lower bound on its optimized
counterpart -- which is the direction the AEP needs, since the Petz route produces one explicit
reference and must not be charged for the optimization.

Each of the three variants (normalized, subnormalized, and normalized center with subnormalized
witnesses) gets its candidate predicate, its `sSup` definition, the boundedness lemma that makes
the `sSup` meaningful, and the comparison with the optimized quantity.  Boundedness is where the
subnormalized case is delicate: it needs a positive lower bound on `Tr σ_B`, supplied here by
`ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower`.

Two facts of independent interest fall out along the way:
`conditionalMinEntropy_le_conditionalEntropy`, proved by perturbing an arbitrary feasible reference
to a positive definite one, and the center migration lemmas that move a subnormalized smoothing
ball from a subnormalized center to a normalized one.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal
open Filter

noncomputable section
universe u v w
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace MState

theorem rpow_two_mul_log2_pos {x gamma : ℝ} (hx : 0 < x) :
    Real.rpow 2 (gamma * log2 x) = x ^ gamma := by
  apply Real.log_injOn_pos
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    (Real.rpow_pos_of_pos hx gamma)
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow hx]
  unfold log2
  field_simp [ne_of_gt (Real.log_pos one_lt_two)]

theorem rpow_two_neg_sub_mul_log2_pos {H gamma x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (-(H - gamma * log2 x)) =
      Real.rpow 2 (-H) * x ^ gamma := by
  calc
    Real.rpow 2 (-(H - gamma * log2 x)) =
        Real.rpow 2 (-H + gamma * log2 x) := by ring_nf
    _ = Real.rpow 2 (-H) * Real.rpow 2 (gamma * log2 x) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-H) (gamma * log2 x)
    _ = Real.rpow 2 (-H) * x ^ gamma := by
        rw [rpow_two_mul_log2_pos hx]

theorem trace_conjTranspose_mul_hermitian_re_eq
    {ι : Type*} [Fintype ι] {G D : CMatrix ι} (hD : D.IsHermitian) :
    ((Matrix.conjTranspose G * D).trace).re = ((G * D).trace).re := by
  have htrace :
      (Matrix.conjTranspose G * D).trace = star ((G * D).trace) := by
    calc
      (Matrix.conjTranspose G * D).trace =
          (D * Matrix.conjTranspose G).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (Matrix.conjTranspose (G * D)).trace := by
        rw [Matrix.conjTranspose_mul, hD.eq]
      _ = star ((G * D).trace) := Matrix.trace_conjTranspose _
  rw [htrace]
  simp

/-- Fuchs--van de Graaf lower bound gives a trace-distance control on
purified distance. -/
theorem purifiedDistance_le_sqrt_two_mul_normalizedTraceDistance
    (ρ σ : MState (a × b)) :
    ρ.purifiedDistance σ ≤
      Real.sqrt (2 * ρ.normalizedTraceDistance σ) := by
  have hF_nonneg : 0 ≤ ρ.fidelity σ := ρ.fidelity_nonneg σ
  have hF_sq_le : ρ.fidelity σ ^ 2 ≤ 1 := by
    simpa [MState.squaredFidelity_eq_fidelity_sq] using
      ρ.squaredFidelity_le_one σ
  have hF_le_one : ρ.fidelity σ ≤ 1 := by
    nlinarith [hF_nonneg, hF_sq_le]
  have hD_nonneg : 0 ≤ ρ.normalizedTraceDistance σ :=
    MState.normalizedTraceDistance_nonneg ρ σ
  have hlow : 1 - ρ.fidelity σ ≤ ρ.normalizedTraceDistance σ :=
    ρ.fuchs_van_de_graaf_lower σ
  have hprod :
      (1 - ρ.fidelity σ) * (1 + ρ.fidelity σ) ≤
        ρ.normalizedTraceDistance σ * 2 := by
    refine mul_le_mul hlow ?_ ?_ hD_nonneg
    · nlinarith [hF_le_one]
    · nlinarith [hF_nonneg]
  have hsf_le_one : ρ.squaredFidelity σ ≤ 1 :=
    ρ.squaredFidelity_le_one σ
  have harg_nonneg : 0 ≤ 1 - ρ.squaredFidelity σ := by
    linarith
  rw [MState.purifiedDistance_eq]
  refine Real.le_sqrt_of_sq_le ?_
  rw [Real.sq_sqrt harg_nonneg]
  rw [MState.squaredFidelity_eq_fidelity_sq]
  nlinarith [hprod]

/-- Normalized trace distance from a fixed state is continuous. -/
theorem finiteAEP_normalizedTraceDistance_continuous_left
    (σ : MState (a × b)) :
    Continuous fun ρ : MState (a × b) => ρ.normalizedTraceDistance σ := by
  rw [show (fun ρ : MState (a × b) => ρ.normalizedTraceDistance σ) =
      fun ρ : MState (a × b) =>
        (1 / 2 : ℝ) * traceNorm (ρ.m - σ.m) by
    funext ρ
    rw [MState.normalizedTraceDistance_eq_matrix, QIT.normalizedTraceDistance_eq,
      QIT.traceNormDistance]]
  exact continuous_const.mul
    (QIT.traceNorm_continuous.comp (by fun_prop))

private theorem log2_card_left_nonneg (ρ : MState (a × b)) :
    0 ≤ log2 (Fintype.card a : ℝ) := by
  have : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  have hcard_one : 1 ≤ (Fintype.card a : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr inferInstance))
  exact div_nonneg (Real.log_nonneg hcard_one)
    (le_of_lt (Real.log_pos one_lt_two))

theorem ConditionalMinEntropyFeasible_scale_lower_bound
    {ρ : MState (a × b)} {σ : MState b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (Fintype.card a : ℝ)⁻¹ ≤ Real.rpow 2 (-lam) := by
  have : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  have htrace := cMatrix_trace_re_le_of_le h
  have hleft : ρ.m.trace.re = 1 := by
    rw [ρ.tr']
    norm_num
  have hright :
      (((Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ).trace).re =
        Real.rpow 2 (-lam) * (Fintype.card a : ℝ) := by
    rw [Matrix.trace_smul]
    simp [identityTensorStateMatrix_trace_re (a := a) σ]
  rw [hleft, hright] at htrace
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  rw [inv_le_iff_one_le_mul₀ hcard_pos]
  simpa [mul_comm] using htrace

private theorem conditionalMinEntropyFeasibleSet_bddAbove
    (ρ : MState (a × b)) :
    BddAbove {lam : ℝ | ∃ τ : MState b,
      ConditionalMinEntropyFeasible (a := a) ρ τ lam} := by
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro lam hlam
  rcases hlam with ⟨τ, hτ⟩
  exact conditionalMinEntropyFeasible_le_log2_card_left (a := a) hτ

/-! ## Fixed-reference conditional min-entropy -/

/-- Conditional min-entropy with the conditioning state `σ_B` fixed.

This is the fixed-reference candidate
`sup {λ | ρ_AB ≤ 2^{-λ} (I_A ⊗ σ_B)}`.  Optimizing this quantity over `σ_B`
recovers the candidate set used by `MState.conditionalMinEntropy`. -/
def conditionalMinEntropyFixed (ρ : MState (a × b)) (σ : MState b) : ℝ :=
  sSup {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam}

@[simp]
theorem conditionalMinEntropyFixed_eq (ρ : MState (a × b)) (σ : MState b) :
    ρ.conditionalMinEntropyFixed σ =
      sSup {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam} :=
  rfl

/-- A fixed-reference feasible exponent is an optimized feasible exponent, so
the fixed-reference min-entropy is bounded by the optimized min-entropy.

The nonemptiness hypothesis is necessary for this real-valued `sSup` API:
if the fixed `σ_B` has no feasible exponent, the mathematical value should be
`-∞`, while Lean's real `sSup ∅` is `0`. -/
theorem conditionalMinEntropyFixed_le_conditionalMinEntropy
    (ρ : MState (a × b)) (σ : MState b)
    (hfixed : ({lam : ℝ |
      ConditionalMinEntropyFeasible (a := a) ρ σ lam}).Nonempty) :
    ρ.conditionalMinEntropyFixed σ ≤ ρ.conditionalMinEntropy := by
  rw [conditionalMinEntropyFixed_eq, conditionalMinEntropy_eq]
  refine csSup_le hfixed ?_
  intro lam hlam
  exact le_csSup (conditionalMinEntropyFeasibleSet_bddAbove (a := a) ρ)
    (show ∃ τ : MState b, ConditionalMinEntropyFeasible (a := a) ρ τ lam from
      ⟨σ, hlam⟩)

/-- Fixed-reference conditional min-entropy is bounded above by the left-system
dimension. -/
theorem conditionalMinEntropyFixed_le_log2_card_left
    (ρ : MState (a × b)) (σ : MState b) :
    ρ.conditionalMinEntropyFixed σ ≤ log2 (Fintype.card a : ℝ) := by
  rw [conditionalMinEntropyFixed_eq]
  by_cases hne :
      ({lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam}).Nonempty
  · exact csSup_le hne fun lam hlam =>
      conditionalMinEntropyFeasible_le_log2_card_left (a := a) hlam
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact log2_card_left_nonneg (a := a) ρ

theorem ConditionalMinEntropyFeasible_le_conditionalEntropy_of_posDef_reference
    (ρ : MState (a × b)) (σ : MState b) (hσ : σ.m.PosDef) {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ ρ.conditionalEntropy :=
  conditionalMinEntropyFeasible_le_conditionalEntropy_of_supportTraceLog_nonneg
    (ρ := ρ) (σ := σ) hσ hfeas
    (conditionalMinEntropyFeasible_supportTraceLog_residual_nonneg
      (ρ := ρ) (σ := σ) hσ hfeas)

private theorem ConditionalMinEntropyFeasible.exists_posDef_reference_below
    {ρ : MState (a × b)} {σ : MState b} {lam μ : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam)
    (hμ : μ < lam) :
    ∃ σ' : MState b, σ'.m.PosDef ∧
      ConditionalMinEntropyFeasible (a := a) ρ σ' μ := by
  classical
  let : Nonempty b := σ.nonempty
  let q : ℝ := Real.rpow 2 (μ - lam)
  let p : ℝ := 1 - q
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    linarith
  have hp1 : p ≤ 1 := by
    dsimp [p]
    linarith
  have hp_pos : 0 < p := by
    dsimp [p]
    linarith
  let m : MState b := (MState.uniform : MState b)
  let σ' : MState b := MState.regularizedWithState σ m p hp0 hp1
  have hσ'pos : σ'.m.PosDef := by
    simpa [σ'] using
      MState.regularizedWithState_posDef_of_noise σ m
        (MState.uniform_posDef (d := b)) hp0 hp1 hp_pos
  refine ⟨σ', hσ'pos, ?_⟩
  rw [ConditionalMinEntropyFeasible] at hfeas ⊢
  let cμ : ℝ := Real.rpow 2 (-μ)
  let cLam : ℝ := Real.rpow 2 (-lam)
  let Tσ : CMatrix (a × b) := identityTensorStateMatrix (a := a) σ
  let Tm : CMatrix (a × b) := identityTensorStateMatrix (a := a) m
  have hcμ_nonneg : 0 ≤ cμ := by
    dsimp [cμ]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-μ)
  have hp_nonneg : 0 ≤ p := hp0
  have hcoef :
      cμ * (1 - p) = cLam := by
    have hq_def : 1 - p = q := by
      dsimp [p]
      ring
    calc
      cμ * (1 - p) = cμ * q := by rw [hq_def]
      _ = Real.rpow 2 (-μ) * Real.rpow 2 (μ - lam) := rfl
      _ = Real.rpow 2 ((-μ) + (μ - lam)) := by
        exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-μ) (μ - lam)).symm
      _ = cLam := by
        dsimp [cLam]
        ring_nf
  have hσ'_tensor :
      identityTensorStateMatrix (a := a) σ' =
        ((1 - p : ℝ) : ℂ) • Tσ + ((p : ℝ) : ℂ) • Tm := by
    ext x y
    simp [σ', MState.regularizedWithState_matrix, MState.regularizedStateMatrix,
      Tσ, Tm, identityTensorStateMatrix, Matrix.kroneckerMap_apply,
      Complex.real_smul]
    ring
  have hside :
      ((cμ : ℂ) • identityTensorStateMatrix (a := a) σ') =
        ((cLam : ℂ) • Tσ) + (((cμ * p : ℝ) : ℂ) • Tm) := by
    rw [hσ'_tensor, smul_add, smul_smul, smul_smul]
    have hcoefC : (cμ : ℂ) * ((1 - p : ℝ) : ℂ) = (cLam : ℂ) := by
      exact_mod_cast hcoef
    have hcoefCp : (cμ : ℂ) * ((p : ℝ) : ℂ) = ((cμ * p : ℝ) : ℂ) := by
      norm_num
    rw [hcoefC, hcoefCp]
  refine le_trans hfeas ?_
  rw [hside]
  exact le_add_of_nonneg_right (by
    have hscaleC : (0 : ℂ) ≤ ((cμ * p : ℝ) : ℂ) := by
      exact_mod_cast mul_nonneg hcμ_nonneg hp_nonneg
    simpa [Matrix.le_iff, Tm] using
      Matrix.PosSemidef.smul (identityTensorStateMatrix_posSemidef (a := a) m)
        hscaleC)

theorem ConditionalMinEntropyFeasible_le_conditionalEntropy
    (ρ : MState (a × b)) (σ : MState b) {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ ρ.conditionalEntropy := by
  by_contra hnot
  have hlt : ρ.conditionalEntropy < lam := lt_of_not_ge hnot
  let μ : ℝ := (ρ.conditionalEntropy + lam) / 2
  have hμ_lam : μ < lam := by
    change (ρ.conditionalEntropy + lam) / 2 < lam
    linarith
  have hH_μ : ρ.conditionalEntropy < μ := by
    change ρ.conditionalEntropy < (ρ.conditionalEntropy + lam) / 2
    linarith
  rcases ConditionalMinEntropyFeasible.exists_posDef_reference_below
      (a := a) hfeas hμ_lam with ⟨σ', hσ', hfeas'⟩
  have hμ_le_H :
      μ ≤ ρ.conditionalEntropy :=
    ConditionalMinEntropyFeasible_le_conditionalEntropy_of_posDef_reference
      (ρ := ρ) (σ := σ') hσ' hfeas'
  linarith

theorem conditionalMinEntropy_le_conditionalEntropy
    (ρ : MState (a × b)) :
    ρ.conditionalMinEntropy ≤ ρ.conditionalEntropy := by
  classical
  let : Nonempty b := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  rw [conditionalMinEntropy_eq]
  change sSup (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)) ≤
    ρ.conditionalEntropy
  refine csSup_le (ρ.conditionalMinEntropyFeasibleExponentValueSet_nonempty (a := a)) ?_
  intro lam hlam
  rcases hlam with ⟨σ, hfeas⟩
  exact ConditionalMinEntropyFeasible_le_conditionalEntropy
    (ρ := ρ) (σ := σ) hfeas

/-! ## Fixed-reference smooth conditional min-entropy -/

/-- Candidate values for the fixed-reference smooth conditional min-entropy.

The nearby state is smoothed in purified distance, while the side-information
reference `σ_B` is kept fixed in the unsmoothed min-entropy of each witness. -/
def SmoothConditionalMinEntropyFixedCandidate
    (ρ : MState (a × b)) (σ : MState b) (ε h : ℝ) : Prop :=
  ∃ ρ' : MState (a × b), ρ.purifiedBall ε ρ' ∧
    h = ρ'.conditionalMinEntropyFixed σ

@[simp]
theorem SmoothConditionalMinEntropyFixedCandidate_eq
    (ρ : MState (a × b)) (σ : MState b) (ε h : ℝ) :
    SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h ↔
      ∃ ρ' : MState (a × b), ρ.purifiedBall ε ρ' ∧
        h = ρ'.conditionalMinEntropyFixed σ :=
  Iff.rfl

/-- Fixed-reference smooth min-entropy candidates are monotone in the smoothing
radius. -/
theorem SmoothConditionalMinEntropyFixedCandidate_mono
    {ρ : MState (a × b)} {σ : MState b} {ε δ h : ℝ} (hεδ : ε ≤ δ) :
    SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h →
      SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ δ h := by
  rintro ⟨ρ', hball, hh⟩
  exact ⟨ρ', purifiedBall_mono hεδ hball, hh⟩

/-- Fixed-reference smooth conditional min-entropy as the supremum of
fixed-reference min-entropies over the purified-distance epsilon ball. -/
def smoothConditionalMinEntropyFixed
    (ρ : MState (a × b)) (σ : MState b) (ε : ℝ) : ℝ :=
  sSup {h : ℝ | SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h}

theorem smoothConditionalMinEntropyFixed_eq_sSup_candidates
    (ρ : MState (a × b)) (σ : MState b) (ε : ℝ) :
    ρ.smoothConditionalMinEntropyFixed σ ε =
      sSup {h : ℝ |
        SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMinEntropyFixed_eq
    (ρ : MState (a × b)) (σ : MState b) (ε : ℝ) :
    ρ.smoothConditionalMinEntropyFixed σ ε =
      sSup {h : ℝ |
        ∃ ρ' : MState (a × b), ρ.purifiedBall ε ρ' ∧
          h = ρ'.conditionalMinEntropyFixed σ} :=
  rfl

/-- Fixed-reference smooth min-entropy candidates are bounded above by the
left-system dimension. -/
theorem SmoothConditionalMinEntropyFixedCandidate_bddAbove
    (ρ : MState (a × b)) (σ : MState b) (ε : ℝ) :
    BddAbove {h : ℝ |
      SmoothConditionalMinEntropyFixedCandidate (a := a) ρ σ ε h} := by
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro h hh
  rcases hh with ⟨ρ', _hball, rfl⟩
  exact conditionalMinEntropyFixed_le_log2_card_left (a := a) ρ' σ

/-- Fixed-reference smooth conditional min-entropy is monotone in the smoothing
radius. -/
theorem smoothConditionalMinEntropyFixed_mono
    {ρ : MState (a × b)} {σ : MState b} {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    ρ.smoothConditionalMinEntropyFixed σ ε ≤
      ρ.smoothConditionalMinEntropyFixed σ δ := by
  rw [smoothConditionalMinEntropyFixed_eq_sSup_candidates,
    smoothConditionalMinEntropyFixed_eq_sSup_candidates]
  refine csSup_le ?_ ?_
  · exact ⟨ρ.conditionalMinEntropyFixed σ, ρ, MState.purifiedBall_self_of_nonneg ρ hε, rfl⟩
  intro h hh
  exact le_csSup
    (SmoothConditionalMinEntropyFixedCandidate_bddAbove (a := a) ρ σ δ)
    (SmoothConditionalMinEntropyFixedCandidate_mono (a := a) (ρ := ρ)
      (σ := σ) hεδ hh)

/-- Fixed-reference smooth min-entropy is bounded by the normalized-candidate
optimized smooth min-entropy variant. -/
theorem smoothConditionalMinEntropyFixed_le_smoothConditionalMinEntropyNormalizedCandidates
    (ρ : MState (a × b)) (σ : MState b) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hfixed : ∀ ρ' : MState (a × b), ρ.purifiedBall ε ρ' →
      ({lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ' σ lam}).Nonempty) :
    ρ.smoothConditionalMinEntropyFixed σ ε ≤
      ρ.smoothConditionalMinEntropyNormalizedCandidates ε := by
  rw [smoothConditionalMinEntropyFixed_eq_sSup_candidates,
    smoothConditionalMinEntropyNormalizedCandidates_eq_sSup_candidates]
  refine csSup_le ?_ ?_
  · exact ⟨ρ.conditionalMinEntropyFixed σ, ρ, MState.purifiedBall_self_of_nonneg ρ hε, rfl⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  exact le_trans
    (conditionalMinEntropyFixed_le_conditionalMinEntropy ρ' σ (hfixed ρ' hball))
    (le_csSup
      (SmoothConditionalMinEntropyCandidate_bddAbove (a := a) ρ ε)
      (show SmoothConditionalMinEntropyCandidate (a := a) ρ ε
        ρ'.conditionalMinEntropy from ⟨ρ', hball, rfl⟩))

end MState

namespace QIT

namespace SubnormalizedState

private theorem identityTensorStateMatrix_trace_re_le_card
    (σ : SubnormalizedState b) :
    (identityTensorStateMatrix (a := a) σ).trace.re ≤ (Fintype.card a : ℝ) := by
  change ((1 : CMatrix a) ⊗ₖ σ.matrix).trace.re ≤
    (Fintype.card a : ℝ)
  rw [Matrix.trace_kronecker, Matrix.trace_one]
  rw [Complex.mul_re, σ.trace_im_zero]
  simp
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by positivity
  exact mul_le_of_le_one_right hcard_nonneg σ.trace_le_one

private theorem ConditionalMinEntropyFeasible_scale_lower_bound_of_trace_lower
    [Nonempty a]
    {ρ : SubnormalizedState (a × b)} {σ : SubnormalizedState b}
    {lam δ : ℝ}
    (_hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re)
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    δ / (Fintype.card a : ℝ) ≤ Real.rpow 2 (-lam) := by
  have htrace := cMatrix_trace_re_le_of_le h
  have hright_le :
      (((Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ).trace).re ≤
        Real.rpow 2 (-lam) * (Fintype.card a : ℝ) := by
    rw [Matrix.trace_smul]
    simp
    exact mul_le_mul_of_nonneg_left
      (identityTensorStateMatrix_trace_re_le_card (a := a) σ)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hδ_le : δ ≤ Real.rpow 2 (-lam) * (Fintype.card a : ℝ) :=
    le_trans hδρ (le_trans htrace hright_le)
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  exact (div_le_iff₀ hcard_pos).mpr hδ_le

private theorem one_le_inv_smul_identityTensorStateMatrix_toSubnormalized_of_posDef
    (σ : MState b) (hσ : σ.m.PosDef) :
    ∃ c : ℝ, 0 < c ∧
      (1 : CMatrix (a × b)) ≤
        ((c⁻¹ : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ.toSubnormalized := by
  rcases MState.exists_pos_scalar_smul_one_le_matrix_of_posDef σ hσ
    with ⟨c, hc_pos, hc_le⟩
  refine ⟨c, hc_pos, ?_⟩
  have hdiffB : (σ.m - c • (1 : CMatrix b)).PosSemidef := by
    simpa [Matrix.le_iff] using hc_le
  rw [Matrix.le_iff]
  have hdiff :
      ((c⁻¹ : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ.toSubnormalized -
          (1 : CMatrix (a × b)) =
        ((c⁻¹ : ℝ) : ℂ) •
          ((1 : CMatrix a) ⊗ₖ (σ.m - c • (1 : CMatrix b))) := by
    ext x y
    rcases x with ⟨xa, xb⟩
    rcases y with ⟨ya, yb⟩
    by_cases hA : xa = ya
    · subst ya
      by_cases hB : xb = yb
      · subst yb
        simp [SubnormalizedState.identityTensorStateMatrix, identityTensorStateMatrix,
          Matrix.kroneckerMap_apply]
        field_simp [ne_of_gt hc_pos]
      · simp [SubnormalizedState.identityTensorStateMatrix, identityTensorStateMatrix,
          Matrix.kroneckerMap_apply, hB]
    · simp [SubnormalizedState.identityTensorStateMatrix, identityTensorStateMatrix,
        Matrix.kroneckerMap_apply, hA]
  rw [hdiff]
  exact Matrix.PosSemidef.smul
    (Matrix.PosSemidef.one.kronecker hdiffB)
    (by exact_mod_cast inv_nonneg.mpr hc_pos.le)

/-- A positive-definite fixed normalized side reference makes every
subnormalized joint witness feasible for some fixed-reference min-entropy
exponent. -/
theorem conditionalMinEntropyFixed_feasibleSet_nonempty_of_posDef_reference
    (ρ : SubnormalizedState (a × b)) (σ : MState b) (hσ : σ.m.PosDef) :
    ({lam : ℝ |
      ConditionalMinEntropyFeasible (a := a) ρ σ.toSubnormalized lam}).Nonempty := by
  rcases one_le_inv_smul_identityTensorStateMatrix_toSubnormalized_of_posDef
      (a := a) σ hσ with ⟨c, hc_pos, hone_le⟩
  let lam : ℝ := -log2 c⁻¹
  refine ⟨lam, ?_⟩
  have hρ_le :
      ρ.matrix ≤
        ((c⁻¹ : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ.toSubnormalized :=
    le_trans ρ.matrix_le_one hone_le
  have hrpow : Real.rpow 2 (-lam) = c⁻¹ := by
    dsimp [lam]
    rw [neg_neg]
    exact rpow_two_log2_pos (inv_pos.mpr hc_pos)
  change ρ.matrix ≤
    ((Real.rpow 2 (-lam) : ℝ) : ℂ) • identityTensorStateMatrix (a := a) σ.toSubnormalized
  rw [hrpow]
  exact hρ_le

private theorem ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
    [Nonempty a]
    {ρ : SubnormalizedState (a × b)} {σ : SubnormalizedState b}
    {lam δ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re)
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ log2 (Fintype.card a : ℝ) - log2 δ := by
  have hscale :=
    ConditionalMinEntropyFeasible_scale_lower_bound_of_trace_lower
      (a := a) hδ hδρ h
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hδ_div_pos : 0 < δ / (Fintype.card a : ℝ) :=
    div_pos hδ hcard_pos
  have hlog := Real.log_le_log hδ_div_pos hscale
  have hdiv := div_le_div_of_nonneg_right hlog
    (le_of_lt (Real.log_pos one_lt_two))
  change log2 (δ / (Fintype.card a : ℝ)) ≤
    log2 (Real.rpow 2 (-lam)) at hdiv
  have hneg := neg_le_neg hdiv
  have hleft :
      -log2 (δ / (Fintype.card a : ℝ)) =
        log2 (Fintype.card a : ℝ) - log2 δ := by
    unfold log2
    rw [Real.log_div hδ.ne' hcard_pos.ne']
    ring
  rw [neg_log2_rpow_two_neg lam, hleft] at hneg
  exact hneg

/-! ## Subnormalized fixed-reference conditional min-entropy -/

/-- Subnormalized conditional min-entropy with the conditioning state fixed.

Both the joint witness and the side reference are subnormalized, matching the
subnormalized `ConditionalMinEntropyFeasible` API in `Smooth.lean`. -/
def conditionalMinEntropyFixed
    (ρ : SubnormalizedState (a × b)) (σ : SubnormalizedState b) : ℝ :=
  sSup {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam}

@[simp]
theorem conditionalMinEntropyFixed_eq
    (ρ : SubnormalizedState (a × b)) (σ : SubnormalizedState b) :
    ρ.conditionalMinEntropyFixed σ =
      sSup {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam} :=
  rfl

/-- Fixed-reference subnormalized min-entropy candidates are bounded above
when the joint state has a positive trace lower bound. -/
theorem conditionalMinEntropyFixed_feasibleSet_bddAbove_of_trace_lower
    [Nonempty a]
    (ρ : SubnormalizedState (a × b)) (σ : SubnormalizedState b)
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re) :
    BddAbove {lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam} := by
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro lam hlam
  exact ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
    (a := a) hδ hδρ hlam

/-- Fixed-reference subnormalized min-entropy is bounded above when the joint
state has a positive trace lower bound. -/
theorem conditionalMinEntropyFixed_le_of_trace_lower_bound
    [Nonempty a]
    (ρ : SubnormalizedState (a × b)) (σ : SubnormalizedState b)
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re)
    (hδ_le_one : δ ≤ 1) :
    ρ.conditionalMinEntropyFixed σ ≤ log2 (Fintype.card a : ℝ) - log2 δ := by
  rw [conditionalMinEntropyFixed_eq]
  by_cases hne :
      ({lam : ℝ | ConditionalMinEntropyFeasible (a := a) ρ σ lam}).Nonempty
  · exact csSup_le hne fun lam hlam =>
      ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
        (a := a) hδ hδρ hlam
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    have hcard_one : 1 ≤ (Fintype.card a : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr inferInstance))
    have hlog_card_nonneg : 0 ≤ log2 (Fintype.card a : ℝ) := by
      exact div_nonneg (Real.log_nonneg hcard_one)
        (le_of_lt (Real.log_pos one_lt_two))
    have hlogδ_nonpos : log2 δ ≤ 0 := by
      unfold log2
      have hlogδ : Real.log δ ≤ Real.log 1 := Real.log_le_log hδ hδ_le_one
      rw [Real.log_one] at hlogδ
      exact div_nonpos_of_nonpos_of_nonneg hlogδ
        (le_of_lt (Real.log_pos one_lt_two))
    linarith

/-- Optimized subnormalized min-entropy feasible exponents are bounded above
when the joint state has a positive trace lower bound. -/
theorem conditionalMinEntropy_feasibleSet_bddAbove_of_trace_lower
    [Nonempty a]
    (ρ : SubnormalizedState (a × b))
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ.matrix.trace.re) :
    BddAbove {lam : ℝ | ∃ σ : SubnormalizedState b,
      ConditionalMinEntropyFeasible (a := a) ρ σ lam} := by
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro lam hlam
  rcases hlam with ⟨σ, hσ⟩
  exact ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
    (a := a) hδ hδρ hσ

/-- Fixed-reference subnormalized min-entropy is bounded by the optimized
subnormalized min-entropy, provided the fixed feasible set is nonempty.

The nonempty hypothesis mirrors the normalized fixed-reference API and avoids
assigning artificial finite content to zero-support corner cases. -/
theorem conditionalMinEntropyFixed_le_conditionalMinEntropy
    [Nonempty a]
    (ρ : SubnormalizedState (a × b)) (σ : SubnormalizedState b)
    (hfixed : ({lam : ℝ |
      ConditionalMinEntropyFeasible (a := a) ρ σ lam}).Nonempty)
    (hρtr : 0 < ρ.matrix.trace.re) :
    ρ.conditionalMinEntropyFixed σ ≤ ρ.conditionalMinEntropyRaw := by
  rw [conditionalMinEntropyFixed_eq, conditionalMinEntropyRaw_eq]
  refine csSup_le hfixed ?_
  intro lam hlam
  exact le_csSup
    (conditionalMinEntropy_feasibleSet_bddAbove_of_trace_lower
      (a := a) ρ hρtr le_rfl)
    (show ∃ τ : SubnormalizedState b,
      ConditionalMinEntropyFeasible (a := a) ρ τ lam from ⟨σ, hlam⟩)

/-- Any feasible fixed-reference exponent lower-bounds the subnormalized
fixed-reference conditional min-entropy, provided the witness has positive
trace.  The trace hypothesis is the real-valued `sSup` replacement for the
usual extended-real `-∞` zero-trace corner. -/
theorem le_conditionalMinEntropyFixed_of_feasible
    [Nonempty a]
    {ρ : SubnormalizedState (a × b)} {σ : SubnormalizedState b} {lam : ℝ}
    (hρtr : 0 < ρ.matrix.trace.re)
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ ρ.conditionalMinEntropyFixed σ := by
  rw [conditionalMinEntropyFixed_eq]
  exact le_csSup
    (conditionalMinEntropyFixed_feasibleSet_bddAbove_of_trace_lower
      (a := a) ρ σ hρtr le_rfl)
    hfeas

end SubnormalizedState

end QIT

namespace MState

/-! ## Fixed-reference smooth min-entropy with subnormalized witnesses -/

/-- Candidate values for fixed-reference smooth conditional min-entropy around
a normalized center, allowing subnormalized witnesses in the purified ball. -/
def SmoothConditionalMinEntropyFixedSubnormalizedCandidate
    (ρ : MState (a × b)) (σ : SubnormalizedState b) (ε h : ℝ) : Prop :=
  ∃ ρ' : SubnormalizedState (a × b),
    ρ.toSubnormalized.purifiedBall ε ρ' ∧
      h = ρ'.conditionalMinEntropyFixed σ

@[simp]
theorem SmoothConditionalMinEntropyFixedSubnormalizedCandidate_eq
    (ρ : MState (a × b)) (σ : SubnormalizedState b) (ε h : ℝ) :
    SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε h ↔
      ∃ ρ' : SubnormalizedState (a × b),
        ρ.toSubnormalized.purifiedBall ε ρ' ∧
          h = ρ'.conditionalMinEntropyFixed σ :=
  Iff.rfl

/-- Fixed-reference smooth conditional min-entropy with subnormalized witnesses
and a fixed subnormalized side reference. -/
def smoothConditionalMinEntropyFixedSubnormalized
    (ρ : MState (a × b)) (σ : SubnormalizedState b) (ε : ℝ) : ℝ :=
  sSup {h : ℝ |
    SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε h}

theorem smoothConditionalMinEntropyFixedSubnormalized_eq_sSup_candidates
    (ρ : MState (a × b)) (σ : SubnormalizedState b) (ε : ℝ) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε =
      sSup {h : ℝ |
        SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε h} :=
  rfl

@[simp]
theorem smoothConditionalMinEntropyFixedSubnormalized_eq
    (ρ : MState (a × b)) (σ : SubnormalizedState b) (ε : ℝ) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε =
      sSup {h : ℝ |
        ∃ ρ' : SubnormalizedState (a × b),
          ρ.toSubnormalized.purifiedBall ε ρ' ∧
            h = ρ'.conditionalMinEntropyFixed σ} :=
  rfl

/-- Subnormalized fixed-reference smooth-min candidates around a normalized
center are bounded above for radii below one. -/
theorem SmoothConditionalMinEntropyFixedSubnormalizedCandidate_bddAbove
    (ρ : MState (a × b)) (σ : SubnormalizedState b) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) :
    BddAbove {h : ℝ |
      SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε h} := by
  have : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  let δ : ℝ := (1 - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε_lt)
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    nlinarith
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hε_sqrt : ε < Real.sqrt ρ.toSubnormalized.matrix.trace.re := by
    rw [MState.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hδρ' : δ ≤ ρ'.matrix.trace.re := by
    have hcenter_trace : ρ.m.trace.re = 1 := by
      rw [ρ.tr']
      norm_num
    simpa [δ, hcenter_trace] using
      ρ.toSubnormalized.purifiedBall_trace_lower_bound ρ' hε_sqrt hball
  exact SubnormalizedState.conditionalMinEntropyFixed_le_of_trace_lower_bound
    (a := a) ρ' σ hδ hδρ' hδ_le_one

/-- Subnormalized smooth min-entropy candidates around a normalized center are
bounded above for radii below one. -/
theorem SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_state_center
    (ρ : MState (a × b)) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1) :
    BddAbove {h : ℝ |
      SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := a)
        ρ.toSubnormalized ε h} := by
  have : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  let δ : ℝ := (1 - ε) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (sub_pos.mpr hε_lt)
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    nlinarith
  refine ⟨log2 (Fintype.card a : ℝ) - log2 δ, ?_⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hε_sqrt : ε < Real.sqrt ρ.toSubnormalized.matrix.trace.re := by
    rw [MState.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hδρ' : δ ≤ ρ'.matrix.trace.re := by
    have hcenter_trace : ρ.m.trace.re = 1 := by
      rw [ρ.tr']
      norm_num
    simpa [δ, hcenter_trace] using
      ρ.toSubnormalized.purifiedBall_trace_lower_bound ρ' hε_sqrt hball
  rw [SubnormalizedState.conditionalMinEntropyRaw_eq]
  by_cases hne :
      ({lam : ℝ | ∃ σ : SubnormalizedState b,
        SubnormalizedState.ConditionalMinEntropyFeasible (a := a) ρ' σ lam}).Nonempty
  · exact csSup_le hne fun lam hlam =>
      SubnormalizedState.ConditionalMinEntropyFeasible_le_log2_card_sub_log2_trace_lower
        (a := a) hδ hδρ' hlam.choose_spec
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    have hcard_one : 1 ≤ (Fintype.card a : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr inferInstance))
    have hlog_card_nonneg : 0 ≤ log2 (Fintype.card a : ℝ) := by
      exact div_nonneg (Real.log_nonneg hcard_one)
        (le_of_lt (Real.log_pos one_lt_two))
    have hlogδ_nonpos : log2 δ ≤ 0 := by
      unfold log2
      have hlogδ : Real.log δ ≤ Real.log 1 := Real.log_le_log hδ hδ_le_one
      rw [Real.log_one] at hlogδ
      exact div_nonpos_of_nonpos_of_nonneg hlogδ
        (le_of_lt (Real.log_pos one_lt_two))
    linarith

/-- Moving a normalized center only increases the smoothing radius needed for
subnormalized smooth min-entropy.  This is the `sSup`-level form of
`SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_center_migration`. -/
theorem subnormalizedSmoothConditionalMinEntropyRaw_center_migration
    (ρ η : MState (a × b)) {ε δ : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hεδ_nonneg : 0 ≤ ε + δ) (hεδ_lt : ε + δ < 1)
    (hcenter : η.toSubnormalized.purifiedDistance ρ.toSubnormalized ≤ δ) :
    η.toSubnormalized.smoothConditionalMinEntropyRaw ε ≤
      ρ.toSubnormalized.smoothConditionalMinEntropyRaw (ε + δ) := by
  rw [SubnormalizedState.smoothConditionalMinEntropyRaw_eq_sSup_candidates,
    SubnormalizedState.smoothConditionalMinEntropyRaw_eq_sSup_candidates]
  refine csSup_le ?_ ?_
  · exact ⟨η.toSubnormalized.conditionalMinEntropyRaw, η.toSubnormalized,
      SubnormalizedState.purifiedBall_self_of_nonneg η.toSubnormalized hε_nonneg, rfl⟩
  intro h hh
  exact le_csSup
    (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_state_center
      (a := a) ρ hεδ_nonneg hεδ_lt)
    (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_center_migration
      (a := a) hcenter hh)

/-- Tensor-power spelling of center migration for the unrestricted internal
smooth-min helper. Source-facing finite-AEP statements use the canonical
finite-domain API instead. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_center_migration
    (ρ η : MState (a × b)) (n : ℕ) {ε δ : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hεδ_nonneg : 0 ≤ ε + δ) (hεδ_lt : ε + δ < 1)
    (hcenter :
      (η.tensorPowerBipartite n).toSubnormalized.purifiedDistance
        (ρ.tensorPowerBipartite n).toSubnormalized ≤ δ) :
    η.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n ≤
      ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw (ε + δ) n := by
  simpa [MState.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_eq] using
    subnormalizedSmoothConditionalMinEntropyRaw_center_migration
      (a := TensorPower a n) (b := TensorPower b n)
      (ρ := ρ.tensorPowerBipartite n) (η := η.tensorPowerBipartite n)
      hε_nonneg hεδ_nonneg hεδ_lt hcenter

/-- Transfer a tensor-power smooth-min lower bound across nearby centers by
paying the purified-distance gap in the smoothing radius. -/
theorem tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_lower_bound_of_center_migration
    (ρ η : MState (a × b)) (n : ℕ) {ε δ L : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hεδ_nonneg : 0 ≤ ε + δ) (hεδ_lt : ε + δ < 1)
    (hcenter :
      (η.tensorPowerBipartite n).toSubnormalized.purifiedDistance
        (ρ.tensorPowerBipartite n).toSubnormalized ≤ δ)
    (hlower :
      L ≤ η.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw ε n) :
    L ≤ ρ.tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw (ε + δ) n := by
  exact le_trans hlower
    (tensorPowerSubnormalizedSmoothConditionalMinEntropyRaw_center_migration
      (ρ := ρ) (η := η) (n := n)
      hε_nonneg hεδ_nonneg hεδ_lt hcenter)

/-- Fixed-reference subnormalized smooth min-entropy is bounded by the
optimized subnormalized smooth min-entropy around the embedded normalized
center.

The fixed-reference nonempty hypothesis is local to each subnormalized witness,
matching the unsmoothed comparison. -/
theorem smoothConditionalMinEntropyFixedSubnormalized_le_subnormalizedSmoothConditionalMinEntropy
    (ρ : MState (a × b)) (σ : SubnormalizedState b) (ε : ℝ)
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1)
    (hfixed : ∀ ρ' : SubnormalizedState (a × b),
      ρ.toSubnormalized.purifiedBall ε ρ' →
        ({lam : ℝ |
          SubnormalizedState.ConditionalMinEntropyFeasible (a := a)
            ρ' σ lam}).Nonempty) :
    ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε ≤
      ρ.toSubnormalized.smoothConditionalMinEntropy ε hε_nonneg
        (by rw [MState.toSubnormalized_trace]; simpa using hε_lt) := by
  have : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  rw [smoothConditionalMinEntropyFixedSubnormalized_eq_sSup_candidates,
    SubnormalizedState.smoothConditionalMinEntropy_eq_sSup_candidates]
  refine csSup_le ?_ ?_
  · exact ⟨ρ.toSubnormalized.conditionalMinEntropyFixed σ,
      ρ.toSubnormalized, SubnormalizedState.purifiedBall_self_of_nonneg
        ρ.toSubnormalized hε_nonneg, rfl⟩
  intro h hh
  rcases hh with ⟨ρ', hball, rfl⟩
  have hε_sqrt : ε < Real.sqrt ρ.toSubnormalized.matrix.trace.re := by
    rw [MState.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hρ'tr : 0 < ρ'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      ρ.toSubnormalized ρ' hε_sqrt hball
  exact le_trans
    (SubnormalizedState.conditionalMinEntropyFixed_le_conditionalMinEntropy
      (a := a) ρ' σ (hfixed ρ' hball) hρ'tr)
    (le_csSup
      (SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw_bddAbove_of_state_center
        (a := a) ρ hε_nonneg hε_lt)
      (show SubnormalizedState.SmoothConditionalMinEntropyCandidateRaw (a := a)
          ρ.toSubnormalized ε ρ'.conditionalMinEntropyRaw from
        ⟨ρ', hball, rfl⟩))

/-- A subnormalized purified-ball witness with a fixed-reference feasible
exponent gives a lower bound on normalized-center, subnormalized-witness smooth
min-entropy. -/
theorem le_smoothConditionalMinEntropyFixedSubnormalized_of_feasible_witness
    {ρ : MState (a × b)} {ρ' : SubnormalizedState (a × b)}
    {σ : SubnormalizedState b} {ε lam lower : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_lt : ε < 1)
    (hball : ρ.toSubnormalized.purifiedBall ε ρ')
    (hfeas : SubnormalizedState.ConditionalMinEntropyFeasible (a := a) ρ' σ lam)
    (hlower : lower ≤ lam) :
    lower ≤ ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε := by
  have : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  have hε_sqrt : ε < Real.sqrt ρ.toSubnormalized.matrix.trace.re := by
    rw [MState.toSubnormalized_trace]
    norm_num
    exact hε_lt
  have hρ'tr : 0 < ρ'.matrix.trace.re :=
    SubnormalizedState.purifiedBall_trace_pos_of_lt_sqrt_trace
      ρ.toSubnormalized ρ' hε_sqrt hball
  have hmin : lam ≤ ρ'.conditionalMinEntropyFixed σ :=
    SubnormalizedState.le_conditionalMinEntropyFixed_of_feasible
      (a := a) hρ'tr hfeas
  have hsmooth :
      ρ'.conditionalMinEntropyFixed σ ≤
        ρ.smoothConditionalMinEntropyFixedSubnormalized σ ε := by
    rw [smoothConditionalMinEntropyFixedSubnormalized_eq_sSup_candidates]
    exact le_csSup
      (SmoothConditionalMinEntropyFixedSubnormalizedCandidate_bddAbove
        (a := a) ρ σ hε_nonneg hε_lt)
      (show SmoothConditionalMinEntropyFixedSubnormalizedCandidate (a := a) ρ σ ε
        (ρ'.conditionalMinEntropyFixed σ) from ⟨ρ', hball, rfl⟩)
  exact le_trans hlower (le_trans hmin hsmooth)

end MState
