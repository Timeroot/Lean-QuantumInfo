/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.SandwichedTensorPower

/-!
# Asymptotic lower-bound support

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.  It was split out mechanically from the historical
`EntanglementAssistedAsymptotic` files; theorem statements and proof routes are
unchanged.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

variable (N : Channel a b)

namespace OneShotNonempty

/-- The unique-outcome POVM, used only to show one-shot code candidate sets are
nonempty. -/
def unitPOVM (q : Type*) [Fintype q] [DecidableEq q] : POVM PUnit q where
  effects _ := 1
  pos _ := Matrix.PosSemidef.one
  sum_eq_one := by
    ext i j
    simp

end OneShotNonempty

/-- A one-message one-shot code used only as a nonemptiness witness for the
one-shot operational supremum. -/
def trivialOneShotEntanglementAssistedCode [Nonempty a] :
    EntanglementAssistedClassicalCode N 1 PUnit PUnit PUnit where
  sharedState := State.unit.prod State.unit
  encoder _ :=
    Channel.prepare (fun _ : PUnit =>
      (PureVector.basisPureVector : PureVector (QIT.TensorPower a 1)).state)
  decoder := OneShotNonempty.unitPOVM (Prod (QIT.TensorPower b 1) PUnit)

theorem trivialOneShotEntanglementAssistedCode_maxErrorAtMost
    [Nonempty a] {ε : ℝ} (hε : 0 ≤ ε) :
    (N.trivialOneShotEntanglementAssistedCode).maxErrorAtMost ε := by
  intro m
  cases m
  unfold EntanglementAssistedClassicalCode.error
    EntanglementAssistedClassicalCode.successProbability
  have hsum :=
    POVM.sum_prob (N.trivialOneShotEntanglementAssistedCode.decoder)
      (N.trivialOneShotEntanglementAssistedCode.outputState PUnit.unit)
  have hprob :
      ((N.trivialOneShotEntanglementAssistedCode.decoder.prob
        (N.trivialOneShotEntanglementAssistedCode.outputState PUnit.unit)
        PUnit.unit) : ℝ) = 1 := by
    have hreal := congrArg (fun x : ℝ≥0 => (x : ℝ)) hsum
    simpa using hreal
  rw [hprob]
  linarith

theorem oneShotEntanglementAssistedClassicalCapacityE_candidateSet_nonempty
    [Nonempty a] {ε : ℝ} (hε : 0 ≤ ε) :
    {R : EReal |
      ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
        ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
          ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
            ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
              C.maxErrorAtMost ε ∧ R = (C.rate : EReal)}.Nonempty := by
  refine ⟨((N.trivialOneShotEntanglementAssistedCode).rate : EReal), ?_⟩
  exact ⟨PUnit, inferInstance, inferInstance, inferInstance,
    PUnit, inferInstance, inferInstance,
    PUnit, inferInstance, inferInstance,
    N.trivialOneShotEntanglementAssistedCode,
    N.trivialOneShotEntanglementAssistedCode_maxErrorAtMost hε, rfl⟩

/-- Extract a concrete one-shot entanglement-assisted code from any strict
lower bound below the extended-real one-shot capacity. -/
theorem exists_oneShotCode_rate_gt_of_lt_oneShotCapacityE
    [Nonempty a] {ε lower : ℝ} (hε : 0 ≤ ε)
    (hlower : (lower : EReal) < N.oneShotEntanglementAssistedClassicalCapacityE ε) :
    ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M), ∃ (_ : Nonempty M),
      ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
        ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
          ∃ C : EntanglementAssistedClassicalCode N 1 M EA EB,
            C.maxErrorAtMost ε ∧ lower < C.rate := by
  unfold oneShotEntanglementAssistedClassicalCapacityE at hlower
  obtain ⟨value, hvalue_mem, hlt⟩ :=
    exists_lt_of_lt_csSup
      (N.oneShotEntanglementAssistedClassicalCapacityE_candidateSet_nonempty hε)
      hlower
  rcases hvalue_mem with
    ⟨M, hMfin, hMdec, hMnonempty,
      EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, C, hCerr, rfl⟩
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  exact ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance,
    C, hCerr, EReal.coe_lt_coe_iff.mp hlt⟩

/-- The single-letter channel mutual information is superadditive under
memoryless tensor powers in the direction needed for achievability:
`I(N^{⊗n}) ≥ n I(N)`. -/
theorem entanglementAssistedInformation_tensorPower_lower_bound
    [Nonempty a] (n : ℕ) :
    (n : ℝ) * N.entanglementAssistedInformation ≤
      (N.tensorPower n).entanglementAssistedInformation := by
  obtain ⟨ψ, hψ⟩ := N.exists_entanglementAssistedInformation_maximizer
  have hcandidate :
      (N.tensorPower n).entanglementAssistedMutualInformation
          (ψ.tensorPowerBipartite n) =
        (n : ℝ) * N.entanglementAssistedInformation := by
    rw [hψ]
    unfold Channel.entanglementAssistedMutualInformation
    rw [← Channel.hypothesisTestingOutputState_eq_entanglementAssistedOutputState
      (N.tensorPower n) (ψ.tensorPowerBipartite n)]
    rw [Channel.hypothesisTestingOutputState_tensorPowerBipartite]
    rw [Channel.hypothesisTestingOutputState_eq_entanglementAssistedOutputState]
    exact State.mutualInformation_tensorPowerBipartite
      (N.entanglementAssistedOutputState ψ) n
  calc
    (n : ℝ) * N.entanglementAssistedInformation =
        (N.tensorPower n).entanglementAssistedMutualInformation
          (ψ.tensorPowerBipartite n) := hcandidate.symm
    _ ≤ (N.tensorPower n).entanglementAssistedInformation :=
        (N.tensorPower n).entanglementAssistedMutualInformation_le_information
          (ψ.tensorPowerBipartite n)

/-- Fixed-input PSD barred Petz--Renyi mutual information is additive under
memoryless tensor powers. -/
theorem inputBarPetzRenyiMutualInformationPSDFinite_tensorPowerBipartite
    (ψ : PureVector (Prod a a)) (n : ℕ) (alpha : PetzRenyiAlpha) :
    (N.tensorPower n).inputBarPetzRenyiMutualInformationPSDFinite
        (ψ.tensorPowerBipartite n)
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) =
      (n : ℝ) *
        N.inputBarPetzRenyiMutualInformationPSDFinite
          ψ alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) := by
  unfold Channel.inputBarPetzRenyiMutualInformationPSDFinite
  rw [Channel.hypothesisTestingOutputState_tensorPowerBipartite]
  exact State.barPetzRenyiMutualInformationPSDFinite_tensorPowerBipartite
    (N.hypothesisTestingOutputState ψ) alpha.2.1 alpha.2.2 n

/-- The PSD barred Petz--Renyi channel mutual information is superadditive
under tensor powers in the direction needed by the asymptotic achievability
proof. -/
theorem barPetzRenyiMutualInformationPSDFinite_tensorPower_lower_bound
    [Nonempty a] {n : ℕ} (hn : 0 < n) (alpha : PetzRenyiAlpha) :
    (n : ℝ) *
        N.barPetzRenyiMutualInformationPSDFinite
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
      (N.tensorPower n).barPetzRenyiMutualInformationPSDFinite
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) := by
  classical
  rw [N.barPetzRenyiMutualInformationPSDFinite_eq_sSup,
    (N.tensorPower n).barPetzRenyiMutualInformationPSDFinite_eq_sSup]
  let S := N.barPetzRenyiMutualInformationPSDFiniteValueSet
    alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)
  let T := (N.tensorPower n).barPetzRenyiMutualInformationPSDFiniteValueSet
    alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)
  have hne : S.Nonempty := by
    let ψ0 : PureVector (Prod a a) := PureVector.basisPureVector
    refine ⟨N.inputBarPetzRenyiMutualInformationPSDFinite
      ψ0 alpha.1 alpha.2.1 (ne_of_lt alpha.2.2), ?_⟩
    exact ⟨ψ0, rfl⟩
  have hbddTensor : BddAbove T :=
    (N.tensorPower n).barPetzRenyiMutualInformationPSDFiniteValueSet_bddAbove alpha
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hsSup :
      sSup S ≤ sSup T / (n : ℝ) := by
    refine csSup_le hne ?_
    intro x hx
    rcases hx with ⟨ψ, rfl⟩
    have hmemT :
        (n : ℝ) *
            N.inputBarPetzRenyiMutualInformationPSDFinite
              ψ alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ∈ T := by
      refine ⟨ψ.tensorPowerBipartite n, ?_⟩
      exact (N.inputBarPetzRenyiMutualInformationPSDFinite_tensorPowerBipartite
        ψ n alpha).symm
    have hleT :
        (n : ℝ) *
            N.inputBarPetzRenyiMutualInformationPSDFinite
              ψ alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤ sSup T :=
      le_csSup hbddTensor hmemT
    exact (le_div_iff₀ hnR).mpr (by simpa [mul_comm] using hleT)
  calc
    (n : ℝ) * sSup S ≤ (n : ℝ) * (sSup T / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsSup (le_of_lt hnR)
    _ = sSup T := by
      field_simp [ne_of_gt hnR]

/-- Source-shaped `n`-use lower-bound witness used for the asymptotic
achievability passage.

For a fixed blocklength `n`, the witness packages a reliable `n`-use code whose
rate is lower-bounded by a supplied expression.  The one-shot lower-bound proof
constructs these witnesses for block channels; this structure is the
operational handoff to the asymptotic achievability statement. -/
structure EntanglementAssistedNUseLowerBoundWitness
    (n : ℕ) (ε lowerBound : ℝ)
    (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M]
    (EA : Type u) [Fintype EA] [DecidableEq EA]
    (EB : Type u) [Fintype EB] [DecidableEq EB] where
  code : EntanglementAssistedClassicalCode N n M EA EB
  maxError_le : code.maxErrorAtMost ε
  lowerBound_le_rate : lowerBound ≤ code.rate

/-- A reliable one-shot code for the block channel `N^{⊗n}` gives the
corresponding `n`-use lower-bound witness for `N`, with rate divided by `n`. -/
theorem nUseLowerBoundWitness_of_blockOneShotCode
    {n : ℕ} {ε lowerBound : ℝ}
    {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
    {EA : Type u} [Fintype EA] [DecidableEq EA]
    {EB : Type u} [Fintype EB] [DecidableEq EB]
    (hn_pos : 0 < n)
    (C : EntanglementAssistedClassicalCode (N.tensorPower n) 1 M EA EB)
    (hCerr : C.maxErrorAtMost ε)
    (hCrate : (n : ℝ) * lowerBound ≤ C.rate) :
    Nonempty (N.EntanglementAssistedNUseLowerBoundWitness n ε lowerBound M EA EB) := by
  refine ⟨EntanglementAssistedNUseLowerBoundWitness.mk
    C.liftBlockOneShot
    (C.liftBlockOneShot_maxErrorAtMost hCerr)
    ?_⟩
  exact C.liftBlockOneShot_rate_ge_of_mul_le_rate hn_pos hCrate

/-- A lower-bound witness at blocklength `n` contributes an explicit reliable
`n`-use code to the operational achievability definition. -/
theorem exists_code_of_nUseLowerBoundWitness
    {n : ℕ} {ε lowerBound : ℝ}
    {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
    {EA : Type u} [Fintype EA] [DecidableEq EA]
    {EB : Type u} [Fintype EB] [DecidableEq EB]
    (W : N.EntanglementAssistedNUseLowerBoundWitness n ε lowerBound M EA EB) :
    ∃ (M' : Type u), ∃ (_ : Fintype M'), ∃ (_ : DecidableEq M'), ∃ (_ : Nonempty M'),
      ∃ (EA' : Type u), ∃ (_ : Fintype EA'), ∃ (_ : DecidableEq EA'),
        ∃ (EB' : Type u), ∃ (_ : Fintype EB'), ∃ (_ : DecidableEq EB'),
          ∃ C : EntanglementAssistedClassicalCode N n M' EA' EB',
            C.rate ≥ lowerBound ∧ C.maxErrorAtMost ε := by
  exact ⟨M, inferInstance, inferInstance, inferInstance,
    EA, inferInstance, inferInstance, EB, inferInstance, inferInstance,
    W.code, W.lowerBound_le_rate, W.maxError_le⟩

/-- Asymptotic achievability from a family of `n`-use lower-bound witnesses.

This is the rate-normalization layer for the Khatri--Wilde asymptotic lower
bound: if, after any slack `δ`, sufficiently large blocklengths have reliable
codes with rate at least `R - δ`, then `R` is an operationally achievable
entanglement-assisted classical communication rate. -/
theorem entanglementAssisted_achievable_of_nUseLowerBoundWitness
    (R : ℝ)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          ∃ (M : Type u), ∃ (_ : Fintype M), ∃ (_ : DecidableEq M),
            ∃ (_ : Nonempty M),
              ∃ (EA : Type u), ∃ (_ : Fintype EA), ∃ (_ : DecidableEq EA),
                ∃ (EB : Type u), ∃ (_ : Fintype EB), ∃ (_ : DecidableEq EB),
                  Nonempty (N.EntanglementAssistedNUseLowerBoundWitness
                    n ε (R - δ) M EA EB)) :
    N.IsAchievableEntanglementAssistedClassicalRate R := by
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty,
    EA, hEAfin, hEAdec, EB, hEBfin, hEBdec, ⟨W⟩⟩ := hN0 n hn
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  letI : Fintype EA := hEAfin
  letI : DecidableEq EA := hEAdec
  letI : Fintype EB := hEBfin
  letI : DecidableEq EB := hEBdec
  exact N.exists_code_of_nUseLowerBoundWitness W

set_option maxHeartbeats 2000000

end Channel

end

end QIT
