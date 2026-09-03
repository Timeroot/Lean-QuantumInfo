/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.HypothesisTesting.Basic
public import QIT.Information.Entropy.Entropy
public import QIT.Core.Channel
public import QIT.Core.Pure
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import Mathlib.Data.EReal.Basic

/-!
# Hypothesis-testing mutual information

This module records the one-shot hypothesis-testing information API used by
the entanglement-assisted classical communication lower- and upper-bound
queues.  The definitions use the beta-first convention
`D_H^epsilon(rho || sigma) = -log_2 beta_epsilon(rho || sigma)`, where
`beta_epsilon` is the infimum of the type-II error over effects
`0 <= Lambda <= 1` with `Tr[Lambda rho] >= 1 - epsilon`.

The channel-level optimized quantity `I_H^epsilon(N)` follows
[KhatriWilde2024Principles, Chapters/entropies.tex:8042-8052].  The barred
non-optimized quantity `bar I_H^epsilon(N)` follows the one-shot
entanglement-assisted lower-bound statement
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:530-665].

This is a definition-level API: SDP duality, optimizer existence,
position-based coding, sequential decoding, and the one-shot lower-bound
theorem are downstream proof obligations.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private theorem state_matrix_le_one_for_htmi (rho : State a) :
    rho.matrix ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := rho.pos.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((rho.pos.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : rho.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using rho.pos.1.spectral_theorem
  have heig_sum : ∑ i, rho.pos.1.eigenvalues i = 1 := by
    have hc : (∑ i, ((rho.pos.1.eigenvalues i : ℝ) : ℂ)) = 1 := by
      exact rho.pos.1.trace_eq_sum_eigenvalues.symm.trans rho.trace_eq_one
    exact Complex.ofReal_injective (by simpa using hc)
  have heig_le_one : ∀ i, rho.pos.1.eigenvalues i ≤ 1 := by
    intro i
    have hnonneg (j : a) : 0 ≤ rho.pos.1.eigenvalues j :=
      rho.pos.eigenvalues_nonneg j
    calc rho.pos.1.eigenvalues i
        ≤ rho.pos.1.eigenvalues i +
            ∑ j ∈ Finset.univ.erase i, rho.pos.1.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
      _ = ∑ j, rho.pos.1.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => rho.pos.1.eigenvalues j) (Finset.mem_univ i)
      _ = 1 := heig_sum
  have hsub :
      1 - rho.matrix = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
    rw [hdiag]
    have hUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
      simp
    calc
      1 - (U : CMatrix a) * D * star (U : CMatrix a) =
          (U : CMatrix a) * 1 * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
            rw [Matrix.mul_one, hUstar]
      _ = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
            noncomm_ring
  have hdiag_sub :
      (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((1 : ℝ) - rho.pos.1.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (1 : ℝ) - rho.pos.1.eigenvalues i := by
    exact sub_nonneg.mpr (heig_le_one i)
  exact_mod_cast hnonneg

/-- Accept probability of an effect against a state, written as a real trace. -/
def effectAcceptProbability (rho : State a) (Lambda : CMatrix a) : ℝ :=
  ((rho.matrix * Lambda).trace).re

/-- Type-II error of an effect against the second hypothesis. -/
def effectTypeIIError (sigma : State a) (Lambda : CMatrix a) : ℝ :=
  effectAcceptProbability sigma Lambda

/-- A feasible hypothesis-testing effect for the type-I constraint
`Tr[Lambda rho] >= 1 - epsilon`. -/
structure HypothesisTestingEffect (rho : State a) (epsilon : ℝ) where
  effect : CMatrix a
  pos : effect.PosSemidef
  le_one : effect ≤ 1
  accept_ge : 1 - epsilon ≤ effectAcceptProbability rho effect

namespace HypothesisTestingEffect

variable {rho sigma : State a} {epsilon : ℝ}

/-- The type-II error induced by a feasible effect. -/
def typeIIError (Lambda : HypothesisTestingEffect rho epsilon) (sigma : State a) : ℝ :=
  effectTypeIIError sigma Lambda.effect

@[simp]
theorem typeIIError_eq (Lambda : HypothesisTestingEffect rho epsilon) (sigma : State a) :
    Lambda.typeIIError sigma = effectTypeIIError sigma Lambda.effect :=
  rfl

theorem typeIIError_nonneg_htmi (Lambda : HypothesisTestingEffect rho epsilon)
    (sigma : State a) :
    0 ≤ Lambda.typeIIError sigma := by
  unfold typeIIError effectTypeIIError effectAcceptProbability
  exact cMatrix_trace_mul_posSemidef_re_nonneg sigma.pos Lambda.pos

theorem effectAcceptProbability_real_smul (rho : State a)
    (c : ℝ) (E : CMatrix a) :
    effectAcceptProbability rho (c • E) = c * effectAcceptProbability rho E := by
  unfold effectAcceptProbability
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp

theorem effectTypeIIError_real_smul (sigma : State a)
    (c : ℝ) (E : CMatrix a) :
    effectTypeIIError sigma (c • E) = c * effectTypeIIError sigma E := by
  exact effectAcceptProbability_real_smul sigma c E

omit [Fintype a] in
theorem real_smul_le_one_of_le_one {E : CMatrix a} {c : ℝ}
    (hEle : E ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c • E ≤ (1 : CMatrix a) := by
  rw [Matrix.le_iff]
  have hcomp : ((1 : CMatrix a) - E).PosSemidef := by
    simpa [Matrix.le_iff] using hEle
  have hdecomp :
      (1 : CMatrix a) - c • E =
        (1 - c) • (1 : CMatrix a) + c • (1 - E) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    · simp [h]
  rw [hdecomp]
  exact (Matrix.PosSemidef.smul Matrix.PosSemidef.one (sub_nonneg.mpr hc1)).add
    (Matrix.PosSemidef.smul hcomp hc0)

theorem one_minus_epsilon_div_accept_nonneg
    (Lambda : HypothesisTestingEffect rho epsilon) (hε_lt_one : epsilon < 1) :
    0 ≤ (1 - epsilon) / effectAcceptProbability rho Lambda.effect := by
  have hnum : 0 ≤ 1 - epsilon := le_of_lt (sub_pos.mpr hε_lt_one)
  have hden : 0 < effectAcceptProbability rho Lambda.effect :=
    (sub_pos.mpr hε_lt_one).trans_le Lambda.accept_ge
  exact div_nonneg hnum hden.le

theorem one_minus_epsilon_div_accept_le_one
    (Lambda : HypothesisTestingEffect rho epsilon) (hε_lt_one : epsilon < 1) :
    (1 - epsilon) / effectAcceptProbability rho Lambda.effect ≤ 1 := by
  have hden : 0 < effectAcceptProbability rho Lambda.effect :=
    (sub_pos.mpr hε_lt_one).trans_le Lambda.accept_ge
  exact (div_le_one hden).mpr Lambda.accept_ge

/-- Rescale a feasible test so that the type-I constraint is saturated.

The source proof of the weak-converse comparison restricts the optimizer to
tests with `Tr[Lambda rho] = 1 - epsilon`.  The repository's beta-first API
uses the equivalent `>=` feasibility convention; this construction is the
bridge from the repository convention to the source equality convention. -/
def scaleToAcceptEquality (Lambda : HypothesisTestingEffect rho epsilon)
    (hε_lt_one : epsilon < 1) : HypothesisTestingEffect rho epsilon where
  effect :=
    ((1 - epsilon) / effectAcceptProbability rho Lambda.effect) • Lambda.effect
  pos :=
    Matrix.PosSemidef.smul Lambda.pos
      (one_minus_epsilon_div_accept_nonneg Lambda hε_lt_one)
  le_one :=
    real_smul_le_one_of_le_one Lambda.le_one
      (one_minus_epsilon_div_accept_nonneg Lambda hε_lt_one)
      (one_minus_epsilon_div_accept_le_one Lambda hε_lt_one)
  accept_ge := by
    have hden : effectAcceptProbability rho Lambda.effect ≠ 0 := by
      exact ne_of_gt ((sub_pos.mpr hε_lt_one).trans_le Lambda.accept_ge)
    rw [effectAcceptProbability_real_smul]
    field_simp [hden]
    exact le_rfl

theorem scaleToAcceptEquality_accept_eq
    (Lambda : HypothesisTestingEffect rho epsilon) (hε_lt_one : epsilon < 1) :
    effectAcceptProbability rho (Lambda.scaleToAcceptEquality hε_lt_one).effect =
      1 - epsilon := by
  have hden : effectAcceptProbability rho Lambda.effect ≠ 0 := by
    exact ne_of_gt ((sub_pos.mpr hε_lt_one).trans_le Lambda.accept_ge)
  simp [scaleToAcceptEquality, effectAcceptProbability_real_smul]
  field_simp [hden]

theorem scaleToAcceptEquality_typeIIError_le
    (Lambda : HypothesisTestingEffect rho epsilon) (hε_lt_one : epsilon < 1)
    (sigma : State a) :
    (Lambda.scaleToAcceptEquality hε_lt_one).typeIIError sigma ≤
      Lambda.typeIIError sigma := by
  have hcoef0 :=
    one_minus_epsilon_div_accept_nonneg Lambda hε_lt_one
  have hcoef1 :=
    one_minus_epsilon_div_accept_le_one Lambda hε_lt_one
  have htype_nonneg : 0 ≤ Lambda.typeIIError sigma :=
    Lambda.typeIIError_nonneg_htmi sigma
  unfold typeIIError
  simp [scaleToAcceptEquality, effectTypeIIError_real_smul]
  exact mul_le_of_le_one_left htype_nonneg hcoef1

@[simp]
theorem effectAcceptProbability_effect (Lambda : HypothesisTestingEffect rho epsilon) :
    effectAcceptProbability rho Lambda.effect = ((rho.matrix * Lambda.effect).trace).re :=
  rfl

/-- The identity effect is feasible whenever `epsilon >= 0`. -/
def identity (rho : State a) (epsilon : ℝ) (hε : 0 ≤ epsilon) :
    HypothesisTestingEffect rho epsilon where
  effect := 1
  pos := Matrix.PosSemidef.one
  le_one := le_rfl
  accept_ge := by
    unfold effectAcceptProbability
    rw [Matrix.mul_one, rho.trace_eq_one]
    simp
    linarith

@[simp]
theorem identity_effect (rho : State a) (epsilon : ℝ) (hε : 0 ≤ epsilon) :
    (identity rho epsilon hε).effect = 1 :=
  rfl

@[simp]
theorem identity_typeIIError (rho sigma : State a) (epsilon : ℝ) (hε : 0 ≤ epsilon) :
    (identity rho epsilon hε).typeIIError sigma = 1 := by
  unfold typeIIError effectTypeIIError effectAcceptProbability identity
  rw [Matrix.mul_one, sigma.trace_eq_one]
  simp

/-- A feasible hypothesis-testing effect determines a binary POVM whose `true`
outcome accepts the first hypothesis. -/
def toBinaryHypothesisTest (Lambda : HypothesisTestingEffect rho epsilon) :
    BinaryHypothesisTest a where
  effects := fun accept => if accept then Lambda.effect else 1 - Lambda.effect
  pos := by
    intro accept
    by_cases haccept : accept
    · simp [haccept, Lambda.pos]
    · have hcomp : (1 - Lambda.effect).PosSemidef := by
        simpa [Matrix.le_iff] using Lambda.le_one
      simp [haccept, hcomp]
  sum_eq_one := by
    rw [Fintype.sum_bool]
    simp

@[simp]
theorem toBinaryHypothesisTest_acceptRhoEffect
    (Lambda : HypothesisTestingEffect rho epsilon) :
    Lambda.toBinaryHypothesisTest.acceptRhoEffect = Lambda.effect :=
  rfl

@[simp]
theorem toBinaryHypothesisTest_rejectRhoEffect
    (Lambda : HypothesisTestingEffect rho epsilon) :
    Lambda.toBinaryHypothesisTest.rejectRhoEffect = 1 - Lambda.effect :=
  rfl

theorem toBinaryHypothesisTest_acceptProb_ge
    (Lambda : HypothesisTestingEffect rho epsilon) :
    1 - epsilon ≤ (Lambda.toBinaryHypothesisTest.acceptProb rho : ℝ) := by
  rw [BinaryHypothesisTest.acceptProb_eq_trace_re]
  exact Lambda.accept_ge

theorem toBinaryHypothesisTest_typeIIError
    (Lambda : HypothesisTestingEffect rho epsilon) (sigma : State a) :
    (Lambda.toBinaryHypothesisTest.typeIIError sigma : ℝ) =
      Lambda.typeIIError sigma := by
  change (Lambda.toBinaryHypothesisTest.prob sigma true : ℝ) =
    ((sigma.matrix * Lambda.effect).trace).re
  rw [POVM.prob_eq_trace_re]
  rfl

end HypothesisTestingEffect

namespace BinaryHypothesisTest

variable {rho : State a} {epsilon : ℝ}

/-- A two-outcome POVM whose accept probability meets the type-I constraint
gives a feasible hypothesis-testing effect. -/
def toHypothesisTestingEffect (T : BinaryHypothesisTest a)
    (haccept : 1 - epsilon ≤ (T.acceptProb rho : ℝ)) :
    HypothesisTestingEffect rho epsilon where
  effect := T.acceptRhoEffect
  pos := T.acceptRhoEffect_pos
  le_one := T.acceptRhoEffect_le_one
  accept_ge := by
    unfold effectAcceptProbability
    rw [← T.acceptProb_eq_trace_re rho]
    exact haccept

@[simp]
theorem toHypothesisTestingEffect_effect (T : BinaryHypothesisTest a)
    (haccept : 1 - epsilon ≤ (T.acceptProb rho : ℝ)) :
    (T.toHypothesisTestingEffect haccept).effect = T.acceptRhoEffect :=
  rfl

@[simp]
theorem toHypothesisTestingEffect_typeIIError (T : BinaryHypothesisTest a)
    (haccept : 1 - epsilon ≤ (T.acceptProb rho : ℝ)) (sigma : State a) :
    (T.toHypothesisTestingEffect haccept).typeIIError sigma = (T.typeIIError sigma : ℝ) := by
  unfold HypothesisTestingEffect.typeIIError effectTypeIIError effectAcceptProbability
    toHypothesisTestingEffect BinaryHypothesisTest.typeIIError
  rw [← T.acceptProb_eq_trace_re sigma]

end BinaryHypothesisTest

namespace State

variable (rho sigma : State a) (epsilon : ℝ)

/-- Candidate set for the beta quantity in hypothesis-testing relative entropy. -/
def hypothesisTestingBetaCandidateSet : Set ℝ :=
  {beta | ∃ Lambda : HypothesisTestingEffect rho epsilon,
    beta = Lambda.typeIIError sigma}

/-- The beta quantity `beta_epsilon(rho || sigma)`, as an infimum of type-II errors. -/
def hypothesisTestingBeta : ℝ :=
  sInf (rho.hypothesisTestingBetaCandidateSet sigma epsilon)

/-- Finite real helper `-log₂ β_ε`.  At `β_ε = 0` this uses Lean's totalized
real logarithm; source-facing statements should use
`hypothesisTestingRelativeEntropy` instead. -/
def hypothesisTestingRelativeEntropyFinite : ℝ :=
  -log2 (rho.hypothesisTestingBeta sigma epsilon)

/-- Canonical extended-real hypothesis-testing relative entropy.  This is the
source-faithful convention: `β_ε = 0` gives `⊤`. -/
def hypothesisTestingRelativeEntropy : EReal :=
  if rho.hypothesisTestingBeta sigma epsilon = 0 then ⊤
  else (rho.hypothesisTestingRelativeEntropyFinite sigma epsilon : EReal)

theorem hypothesisTestingBeta_eq_sInf :
    rho.hypothesisTestingBeta sigma epsilon =
      sInf (rho.hypothesisTestingBetaCandidateSet sigma epsilon) :=
  rfl

theorem hypothesisTestingRelativeEntropyFinite_eq :
    rho.hypothesisTestingRelativeEntropyFinite sigma epsilon =
      -log2 (rho.hypothesisTestingBeta sigma epsilon) :=
  rfl

theorem hypothesisTestingRelativeEntropy_eq :
    rho.hypothesisTestingRelativeEntropy sigma epsilon =
      if rho.hypothesisTestingBeta sigma epsilon = 0 then ⊤
      else (rho.hypothesisTestingRelativeEntropyFinite sigma epsilon : EReal) :=
  rfl

/-- The canonical hypothesis-testing relative entropy is infinite exactly on
the explicit zero-`β` branch. -/
theorem hypothesisTestingRelativeEntropy_eq_top_of_beta_eq_zero
    (hzero : rho.hypothesisTestingBeta sigma epsilon = 0) :
    rho.hypothesisTestingRelativeEntropy sigma epsilon = (⊤ : EReal) := by
  simp [hypothesisTestingRelativeEntropy, hzero]

/-- A positive `β` value selects the finite real branch of the canonical
hypothesis-testing relative entropy. -/
theorem hypothesisTestingRelativeEntropy_eq_coe_finite_of_beta_pos
    (hpos : 0 < rho.hypothesisTestingBeta sigma epsilon) :
    rho.hypothesisTestingRelativeEntropy sigma epsilon =
      (rho.hypothesisTestingRelativeEntropyFinite sigma epsilon : EReal) := by
  simp [hypothesisTestingRelativeEntropy, ne_of_gt hpos]

theorem hypothesisTestingBetaCandidateSet_nonempty_of_nonneg (hε : 0 ≤ epsilon) :
    (rho.hypothesisTestingBetaCandidateSet sigma epsilon).Nonempty := by
  refine ⟨1, ?_⟩
  refine ⟨HypothesisTestingEffect.identity rho epsilon hε, ?_⟩
  rw [HypothesisTestingEffect.identity_typeIIError]

/-- The beta quantity is nonnegative because all feasible type-II errors are
nonnegative. -/
theorem hypothesisTestingBeta_nonneg (hε : 0 ≤ epsilon) :
    0 ≤ rho.hypothesisTestingBeta sigma epsilon := by
  rw [hypothesisTestingBeta_eq_sInf]
  exact le_csInf
    (rho.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg sigma epsilon hε)
    (by
      intro beta hbeta
      rcases hbeta with ⟨Lambda, rfl⟩
      exact Lambda.typeIIError_nonneg_htmi sigma)

private theorem effectAcceptProbability_le_effect_trace_for_htmi
    (Lambda : HypothesisTestingEffect rho epsilon) :
    effectAcceptProbability rho Lambda.effect ≤ Lambda.effect.trace.re := by
  have hle : rho.matrix ≤ (1 : CMatrix a) := state_matrix_le_one_for_htmi rho
  have htrace := cMatrix_trace_mul_le_of_le_posSemidef_left Lambda.pos hle
  unfold effectAcceptProbability
  calc
    ((rho.matrix * Lambda.effect).trace).re =
        ((Lambda.effect * rho.matrix).trace).re := by
          rw [Matrix.trace_mul_comm]
    _ ≤ ((Lambda.effect * (1 : CMatrix a)).trace).re := htrace
    _ = Lambda.effect.trace.re := by
          rw [Matrix.mul_one]

private theorem real_smul_one_effect_trace_re_for_htmi
    (c : ℝ) (E : CMatrix a) :
    (((E * (c • (1 : CMatrix a))).trace).re : ℝ) = c * E.trace.re := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  simp

private theorem scalar_trace_le_typeIIError_of_matrix_lower_bound_for_htmi
    {c : ℝ} (Lambda : HypothesisTestingEffect rho epsilon)
    (hlower : c • (1 : CMatrix a) ≤ sigma.matrix) :
    c * Lambda.effect.trace.re ≤ Lambda.typeIIError sigma := by
  have htrace := cMatrix_trace_mul_le_of_le_posSemidef_left Lambda.pos hlower
  unfold HypothesisTestingEffect.typeIIError effectTypeIIError effectAcceptProbability
  calc
    c * Lambda.effect.trace.re =
        ((Lambda.effect * (c • (1 : CMatrix a))).trace).re := by
          rw [real_smul_one_effect_trace_re_for_htmi]
    _ ≤ ((Lambda.effect * sigma.matrix).trace).re := htrace
    _ = ((sigma.matrix * Lambda.effect).trace).re := by
          rw [Matrix.trace_mul_comm]

/-- If the second hypothesis dominates a positive scalar multiple of the
identity, then every feasible effect has type-II error bounded below by
`c * (1 - ε)`. -/
theorem hypothesisTestingEffect_typeIIError_ge_scalar_one_minus_epsilon
    {c : ℝ} (Lambda : HypothesisTestingEffect rho epsilon)
    (hc : 0 ≤ c) (hlower : c • (1 : CMatrix a) ≤ sigma.matrix) :
    c * (1 - epsilon) ≤ Lambda.typeIIError sigma := by
  have haccept_trace :
      1 - epsilon ≤ Lambda.effect.trace.re :=
    Lambda.accept_ge.trans
      (effectAcceptProbability_le_effect_trace_for_htmi
        (rho := rho) (epsilon := epsilon) Lambda)
  have hmul :
      c * (1 - epsilon) ≤ c * Lambda.effect.trace.re :=
    mul_le_mul_of_nonneg_left haccept_trace hc
  exact hmul.trans
    (scalar_trace_le_typeIIError_of_matrix_lower_bound_for_htmi
      (rho := rho) (epsilon := epsilon) (sigma := sigma) Lambda hlower)

/-- A positive scalar lower bound on the second hypothesis makes the real-valued
beta branch strictly positive for `ε < 1`. -/
theorem hypothesisTestingBeta_pos_of_matrix_lower_bound
    {c : ℝ} (hε_nonneg : 0 ≤ epsilon) (hε_lt_one : epsilon < 1)
    (hc : 0 < c) (hlower : c • (1 : CMatrix a) ≤ sigma.matrix) :
    0 < rho.hypothesisTestingBeta sigma epsilon := by
  have hcandidate_nonempty :
      (rho.hypothesisTestingBetaCandidateSet sigma epsilon).Nonempty :=
    rho.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg sigma epsilon hε_nonneg
  have hlower_all :
      ∀ beta ∈ rho.hypothesisTestingBetaCandidateSet sigma epsilon,
        c * (1 - epsilon) ≤ beta := by
    intro beta hbeta
    rcases hbeta with ⟨Lambda, rfl⟩
    exact hypothesisTestingEffect_typeIIError_ge_scalar_one_minus_epsilon
      (rho := rho) (epsilon := epsilon)
      (sigma := sigma) (c := c) Lambda (le_of_lt hc) hlower
  have hβ_ge :
      c * (1 - epsilon) ≤ rho.hypothesisTestingBeta sigma epsilon := by
    rw [hypothesisTestingBeta_eq_sInf]
    exact le_csInf hcandidate_nonempty hlower_all
  have hpos : 0 < c * (1 - epsilon) :=
    mul_pos hc (sub_pos.mpr hε_lt_one)
  exact hpos.trans_le hβ_ge

/-- A positive-definite state matrix dominates a positive scalar multiple of
the identity.  The scalar is the finite minimum eigenvalue. -/
theorem exists_pos_scalar_smul_one_le_matrix_of_posDef
    (hσ : sigma.matrix.PosDef) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : CMatrix a) ≤ sigma.matrix := by
  classical
  haveI : Nonempty a := sigma.nonempty
  let c : ℝ := Finset.univ.inf' Finset.univ_nonempty
    (fun i : a => hσ.1.eigenvalues i)
  have hc_pos : 0 < c := by
    dsimp [c]
    rw [Finset.lt_inf'_iff]
    intro i hi
    exact hσ.eigenvalues_pos i
  have hc_le_eig : ∀ i : a, c ≤ hσ.1.eigenvalues i := by
    intro i
    exact Finset.inf'_le (f := fun i : a => hσ.1.eigenvalues i) (Finset.mem_univ i)
  refine ⟨c, hc_pos, ?_⟩
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := hσ.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((hσ.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : sigma.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hσ.1.spectral_theorem
  have hUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
    simp
  have hscalar :
      (U : CMatrix a) * (c • (1 : CMatrix a)) * star (U : CMatrix a) =
        c • (1 : CMatrix a) := by
    calc
      (U : CMatrix a) * (c • (1 : CMatrix a)) * star (U : CMatrix a) =
          c • ((U : CMatrix a) * (1 : CMatrix a) * star (U : CMatrix a)) := by
            simp
      _ = c • (1 : CMatrix a) := by
            rw [Matrix.mul_one, hUstar]
  have hsub :
      sigma.matrix - c • (1 : CMatrix a) =
        (U : CMatrix a) * (D - c • (1 : CMatrix a)) * star (U : CMatrix a) := by
    calc
      sigma.matrix - c • (1 : CMatrix a) =
          (U : CMatrix a) * D * star (U : CMatrix a) -
            (U : CMatrix a) * (c • (1 : CMatrix a)) * star (U : CMatrix a) := by
            rw [hdiag, hscalar]
      _ = (U : CMatrix a) * (D - c • (1 : CMatrix a)) *
            star (U : CMatrix a) := by
            rw [Matrix.mul_sub, Matrix.sub_mul]
  have hdiag_sub :
      D - c • (1 : CMatrix a) =
        Matrix.diagonal fun i => (((hσ.1.eigenvalues i : ℝ) - c : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (hσ.1.eigenvalues i : ℝ) - c :=
    sub_nonneg.mpr (hc_le_eig i)
  exact_mod_cast hnonneg

/-- Approximate the beta infimum by a concrete feasible effect.  This is the
non-optimizer form needed by one-shot coding proofs: whenever a strict upper
budget lies above `β_ε(ρ‖σ)`, some feasible effect attains type-II error below
that budget. -/
theorem exists_hypothesisTestingEffect_typeIIError_lt_of_hypothesisTestingBeta_lt
    (hε : 0 ≤ epsilon) {betaBudget : ℝ}
    (hbeta : rho.hypothesisTestingBeta sigma epsilon < betaBudget) :
    ∃ Lambda : HypothesisTestingEffect rho epsilon,
      Lambda.typeIIError sigma < betaBudget := by
  rw [hypothesisTestingBeta_eq_sInf] at hbeta
  obtain ⟨beta, hbeta_mem, hbeta_lt⟩ :=
    exists_lt_of_csInf_lt
      (rho.hypothesisTestingBetaCandidateSet_nonempty_of_nonneg sigma epsilon hε)
      hbeta
  rcases hbeta_mem with ⟨Lambda, rfl⟩
  exact ⟨Lambda, hbeta_lt⟩

/-- Convert a strict lower bound on `-log₂ β` into the corresponding strict
upper bound `β < 2^{-lower}`.  The positivity assumption is exactly the
real-valued, non-extended branch of hypothesis-testing relative entropy. -/
private theorem hypothesisTestingBeta_lt_rpow_two_neg_of_lt_neg_log2
    {beta lower : ℝ} (hbeta_pos : 0 < beta)
    (hlower : lower < -log2 beta) :
    beta < Real.rpow 2 (-lower) := by
  have hlog : log2 beta < -lower := by
    linarith
  have hlog' : Real.log beta < (-lower) * Real.log 2 := by
    unfold log2 at hlog
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    exact (div_lt_iff₀ hlog2_pos).mp hlog
  have hrpow_pos : 0 < Real.rpow 2 (-lower) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lower)
  have hlog_rpow :
      Real.log (Real.rpow 2 (-lower)) = (-lower) * Real.log 2 := by
    exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-lower)
  rw [← hlog_rpow] at hlog'
  exact (Real.log_lt_log_iff hbeta_pos hrpow_pos).mp hlog'

/-- Approximate a real-valued hypothesis-testing relative entropy lower bound
by a concrete feasible effect.

If `lower < D_H^ε(ρ‖σ)` and the beta value is positive, some feasible
hypothesis-testing effect has type-II error strictly below `2^{-lower}`.  This
is the exact non-optimizer witness form used by one-shot coding proofs. -/
theorem exists_hypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt_relativeEntropyFinite
    (hε : 0 ≤ epsilon)
    (hbeta_pos : 0 < rho.hypothesisTestingBeta sigma epsilon)
    {lower : ℝ}
    (hlower : lower < rho.hypothesisTestingRelativeEntropyFinite sigma epsilon) :
    ∃ Lambda : HypothesisTestingEffect rho epsilon,
      Lambda.typeIIError sigma < Real.rpow 2 (-lower) := by
  rw [hypothesisTestingRelativeEntropyFinite_eq] at hlower
  have hbeta_lt :
      rho.hypothesisTestingBeta sigma epsilon < Real.rpow 2 (-lower) :=
    hypothesisTestingBeta_lt_rpow_two_neg_of_lt_neg_log2 hbeta_pos hlower
  exact rho.exists_hypothesisTestingEffect_typeIIError_lt_of_hypothesisTestingBeta_lt
    sigma epsilon hε hbeta_lt

/-- Extended-real form of the optimizer-free extraction lemma.

For any finite real `lower` strictly below the extended-real
`D_H^ε(ρ‖σ)`, some feasible effect has type-II error below `2^{-lower}`.  This
handles both branches of the source convention: the usual positive-beta branch
and the zero-beta branch, where `D_H = ⊤`. -/
theorem exists_hypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt_relativeEntropy
    (hε : 0 ≤ epsilon)
    {lower : ℝ}
    (hlower : (lower : EReal) < rho.hypothesisTestingRelativeEntropy sigma epsilon) :
    ∃ Lambda : HypothesisTestingEffect rho epsilon,
      Lambda.typeIIError sigma < Real.rpow 2 (-lower) := by
  rw [hypothesisTestingRelativeEntropy_eq] at hlower
  by_cases hzero :
      rho.hypothesisTestingBeta sigma epsilon = 0
  · rw [if_pos hzero] at hlower
    have hbudget_pos : 0 < Real.rpow 2 (-lower) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lower)
    have hbeta_lt :
        rho.hypothesisTestingBeta sigma epsilon < Real.rpow 2 (-lower) := by
      simpa [hzero] using hbudget_pos
    exact rho.exists_hypothesisTestingEffect_typeIIError_lt_of_hypothesisTestingBeta_lt
      sigma epsilon hε hbeta_lt
  · rw [if_neg hzero] at hlower
    have hlower_real :
        lower < rho.hypothesisTestingRelativeEntropyFinite sigma epsilon :=
      EReal.coe_lt_coe_iff.mp hlower
    have hbeta_nonneg :
        0 ≤ rho.hypothesisTestingBeta sigma epsilon :=
      rho.hypothesisTestingBeta_nonneg sigma epsilon hε
    have hbeta_pos :
        0 < rho.hypothesisTestingBeta sigma epsilon :=
      lt_of_le_of_ne hbeta_nonneg (Ne.symm hzero)
    exact
      rho.exists_hypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt_relativeEntropyFinite
        sigma epsilon hε hbeta_pos hlower_real

/-- Finite-real candidate set retained for internal real arithmetic. -/
def hypothesisTestingMutualInformationFiniteCandidateSet
    (rhoAB : State (Prod a b)) (epsilon : ℝ) : Set ℝ :=
  {value | ∃ sigmaB : State b,
    value =
      rhoAB.hypothesisTestingRelativeEntropyFinite (rhoAB.marginalA.prod sigmaB) epsilon}

/-- Candidate set for optimized extended-real state hypothesis-testing mutual
information. -/
def hypothesisTestingMutualInformationCandidateSet
    (rhoAB : State (Prod a b)) (epsilon : ℝ) : Set EReal :=
  {value | ∃ sigmaB : State b,
    value =
      rhoAB.hypothesisTestingRelativeEntropy (rhoAB.marginalA.prod sigmaB) epsilon}

/-- Finite-real helper for optimized hypothesis-testing mutual information. -/
def hypothesisTestingMutualInformationFinite
    (rhoAB : State (Prod a b)) (epsilon : ℝ) : ℝ :=
  sInf (hypothesisTestingMutualInformationFiniteCandidateSet (a := a) (b := b) rhoAB epsilon)

/-- Canonical extended-real optimized hypothesis-testing mutual information. -/
def hypothesisTestingMutualInformation
    (rhoAB : State (Prod a b)) (epsilon : ℝ) : EReal :=
  sInf (hypothesisTestingMutualInformationCandidateSet (a := a) (b := b) rhoAB epsilon)

/-- Finite-real helper for non-optimized barred hypothesis-testing mutual
information. -/
def barHypothesisTestingMutualInformationFinite
    (rhoAB : State (Prod a b)) (epsilon : ℝ) : ℝ :=
  rhoAB.hypothesisTestingRelativeEntropyFinite (rhoAB.marginalA.prod rhoAB.marginalB) epsilon

/-- Non-optimized, barred extended-real hypothesis-testing mutual information
`bar I_H^epsilon(A;B)_rho`, with the source-faithful zero-beta branch. -/
def barHypothesisTestingMutualInformation
    (rhoAB : State (Prod a b)) (epsilon : ℝ) : EReal :=
  rhoAB.hypothesisTestingRelativeEntropy (rhoAB.marginalA.prod rhoAB.marginalB) epsilon

theorem hypothesisTestingMutualInformationFinite_eq_sInf
    (rhoAB : State (Prod a b)) (epsilon : ℝ) :
    rhoAB.hypothesisTestingMutualInformationFinite epsilon =
      sInf (hypothesisTestingMutualInformationFiniteCandidateSet (a := a) (b := b) rhoAB epsilon) :=
  rfl

theorem hypothesisTestingMutualInformation_eq_sInf
    (rhoAB : State (Prod a b)) (epsilon : ℝ) :
    rhoAB.hypothesisTestingMutualInformation epsilon =
      sInf (hypothesisTestingMutualInformationCandidateSet (a := a) (b := b) rhoAB epsilon) :=
  rfl

theorem barHypothesisTestingMutualInformationFinite_eq
    (rhoAB : State (Prod a b)) (epsilon : ℝ) :
    rhoAB.barHypothesisTestingMutualInformationFinite epsilon =
      rhoAB.hypothesisTestingRelativeEntropyFinite (rhoAB.marginalA.prod rhoAB.marginalB) epsilon :=
  rfl

theorem barHypothesisTestingMutualInformation_eq
    (rhoAB : State (Prod a b)) (epsilon : ℝ) :
    rhoAB.barHypothesisTestingMutualInformation epsilon =
      rhoAB.hypothesisTestingRelativeEntropy
        (rhoAB.marginalA.prod rhoAB.marginalB) epsilon :=
  rfl

/-- The real-valued barred hypothesis-testing mutual information embeds below
the extended-real source-faithful version. -/
theorem barHypothesisTestingMutualInformationFinite_le_E
    (rhoAB : State (Prod a b)) (epsilon : ℝ) :
    (rhoAB.barHypothesisTestingMutualInformationFinite epsilon : EReal) ≤
      rhoAB.barHypothesisTestingMutualInformation epsilon := by
  rw [barHypothesisTestingMutualInformationFinite_eq,
    barHypothesisTestingMutualInformation_eq,
    hypothesisTestingRelativeEntropy_eq]
  by_cases hzero :
      rhoAB.hypothesisTestingBeta
        (rhoAB.marginalA.prod rhoAB.marginalB) epsilon = 0
  · simp [hzero]
  · simp [hzero]

end State

namespace Channel

variable (N : Channel a b)

/-- Output state `(id_R tensor N)(|psi><psi|)` for one-shot information quantities. -/
def hypothesisTestingOutputState {r : Type w} [Fintype r] [DecidableEq r]
    (psi : PureVector (Prod r a)) : State (Prod r b) :=
  ((Channel.idChannel r).prod N).applyState psi.state

/-- Finite-real input-state helper for optimized hypothesis-testing mutual information. -/
def inputHypothesisTestingMutualInformationFinite {r : Type w} [Fintype r] [DecidableEq r]
    (psi : PureVector (Prod r a)) (epsilon : ℝ) : ℝ :=
  (N.hypothesisTestingOutputState psi).hypothesisTestingMutualInformationFinite epsilon

/-- Optimized extended-real hypothesis-testing mutual information of an
input-reference pure state. -/
def inputHypothesisTestingMutualInformation {r : Type w} [Fintype r] [DecidableEq r]
    (psi : PureVector (Prod r a)) (epsilon : ℝ) : EReal :=
  (N.hypothesisTestingOutputState psi).hypothesisTestingMutualInformation epsilon

/-- Non-optimized barred hypothesis-testing mutual information of an input-reference pure state. -/
def inputBarHypothesisTestingMutualInformationFinite {r : Type w} [Fintype r] [DecidableEq r]
    (psi : PureVector (Prod r a)) (epsilon : ℝ) : ℝ :=
  (N.hypothesisTestingOutputState psi).barHypothesisTestingMutualInformationFinite epsilon

/-- Non-optimized barred extended-real hypothesis-testing mutual information
of an input-reference pure state. -/
def inputBarHypothesisTestingMutualInformation {r : Type w} [Fintype r] [DecidableEq r]
    (psi : PureVector (Prod r a)) (epsilon : ℝ) : EReal :=
  (N.hypothesisTestingOutputState psi).barHypothesisTestingMutualInformation epsilon

/-- Finite-real value set for channel `I_H^epsilon(N)`. -/
def hypothesisTestingMutualInformationFiniteValueSet (epsilon : ℝ) : Set ℝ :=
  Set.range fun psi : PureVector (Prod a a) =>
    N.inputHypothesisTestingMutualInformationFinite psi epsilon

/-- Finite-real helper for channel hypothesis-testing mutual information. -/
def hypothesisTestingMutualInformationFinite (epsilon : ℝ) : ℝ :=
  sSup (N.hypothesisTestingMutualInformationFiniteValueSet epsilon)

/-- Value set for channel extended-real `I_H^epsilon(N)`, using a reference copy
of the input system. -/
def hypothesisTestingMutualInformationValueSet (epsilon : ℝ) : Set EReal :=
  Set.range fun psi : PureVector (Prod a a) =>
    N.inputHypothesisTestingMutualInformation psi epsilon

/-- Canonical extended-real channel hypothesis-testing mutual information. -/
def hypothesisTestingMutualInformation (epsilon : ℝ) : EReal :=
  sSup (N.hypothesisTestingMutualInformationValueSet epsilon)

/-- Value set for the barred non-optimized channel quantity `bar I_H^epsilon(N)`. -/
def barHypothesisTestingMutualInformationFiniteValueSet (epsilon : ℝ) : Set ℝ :=
  Set.range fun psi : PureVector (Prod a a) =>
    N.inputBarHypothesisTestingMutualInformationFinite psi epsilon

/-- Barred non-optimized channel hypothesis-testing mutual information
`bar I_H^epsilon(N)`. -/
def barHypothesisTestingMutualInformationFinite (epsilon : ℝ) : ℝ :=
  sSup (N.barHypothesisTestingMutualInformationFiniteValueSet epsilon)

/-- Value set for the barred non-optimized extended-real channel quantity
`bar I_H^epsilon(N)`. -/
def barHypothesisTestingMutualInformationValueSet (epsilon : ℝ) : Set EReal :=
  Set.range fun psi : PureVector (Prod a a) =>
    N.inputBarHypothesisTestingMutualInformation psi epsilon

/-- Barred non-optimized extended-real channel hypothesis-testing mutual
information. -/
def barHypothesisTestingMutualInformation (epsilon : ℝ) : EReal :=
  sSup (N.barHypothesisTestingMutualInformationValueSet epsilon)

theorem hypothesisTestingOutputState_eq {r : Type w} [Fintype r] [DecidableEq r]
    (psi : PureVector (Prod r a)) :
    N.hypothesisTestingOutputState psi =
      ((Channel.idChannel r).prod N).applyState psi.state :=
  rfl

theorem hypothesisTestingMutualInformationFinite_eq_sSup (epsilon : ℝ) :
    N.hypothesisTestingMutualInformationFinite epsilon =
      sSup (N.hypothesisTestingMutualInformationFiniteValueSet epsilon) :=
  rfl

theorem hypothesisTestingMutualInformation_eq_sSup (epsilon : ℝ) :
    N.hypothesisTestingMutualInformation epsilon =
      sSup (N.hypothesisTestingMutualInformationValueSet epsilon) :=
  rfl

theorem inputHypothesisTestingMutualInformation_le_channel
    (epsilon : ℝ) (psi : PureVector (Prod a a)) :
    N.inputHypothesisTestingMutualInformation psi epsilon ≤
      N.hypothesisTestingMutualInformation epsilon := by
  rw [hypothesisTestingMutualInformation_eq_sSup]
  exact le_sSup ⟨psi, rfl⟩

theorem inputBarHypothesisTestingMutualInformationFinite_le_E {r : Type w}
    [Fintype r] [DecidableEq r]
    (psi : PureVector (Prod r a)) (epsilon : ℝ) :
    (N.inputBarHypothesisTestingMutualInformationFinite psi epsilon : EReal) ≤
      N.inputBarHypothesisTestingMutualInformation psi epsilon := by
  exact State.barHypothesisTestingMutualInformationFinite_le_E
    (N.hypothesisTestingOutputState psi) epsilon

theorem barHypothesisTestingMutualInformationFinite_eq_sSup (epsilon : ℝ) :
    N.barHypothesisTestingMutualInformationFinite epsilon =
      sSup (N.barHypothesisTestingMutualInformationFiniteValueSet epsilon) :=
  rfl

theorem barHypothesisTestingMutualInformation_eq_sSup (epsilon : ℝ) :
    N.barHypothesisTestingMutualInformation epsilon =
      sSup (N.barHypothesisTestingMutualInformationValueSet epsilon) :=
  rfl

theorem inputBarHypothesisTestingMutualInformation_le_channel
    (epsilon : ℝ) (psi : PureVector (Prod a a)) :
    N.inputBarHypothesisTestingMutualInformation psi epsilon ≤
      N.barHypothesisTestingMutualInformation epsilon := by
  rw [barHypothesisTestingMutualInformation_eq_sSup]
  exact le_sSup ⟨psi, rfl⟩

/-- Approximate the barred extended-real channel hypothesis-testing mutual
information supremum by a concrete pure input-reference state. -/
theorem exists_inputBarHypothesisTestingMutualInformation_gt_of_lt
    [Nonempty (PureVector (Prod a a))]
    {epsilon lower : ℝ}
    (hlower : (lower : EReal) < N.barHypothesisTestingMutualInformation epsilon) :
    ∃ psi : PureVector (Prod a a),
      (lower : EReal) < N.inputBarHypothesisTestingMutualInformation psi epsilon := by
  rw [barHypothesisTestingMutualInformation_eq_sSup] at hlower
  obtain ⟨value, hvalue_mem, hlt⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty
      (fun psi : PureVector (Prod a a) =>
        N.inputBarHypothesisTestingMutualInformation psi epsilon)) hlower
  rcases hvalue_mem with ⟨psi, rfl⟩
  exact ⟨psi, hlt⟩

/-- Approximate the barred channel hypothesis-testing mutual information
supremum by a concrete pure input-reference state.  This avoids assuming a
maximizer while giving downstream coding proofs the concrete state they need. -/
theorem exists_inputBarHypothesisTestingMutualInformationFinite_gt_of_lt
    [Nonempty (PureVector (Prod a a))]
    {epsilon lower : ℝ}
    (hlower : lower < N.barHypothesisTestingMutualInformationFinite epsilon) :
    ∃ psi : PureVector (Prod a a),
      lower < N.inputBarHypothesisTestingMutualInformationFinite psi epsilon := by
  rw [barHypothesisTestingMutualInformationFinite_eq_sSup] at hlower
  obtain ⟨value, hvalue_mem, hlt⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty
      (fun psi : PureVector (Prod a a) =>
        N.inputBarHypothesisTestingMutualInformationFinite psi epsilon)) hlower
  rcases hvalue_mem with ⟨psi, rfl⟩
  exact ⟨psi, hlt⟩

/-- The real barred channel hypothesis-testing information embeds below the
extended-real barred channel information. -/
theorem barHypothesisTestingMutualInformationFinite_le_E
    [Nonempty (PureVector (Prod a a))] (epsilon : ℝ) :
    (N.barHypothesisTestingMutualInformationFinite epsilon : EReal) ≤
      N.barHypothesisTestingMutualInformation epsilon := by
  rw [barHypothesisTestingMutualInformationFinite_eq_sSup]
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have hz_real :
      z < N.barHypothesisTestingMutualInformationFinite epsilon :=
    EReal.coe_lt_coe_iff.mp hz
  obtain ⟨psi, hpsi⟩ :=
    N.exists_inputBarHypothesisTestingMutualInformationFinite_gt_of_lt hz_real
  exact (EReal.coe_le_coe_iff.mpr hpsi.le).trans
    ((N.inputBarHypothesisTestingMutualInformationFinite_le_E psi epsilon).trans
      (N.inputBarHypothesisTestingMutualInformation_le_channel epsilon psi))

/-- Concrete input state and feasible effect witnessing any strict lower bound
on the barred channel hypothesis-testing mutual information.

This is the optimizer-free channel-level extraction used by the one-shot
entanglement-assisted lower-bound proof: strict inequality below the channel
`sSup` gives a pure input-reference state, and strict inequality below the
state `D_H` gives a feasible test whose type-II error is below the corresponding
power-of-two threshold.  The beta positivity hypothesis marks the real-valued
branch; the extended-real zero-beta branch is handled separately downstream. -/
theorem exists_inputBarHypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt_Finite
    [Nonempty (PureVector (Prod a a))]
    {epsilon lower : ℝ}
    (hε : 0 ≤ epsilon)
    (hlower : lower < N.barHypothesisTestingMutualInformationFinite epsilon)
    (hbeta_pos :
      ∀ psi : PureVector (Prod a a),
        lower < N.inputBarHypothesisTestingMutualInformationFinite psi epsilon →
          0 <
            (N.hypothesisTestingOutputState psi).hypothesisTestingBeta
              ((N.hypothesisTestingOutputState psi).marginalA.prod
                (N.hypothesisTestingOutputState psi).marginalB)
              epsilon) :
    ∃ psi : PureVector (Prod a a),
      ∃ Lambda : HypothesisTestingEffect (N.hypothesisTestingOutputState psi) epsilon,
        Lambda.typeIIError
            ((N.hypothesisTestingOutputState psi).marginalA.prod
              (N.hypothesisTestingOutputState psi).marginalB)
          < Real.rpow 2 (-lower) := by
  obtain ⟨psi, hpsi⟩ :=
    N.exists_inputBarHypothesisTestingMutualInformationFinite_gt_of_lt hlower
  unfold inputBarHypothesisTestingMutualInformationFinite State.barHypothesisTestingMutualInformationFinite
    at hpsi
  obtain ⟨Lambda, hLambda⟩ :=
    (N.hypothesisTestingOutputState psi)
      |>.exists_hypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt_relativeEntropyFinite
        ((N.hypothesisTestingOutputState psi).marginalA.prod
          (N.hypothesisTestingOutputState psi).marginalB)
        epsilon hε (hbeta_pos psi (by
          simpa [inputBarHypothesisTestingMutualInformationFinite,
            State.barHypothesisTestingMutualInformationFinite] using hpsi))
        hpsi
  exact ⟨psi, Lambda, hLambda⟩

/-- Extended-real concrete input-state and feasible-effect extraction for the
barred channel hypothesis-testing information. -/
theorem exists_inputBarHypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt
    [Nonempty (PureVector (Prod a a))]
    {epsilon lower : ℝ}
    (hε : 0 ≤ epsilon)
    (hlower : (lower : EReal) < N.barHypothesisTestingMutualInformation epsilon) :
    ∃ psi : PureVector (Prod a a),
      ∃ Lambda : HypothesisTestingEffect (N.hypothesisTestingOutputState psi) epsilon,
        Lambda.typeIIError
            ((N.hypothesisTestingOutputState psi).marginalA.prod
              (N.hypothesisTestingOutputState psi).marginalB)
          < Real.rpow 2 (-lower) := by
  obtain ⟨psi, hpsi⟩ :=
    N.exists_inputBarHypothesisTestingMutualInformation_gt_of_lt hlower
  unfold inputBarHypothesisTestingMutualInformation State.barHypothesisTestingMutualInformation
    at hpsi
  obtain ⟨Lambda, hLambda⟩ :=
    (N.hypothesisTestingOutputState psi)
      |>.exists_hypothesisTestingEffect_typeIIError_lt_rpow_two_neg_of_lt_relativeEntropy
        ((N.hypothesisTestingOutputState psi).marginalA.prod
          (N.hypothesisTestingOutputState psi).marginalB)
        epsilon hε hpsi
  exact ⟨psi, Lambda, hLambda⟩

end Channel

end

end QIT
