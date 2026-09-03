/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

import QIT.Channels.Diamond

public import QIT.Information.Renyi.RenyiDPI.ReferenceOrder
public import QIT.Information.Renyi.ConditionalSandwichedRenyiClassicalConditioning
public import QIT.Information.Renyi.AlphaEntropyContinuity
public import QIT.Information.Renyi.RenyiOrderParameter

/-!
# Source proof of conditional sandwiched Renyi monotonicity under measurement

This module formalizes Tomamichel's proof route in `cond.tex:268-291`. For the channel
`Phi = measure M x id`, sub-unitality gives

`Phi (I_A x sigma_B) <= I_X x sigma_B`.

Sandwiched Renyi data processing and antitonicity in the reference then
compare every input conditional-entropy candidate with the corresponding
output candidate. Taking the supremum over `sigma_B` proves the finite-order
conditional-entropy inequality. The endpoint orders are discharged by the
same source route: Umegaki relative-entropy DPI at `alpha = 1`, and direct
transport of the min-entropy order constraint at `alpha = infinity`. No
conditional duality or reverse channel enters the pointwise measurement
comparison.

Source: [Tomamichel2015FiniteResources, cond.tex:268-291].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal
open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

/-- A sub-unital measurement channel sends `I_A x sigma_B` below
`I_X x sigma_B`.

This is the reference-dominance step in Tomamichel's conditional Renyi DPI
proof (`cond.tex:286-289`). -/
theorem measurementMap_identityTensorStateMatrix_le
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M)
    (sigma : State b) :
    (Channel.prod (Channel.measure M) (Channel.idChannel b)).map
        (identityTensorStateMatrix (a := a) sigma) <=
      identityTensorStateMatrix (a := c) sigma := by
  change (Channel.prod (Channel.measure M) (Channel.idChannel b)).map
      (Matrix.kronecker (1 : CMatrix a) sigma.matrix) <=
    Matrix.kronecker (1 : CMatrix c) sigma.matrix
  rw [Channel.prod_map_kronecker]
  have hid : (Channel.idChannel b).map sigma.matrix = sigma.matrix := by
    simp [Channel.idChannel, MatrixMap.ofKraus]
  rw [hid]
  have hkron := (Matrix.le_iff.mp hMUnit).kronecker sigma.pos
  apply Matrix.le_iff.mpr
  have heq :
      Matrix.kronecker (1 : CMatrix c) sigma.matrix -
          Matrix.kronecker ((Channel.measure M).map (1 : CMatrix a)) sigma.matrix =
        Matrix.kronecker
          ((1 : CMatrix c) - (Channel.measure M).map (1 : CMatrix a)) sigma.matrix := by
    ext i j
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, sub_mul]
  rw [heq]
  exact hkron

/-- Full-rank sandwiched Renyi divergence is nonnegative throughout the
source DPI range `alpha >= 1/2`, `alpha != 1`.

The proof applies the established channel DPI to the terminal one-outcome
measurement channel.  This supplies the finite upper bound needed by the
real-valued conditional-entropy supremum. -/
theorem sandwichedRenyi_nonneg_of_half_le_ne_one
    (rho sigma : State a) (hrho : rho.matrix.PosDef) (hsigma : sigma.matrix.PosDef)
    (alpha : Real) (halpha : 1 / 2 <= alpha) (halpha1 : alpha ≠ 1) :
    0 <= sandwichedRenyi rho sigma hrho hsigma alpha
      (lt_of_lt_of_le (by norm_num) halpha) halpha1 := by
  let Phi : Channel a PUnit.{1} := terminalMeasureChannel a
  have hrhoPhi_eq : Phi.applyState rho = State.unit := by
    simpa [Phi] using terminalMeasureChannel_applyState rho
  have hsigmaPhi_eq : Phi.applyState sigma = State.unit := by
    simpa [Phi] using terminalMeasureChannel_applyState sigma
  have hunit_pos : (State.unit.matrix : CMatrix PUnit.{1}).PosDef := by
    change (1 : CMatrix PUnit.{1}).PosDef
    exact Matrix.PosDef.one
  have hrhoPhi : (Phi.applyState rho).matrix.PosDef := by
    rw [hrhoPhi_eq]
    exact hunit_pos
  have hsigmaPhi : (Phi.applyState sigma).matrix.PosDef := by
    rw [hsigmaPhi_eq]
    exact hunit_pos
  have hrange : (1 / 2 <= alpha ∧ alpha < 1) ∨ 1 < alpha := by
    rcases lt_or_gt_of_ne halpha1 with hlt | hgt
    · exact Or.inl ⟨halpha, hlt⟩
    · exact Or.inr hgt
  have hDPI :=
    sandwichedRenyi_dataProcessing_channel_statement_of_half_le_lt_one_or_one_lt_channel
      rho sigma Phi hrho hsigma hrhoPhi hsigmaPhi alpha hrange
  unfold RenyiDPI.Statement.sandwichedRenyi_dataProcessing_channel_statement at hDPI
  have hleft :
      sandwichedRenyi (Phi.applyState rho) (Phi.applyState sigma)
          hrhoPhi hsigmaPhi alpha (lt_of_lt_of_le (by norm_num) halpha) halpha1 = 0 := by
    simpa [hrhoPhi_eq, hsigmaPhi_eq] using
      sandwichedRenyi_self_eq_zero State.unit hunit_pos alpha
        (lt_of_lt_of_le (by norm_num) halpha) halpha1
  rw [hleft] at hDPI
  exact hDPI

/-- Pointwise source comparison for upward conditional sandwiched Renyi
candidates under a sub-unital measurement map.

The proof is exactly the source chain: PSD-reference channel DPI, reference
dominance, and negation to pass from divergence to conditional entropy. -/
theorem conditionalSandwichedRenyiUpSourceCandidate_le_measureSubsystemState
    (rho : State (Prod a b))
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M)
    (alpha : Real) (halpha : 1 / 2 <= alpha) (halpha1 : alpha ≠ 1)
    (sigma : State b) (hsigma : sigma.matrix.PosDef) :
    rho.conditionalSandwichedRenyiUpSourceCandidate
        sigma hsigma alpha (by linarith) halpha1 <=
      (measureSubsystemState M rho).conditionalSandwichedRenyiUpSourceCandidate
        sigma hsigma alpha (by linarith) halpha1 := by
  let Phi : Channel (Prod a b) (Prod c b) :=
    Channel.prod (Channel.measure M) (Channel.idChannel b)
  let rin : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) sigma
  let rout : CMatrix (Prod c b) := identityTensorStateMatrix (a := c) sigma
  have halpha_pos : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha
  have hrange : (1 / 2 <= alpha ∧ alpha < 1) ∨ 1 < alpha := by
    rcases lt_or_gt_of_ne halpha1 with hlt | hgt
    · exact Or.inl ⟨halpha, hlt⟩
    · exact Or.inr hgt
  have hrin : rin.PosSemidef := by
    exact (identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma).posSemidef
  have hrout : rout.PosSemidef := by
    exact (identityTensorStateMatrix_posDef_of_posDef (a := c) sigma hsigma).posSemidef
  have hmap : Phi.map rin <= rout := by
    simpa [Phi, rin, rout] using measurementMap_identityTensorStateMatrix_le M hMUnit sigma
  have hDPI :=
    sandwichedRenyiPSDReferenceE_dataProcessing_channel_of_half_le_lt_one_or_one_lt
      rho hrin Phi alpha hrange
  have hreference :=
    sandwichedRenyiPSDReferenceE_antitone_reference (Phi.applyState rho)
      (Phi.mapsPositive rin hrin) hrout hmap halpha
  have hdiv :
      (Phi.applyState rho).sandwichedRenyiPSDReferenceE rout hrout alpha <=
        rho.sandwichedRenyiPSDReferenceE rin hrin alpha :=
    le_trans hreference hDPI
  have hdiv' :
      (measureSubsystemState M rho).sandwichedRenyiPSDReferenceE
          (identityTensorStateMatrix (a := c) sigma)
          (identityTensorStateMatrix_posSemidef_of_state (a := c) sigma) alpha <=
        rho.sandwichedRenyiPSDReferenceE
          (identityTensorStateMatrix (a := a) sigma)
          (identityTensorStateMatrix_posSemidef_of_state (a := a) sigma) alpha := by
    simpa [Phi, rin, rout, measureSubsystemState] using hdiv
  have hinBridge := sandwichedUpSourceCandidate_eq_neg_referenceE
    rho sigma hsigma alpha halpha_pos halpha1
  have houtBridge := sandwichedUpSourceCandidate_eq_neg_referenceE
    (measureSubsystemState M rho) sigma hsigma alpha halpha_pos halpha1
  have hsource :
      (rho.conditionalSandwichedRenyiUpSourceCandidate
          sigma hsigma alpha halpha_pos halpha1 : EReal) <=
        ((measureSubsystemState M rho).conditionalSandwichedRenyiUpSourceCandidate
          sigma hsigma alpha halpha_pos halpha1 : EReal) := by
    rw [hinBridge, houtBridge]
    exact EReal.neg_le_neg_iff.mpr hdiv'
  exact EReal.coe_le_coe_iff.mp hsource

/-! ## Source-shaped arbitrary-state finite orders -/

/-- The source-shaped upward candidate set is bounded above throughout the
closed finite DPI range `alpha >= 1/2`, `alpha != 1`.

At the half-order endpoint every candidate is bounded by conditional
max-entropy. On the strict interior this reuses the established source
boundedness theorem. -/
theorem conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_half_le_ne_one
    (rho : State (Prod a b)) (alpha : Real)
    (halpha : 1 / 2 <= alpha) (halpha1 : alpha ≠ 1) :
    BddAbove (rho.conditionalSandwichedRenyiUpSourceValueSet alpha
      (lt_of_lt_of_le (by norm_num) halpha) halpha1) := by
  by_cases hhalf : alpha = 1 / 2
  · subst alpha
    refine ⟨rho.conditionalMaxEntropy, ?_⟩
    intro x hx
    rcases hx with ⟨sigma, hsigma, rfl⟩
    exact sandwichedUpSourceCandidate_half_le_conditionalMaxEntropy rho sigma hsigma
  · have hhalf' : 1 / 2 < alpha := lt_of_le_of_ne halpha (Ne.symm hhalf)
    simpa using
      rho.conditionalSandwichedRenyiUpSourceValueSet_bddAbove hhalf' halpha1

/-- Measuring the first subsystem by a sub-unital measurement cannot decrease
the source-shaped upward sandwiched conditional Renyi entropy at any finite
order `alpha >= 1/2`, `alpha != 1`.

No full-rank condition is imposed on the input or measured state. The proof
maps each full-rank side-reference candidate by divergence DPI and reference
dominance, then takes the source optimizer supremum. -/
theorem measurementMap_conditionalSandwichedRenyiUpSource_monotonicity
    (rho : State (Prod a b))
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M)
    (alpha : Real) (halpha : 1 / 2 <= alpha) (halpha1 : alpha ≠ 1) :
    rho.conditionalSandwichedRenyiUpSource alpha (by linarith) halpha1 <=
      (measureSubsystemState M rho).conditionalSandwichedRenyiUpSource
        alpha (by linarith) halpha1 := by
  letI : Nonempty b := by
    rcases rho.nonempty with ⟨z⟩
    exact ⟨z.2⟩
  unfold conditionalSandwichedRenyiUpSource
  refine csSup_le
    (rho.conditionalSandwichedRenyiUpSourceValueSet_nonempty
      alpha (by linarith) halpha1) ?_
  intro x hx
  rcases hx with ⟨sigma, hsigma, rfl⟩
  exact
    (conditionalSandwichedRenyiUpSourceCandidate_le_measureSubsystemState
      rho M hMUnit alpha halpha halpha1 sigma hsigma).trans
      (le_csSup
        (conditionalSandwichedRenyiUpSourceValueSet_bddAbove_of_half_le_ne_one
          (measureSubsystemState M rho) alpha halpha halpha1)
        ⟨sigma, hsigma, rfl⟩)

/-! ## Boundary order `alpha = infinity` -/


/-- A conditional-min feasible exponent remains feasible after a sub-unital
measurement of the first subsystem. -/
theorem ConditionalMinEntropyFeasible.measureSubsystemState
    (rho : State (Prod a b)) (sigma : State b) (lam : Real)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M)
    (h : ConditionalMinEntropyFeasible (a := a) rho sigma lam) :
    ConditionalMinEntropyFeasible (a := c) (measureSubsystemState M rho) sigma lam := by
  let Phi : Channel (Prod a b) (Prod c b) :=
    Channel.prod (Channel.measure M) (Channel.idChannel b)
  let rin : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) sigma
  let rout : CMatrix (Prod c b) := identityTensorStateMatrix (a := c) sigma
  let t : Real := Real.rpow 2 (-lam)
  have ht : 0 <= t := Real.rpow_nonneg (by norm_num) _
  have hmapRef : Phi.map rin <= rout := by
    simpa [Phi, rin, rout] using
      measurementMap_identityTensorStateMatrix_le M hMUnit sigma
  have hmapFeas : Phi.map rho.matrix <= Phi.map ((t : Complex) • rin) := by
    apply Matrix.le_iff.mpr
    have hpos : (((t : Complex) • rin) - rho.matrix).PosSemidef := by
      simpa [t, rin, ConditionalMinEntropyFeasible, Matrix.le_iff] using h
    simpa [map_sub, map_smul] using Phi.mapsPositive _ hpos
  have hscaleRef : (t : Complex) • Phi.map rin <= (t : Complex) • rout :=
    cMatrix_ofReal_smul_le_smul ht hmapRef
  rw [ConditionalMinEntropyFeasible]
  have hfinal : Phi.map rho.matrix <= (t : Complex) • rout :=
    hmapFeas.trans (by simpa [map_smul] using hscaleRef)
  simpa [Phi, rin, rout, t, measureSubsystemState] using hfinal

/-- Conditional min-entropy cannot decrease under a sub-unital measurement of
the first subsystem. This is the `alpha = infinity` endpoint of the total
conditional sandwiched Renyi theorem. -/
theorem measurementMap_conditionalMinEntropy_monotonicity
    (rho : State (Prod a b))
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) :
    rho.conditionalMinEntropy <=
      (measureSubsystemState M rho).conditionalMinEntropy := by
  letI : Nonempty b := by
    rcases rho.nonempty with ⟨z⟩
    exact ⟨z.2⟩
  rw [conditionalMinEntropy_eq, conditionalMinEntropy_eq]
  change sSup (rho.conditionalMinEntropyFeasibleExponentValueSet (a := a)) <=
    sSup ((measureSubsystemState M rho).conditionalMinEntropyFeasibleExponentValueSet
      (a := c))
  refine csSup_le
    (rho.conditionalMinEntropyFeasibleExponentValueSet_nonempty (a := a)) ?_
  intro lam hlam
  rcases hlam with ⟨sigma, hfeas⟩
  exact le_csSup
    ((measureSubsystemState M rho).conditionalMinEntropyFeasibleExponentValueSet_bddAbove
      (a := c))
    ⟨sigma, ConditionalMinEntropyFeasible.measureSubsystemState
      rho sigma lam M hMUnit hfeas⟩

/-! ## Boundary order `alpha = 1` -/

/-- Against a full-rank side reference, the support-aware trace-log relative
entropy is the negative fixed-reference conditional entropy. -/
theorem relativeEntropyPSDReferenceTraceLogFinite_identityTensor_eq_neg_conditionalEntropy
    (rho : State (Prod a b)) (sigma : State b) (hsigma : sigma.matrix.PosDef) :
    relativeEntropyPSDReferenceTraceLogFinite rho
        (identityTensorStateMatrix (a := a) sigma)
        (identityTensorStateMatrix_posSemidef_of_state (a := a) sigma)
        (Matrix.Supports.of_right_posDef rho.matrix
          (identityTensorStateMatrix (a := a) sigma)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma)) =
      -rho.conditionalEntropyRelativeFullReference sigma hsigma := by
  let ref : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) sigma
  let href : ref.PosDef :=
    identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma
  let hsupp : Matrix.Supports rho.matrix ref :=
    Matrix.Supports.of_right_posDef rho.matrix ref href
  have hEntropy :
      (_root_.QIT.psdSupportCompressedState rho href.posSemidef hsupp).vonNeumann =
        rho.vonNeumann :=
    relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq
      rho href.posSemidef hsupp
  have hTrace :
      ((psdSupportCompress ref href.posSemidef rho.matrix *
        State.psdLog (psdSupportCompress ref href.posSemidef ref)
          (psdSupportCompress_self_posDef ref href.posSemidef)).trace).re =
        ((rho.matrix *
          cfc (fun x : Real => if x = 0 then 0 else Real.log x) ref).trace).re :=
    relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
      rho href.posSemidef hsupp
  have hLogZero :
      cfc (fun x : Real => if x = 0 then 0 else Real.log x) ref =
        State.psdLog ref href :=
    relativeEntropyTraceLog_cfc_logZero_eq_psdLog_of_posDef ref href
  have hSupportEntropy :
      rho.supportEntropyTraceTerm = -rho.vonNeumann * Real.log 2 :=
    rho.supportEntropyTraceTerm_eq_neg_vonNeumann_mul_log_two
  change relativeEntropyPSDReferenceTraceLogFinite rho ref href.posSemidef hsupp =
    -rho.conditionalEntropyRelativeFullReference sigma hsigma
  calc
    relativeEntropyPSDReferenceTraceLogFinite rho ref href.posSemidef hsupp =
        -(_root_.QIT.psdSupportCompressedState rho href.posSemidef hsupp).vonNeumann -
          ((psdSupportCompress ref href.posSemidef rho.matrix *
            State.psdLog (psdSupportCompress ref href.posSemidef ref)
              (psdSupportCompress_self_posDef ref href.posSemidef)).trace).re /
            Real.log 2 := by rfl
    _ = -rho.vonNeumann -
          ((rho.matrix * State.psdLog ref href).trace).re / Real.log 2 := by
      rw [hEntropy, hTrace, hLogZero]
    _ = -rho.conditionalEntropyRelativeFullReference sigma hsigma := by
      rw [conditionalEntropyRelativeFullReference, hSupportEntropy]
      simp only [ref]
      field_simp [(Real.log_pos one_lt_two).ne']

/-- Extended-real form of the full-reference trace-log bridge. -/
theorem relativeEntropyPSDReferenceTraceLogE_identityTensor_eq_neg_conditionalEntropy
    (rho : State (Prod a b)) (sigma : State b) (hsigma : sigma.matrix.PosDef) :
    relativeEntropyPSDReferenceTraceLogE rho
        (identityTensorStateMatrix (a := a) sigma)
        (identityTensorStateMatrix_posSemidef_of_state (a := a) sigma) =
      (-rho.conditionalEntropyRelativeFullReference sigma hsigma : EReal) := by
  let hsupp : Matrix.Supports rho.matrix
      (identityTensorStateMatrix (a := a) sigma) :=
    Matrix.Supports.of_right_posDef rho.matrix
      (identityTensorStateMatrix (a := a) sigma)
      (identityTensorStateMatrix_posDef_of_posDef (a := a) sigma hsigma)
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports rho
    (identityTensorStateMatrix_posSemidef_of_state (a := a) sigma) hsupp]
  rw [relativeEntropyPSDReferenceTraceLogFinite_identityTensor_eq_neg_conditionalEntropy
    rho sigma hsigma]
  simp

/-- The support-aware trace-log divergence from the positive scaling of the
canonical side reference is the negative conditional entropy, shifted by the
reference scale.  Unlike the full-reference bridge above, this theorem allows
the canonical marginal `rho_B` to be singular.

The proof diagonalizes `rho_B`.  In the product basis `I_A tensor U_B`, the
diagonal coefficients of `rho_AB` sum over `A` to the spectral weights of
`rho_B`; hence the trace-log term is `log scale - H(B)`.  The support theorem
for `rho_AB` against `I_A tensor rho_B` supplies the finite branch of the
extended-real divergence. -/
theorem relativeEntropyPSDReferenceTraceLogE_real_smul_identityTensor_marginalB_eq
    (rho : State (Prod a b)) {scale : Real} (hscale : 0 < scale) :
    relativeEntropyPSDReferenceTraceLogE rho
        (scale • identityTensorStateMatrix (a := a) rho.marginalB)
        (Matrix.PosSemidef.smul
          (identityTensorStateMatrix_posSemidef_of_state
            (a := a) rho.marginalB) hscale.le) =
      (-rho.conditionalEntropy - log2 scale : EReal) := by
  classical
  let sigma := rho.marginalB
  let ref : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) sigma
  let scaledRef : CMatrix (Prod a b) := scale • ref
  let href : ref.PosSemidef :=
    identityTensorStateMatrix_posSemidef_of_state (a := a) sigma
  let hscaledRef : scaledRef.PosSemidef := Matrix.PosSemidef.smul href hscale.le
  have hsupport : Matrix.Supports rho.matrix ref := by
    simpa [ref, sigma, identityTensorStateMatrix] using
      matrix_supports_identityTensor_marginalB (a := a) (b := b) rho
  have hsupportScaled : Matrix.Supports rho.matrix scaledRef := by
    intro v hv
    have hscaledZero : scale • Matrix.mulVec ref v = 0 := by
      simpa [scaledRef, Matrix.smul_mulVec] using hv
    have hrefZero : Matrix.mulVec ref v = 0 := by
      exact (smul_eq_zero.mp hscaledZero).resolve_left hscale.ne'
    exact hsupport v hrefZero
  let UB : Matrix.unitaryGroup b Complex :=
    sigma.pos.isHermitian.eigenvectorUnitary
  let UA : Matrix.unitaryGroup a Complex := 1
  let U : Matrix.unitaryGroup (Prod a b) Complex :=
    ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
      Matrix.kronecker_mem_unitary UA.2 UB.2⟩
  let mu : b -> Real := fun j => sigma.pos.isHermitian.eigenvalues j
  let d : Prod a b -> Real := fun ij => scale * mu ij.2
  let coeff : Prod a b -> Real := fun ij =>
    ((star (U : CMatrix (Prod a b)) * rho.matrix *
      (U : CMatrix (Prod a b))) ij ij).re
  let f : Real -> Real := fun x => if x = 0 then 0 else Real.log x
  have hsigmaSpec :
      sigma.matrix = (UB : CMatrix b) *
          Matrix.diagonal (fun j : b => ((mu j : Real) : Complex)) *
          star (UB : CMatrix b) := by
    simpa [UB, mu, Function.comp_def, Unitary.conjStarAlgAut_apply] using
      sigma.pos.isHermitian.spectral_theorem
  have hdiagKron :
      Matrix.kronecker (1 : CMatrix a)
          (Matrix.diagonal (fun j : b => ((mu j : Real) : Complex))) =
        Matrix.diagonal
          (fun ij : Prod a b => ((mu ij.2 : Real) : Complex)) := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨k, l⟩
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.diagonal,
        hik, hjl]
  have hrefSpec :
      ref = (U : CMatrix (Prod a b)) *
          Matrix.diagonal
            (fun ij : Prod a b => ((mu ij.2 : Real) : Complex)) *
          star (U : CMatrix (Prod a b)) := by
    change Matrix.kronecker (1 : CMatrix a) sigma.matrix = _
    rw [hsigmaSpec]
    rw [← hdiagKron]
    calc
      Matrix.kronecker (1 : CMatrix a)
          (((UB : CMatrix b) *
            Matrix.diagonal (fun j : b => ((mu j : Real) : Complex))) *
              star (UB : CMatrix b)) =
          Matrix.kronecker ((1 : CMatrix a) * 1)
            ((UB : CMatrix b) *
              Matrix.diagonal (fun j : b => ((mu j : Real) : Complex))) *
          Matrix.kronecker (1 : CMatrix a) (star (UB : CMatrix b)) := by
        simpa using
          (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
            ((UB : CMatrix b) *
              Matrix.diagonal (fun j : b => ((mu j : Real) : Complex)))
            (star (UB : CMatrix b)))
      _ = (Matrix.kronecker (1 : CMatrix a) (UB : CMatrix b) *
          Matrix.kronecker (1 : CMatrix a)
            (Matrix.diagonal (fun j : b => ((mu j : Real) : Complex)))) *
          Matrix.kronecker (1 : CMatrix a) (star (UB : CMatrix b)) := by
        exact congrArg
          (fun M : CMatrix (Prod a b) =>
            M * Matrix.kronecker (1 : CMatrix a) (star (UB : CMatrix b)))
          (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a)
            (UB : CMatrix b)
            (Matrix.diagonal (fun j : b => ((mu j : Real) : Complex))))
      _ = _ := by
        simp [U, UA, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_kronecker, Matrix.mul_assoc]
  have hdiagScale :
      ((scale : Complex) • Matrix.diagonal
          (fun ij : Prod a b => ((mu ij.2 : Real) : Complex))) =
        Matrix.diagonal (fun ij : Prod a b => ((d ij : Real) : Complex)) := by
    ext ij kl
    simp [d, Matrix.diagonal]
  have hscaledSpec :
      scaledRef = (U : CMatrix (Prod a b)) *
          Matrix.diagonal (fun ij : Prod a b => ((d ij : Real) : Complex)) *
          star (U : CMatrix (Prod a b)) := by
    rw [show scaledRef = (scale : Complex) • ref by rfl, hrefSpec]
    calc
      (scale : Complex) •
          ((U : CMatrix (Prod a b)) *
            Matrix.diagonal
              (fun ij : Prod a b => ((mu ij.2 : Real) : Complex)) *
            star (U : CMatrix (Prod a b))) =
        ((scale : Complex) •
          ((U : CMatrix (Prod a b)) *
            Matrix.diagonal
              (fun ij : Prod a b => ((mu ij.2 : Real) : Complex)))) *
            star (U : CMatrix (Prod a b)) := by
              rw [Matrix.smul_mul]
      _ = ((U : CMatrix (Prod a b)) *
          ((scale : Complex) • Matrix.diagonal
            (fun ij : Prod a b => ((mu ij.2 : Real) : Complex)))) *
            star (U : CMatrix (Prod a b)) := by
              rw [Matrix.mul_smul]
      _ = (U : CMatrix (Prod a b)) *
          Matrix.diagonal (fun ij : Prod a b => ((d ij : Real) : Complex)) *
            star (U : CMatrix (Prod a b)) := by rw [hdiagScale]
  have hlogScaled :
      cfc f scaledRef = (U : CMatrix (Prod a b)) *
          Matrix.diagonal (fun ij : Prod a b => ((f (d ij) : Real) : Complex)) *
          star (U : CMatrix (Prod a b)) := by
    rw [hscaledSpec]
    exact cfc_unitary_conj_diagonal_ofReal U d f
  have hpartial :
      partialTraceA (a := a) (b := b)
          (star (U : CMatrix (Prod a b)) * rho.matrix *
            (U : CMatrix (Prod a b))) =
        star (UB : CMatrix b) * sigma.matrix * (UB : CMatrix b) := by
    have h := partialTraceA_local_unitary_conj
      (a := a) (b := b) rho.matrix UA UB
    simpa [U, sigma, State.marginalB_matrix] using h
  have hdiagB :
      star (UB : CMatrix b) * sigma.matrix * (UB : CMatrix b) =
        Matrix.diagonal (fun j : b => ((mu j : Real) : Complex)) := by
    calc
      star (UB : CMatrix b) * sigma.matrix * (UB : CMatrix b) =
          (star (UB : CMatrix b) * (UB : CMatrix b)) *
            Matrix.diagonal (fun j : b => ((mu j : Real) : Complex)) *
              (star (UB : CMatrix b) * (UB : CMatrix b)) := by
        rw [hsigmaSpec]
        noncomm_ring
      _ = Matrix.diagonal (fun j : b => ((mu j : Real) : Complex)) := by
        rw [Unitary.coe_star_mul_self]
        simp
  have hcoeffSum (j : b) : (∑ i : a, coeff (i, j)) = mu j := by
    have hentry := congrFun (congrFun hpartial j) j
    rw [hdiagB] at hentry
    have hre := congrArg Complex.re hentry
    simpa [partialTraceA, coeff, Matrix.diagonal] using hre
  have htrace :
      ((rho.matrix * cfc f scaledRef).trace).re =
        ∑ ij : Prod a b, coeff ij * f (d ij) := by
    rw [hlogScaled]
    let D : CMatrix (Prod a b) :=
      Matrix.diagonal fun ij => ((f (d ij) : Real) : Complex)
    have htraceCycle :
        (rho.matrix * ((U : CMatrix (Prod a b)) * D *
          star (U : CMatrix (Prod a b)))).trace =
          ((star (U : CMatrix (Prod a b)) * rho.matrix *
            (U : CMatrix (Prod a b))) * D).trace := by
      calc
        (rho.matrix * ((U : CMatrix (Prod a b)) * D *
            star (U : CMatrix (Prod a b)))).trace =
            (((rho.matrix * (U : CMatrix (Prod a b))) * D) *
              star (U : CMatrix (Prod a b))).trace := by
                simp [Matrix.mul_assoc]
        _ = (star (U : CMatrix (Prod a b)) *
            ((rho.matrix * (U : CMatrix (Prod a b))) * D)).trace := by
              rw [Matrix.trace_mul_comm]
        _ = ((star (U : CMatrix (Prod a b)) * rho.matrix *
            (U : CMatrix (Prod a b))) * D).trace := by
              simp [Matrix.mul_assoc]
    rw [htraceCycle]
    simp [D, coeff, Matrix.trace, Matrix.diagonal, Matrix.mul_apply,
      Complex.mul_re]
  have hpoint (j : b) :
      mu j * f (scale * mu j) =
        mu j * Real.log scale + mu j * Real.log (mu j) := by
    by_cases hj : mu j = 0
    · simp [hj]
    · have hjpos : 0 < mu j :=
        lt_of_le_of_ne (sigma.pos.eigenvalues_nonneg j) (Ne.symm hj)
      simp [f, hj, hscale.ne', Real.log_mul hscale.ne' hjpos.ne', mul_add]
  have hsum :
      (∑ ij : Prod a b, coeff ij * f (d ij)) =
        Real.log scale + ∑ j : b, mu j * Real.log (mu j) := by
    calc
      (∑ ij : Prod a b, coeff ij * f (d ij)) =
          ∑ j : b, (∑ i : a, coeff (i, j)) * f (scale * mu j) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [d, Finset.sum_mul]
      _ = ∑ j : b, mu j * f (scale * mu j) := by
        simp [hcoeffSum]
      _ = ∑ j : b,
          (mu j * Real.log scale + mu j * Real.log (mu j)) := by
        refine Finset.sum_congr rfl fun j _ => hpoint j
      _ = Real.log scale + ∑ j : b, mu j * Real.log (mu j) := by
        rw [Finset.sum_add_distrib]
        have hmu : ∑ j : b, mu j = 1 := by
          have hmuComplex :
              (∑ j : b, ((mu j : Real) : Complex)) = 1 := by
            simpa [mu] using
              sigma.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans
                sigma.trace_eq_one
          exact Complex.ofReal_injective (by simpa using hmuComplex)
        rw [← Finset.sum_mul, hmu]
        ring
  have hEntropy :
      (_root_.QIT.psdSupportCompressedState rho hscaledRef hsupportScaled).vonNeumann =
        rho.vonNeumann :=
    relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq
      rho hscaledRef hsupportScaled
  have hTraceCompress :
      (((_root_.QIT.psdSupportCompressedState rho hscaledRef hsupportScaled).matrix *
        State.psdLog (psdSupportCompress scaledRef hscaledRef scaledRef)
          (psdSupportCompress_self_posDef scaledRef hscaledRef)).trace).re =
        ((rho.matrix * cfc f scaledRef).trace).re := by
    simpa [f, _root_.QIT.psdSupportCompressedState] using
      relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
        rho hscaledRef hsupportScaled
  have hMarginalEntropy :
      (∑ j : b, mu j * Real.log (mu j)) / Real.log 2 =
        -sigma.vonNeumann := by
    unfold State.vonNeumann xlog2 log2
    have hpointLog (j : b) :
        mu j * Real.log (mu j) / Real.log 2 =
          if mu j = 0 then 0 else mu j * (Real.log (mu j) / Real.log 2) := by
      by_cases hj : mu j = 0 <;> simp [hj]
      ring
    rw [Finset.sum_div]
    simp_rw [hpointLog]
    simp [mu]
  rw [relativeEntropyPSDReferenceTraceLogE_eq_coe_of_supports
      rho hscaledRef hsupportScaled]
  congr 1
  simp only [relativeEntropyPSDReferenceTraceLogFinite]
  rw [hEntropy, hTraceCompress, htrace, hsum]
  rw [conditionalEntropy_eq]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold log2
  rw [show (Real.log scale + ∑ j : b, mu j * Real.log (mu j)) /
      Real.log 2 = Real.log scale / Real.log 2 +
        (∑ j : b, mu j * Real.log (mu j)) / Real.log 2 by
      field_simp [hlog]]
  rw [hMarginalEntropy]
  ring

/-- Conditional von Neumann entropy cannot decrease under the sub-unital
measurement when the side marginal is full-rank. The proof is exactly
reference dominance followed by trace-log relative-entropy DPI. -/
theorem measurementMap_conditionalEntropy_monotonicity_of_marginalB_posDef
    (rho : State (Prod a b)) (hrhoB : rho.marginalB.matrix.PosDef)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) :
    rho.conditionalEntropy <= (measureSubsystemState M rho).conditionalEntropy := by
  let out : State (Prod c b) := measureSubsystemState M rho
  have hmarg : out.marginalB = rho.marginalB := by
    simpa [out, measureSubsystemState] using
      marginalB_applyState_prod_id rho (Channel.measure M)
  have houtB : out.marginalB.matrix.PosDef := by
    rw [hmarg]
    exact hrhoB
  let Phi : Channel (Prod a b) (Prod c b) :=
    Channel.prod (Channel.measure M) (Channel.idChannel b)
  let rin : CMatrix (Prod a b) :=
    identityTensorStateMatrix (a := a) rho.marginalB
  let rout : CMatrix (Prod c b) :=
    identityTensorStateMatrix (a := c) out.marginalB
  have hrin : rin.PosSemidef :=
    identityTensorStateMatrix_posSemidef_of_state (a := a) rho.marginalB
  have hrout : rout.PosSemidef :=
    identityTensorStateMatrix_posSemidef_of_state (a := c) out.marginalB
  have hmap : Phi.map rin <= rout := by
    simpa [Phi, rin, rout, hmarg] using
      measurementMap_identityTensorStateMatrix_le M hMUnit rho.marginalB
  have hDPI :=
    relativeEntropyPSDReferenceTraceLogE_dataProcessing_channel_ge rho hrin Phi
  have hreference :=
    relativeEntropyPSDReferenceTraceLogE_antitone_reference (Phi.applyState rho)
      (Phi.mapsPositive rin hrin) hrout hmap
  have hdiv :
      relativeEntropyPSDReferenceTraceLogE (Phi.applyState rho) rout hrout <=
        relativeEntropyPSDReferenceTraceLogE rho rin hrin :=
    hreference.trans hDPI
  have hdiv' :
      relativeEntropyPSDReferenceTraceLogE out
          (identityTensorStateMatrix (a := c) out.marginalB)
          (identityTensorStateMatrix_posSemidef_of_state (a := c) out.marginalB) <=
        relativeEntropyPSDReferenceTraceLogE rho
          (identityTensorStateMatrix (a := a) rho.marginalB)
          (identityTensorStateMatrix_posSemidef_of_state (a := a) rho.marginalB) := by
    simpa [Phi, rin, rout, out, measureSubsystemState] using hdiv
  rw [relativeEntropyPSDReferenceTraceLogE_identityTensor_eq_neg_conditionalEntropy
      out out.marginalB houtB,
    relativeEntropyPSDReferenceTraceLogE_identityTensor_eq_neg_conditionalEntropy
      rho rho.marginalB hrhoB,
    conditionalEntropyRelativeFullReference_to_conditionalEntropy out houtB,
    conditionalEntropyRelativeFullReference_to_conditionalEntropy rho hrhoB] at hdiv'
  have hreal : -out.conditionalEntropy <= -rho.conditionalEntropy :=
    EReal.coe_le_coe_iff.mp hdiv'
  simpa [out] using (neg_le_neg_iff.mp hreal)

/-- Conditional von Neumann entropy cannot decrease under a sub-unital
measurement, with no rank assumption on the state.

The conditioning register is first compressed to the support of its marginal,
where the canonical side reference is full-rank. Measurement commutes with the
conditioning isometry, so the source trace-log DPI proof transports back to
the original register. -/
theorem measurementMap_conditionalEntropy_monotonicity
    (rho : State (Prod a b))
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) :
    rho.conditionalEntropy <= (measureSubsystemState M rho).conditionalEntropy := by
  let rhoC := rho.conditioningSupportCompressedState
  let V : ReferenceIsometry
      (psdSupportIndex rho.marginalB.matrix rho.marginalB.pos) b :=
    psdSupportReferenceIsometry rho.marginalB.matrix rho.marginalB.pos
  let outC := measureSubsystemState M rhoC
  let out := measureSubsystemState M rho
  have hrhoMatrix : V.applyMatrixRight rhoC.matrix = rho.matrix := by
    have hrec := congrArg State.matrix
      (rho.conditioningSupportCompressedState_conditioningIsometryApply)
    simpa [rhoC, V, State.conditioningIsometryApply_matrix] using hrec
  have houtRec : outC.conditioningIsometryApply V = out := by
    apply State.ext
    rw [State.conditioningIsometryApply_matrix]
    change V.applyMatrixRight
        (MatrixMap.kron (Channel.measure M).map
          (Channel.idChannel
            (psdSupportIndex rho.marginalB.matrix rho.marginalB.pos)).map
          rhoC.matrix) =
      MatrixMap.kron (Channel.measure M).map (Channel.idChannel b).map rho.matrix
    rw [← hrhoMatrix]
    exact (MatrixMap.kron_idChannel_apply_applyMatrixRight
      (Channel.measure M).map V rhoC.matrix).symm
  have hmono : rhoC.conditionalEntropy <= outC.conditionalEntropy :=
    measurementMap_conditionalEntropy_monotonicity_of_marginalB_posDef rhoC
      (State.conditioningSupportCompressedState_marginalB_posDef rho) M hMUnit
  calc
    rho.conditionalEntropy = rhoC.conditionalEntropy := by
      symm
      exact State.conditionalEntropy_conditioningSupportCompressedState rho
    _ <= outC.conditionalEntropy := hmono
    _ = out.conditionalEntropy := by
      have h := State.conditionalEntropy_conditioningIsometryApply outC V
      rw [houtRec] at h
      exact h.symm
    _ = (measureSubsystemState M rho).conditionalEntropy := rfl

/-! ## Full closed Renyi-order theorem -/

/-- Measuring the first subsystem by a sub-unital measurement cannot decrease
the upward sandwiched conditional Renyi entropy for any
`alpha in [1/2, infinity]` and any normalized finite-dimensional state.

This is the source-shaped theorem from Tomamichel `cond.tex:268-291`. The
finite non-unit orders use reference dominance, divergence DPI, and
side-reference optimization. The unit and infinity endpoints use the same
trace-log and operator-order routes. No full-rank state assumption, conditional
duality, or reverse-channel hypothesis remains; the pointwise comparison is
the direct source DPI route. -/
theorem measurementMap_conditionalSandwichedRenyiUpExtendedOrder_monotonicity
    (rho : State (Prod a b))
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M)
    (alpha : RenyiOrder) :
    rho.conditionalSandwichedRenyiUpExtendedOrder alpha <=
      (measureSubsystemState M rho).conditionalSandwichedRenyiUpExtendedOrder alpha := by
  obtain ⟨val, hval⟩ := alpha
  cases val with
  | top =>
      change rho.conditionalMinEntropy <=
        (measureSubsystemState M rho).conditionalMinEntropy
      exact measurementMap_conditionalMinEntropy_monotonicity rho M hMUnit
  | coe r =>
      have hr : 1 / 2 <= r := by exact_mod_cast hval
      change rho.conditionalSandwichedRenyiUpFiniteOrder r <=
        (measureSubsystemState M rho).conditionalSandwichedRenyiUpFiniteOrder r
      by_cases hone : r = 1
      · subst r
        rw [conditionalSandwichedRenyiUpFiniteOrder_one,
          conditionalSandwichedRenyiUpFiniteOrder_one]
        exact measurementMap_conditionalEntropy_monotonicity rho M hMUnit
      by_cases hhalf : r = (2 : Real)⁻¹
      · subst r
        rw [conditionalSandwichedRenyiUpFiniteOrder_half,
          conditionalSandwichedRenyiUpFiniteOrder_half]
        have hsource :=
          measurementMap_conditionalSandwichedRenyiUpSource_monotonicity
            rho M hMUnit (1 / 2 : Real) (by norm_num) (by norm_num)
        simpa only [conditionalSandwichedRenyiUpSource_half_eq_conditionalMaxEntropy]
          using hsource
      · have hpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
        rw [conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
            rho hpos hone hhalf,
          conditionalSandwichedRenyiUpFiniteOrder_of_pos_ne_one_ne_half
            (measureSubsystemState M rho) hpos hone hhalf]
        exact measurementMap_conditionalSandwichedRenyiUpSource_monotonicity
          rho M hMUnit r hr hone

end State

end

end QIT
