/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.Decoupling
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Protocols.FQSW.Core
public import QIT.OneShot.GentleMeasurement
public import QIT.States.Geometry.FuchsVdG
public import QIT.States.Purification.Schatten
public import QIT.Channels.Diamond

/-!
# FQSW one-shot decoupling route

This file is a dependency-ordered leaf of `QIT.Protocols.FQSW`.  Declaration
names, namespaces, statements, and proof terms are preserved from the original
monolithic module.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p u1 v1 w1

noncomputable section

local instance fqswCMatrixContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) :=
  SeminormedAddGroup.toContinuousENorm

private instance fqswUnitaryHaarMeasure_isMulRightInvariant {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    MeasureTheory.Measure.IsMulRightInvariant (unitaryHaarMeasure (a := ι)) := by
  haveI : SecondCountableTopology (Matrix.unitaryGroup ι ℂ) := by
    haveI : SecondCountableTopology (Matrix ι ι ℂ) := by
      change SecondCountableTopology (ι → ι → ℂ)
      infer_instance
    change SecondCountableTopology
      ({x // x ∈ (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ))})
    infer_instance
  refine ⟨?_⟩
  intro g
  let K0 : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup ι ℂ) := ⊤
  have hmass : (MeasureTheory.Measure.map (fun U : Matrix.unitaryGroup ι ℂ => U * g)
        (unitaryHaarMeasure (a := ι))) K0 = 1 := by
    rw [MeasureTheory.Measure.map_apply]
    · change (unitaryHaarMeasure (a := ι)) Set.univ = 1
      exact unitaryHaarMeasure_univ (a := ι)
    · exact continuous_mul_const g |>.measurable
    · exact K0.isCompact.measurableSet
  have hhaar := (MeasureTheory.Measure.haarMeasure_eq_iff K0
    (MeasureTheory.Measure.map (fun U : Matrix.unitaryGroup ι ℂ => U * g)
      (unitaryHaarMeasure (a := ι)))).2 hmass
  simpa [unitaryHaarMeasure, K0] using hhaar.symm

private instance fqswUnitaryHaarMeasure_isInvInvariant {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    MeasureTheory.Measure.IsInvInvariant (unitaryHaarMeasure (a := ι)) := by
  haveI : SecondCountableTopology (Matrix.unitaryGroup ι ℂ) := by
    haveI : SecondCountableTopology (Matrix ι ι ℂ) := by
      change SecondCountableTopology (ι → ι → ℂ)
      infer_instance
    change SecondCountableTopology
      ({x // x ∈ (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ))})
    infer_instance
  refine ⟨?_⟩
  let K0 : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup ι ℂ) := ⊤
  have hmass : (unitaryHaarMeasure (a := ι)).inv K0 = 1 := by
    rw [MeasureTheory.Measure.inv_def, MeasureTheory.Measure.map_apply]
    · change (unitaryHaarMeasure (a := ι)) Set.univ = 1
      exact unitaryHaarMeasure_univ (a := ι)
    · exact measurable_inv
    · exact K0.isCompact.measurableSet
  have hhaar := (MeasureTheory.Measure.haarMeasure_eq_iff K0
    (unitaryHaarMeasure (a := ι)).inv).2 hmass
  simpa [unitaryHaarMeasure, K0] using hhaar.symm

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

/-- Alice/reference marginal `ψ^{AR}` used by the ADHW one-shot FQSW proof
route. -/
def adhwFQSWARState (ψ : PureVector (Prod (Prod a b) r)) : State (Prod a r) :=
  ψ.state.coherentTransferReferenceState

/-- Alice's source split isometry induced by the source assumption
`A = A₁ × A₂` in ADHW `thm:trueoneShotMother` (fqsw.tex lines 553-568). -/
def adhwFQSWAliceIsometryOfSplit (split : a ≃ Prod q e) :
    ReferenceIsometry a (Prod q e) :=
  ReferenceIsometry.ofEquiv split

/-- Alice's source split followed by a unitary on the split `A₁ × A₂`
register, matching the Haar-random unitary stage in ADHW fqsw.tex
lines 580-841. -/
def adhwFQSWAliceIsometryOfSplitUnitary
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    ReferenceIsometry a (Prod q e) :=
  (ReferenceUnitary.toReferenceIsometry ({ matrix := U } : ReferenceUnitary (Prod q e))).comp
    (adhwFQSWAliceIsometryOfSplit split)

/-- The post-Alice state before Bob's isometry, for a concrete Alice isometry
`U : A → A₁A₂`. -/
def adhwFQSWPostAliceStateOfIsometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    State (Prod (Prod q e) (Prod b r)) :=
  let ψA : PureVector (Prod a (Prod b r)) :=
    ψ.reindex (fqswSourceToAliceInputEquiv a b r)
  (U.applyPureVector ψA).state

/-- The post-Alice pure vector regrouped as a purification of the decoupling
marginal `σ^{A₂R}(U)`, with Bob's side `A₁B` as the purifying reference. -/
def adhwFQSWPostAliceA2RPurificationOfIsometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    PureVector (Prod (Prod q b) (Prod e r)) :=
  let ψA : PureVector (Prod a (Prod b r)) :=
    ψ.reindex (fqswSourceToAliceInputEquiv a b r)
  (U.applyPureVector ψA).reindex (fqswAliceOutputToA2REquiv q e b r)

/-- The decoupling marginal `σ^{A₂R}(U)` from ADHW fqsw.tex lines 580-841. -/
def adhwFQSWSigmaA2RStateOfIsometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) : State (Prod e r) :=
  ((adhwFQSWPostAliceStateOfIsometry ψ U).reindex
    (fqswAliceOutputToA2REquiv q e b r)).marginalB

omit [Nonempty e] in
/-- The regrouped post-Alice pure vector purifies the ADHW decoupling marginal
`σ^{A₂R}(U)`. -/
theorem adhwFQSWPostAliceA2RPurificationOfIsometry_purifies
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    (adhwFQSWPostAliceA2RPurificationOfIsometry (q := q) (e := e) ψ U).Purifies
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U) := by
  dsimp [adhwFQSWPostAliceA2RPurificationOfIsometry,
    adhwFQSWSigmaA2RStateOfIsometry, adhwFQSWPostAliceStateOfIsometry]
  exact PureVector.purifies_marginalB _

/-- The `A₂` marginal `σ^{A₂}(U)` in ADHW fqsw.tex lines 767-795. -/
def adhwFQSWSigmaA2StateOfIsometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) : State e :=
  (adhwFQSWSigmaA2RStateOfIsometry (q := q) ψ U).marginalA

/-- The reference marginal `σ^R`, unchanged by Alice's isometry in the ADHW
one-shot proof route. -/
def adhwFQSWSigmaRState (ψ : PureVector (Prod (Prod a b) r)) : State r :=
  (adhwFQSWARState ψ).marginalB

/-- If the left subsystem has only one basis element, every bipartite state is
the product of its two marginals. -/
theorem state_matrix_eq_prod_marginals_of_subsingleton_left
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Subsingleton α] (ρ : State (Prod α β)) :
    ρ.matrix = (ρ.marginalA.prod ρ.marginalB).matrix := by
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  have hxy : xa = ya := Subsingleton.elim _ _
  subst ya
  have hA : ρ.marginalA.matrix xa xa = 1 := by
    have htrace := ρ.marginalA.trace_eq_one
    rw [Matrix.trace] at htrace
    have hsum :
        (∑ x : α, ρ.marginalA.matrix x x) =
          ρ.marginalA.matrix xa xa := by
      apply Finset.sum_eq_single xa
      · intro b _ hb
        exact False.elim (hb (Subsingleton.elim b xa))
      · intro h
        exact False.elim (h (Finset.mem_univ xa))
    have hsum_diag :
        (∑ x : α, Matrix.diag ρ.marginalA.matrix x) =
          ρ.marginalA.matrix xa xa := by
      simpa [Matrix.diag] using hsum
    rw [hsum_diag] at htrace
    exact htrace
  have hB : ρ.marginalB.matrix xb yb = ρ.matrix (xa, xb) (xa, yb) := by
    rw [State.marginalB_matrix]
    simp [partialTraceA]
    exact Finset.sum_eq_single xa
      (by intro b _ hb; exact False.elim (hb (Subsingleton.elim b xa)))
      (by intro h; exact False.elim (h (Finset.mem_univ xa)))
  change ρ.matrix (xa, xb) (xa, yb) =
    ρ.marginalA.matrix xa xa * ρ.marginalB.matrix xb yb
  rw [hA, hB]
  simp

/-- The ADHW notation `σ^R` is the `R` marginal of the original pure source. -/
theorem adhwFQSWSigmaRState_eq_source_marginalB
    (ψ : PureVector (Prod (Prod a b) r)) :
    adhwFQSWSigmaRState ψ = ψ.state.marginalB := by
  apply State.ext
  ext x y
  simp [adhwFQSWSigmaRState, adhwFQSWARState, State.marginalB,
    State.coherentTransferReferenceState, partialTraceA, Fintype.sum_prod_type]

omit [Nonempty e] in
/-- Regrouping Alice's post-isometry state into `A₁B × A₂R` and then tracing
down to `R` is the same as tracing the original post-isometry state down to
`BR` and then to `R`.  This is the register-bookkeeping part of the ADHW
one-shot route before the Schur/HS moment calculation. -/
theorem adhwFQSW_marginalB_marginalB_reindex_a2r
    (ρ : State (Prod (Prod q e) (Prod b r))) :
    ((ρ.reindex (fqswAliceOutputToA2REquiv q e b r)).marginalB).marginalB =
      ρ.marginalB.marginalB := by
  apply State.ext
  ext x y
  simp [State.marginalB, State.reindex, fqswAliceOutputToA2REquiv, partialTraceA,
    Fintype.sum_prod_type]
  calc
    (∑ ee : e, ∑ qq : q, ∑ bb : b,
      ρ.matrix ((qq, ee), bb, x) ((qq, ee), bb, y)) =
        (∑ qq : q, ∑ ee : e, ∑ bb : b,
          ρ.matrix ((qq, ee), bb, x) ((qq, ee), bb, y)) := by
          rw [Finset.sum_comm]
    _ = (∑ qq : q, ∑ bb : b, ∑ ee : e,
          ρ.matrix ((qq, ee), bb, x) ((qq, ee), bb, y)) := by
          apply Finset.sum_congr rfl
          intro qq _
          rw [Finset.sum_comm]
    _ = (∑ bb : b, ∑ qq : q, ∑ ee : e,
          ρ.matrix ((qq, ee), bb, x) ((qq, ee), bb, y)) := by
          rw [Finset.sum_comm]

/-- Alice's source-to-input reindexing leaves the final reference marginal
as the `R` marginal used in the ADHW FQSW source route. -/
theorem adhwFQSW_sourceInput_marginalB_marginalB
    (ψ : PureVector (Prod (Prod a b) r)) :
    (ψ.reindex (fqswSourceToAliceInputEquiv a b r)).state.marginalB.marginalB =
      adhwFQSWSigmaRState ψ := by
  apply State.ext
  ext x y
  simp [adhwFQSWSigmaRState, adhwFQSWARState, State.marginalB,
    State.coherentTransferReferenceState, PureVector.state, fqswSourceToAliceInputEquiv,
    partialTraceA]
  rw [Finset.sum_comm]

omit [Nonempty e] in
/-- Tracing Bob's register after Alice's isometry is the same as applying the
Alice isometry directly to the source `AR` marginal.  This is the register
bridge that lets the ADHW Schur/HS calculation work on `ψ^{AR}` while the
operational protocol is computed from the full pure source `ψ^{ABR}`. -/
theorem adhwFQSWPostAliceStateOfIsometry_coherentTransferReference_matrix
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    (((adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).reindex
      (fqswSourceToAliceInputEquiv (Prod q e) b r).symm).coherentTransferReferenceState).matrix =
      U.applyMatrix (adhwFQSWARState ψ).matrix := by
  ext x y
  simp [adhwFQSWPostAliceStateOfIsometry, adhwFQSWARState,
    State.coherentTransferReferenceState, PureVector.state, State.reindex,
    fqswSourceToAliceInputEquiv, ReferenceIsometry.applyPureVector,
    ReferenceIsometry.applyAmp, ReferenceIsometry.applyMatrix,
    ReferenceIsometry.targetBlock, rankOneMatrix, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aa _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ii _
  apply Finset.sum_congr rfl
  intro bb _
  ring

omit [Nonempty e] in
/-- The decoupling marginal `σ^{A₂R}(U)` can be obtained from the post-Alice
`(A₁A₂)R` marginal by regrouping it as `A₁ × (A₂R)` and tracing out `A₁`.
This is the bookkeeping form used by the ADHW one-shot decoupling proof. -/
theorem adhwFQSWSigmaA2RStateOfIsometry_eq_postAliceAR_marginalB
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U =
      ((((adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).reindex
        (fqswSourceToAliceInputEquiv (Prod q e) b r).symm).coherentTransferReferenceState).reindex
          (fqswQERToA2REquiv q e r)).marginalB := by
  apply State.ext
  ext x y
  simp [adhwFQSWSigmaA2RStateOfIsometry, State.coherentTransferReferenceState,
    State.marginalB, State.reindex, fqswAliceOutputToA2REquiv,
    fqswSourceToAliceInputEquiv, fqswQERToA2REquiv, partialTraceA,
    Fintype.sum_prod_type]

omit [Nonempty e] in
/-- Matrix form of the ADHW decoupling marginal: `σ^{A₂R}(U)` is the
`A₂R` marginal of the source `AR` state after Alice's split isometry.  This is
the exact bridge from the operational full-source protocol state to the
source's Schur/HS one-shot calculation on `ψ^{AR}`. -/
theorem adhwFQSWSigmaA2RStateOfIsometry_matrix_eq_partialTraceA_applyMatrix_AR
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).matrix =
      partialTraceA (a := q) (b := Prod e r)
        ((U.applyMatrix (adhwFQSWARState ψ).matrix).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) := by
  rw [adhwFQSWSigmaA2RStateOfIsometry_eq_postAliceAR_marginalB]
  change partialTraceA (a := q) (b := Prod e r)
      (((((adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).reindex
        (fqswSourceToAliceInputEquiv (Prod q e) b r).symm).coherentTransferReferenceState).matrix).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) = _
  rw [adhwFQSWPostAliceStateOfIsometry_coherentTransferReference_matrix]

omit [Nonempty e] in
/-- The reference marginal `σ^R` in the ADHW one-shot proof is independent of
Alice's isometry.  This is the formal source-route bridge that justifies using
a fixed `σ^R` in the product term
`σ^{A₂}(U) ⊗ σ^R`. -/
theorem adhwFQSWSigmaA2RStateOfIsometry_marginalB_eq_sigmaR
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).marginalB =
      adhwFQSWSigmaRState ψ := by
  have hpost :
      (adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).marginalB =
        (ψ.reindex (fqswSourceToAliceInputEquiv a b r)).state.marginalB := by
    let Ψ : PureVector (Prod a (Prod b r)) :=
      ψ.reindex (fqswSourceToAliceInputEquiv a b r)
    have hpur : (U.applyPureVector Ψ).Purifies Ψ.state.marginalB := by
      exact U.applyPureVector_purifies (PureVector.purifies_marginalB Ψ)
    apply State.ext
    rw [State.marginalB_matrix]
    exact hpur
  calc
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).marginalB =
        (adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).marginalB.marginalB := by
          exact adhwFQSW_marginalB_marginalB_reindex_a2r
            (adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U)
    _ = (ψ.reindex (fqswSourceToAliceInputEquiv a b r)).state.marginalB.marginalB := by
          rw [hpost]
    _ = adhwFQSWSigmaRState ψ := by
          exact adhwFQSW_sourceInput_marginalB_marginalB ψ

/-- The maximally mixed `I^{A₂}/d_{A₂}` state appearing in the ADHW decoupling
target of fqsw.tex lines 580-841. -/
def adhwFQSWMaximallyMixedA2State (e : Type y)
    [Fintype e] [DecidableEq e] [Nonempty e] : State e :=
  State.maximallyMixed e

/-- The source-route trace-norm decoupling integrand for a split Alice system
and a concrete unitary on `A₁ × A₂`, matching the quantity controlled by the
Haar-selection step in ADHW fqsw.tex lines 580-841. -/
def adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  traceNormDistance
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix
    (((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)).matrix)

/-- Product-decoupling trace-norm integrand
`||σ^{A₂R}(U) - σ^{A₂}(U) ⊗ σ^R||₁` from ADHW fqsw.tex
lines 580-592 and 806-815. -/
def adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  traceNormDistance
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).matrix
    (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
      (adhwFQSWSigmaRState ψ)).matrix)

/-- Max-mixed `A₂` trace-norm integrand
`||σ^{A₂}(U) - I^{A₂}/d_{A₂}||₁` from ADHW fqsw.tex lines
767-795 and 806-815. -/
def adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  traceNormDistance
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix
    (adhwFQSWMaximallyMixedA2State e).matrix

/-- Hilbert--Schmidt-square version of the product-decoupling integrand in
ADHW fqsw.tex lines 682-747. -/
def adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  hilbertSchmidtSq
    ((adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).matrix -
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
        (adhwFQSWSigmaRState ψ)).matrix))

/-- Hilbert--Schmidt-square version of the max-mixed `A₂` integrand in ADHW
fqsw.tex lines 776-787. -/
def adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  hilbertSchmidtSq
    ((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix -
      (adhwFQSWMaximallyMixedA2State e).matrix)

/-- Source `A` marginal reindexed by the ADHW split `A ≃ A₁ × A₂`. -/
def adhwFQSWASplitMatrix
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    CMatrix (Prod q e) :=
  ((adhwFQSWARState ψ).marginalA.matrix).submatrix split.symm split.symm

/-- Source `AR` marginal reindexed by the ADHW split `A ≃ A₁ × A₂`. -/
def adhwFQSWARSplitMatrix
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    CMatrix (Prod (Prod q e) r) :=
  ((adhwFQSWARState ψ).matrix).submatrix
    (fqswARSplitEquiv split).symm (fqswARSplitEquiv split).symm

/-- Split form of `ψ^A ⊗ ψ^R` on the `A₁A₂R` register. -/
def adhwFQSWARProductSplitMatrix
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    CMatrix (Prod (Prod q e) r) :=
  Matrix.kronecker (adhwFQSWASplitMatrix ψ split) (adhwFQSWSigmaRState ψ).matrix

theorem referenceIsometry_partialTraceB_applyMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (V : ReferenceIsometry α β) (X : CMatrix (Prod α γ)) :
    partialTraceB (a := β) (b := γ) (V.applyMatrix X) =
      V.matrix * partialTraceB (a := α) (b := γ) X *
        Matrix.conjTranspose V.matrix := by
  ext i j
  simp [partialTraceB, ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- Applying a reference isometry to the left/reference side conjugates the
left marginal by that isometry. -/
theorem referenceIsometry_marginalA_applyPureVector
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (V : ReferenceIsometry α β) (Ψ : PureVector (Prod α γ)) :
    (V.applyPureVector Ψ).state.marginalA.matrix =
      V.matrix * Ψ.state.marginalA.matrix * Matrix.conjTranspose V.matrix := by
  rw [State.marginalA_matrix]
  rw [PureVector.state_matrix]
  rw [ReferenceIsometry.applyPureVector_amp]
  rw [V.rankOne_applyAmp]
  rw [referenceIsometry_partialTraceB_applyMatrix]
  rfl

/-- Conjugating a bipartite matrix by a product reference isometry is the same
as applying the right isometry first and then the left isometry. -/
theorem referenceIsometry_prod_conj_eq_applyMatrix_applyMatrixRight
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (V : ReferenceIsometry α β) (W : ReferenceIsometry γ δ)
    (X : CMatrix (Prod α γ)) :
    Matrix.kronecker V.matrix W.matrix * X *
        Matrix.conjTranspose (Matrix.kronecker V.matrix W.matrix) =
      V.applyMatrix (W.applyMatrixRight X) := by
  ext x y
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.targetBlock, ReferenceIsometry.rightBlock,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_kronecker, Finset.sum_mul, Finset.mul_sum,
    Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm]
  apply Finset.sum_congr rfl
  intro _ _
  rw [Finset.sum_comm]

/-- Taking the right marginal after a product reference-isometry conjugation
leaves only the left isometry conjugating the original left marginal. -/
theorem referenceIsometry_prod_partialTraceB_conj
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (V : ReferenceIsometry α β) (W : ReferenceIsometry γ δ)
    (X : CMatrix (Prod α γ)) :
    partialTraceB (a := β) (b := δ)
        (Matrix.kronecker V.matrix W.matrix * X *
          Matrix.conjTranspose (Matrix.kronecker V.matrix W.matrix)) =
      V.matrix * partialTraceB (a := α) (b := γ) X *
        Matrix.conjTranspose V.matrix := by
  rw [referenceIsometry_prod_conj_eq_applyMatrix_applyMatrixRight]
  rw [referenceIsometry_partialTraceB_applyMatrix]
  rw [W.partialTraceB_applyMatrixRight]

/-- Taking the left marginal after a product reference-isometry conjugation
leaves only the right isometry conjugating the original right marginal. -/
theorem referenceIsometry_prod_partialTraceA_conj
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (V : ReferenceIsometry α β) (W : ReferenceIsometry γ δ)
    (X : CMatrix (Prod α γ)) :
    partialTraceA (a := β) (b := δ)
        (Matrix.kronecker V.matrix W.matrix * X *
          Matrix.conjTranspose (Matrix.kronecker V.matrix W.matrix)) =
      W.matrix * partialTraceA (a := α) (b := γ) X *
        Matrix.conjTranspose W.matrix := by
  rw [referenceIsometry_prod_conj_eq_applyMatrix_applyMatrixRight]
  rw [V.partialTraceA_applyMatrix]
  rw [W.partialTraceA_applyMatrixRight]

/-- Applying composed reference isometries to a matrix is the same as applying
the right factor first and the left factor second. -/
theorem referenceIsometry_comp_applyMatrix
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (W : ReferenceIsometry β γ) (V : ReferenceIsometry α β)
    (X : CMatrix (Prod α δ)) :
    (W.comp V).applyMatrix X = W.applyMatrix (V.applyMatrix X) := by
  ext x y
  let B : CMatrix α := ReferenceIsometry.targetBlock X x.2 y.2
  change (((W.matrix * V.matrix) * B *
        Matrix.conjTranspose (W.matrix * V.matrix)) x.1 y.1) =
      (W.matrix * (V.matrix * B * Matrix.conjTranspose V.matrix) *
        Matrix.conjTranspose W.matrix) x.1 y.1
  rw [Matrix.conjTranspose_mul]
  simp [Matrix.mul_assoc]

/-- The reference isometry induced by an equivalence is simultaneous matrix
reindexing on the reference register. -/
theorem referenceIsometry_ofEquiv_applyMatrix_eq_submatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (E : α ≃ β) (X : CMatrix (Prod α γ)) :
    (ReferenceIsometry.ofEquiv E).applyMatrix X =
      X.submatrix
        (Equiv.prodCongr E.symm (Equiv.refl γ))
        (Equiv.prodCongr E.symm (Equiv.refl γ)) := by
  ext x y
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    ReferenceIsometry.ofEquiv, Matrix.mul_apply, Matrix.conjTranspose]
  rw [Finset.sum_eq_single (E.symm y.1)]
  · rw [Finset.sum_eq_single (E.symm x.1)]
    · simp [Prod.map]
    · intro z _ hz
      have hxz : x.1 ≠ E z := by
        intro hxz
        exact hz (by simp [hxz])
      simp [hxz]
    · intro hz
      exact False.elim (hz (Finset.mem_univ _))
  · intro z _ hz
    have hyz : y.1 ≠ E z := by
      intro hyz
      exact hz (by simp [hyz])
    simp [hyz]
  · intro hz
    exact False.elim (hz (Finset.mem_univ _))

/-- The reference isometry induced by an equivalence is onto its target. -/
theorem referenceIsometry_ofEquiv_mul_conjTranspose
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : α ≃ β) :
    (ReferenceIsometry.ofEquiv E).matrix *
        Matrix.conjTranspose (ReferenceIsometry.ofEquiv E).matrix =
      (1 : CMatrix β) := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (E.symm i)]
    · simp [ReferenceIsometry.ofEquiv, Matrix.conjTranspose]
    · intro x _ hx
      have hne : i ≠ E x := by
        intro h
        exact hx (by simp [h])
      simp [ReferenceIsometry.ofEquiv, Matrix.conjTranspose, hne]
    · intro h
      exact False.elim (h (Finset.mem_univ (E.symm i)))
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro x _
      by_cases hi : i = E x
      · have hj : j ≠ E x := by
          intro hj
          exact hij (hi.trans hj.symm)
        simp [ReferenceIsometry.ofEquiv, Matrix.conjTranspose, hi, hj]
      · simp [ReferenceIsometry.ofEquiv, Matrix.conjTranspose, hi]

/-- A product-index finite sum with a delta on the right coordinate collapses
to the fixed right-coordinate slice. -/
theorem fqsw_sum_prod_right_eq
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : α → β → ζ) :
    (∑ x : Prod α β, if b0 = x.2 then f x.1 x.2 else 0) =
      ∑ a : α, f a b0 := by
  rw [Fintype.sum_prod_type]
  simp

/-- A product-index finite sum with the symmetric delta orientation on the
right coordinate collapses to the fixed right-coordinate slice. -/
theorem fqsw_sum_prod_right_eq'
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : α → β → ζ) :
    (∑ x : Prod α β, if x.2 = b0 then f x.1 x.2 else 0) =
      ∑ a : α, f a b0 := by
  rw [Fintype.sum_prod_type]
  simp

/-- Pair-valued variant of `fqsw_sum_prod_right_eq`. -/
theorem fqsw_sum_prod_right_eq_pair
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : Prod α β → ζ) :
    (∑ x : Prod α β, if b0 = x.2 then f x else 0) =
      ∑ a : α, f (a, b0) := by
  rw [Fintype.sum_prod_type]
  simp

/-- Pair-valued variant of `fqsw_sum_prod_right_eq'`. -/
theorem fqsw_sum_prod_right_eq_pair'
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : Prod α β → ζ) :
    (∑ x : Prod α β, if x.2 = b0 then f x else 0) =
      ∑ a : α, f (a, b0) := by
  rw [Fintype.sum_prod_type]
  simp

/-- Applying a reference isometry to the left factor of a bipartite matrix is
conjugation by `V ⊗ I` on the product register. -/
theorem referenceIsometry_applyMatrix_eq_kronecker_one_conj
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (V : ReferenceIsometry α β) (X : CMatrix (Prod α γ)) :
    V.applyMatrix X =
      (Matrix.kronecker V.matrix (1 : CMatrix γ)) * X *
        Matrix.conjTranspose (Matrix.kronecker V.matrix (1 : CMatrix γ)) := by
  ext x y
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.one_apply,
    Finset.sum_mul, mul_assoc]
  rw [fqsw_sum_prod_right_eq_pair' (b0 := y.2)]
  apply Finset.sum_congr rfl
  intro i _
  rw [fqsw_sum_prod_right_eq_pair (b0 := x.2)]

theorem fqsw_partialTraceB_partialTraceA_qer_reindex
    {q : Type x} {e : Type y} {r : Type w}
    [Fintype q] [Fintype e] [Fintype r]
    (M : CMatrix (Prod (Prod q e) r)) :
    partialTraceB (a := e) (b := r)
      (partialTraceA (a := q) (b := Prod e r)
        (M.submatrix (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)) =
      partialTraceA (a := q) (b := e)
        (partialTraceB (a := Prod q e) (b := r) M) := by
  ext i j
  simp [partialTraceA, partialTraceB, fqswQERToA2REquiv]
  rw [Finset.sum_comm]

/-- Tracing out `q` after regrouping `(q × e) × r` as `q × (e × r)`
turns a product matrix into the product of the `q`-trace and the untouched
`r` matrix. -/
theorem fqsw_partialTraceA_qer_kronecker
    {q : Type x} {e : Type y} {r : Type w}
    [Fintype q] [Fintype e] [Fintype r]
    (A : CMatrix (Prod q e)) (R : CMatrix r) :
    partialTraceA (a := q) (b := Prod e r)
      ((Matrix.kronecker A R).submatrix
        (fqswQERToA2REquiv q e r).symm
        (fqswQERToA2REquiv q e r).symm) =
      Matrix.kronecker (partialTraceA (a := q) (b := e) A) R := by
  ext i j
  simp [partialTraceA, fqswQERToA2REquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- `Tr_A` is compatible with matrix subtraction. -/
theorem fqsw_partialTraceA_sub
    {α : Type u} {β : Type v} [Fintype α]
    (X Y : CMatrix (Prod α β)) :
    partialTraceA (a := α) (b := β) (X - Y) =
      partialTraceA (a := α) (b := β) X -
        partialTraceA (a := α) (b := β) Y := by
  ext i j
  simp [partialTraceA, Finset.sum_sub_distrib]

/-- Matrix trace is invariant under simultaneous finite equivalence
reindexing. -/
theorem fqsw_trace_submatrix_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι ≃ κ) (M : CMatrix κ) :
    (M.submatrix E E).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  exact Fintype.sum_equiv E (fun i => M (E i) (E i)) (fun k => M k k) (fun _ => rfl)

/-- Hermiticity is invariant under simultaneous finite equivalence
reindexing. -/
theorem fqsw_isHermitian_submatrix_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι ≃ κ)
    {M : CMatrix κ} (hM : M.IsHermitian) :
    (M.submatrix E E).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simpa [Matrix.conjTranspose] using hM.apply (E i) (E j)

/-- Simultaneous finite equivalence reindexing commutes with matrix
multiplication. -/
theorem fqsw_mul_submatrix_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι ≃ κ)
    (M N : CMatrix κ) :
    (M.submatrix E E) * (N.submatrix E E) =
      (M * N).submatrix E E := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv E
    (fun k : ι => M (E i) (E k) * N (E k) (E j))
    (fun k : κ => M (E i) k * N k (E j))
    (fun _ => rfl)

/-- For Hermitian matrices the Hilbert--Schmidt square is `Tr[M²]`. -/
theorem fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian
    {α : Type*} [Fintype α] [DecidableEq α] (M : CMatrix α)
    (hM : M.IsHermitian) :
    hilbertSchmidtSq M = (M * M).trace.re := by
  unfold hilbertSchmidtSq
  rw [Matrix.star_eq_conjTranspose, hM.eq]

/-- Hilbert--Schmidt square of a Kronecker product factors. -/
theorem fqsw_hilbertSchmidtSq_kronecker
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : CMatrix α) (N : CMatrix β) :
    hilbertSchmidtSq (Matrix.kronecker M N) =
      hilbertSchmidtSq M * hilbertSchmidtSq N := by
  unfold hilbertSchmidtSq
  change ((Matrix.conjTranspose (Matrix.kronecker M N) *
        Matrix.kronecker M N).trace).re =
      ((Matrix.conjTranspose M * M).trace).re *
        ((Matrix.conjTranspose N * N).trace).re
  have hct :
      Matrix.conjTranspose (Matrix.kronecker M N) =
        Matrix.kronecker (Matrix.conjTranspose M) (Matrix.conjTranspose N) := by
    simpa [Matrix.kronecker] using Matrix.conjTranspose_kronecker M N
  have hmul :
      Matrix.kronecker (Matrix.conjTranspose M) (Matrix.conjTranspose N) *
          Matrix.kronecker M N =
        Matrix.kronecker (Matrix.conjTranspose M * M) (Matrix.conjTranspose N * N) := by
    simpa [Matrix.kronecker] using
      (Matrix.mul_kronecker_mul (Matrix.conjTranspose M) M
        (Matrix.conjTranspose N) N).symm
  rw [hct, hmul]
  have htrace :
      (Matrix.kronecker (Matrix.conjTranspose M * M)
          (Matrix.conjTranspose N * N)).trace =
        (Matrix.conjTranspose M * M).trace *
          (Matrix.conjTranspose N * N).trace := by
    simpa [Matrix.kronecker] using
      Matrix.trace_kronecker (Matrix.conjTranspose M * M)
        (Matrix.conjTranspose N * N)
  rw [htrace]
  have hM_im :
      ((Matrix.conjTranspose M * M).trace).im = 0 := by
    exact (Matrix.PosSemidef.trace_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self M)).2.symm
  have hN_im :
      ((Matrix.conjTranspose N * N).trace).im = 0 := by
    exact (Matrix.PosSemidef.trace_nonneg
      (Matrix.posSemidef_conjTranspose_mul_self N)).2.symm
  simp [Complex.mul_re, hM_im, hN_im]

/-- Hilbert--Schmidt square is invariant under finite equivalence reindexing. -/
theorem fqsw_hilbertSchmidtSq_submatrix_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (E : α ≃ β) (M : CMatrix α) :
    hilbertSchmidtSq (M.submatrix E.symm E.symm) = hilbertSchmidtSq M := by
  unfold hilbertSchmidtSq
  congr 1
  simp only [Matrix.trace]
  calc
    (∑ i : β, ∑ k : β, star (M (E.symm k) (E.symm i)) * M (E.symm k) (E.symm i)) =
        ∑ i : α, ∑ k : β, star (M (E.symm k) i) * M (E.symm k) i := by
          exact Fintype.sum_equiv E.symm
            (fun i : β => ∑ k : β,
              star (M (E.symm k) (E.symm i)) * M (E.symm k) (E.symm i))
            (fun i : α => ∑ k : β, star (M (E.symm k) i) * M (E.symm k) i)
            (by intro i; simp)
    _ = ∑ i : α, ∑ k : α, star (M k i) * M k i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Fintype.sum_equiv E.symm
            (fun k : β => star (M (E.symm k) i) * M (E.symm k) i)
            (fun k : α => star (M k i) * M k i)
            (by intro k; simp)

/-- Two-copy Kronecker commutes with matrix adjoint. -/
theorem fqsw_tensorPowerKroneckerTwo_star
    {α : Type*} [Fintype α] [DecidableEq α] (M : CMatrix α) :
    tensorPowerKroneckerTwo (a := α) (star M) =
      star (tensorPowerKroneckerTwo (a := α) M) := by
  ext x y
  simp [tensorPowerKroneckerTwo, Matrix.star_apply]

/-- On two copies, the tensor-power unitary matrix is the explicit Kronecker
square used by the FQSW second-moment calculation. -/
theorem fqsw_unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) :
    (unitaryTensorPowerMatrix U 2 : CMatrix (TensorPower α 2)) =
      tensorPowerKroneckerTwo (a := α) (U : CMatrix α) := by
  ext x y
  rw [unitaryTensorPowerMatrix_apply_eq_fin_prod]
  simp [tensorPowerKroneckerTwo]

omit [Nonempty e] in
/-- Operational/source bridge for the ADHW max-mixed calculation: the `A₂`
marginal produced by the split-unitary FQSW definitions is the partial trace
of the split source `A` marginal after conjugating by the Haar unitary. -/
theorem adhwFQSWSigmaA2StateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_A
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix =
      partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split *
          star (U : CMatrix (Prod q e))) := by
  rw [adhwFQSWSigmaA2StateOfIsometry]
  rw [State.marginalA_matrix]
  rw [adhwFQSWSigmaA2RStateOfIsometry_matrix_eq_partialTraceA_applyMatrix_AR]
  rw [fqsw_partialTraceB_partialTraceA_qer_reindex]
  rw [referenceIsometry_partialTraceB_applyMatrix]
  congr 1
  have hsplit :
      (adhwFQSWAliceIsometryOfSplitUnitary split U).matrix *
          partialTraceB (a := a) (b := r) (adhwFQSWARState ψ).matrix *
          Matrix.conjTranspose (adhwFQSWAliceIsometryOfSplitUnitary split U).matrix =
        (U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split *
          star (U : CMatrix (Prod q e)) := by
    ext i j
    simp [adhwFQSWAliceIsometryOfSplitUnitary, adhwFQSWAliceIsometryOfSplit,
      ReferenceIsometry.comp, ReferenceUnitary.toReferenceIsometry,
      ReferenceIsometry.ofEquiv, adhwFQSWASplitMatrix, State.marginalA,
      partialTraceB, Matrix.mul_apply, Matrix.conjTranspose,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    change
      (∑ x : a, ∑ y : a, ∑ rr : r,
        (U : CMatrix (Prod q e)) i (split y) *
          ((adhwFQSWARState ψ).matrix (y, rr) (x, rr) *
            star ((U : CMatrix (Prod q e)) j (split x)))) =
        (∑ x : Prod q e, ∑ y : Prod q e, ∑ rr : r,
          (U : CMatrix (Prod q e)) i y *
            ((adhwFQSWARState ψ).matrix (split.symm y, rr) (split.symm x, rr) *
              star ((U : CMatrix (Prod q e)) j x)))
    calc
      (∑ x : a, ∑ y : a, ∑ rr : r,
        (U : CMatrix (Prod q e)) i (split y) *
          ((adhwFQSWARState ψ).matrix (y, rr) (x, rr) *
            star ((U : CMatrix (Prod q e)) j (split x)))) =
        ∑ x : Prod q e, ∑ y : a, ∑ rr : r,
          (U : CMatrix (Prod q e)) i (split y) *
            ((adhwFQSWARState ψ).matrix (y, rr) (split.symm x, rr) *
              star ((U : CMatrix (Prod q e)) j x)) := by
          exact Fintype.sum_equiv split
            (fun x : a => ∑ y : a, ∑ rr : r,
              (U : CMatrix (Prod q e)) i (split y) *
                ((adhwFQSWARState ψ).matrix (y, rr) (x, rr) *
                  star ((U : CMatrix (Prod q e)) j (split x))))
            (fun x : Prod q e => ∑ y : a, ∑ rr : r,
              (U : CMatrix (Prod q e)) i (split y) *
                ((adhwFQSWARState ψ).matrix (y, rr) (split.symm x, rr) *
                  star ((U : CMatrix (Prod q e)) j x)))
            (by intro x; simp)
      _ = ∑ x : Prod q e, ∑ y : Prod q e, ∑ rr : r,
          (U : CMatrix (Prod q e)) i y *
            ((adhwFQSWARState ψ).matrix (split.symm y, rr) (split.symm x, rr) *
              star ((U : CMatrix (Prod q e)) j x)) := by
          apply Finset.sum_congr rfl
          intro x _
          refine Fintype.sum_equiv split
            (fun y : a => ∑ rr : r,
              (U : CMatrix (Prod q e)) i (split y) *
                ((adhwFQSWARState ψ).matrix (y, rr) (split.symm x, rr) *
                  star ((U : CMatrix (Prod q e)) j x)))
            (fun y : Prod q e => ∑ rr : r,
              (U : CMatrix (Prod q e)) i y *
                ((adhwFQSWARState ψ).matrix (split.symm y, rr) (split.symm x, rr) *
                  star ((U : CMatrix (Prod q e)) j x)))
            ?_
          intro y
          simp
  exact hsplit

omit [Nonempty e] in
/-- Applying the split-unitary Alice isometry to the source `AR` matrix is the
same as conjugating the split source matrix by `U ⊗ I_R`. -/
theorem adhwFQSWAliceIsometryOfSplitUnitary_applyMatrix_AR_eq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (adhwFQSWAliceIsometryOfSplitUnitary split U).applyMatrix
        (adhwFQSWARState ψ).matrix =
      (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
        adhwFQSWARSplitMatrix ψ split *
        star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) := by
  unfold adhwFQSWAliceIsometryOfSplitUnitary adhwFQSWAliceIsometryOfSplit
  rw [referenceIsometry_comp_applyMatrix]
  have hsplit :
      (ReferenceIsometry.ofEquiv split).applyMatrix (adhwFQSWARState ψ).matrix =
        adhwFQSWARSplitMatrix ψ split := by
    rw [referenceIsometry_ofEquiv_applyMatrix_eq_submatrix]
    ext x y
    rfl
  rw [hsplit]
  rw [referenceIsometry_applyMatrix_eq_kronecker_one_conj]
  simp [ReferenceUnitary.toReferenceIsometry, Matrix.star_eq_conjTranspose]

omit [Nonempty e] in
/-- Operational/source bridge for the ADHW product calculation: the `A₂R`
marginal produced by a split-unitary Alice isometry is the `q` partial trace of
the split source `AR` matrix after conjugating Alice's split register by the
Haar unitary. -/
theorem adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_AR_split
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix =
      partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            adhwFQSWARSplitMatrix ψ split *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) := by
  rw [adhwFQSWSigmaA2RStateOfIsometry_matrix_eq_partialTraceA_applyMatrix_AR]
  rw [adhwFQSWAliceIsometryOfSplitUnitary_applyMatrix_AR_eq]

omit [Nonempty e] in
/-- The product term `σ^{A₂}(U) ⊗ σ^R` is the same `q` partial trace applied
to the conjugated split product matrix `ψ^A ⊗ ψ^R`. -/
theorem adhwFQSWProductA2RStateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_ARProduct
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (State.prod
      (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U))
      (adhwFQSWSigmaRState ψ)).matrix =
      partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            adhwFQSWARProductSplitMatrix ψ split *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) := by
  let ρA : CMatrix (Prod q e) := adhwFQSWASplitMatrix ψ split
  let ρR : CMatrix r := (adhwFQSWSigmaRState ψ).matrix
  have hconj :
      (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
          adhwFQSWARProductSplitMatrix ψ split *
          star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) =
        Matrix.kronecker
          ((U : CMatrix (Prod q e)) * ρA * star (U : CMatrix (Prod q e)))
          ρR := by
    unfold adhwFQSWARProductSplitMatrix ρA ρR
    rw [Matrix.star_eq_conjTranspose]
    have hct :
        Matrix.conjTranspose
            (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) =
          Matrix.kronecker
            (Matrix.conjTranspose (U : CMatrix (Prod q e)))
            (Matrix.conjTranspose (1 : CMatrix r)) := by
      simpa [Matrix.kronecker] using
        Matrix.conjTranspose_kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
    rw [hct, Matrix.conjTranspose_one]
    have hmul_left :
        Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r) *
            Matrix.kronecker (adhwFQSWASplitMatrix ψ split)
              (adhwFQSWSigmaRState ψ).matrix =
          Matrix.kronecker
            ((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split)
            ((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).matrix) := by
      simpa [Matrix.kronecker] using
        (Matrix.mul_kronecker_mul (U : CMatrix (Prod q e))
          (adhwFQSWASplitMatrix ψ split) (1 : CMatrix r)
          (adhwFQSWSigmaRState ψ).matrix).symm
    rw [hmul_left]
    have hmul_right :
        Matrix.kronecker
            ((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split)
            ((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).matrix) *
          Matrix.kronecker (Matrix.conjTranspose (U : CMatrix (Prod q e)))
            (1 : CMatrix r) =
        Matrix.kronecker
          (((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split) *
            Matrix.conjTranspose (U : CMatrix (Prod q e)))
          (((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).matrix) *
            (1 : CMatrix r)) := by
      simpa [Matrix.kronecker] using
        (Matrix.mul_kronecker_mul
          ((U : CMatrix (Prod q e)) * adhwFQSWASplitMatrix ψ split)
          (Matrix.conjTranspose (U : CMatrix (Prod q e)))
          ((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).matrix)
          (1 : CMatrix r)).symm
    rw [hmul_right]
    simp [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  calc
    (State.prod
      (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U))
      (adhwFQSWSigmaRState ψ)).matrix =
        Matrix.kronecker
          (partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρA * star (U : CMatrix (Prod q e))))
          ρR := by
          simp [State.prod, ρA, ρR,
            adhwFQSWSigmaA2StateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_A]
    _ = partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            adhwFQSWARProductSplitMatrix ψ split *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) := by
          rw [hconj]
          rw [fqsw_partialTraceA_qer_kronecker]

/-- The lifted max-mixed product term
`||σ^{A₂}(U) ⊗ σ^R - I^{A₂}/d_{A₂} ⊗ σ^R||₁` appearing between
the triangle-inequality step and the product-with-state contraction in ADHW
fqsw.tex lines 806-815. -/
def adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) : ℝ :=
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  traceNormDistance
    (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
      (adhwFQSWSigmaRState ψ)).matrix)
    (((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)).matrix)

/-- Raw triangle-inequality form of ADHW fqsw.tex lines 806-810.  This leaves
the product-with-`σ^R` contraction as a separate subsequent lemma. -/
theorem adhwFQSWDecouplingTraceNormIntegrand_le_product_add_liftedMaxMixed
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ≤
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U +
        adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  let ρ : CMatrix (Prod e r) :=
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).matrix
  let σ : CMatrix (Prod e r) :=
    ((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
      (adhwFQSWSigmaRState ψ)).matrix
  let τ : CMatrix (Prod e r) :=
    ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)).matrix
  have htri := normalizedTraceDistance_triangle ρ σ τ
  unfold normalizedTraceDistance traceNormDistance at htri
  have h :
      traceNorm (ρ - τ) ≤ traceNorm (ρ - σ) + traceNorm (σ - τ) := by
    nlinarith
  simpa [adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary,
    adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary,
    adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary,
    ρ, σ, τ, alice, traceNormDistance] using h

/-- Tensoring both `A₂` states with the same `R` state cannot increase the
source trace-norm distance.  This is the ADHW step that turns the lifted
max-mixed comparison into the marginal `A₂` comparison. -/
theorem adhwFQSWLiftedMaxMixedA2TraceNormIntegrand_le_maxMixedA2
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ≤
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  have h := fqswProdRight_traceNormDistance_le
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice)
    (adhwFQSWMaximallyMixedA2State e)
    (adhwFQSWSigmaRState ψ)
  simpa [adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary,
    adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary, alice] using h

/-- Source-shaped pointwise ADHW triangle comparison: the final decoupling
integrand is bounded by the product-decoupling term plus the `A₂` max-mixed
term. -/
theorem adhwFQSWDecouplingTraceNormIntegrand_le_product_add_maxMixed
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ≤
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U +
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  have htri :=
    adhwFQSWDecouplingTraceNormIntegrand_le_product_add_liftedMaxMixed ψ split U
  have hlift :=
    adhwFQSWLiftedMaxMixedA2TraceNormIntegrand_le_maxMixedA2 ψ split U
  linarith

/-- The normalized-distance version of the FQSW split-unitary decoupling
condition is exactly half the source trace-norm integrand. -/
theorem adhwFQSWDecoupling_normalizedTraceDistance_eq_half_integrand
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).normalizedTraceDistance
      ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) =
        (1 / 2 : ℝ) *
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U :=
  rfl

/-- Partial trace over the left tensor factor is continuous as a matrix-valued
finite sum. -/
@[fun_prop]
theorem partialTraceA_continuous_matrix
    {α : Type*} {β : Type*} [Fintype α] [Fintype β] :
    Continuous (fun M : CMatrix (Prod α β) => partialTraceA (a := α) (b := β) M) := by
  refine continuous_pi ?_
  intro j
  refine continuous_pi ?_
  intro j'
  simp only [partialTraceA]
  refine continuous_finsetSum Finset.univ ?_
  intro i _
  exact (continuous_apply (i, j')).comp (continuous_apply (i, j))

/-- Partial trace over the right tensor factor is continuous as a matrix-valued
finite sum. -/
@[fun_prop]
theorem partialTraceB_continuous_matrix
    {α : Type*} {β : Type*} [Fintype α] [Fintype β] :
    Continuous (fun M : CMatrix (Prod α β) => partialTraceB (a := α) (b := β) M) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro i'
  simp only [partialTraceB]
  refine continuous_finsetSum Finset.univ ?_
  intro j _
  exact (continuous_apply (i', j)).comp (continuous_apply (i, j))

/-- The Hilbert--Schmidt square is continuous on finite-dimensional complex
matrices. -/
theorem hilbertSchmidtSq_continuous_matrix
    {α : Type*} [Fintype α] [DecidableEq α] :
    Continuous (fun M : CMatrix α => hilbertSchmidtSq M) := by
  unfold hilbertSchmidtSq
  exact Complex.continuous_re.comp
    (Continuous.matrix_trace ((Continuous.star continuous_id).matrix_mul continuous_id))

/-- Hermitian Hilbert--Schmidt expansion used by ADHW fqsw.tex
Eq. `HSexpand`: `||X - M||₂² = Tr[X²] - 2 Tr[XM] + ||M||₂²`. -/
theorem fqsw_hilbertSchmidtSq_sub_of_isHermitian
    {α : Type*} [Fintype α] [DecidableEq α]
    (X M : CMatrix α) (hX : X.IsHermitian) (hM : M.IsHermitian) :
    hilbertSchmidtSq (X - M) =
      (X * X).trace.re - (2 : ℝ) * (X * M).trace.re + hilbertSchmidtSq M := by
  unfold hilbertSchmidtSq
  simp only [Matrix.star_eq_conjTranspose]
  rw [Matrix.conjTranspose_sub]
  rw [hX.eq, hM.eq]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [Matrix.trace_sub]
  rw [Matrix.trace_sub]
  rw [Matrix.trace_sub]
  have hcomm : (M * X).trace = (X * M).trace := Matrix.trace_mul_comm M X
  rw [hcomm]
  simp [Complex.sub_re]
  ring

/-- Two-copy Kronecker of the identity is the identity, in the recursive
`TensorPower` coordinates used by the Schur/twirl API. -/
theorem fqsw_tensorPowerKroneckerTwo_one
    {α : Type*} [Fintype α] [DecidableEq α] :
    tensorPowerKroneckerTwo (a := α) (1 : CMatrix α) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensorPowerKroneckerTwo]
  · have hcoord :
        tensorPowerEquiv (a := α) 2 x 0 ≠ tensorPowerEquiv (a := α) 2 y 0 ∨
          tensorPowerEquiv (a := α) 2 x 1 ≠ tensorPowerEquiv (a := α) 2 y 1 := by
      by_contra h
      push Not at h
      apply hxy
      apply (tensorPowerEquiv (a := α) 2).injective
      funext i
      fin_cases i <;> simp [h]
    rcases hcoord with h0 | h1
    · simp [tensorPowerKroneckerTwo, Matrix.one_apply, h0, hxy]
    · by_cases h0 :
        tensorPowerEquiv (a := α) 2 x 0 = tensorPowerEquiv (a := α) 2 y 0
      · simp [tensorPowerKroneckerTwo, Matrix.one_apply, h0, h1, hxy]
      · simp [tensorPowerKroneckerTwo, Matrix.one_apply, h0, hxy]

private theorem fqsw_tensorPowerProdEquiv_fst_apply
    {α : Type*} {β : Type*} [Fintype β] [DecidableEq β]
    (n : ℕ) (z : TensorPower (Prod α β) n) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerProdEquiv α β n z).1) i =
      (tensorPowerEquiv n z i).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simp [tensorPowerProdEquiv, tensorPowerEquiv]
              exact ih tail i

private theorem fqsw_tensorPowerProdEquiv_snd_apply
    {α : Type*} {β : Type*} [Fintype β] [DecidableEq β]
    (n : ℕ) (z : TensorPower (Prod α β) n) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerProdEquiv α β n z).2) i =
      (tensorPowerEquiv n z i).2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simp [tensorPowerProdEquiv, tensorPowerEquiv]
              exact ih tail i

/-- Two-copy Kronecker for an operator acting only on the left side of a
product register. -/
private theorem fqsw_tensorPowerKroneckerTwo_kronecker_one_tensorPower
    {α : Type*} {β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : CMatrix α) :
    tensorPowerKroneckerTwo (a := Prod α β) (Matrix.kronecker A (1 : CMatrix β)) =
      twoCopySideOperator (a := α) (e := β) (tensorPowerKroneckerTwo (a := α) A)
        (tensorPowerKroneckerTwo (a := β) (1 : CMatrix β)) := by
  ext x y
  simp [twoCopySideOperator, twoCopyProdReindex, Matrix.kronecker,
    tensorPowerKroneckerTwo, fqsw_tensorPowerProdEquiv_fst_apply]
  rw [fqsw_tensorPowerProdEquiv_snd_apply (α := α) (β := β) 2 x 0,
    fqsw_tensorPowerProdEquiv_snd_apply (α := α) (β := β) 2 y 0,
    fqsw_tensorPowerProdEquiv_snd_apply (α := α) (β := β) 2 x 1,
    fqsw_tensorPowerProdEquiv_snd_apply (α := α) (β := β) 2 y 1]
  ring

/-- Two-copy Kronecker for `A ⊗ I`, with the identity tensor power simplified. -/
private theorem fqsw_tensorPowerKroneckerTwo_kronecker_one
    {α : Type*} {β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : CMatrix α) :
    tensorPowerKroneckerTwo (a := Prod α β) (Matrix.kronecker A (1 : CMatrix β)) =
      twoCopySideOperator (a := α) (e := β) (tensorPowerKroneckerTwo (a := α) A)
        (1 : CMatrix (TensorPower β 2)) := by
  rw [fqsw_tensorPowerKroneckerTwo_kronecker_one_tensorPower,
    fqsw_tensorPowerKroneckerTwo_one]

/-- Enumerate a two-copy tensor power by its first and second tensor words. -/
private theorem fqsw_sum_tensorPower_twoCopyTensorWord
    {α : Type*} [Fintype α] {β : Type*} [AddCommMonoid β]
    (f : TensorPower α 2 → β) :
    (∑ x : TensorPower α 2, f x) =
      ∑ i : α, ∑ j : α, f (twoCopyTensorWord (a := α) i j) := by
  let E : (α × α) ≃ TensorPower α 2 :=
  { toFun p := twoCopyTensorWord (a := α) p.1 p.2
    invFun x :=
      (tensorPowerEquiv (a := α) 2 x 0, tensorPowerEquiv (a := α) 2 x 1)
    left_inv := by
      intro p
      ext <;> simp
    right_inv := by
      intro x
      exact (twoCopyTensorWord_coords (a := α) x).symm }
  calc
    (∑ x : TensorPower α 2, f x) =
        ∑ p : α × α, f (E p) := by
          exact (Fintype.sum_equiv E
            (fun p : α × α => f (E p))
            (fun x : TensorPower α 2 => f x)
            (fun _ => rfl)).symm
    _ = ∑ i : α, ∑ j : α, f (twoCopyTensorWord (a := α) i j) := by
          rw [Fintype.sum_prod_type]
          rfl

private theorem fqsw_partialTraceA_flip_entry_sum
    {α : Type*} {β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (ρ : CMatrix (Prod α β))
    (i j : α) (k l : β) :
    (∑ x : α, ∑ x_1 : β, ∑ x_2 : α, ∑ x_3 : β,
      if x_3 = k ∧ x_1 = l then
        if x = i ∧ x_2 = j then
          ρ (i, k) (x, x_1) * ρ (j, l) (x_2, x_3)
        else 0
      else 0) =
      ρ (i, k) (i, l) * ρ (j, l) (j, k) := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single l]
    · rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single k]
        · simp
        · intro x _ hx
          simp [hx]
        · intro h
          exact False.elim (h (Finset.mem_univ k))
      · intro x _ hx
        simp [hx]
      · intro h
        exact False.elim (h (Finset.mem_univ j))
    · intro x _ hx
      simp [hx]
    · intro h
      exact False.elim (h (Finset.mem_univ l))
  · intro x _ hx
    simp [hx]
  · intro h
    exact False.elim (h (Finset.mem_univ i))

private theorem fqsw_partialTraceA_flip_entry_sum_prod
    {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (ρ : CMatrix (Prod α (Prod β γ)))
    (i j : α) (k l : β) (s t : γ) :
    (∑ x : α, ∑ x_1 : β, ∑ x_2 : γ, ∑ x_3 : α, ∑ x_4 : β, ∑ x_5 : γ,
      if (x_4 = k ∧ x_5 = s) ∧ x_1 = l ∧ x_2 = t then
        if x = i ∧ x_3 = j then
          ρ (i, (k, s)) (x, (x_1, x_2)) *
            ρ (j, (l, t)) (x_3, (x_4, x_5))
        else 0
      else 0) =
      ρ (i, (k, s)) (i, (l, t)) * ρ (j, (l, t)) (j, (k, s)) := by
  simpa [Fintype.sum_prod_type, and_assoc] using
    fqsw_partialTraceA_flip_entry_sum
      (α := α) (β := Prod β γ) ρ i j (k, s) (l, t)

private theorem fqsw_nested_split_flip_entry_sum
    {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (ρ : CMatrix (Prod (Prod α β) γ))
    (i j : α) (k l : β) (s t : γ) :
    (∑ x : α, ∑ x_1 : β, ∑ x_2 : γ, ∑ x_3 : α, ∑ x_4 : β, ∑ x_5 : γ,
      if x_5 = s ∧ x_2 = t then
        if x_4 = k ∧ x_1 = l then
          if x = i ∧ x_3 = j then
            ρ ((i, k), s) ((x, x_1), x_2) *
              ρ ((j, l), t) ((x_3, x_4), x_5)
          else 0
        else 0
      else 0) =
      ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s) := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single l]
    · rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single j]
        · rw [Finset.sum_eq_single k]
          · rw [Finset.sum_eq_single s]
            · simp
            · intro x _ hx
              simp [hx]
            · intro h
              exact False.elim (h (Finset.mem_univ s))
          · intro x _ hx
            simp [hx]
          · intro h
            exact False.elim (h (Finset.mem_univ k))
        · intro x _ hx
          simp [hx]
        · intro h
          exact False.elim (h (Finset.mem_univ j))
      · intro x _ hx
        simp [hx]
      · intro h
        exact False.elim (h (Finset.mem_univ t))
    · intro x _ hx
      simp [hx]
    · intro h
      exact False.elim (h (Finset.mem_univ l))
  · intro x _ hx
    simp [hx]
  · intro h
    exact False.elim (h (Finset.mem_univ i))

/-- Tracing out the left factor of the identity on `q × e` gives
`|q| I_e`. -/
theorem fqsw_partialTraceA_one_prod
    {q : Type x} {e : Type y} [Fintype q] [DecidableEq q] [DecidableEq e] :
    partialTraceA (a := q) (b := e) (1 : CMatrix (Prod q e)) =
      ((Fintype.card q : ℂ) • (1 : CMatrix e)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTraceA]
  · simp [partialTraceA, hij]

/-- Tracing out the right factor of the identity on `q × e` gives
`|e| I_q`. -/
theorem fqsw_partialTraceB_one_prod
    {q : Type x} {e : Type y} [Fintype e] [DecidableEq q] [DecidableEq e] :
    partialTraceB (a := q) (b := e) (1 : CMatrix (Prod q e)) =
      ((Fintype.card e : ℂ) • (1 : CMatrix q)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTraceB]
  · simp [partialTraceB, hij]

/-- Source trace term
`Tr(I^{A₁A₁'} ⊗ F^{A₂}) = d_{A₁}² d_{A₂}` from ADHW fqsw.tex
lines 656-666. -/
theorem fqsw_twoCopySideOperator_one_swap_trace
    {q : Type x} {e : Type y} [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] :
    (twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))).trace =
    ((Fintype.card q : ℂ) * (Fintype.card q : ℂ) * (Fintype.card e : ℂ)) := by
  have h := tensorPowerKroneckerTwo_prod_mul_one_swap_trace
    (a := q) (e := e) (rho := (1 : CMatrix (Prod q e)))
  rw [fqsw_tensorPowerKroneckerTwo_one, Matrix.one_mul] at h
  rw [h]
  rw [fqsw_partialTraceA_one_prod]
  simp [Matrix.trace_smul, Matrix.trace_one]
  ring

/-- Source trace term
`Tr(F^{A₁} ⊗ I^{A₂A₂'}) = d_{A₁} d_{A₂}²` from ADHW fqsw.tex
lines 656-666. -/
theorem fqsw_twoCopySideOperator_swap_one_trace
    {q : Type x} {e : Type y} [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] :
    (twoCopySideOperator (a := q) (e := e)
      (tensorPowerSwapMatrix_two (a := q))
      (1 : CMatrix (TensorPower e 2))).trace =
    ((Fintype.card q : ℂ) * (Fintype.card e : ℂ) * (Fintype.card e : ℂ)) := by
  have h := tensorPowerKroneckerTwo_prod_mul_swap_one_trace
    (a := q) (e := e) (rho := (1 : CMatrix (Prod q e)))
  rw [fqsw_tensorPowerKroneckerTwo_one, Matrix.one_mul] at h
  rw [h]
  rw [fqsw_partialTraceB_one_prod]
  simp [Matrix.trace_smul, Matrix.trace_one]
  ring

/-- Matrix entries of the finite-dimensional unitary group are continuous. -/
@[fun_prop, continuity]
theorem unitaryGroup_entry_continuous
    {α : Type*} [Fintype α] [DecidableEq α] (i j : α) :
    Continuous fun U : Matrix.unitaryGroup α ℂ => (U : CMatrix α) i j :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

omit [Nonempty e] in
/-- The ADHW decoupling marginal `σ^{A₂R}(U)` is continuous as a matrix-valued
function of the Haar unitary. -/
theorem adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix := by
  refine continuous_matrix ?_
  intro x y
  unfold adhwFQSWSigmaA2RStateOfIsometry
    adhwFQSWPostAliceStateOfIsometry
    adhwFQSWAliceIsometryOfSplitUnitary
    adhwFQSWAliceIsometryOfSplit
    ReferenceIsometry.comp
    ReferenceUnitary.toReferenceIsometry
    ReferenceIsometry.ofEquiv
    ReferenceIsometry.applyPureVector
    ReferenceIsometry.applyAmp
    PureVector.state
    State.reindex
    State.marginalB
    partialTraceA
    rankOneMatrix
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mulVec,
    Matrix.vecMulVec_apply, dotProduct]
  continuity

omit [Nonempty e] in
/-- The ADHW marginal `σ^{A₂}(U)` is continuous as a matrix-valued function of
the Haar unitary. -/
theorem adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix := by
  unfold adhwFQSWSigmaA2StateOfIsometry State.marginalA
  exact partialTraceB_continuous_matrix.comp
    (adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split)

/-- The FQSW split-unitary decoupling integrand is continuous in the Haar
unitary. -/
theorem adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U := by
  unfold adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary traceNormDistance
  exact traceNorm_continuous.comp
    ((adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split).sub continuous_const)

/-- The FQSW split-unitary decoupling integrand is Haar-integrable. -/
theorem adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (unitaryHaarMeasure (a := Prod q e)) :=
  (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_continuous ψ split).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The squared FQSW split-unitary decoupling integrand is Haar-integrable. -/
theorem adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2)
      (unitaryHaarMeasure (a := Prod q e)) :=
  ((adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_continuous ψ split).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [Nonempty e] in
/-- The product-decoupling ADHW integrand is continuous in the Haar unitary. -/
theorem adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U := by
  have hsigmaA2R := adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split
  have hprod : Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).prod
          (adhwFQSWSigmaRState ψ)).matrix) := by
    have hsigmaA2 := adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split
    refine continuous_matrix ?_
    intro i j
    simp [State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply]
    continuity
  unfold adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary traceNormDistance
  exact traceNorm_continuous.comp (hsigmaA2R.sub hprod)

/-- The squared product-decoupling ADHW integrand is Haar-integrable. -/
theorem adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2)
      (unitaryHaarMeasure (a := Prod q e)) :=
  ((adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_continuous ψ split).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The max-mixed `A₂` ADHW integrand is continuous in the Haar unitary. -/
theorem adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  unfold adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary traceNormDistance
  exact traceNorm_continuous.comp
    ((adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split).sub continuous_const)

/-- The squared max-mixed `A₂` ADHW integrand is Haar-integrable. -/
theorem adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_sq_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2)
      (unitaryHaarMeasure (a := Prod q e)) :=
  ((adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_continuous ψ split).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [Nonempty e] in
/-- The product-decoupling Hilbert--Schmidt integrand is continuous in the
Haar unitary. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  have hsigmaA2R := adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split
  have hprod : Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).prod
          (adhwFQSWSigmaRState ψ)).matrix) := by
    have hsigmaA2 := adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split
    refine continuous_matrix ?_
    intro i j
    simp [State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply]
    continuity
  unfold adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary
  exact hilbertSchmidtSq_continuous_matrix.comp (hsigmaA2R.sub hprod)

/-- The max-mixed `A₂` Hilbert--Schmidt integrand is continuous in the Haar
unitary. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_continuous
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    Continuous fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  unfold adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary
  exact hilbertSchmidtSq_continuous_matrix.comp
    ((adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split).sub continuous_const)

/-- The product-decoupling Hilbert--Schmidt integrand is Haar-integrable. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U)
      (unitaryHaarMeasure (a := Prod q e)) :=
  (adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_continuous ψ split).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The max-mixed `A₂` Hilbert--Schmidt integrand is Haar-integrable. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_integrable
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U)
      (unitaryHaarMeasure (a := Prod q e)) :=
  (adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_continuous ψ split).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [Nonempty e] in
/-- ADHW fqsw.tex lines 751-754: pointwise Cauchy--Schwarz bridge from the
product-decoupling trace norm to the Hilbert--Schmidt square on `A₂R`. -/
theorem adhwFQSWProductDecouplingTraceNormSq_le_card_mul_hilbertSchmidt
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
      ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  let Δ : CMatrix (Prod e r) :=
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).matrix -
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
        (adhwFQSWSigmaRState ψ)).matrix)
  have h := traceNorm_sq_le_card_mul_hilbertSchmidtSq Δ
  simpa [adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary,
    adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary,
    traceNormDistance, Δ, alice, Fintype.card_prod] using h

/-- ADHW fqsw.tex lines 776-780: pointwise Cauchy--Schwarz bridge from the
max-mixed `A₂` trace norm to the Hilbert--Schmidt square on `A₂`. -/
theorem adhwFQSWMaxMixedA2TraceNormSq_le_card_mul_hilbertSchmidt
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
      (Fintype.card e : ℝ) *
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  let Δ : CMatrix e :=
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).matrix -
      (adhwFQSWMaximallyMixedA2State e).matrix
  have h := traceNorm_sq_le_card_mul_hilbertSchmidtSq Δ
  simpa [adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary,
    adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary,
    traceNormDistance, Δ] using h

/-- Integral form of the ADHW product-decoupling Cauchy--Schwarz tail.  The
remaining source-route task is the exact Hilbert--Schmidt average of
fqsw.tex lines 682-747. -/
theorem adhwFQSWProductDecouplingTraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) := by
  have hpoint : ∀ᵐ U : Matrix.unitaryGroup (Prod q e) ℂ
      ∂unitaryHaarMeasure (a := Prod q e),
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
        ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
    filter_upwards with U
    exact adhwFQSWProductDecouplingTraceNormSq_le_card_mul_hilbertSchmidt ψ split U
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      ∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e) :=
        MeasureTheory.integral_mono_ae
          (adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
          ((adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_integrable
            ψ split).const_mul ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)))
          hpoint
    _ = ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) := by
          rw [MeasureTheory.integral_const_mul]

/-- Integral form of the ADHW max-mixed `A₂` Cauchy--Schwarz tail.  The
remaining source-route task is the exact one-copy `A₂` Hilbert--Schmidt
average from fqsw.tex lines 781-787. -/
theorem adhwFQSWMaxMixedA2TraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) := by
  have hpoint : ∀ᵐ U : Matrix.unitaryGroup (Prod q e) ℂ
      ∂unitaryHaarMeasure (a := Prod q e),
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
        (Fintype.card e : ℝ) *
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
    filter_upwards with U
    exact adhwFQSWMaxMixedA2TraceNormSq_le_card_mul_hilbertSchmidt ψ split U
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      ∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        (Fintype.card e : ℝ) *
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e) :=
        MeasureTheory.integral_mono_ae
          (adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
          ((adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_integrable
            ψ split).const_mul (Fintype.card e : ℝ))
          hpoint
    _ = (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) := by
          rw [MeasureTheory.integral_const_mul]

/-- ADHW fqsw.tex lines 806-815: after the pointwise triangle-inequality
comparison has related the final decoupling integrand to the product-decoupling
and max-mixed integrands, the averaged square is bounded by twice the two
component averaged squares.  The upstream source-route tasks are the pointwise
trace-norm comparison and the two Schur/HS average estimates. -/
theorem adhwFQSWCombinedTraceNormAverageSq_le_two_component_averages
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      2 * (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) +
      2 * (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) := by
  exact integral_sq_le_two_add_two_of_ae_le_add
    (μ := unitaryHaarMeasure (a := Prod q e))
    (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
    (g := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
    (h := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U)
    (by
      filter_upwards with U
      exact traceNormDistance_nonneg _ _)
    (by
      filter_upwards with U
      exact traceNormDistance_nonneg _ _)
    (by
      filter_upwards with U
      exact traceNormDistance_nonneg _ _)
    (by
      filter_upwards with U
      exact adhwFQSWDecouplingTraceNormIntegrand_le_product_add_maxMixed ψ split U)
    (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
    (adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
    (adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)

/-- Finite-sum factorization used by the FQSW product-purification
calculation. -/
theorem fqsw_sum_sum_sum_mul_right
    {ι : Type u} {κ : Type v} {lam : Type w} [Fintype ι] [Fintype κ] [Fintype lam]
    (f : ι → κ → ℂ) (g : lam → ℂ) :
    (∑ i : ι, ∑ j : κ, ∑ k : lam, f i j * g k) =
      (∑ k : lam, g k) * (∑ i : ι, ∑ j : κ, f i j) := by
  calc
    (∑ i : ι, ∑ j : κ, ∑ k : lam, f i j * g k) =
        ∑ i : ι, ∑ j : κ, f i j * (∑ k : lam, g k) := by
      simp [Finset.mul_sum]
    _ = (∑ i : ι, ∑ j : κ, f i j) * (∑ k : lam, g k) := by
      simp [Finset.sum_mul]
    _ = (∑ k : lam, g k) * (∑ i : ι, ∑ j : κ, f i j) := by
      ring

/-- Trace distance is invariant under simultaneous finite reindexing. -/
theorem fqsw_traceNormDistance_submatrix_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (E : α ≃ β) (M N : CMatrix α) :
    traceNormDistance (M.submatrix E.symm E.symm) (N.submatrix E.symm E.symm) =
      traceNormDistance M N := by
  rw [traceNormDistance, traceNormDistance]
  have hsub :
      M.submatrix E.symm E.symm - N.submatrix E.symm E.symm =
        (M - N).submatrix E.symm E.symm := by
    ext i j
    rfl
  rw [hsub]
  exact traceNorm_submatrix_equiv E.symm (M - N)

namespace State

/-- Normalized trace distance is invariant under state reindexing. -/
theorem normalizedTraceDistance_reindex_equiv
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ρ σ : State α) (E : α ≃ β) :
    (ρ.reindex E).normalizedTraceDistance (σ.reindex E) =
      ρ.normalizedTraceDistance σ := by
  change (1 / 2 : ℝ) *
      QIT.traceNormDistance (ρ.matrix.submatrix E.symm E.symm) (σ.matrix.submatrix E.symm E.symm) =
    (1 / 2 : ℝ) * QIT.traceNormDistance ρ.matrix σ.matrix
  rw [fqsw_traceNormDistance_submatrix_equiv E ρ.matrix σ.matrix]

end State

/-- Regroup the ideal FQSW target
`ψ^{R\widehat B} ⊗ Φ^{A₂\widetilde B}` as a purification of the decoupling
target on `A₂R`, with `\widehat B\widetilde B` as the reference. -/
def fqswIdealTargetToA2RPurificationEquiv
    (a : Type u) (b : Type v) (r : Type w) (e : Type y) (et : Type z) :
    Prod (Prod (Prod a b) r) (Prod e et) ≃
      Prod (Prod (Prod a b) et) (Prod e r) where
  toFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
  invFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- The ideal ADHW target, regrouped as a purification of
`I^{A₂}/d_{A₂} ⊗ σ^R`. -/
def adhwFQSWIdealA2RPurification
    (ψ : PureVector (Prod (Prod a b) r)) (pairing : e ≃ et) :
    PureVector (Prod (Prod (Prod a b) et) (Prod e r)) :=
  (ψ.prod (PureVector.maximallyEntangled pairing)).reindex
    (fqswIdealTargetToA2RPurificationEquiv a b r e et)

/-- The ideal ADHW target purifies the decoupling target
`I^{A₂}/d_{A₂} ⊗ σ^R`. -/
theorem adhwFQSWIdealA2RPurification_purifies
    (ψ : PureVector (Prod (Prod a b) r)) (pairing : e ≃ et) :
    (adhwFQSWIdealA2RPurification ψ pairing).Purifies
      ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) := by
  rw [PureVector.purifies_iff]
  ext x y
  simp only [adhwFQSWIdealA2RPurification, fqswIdealTargetToA2RPurificationEquiv,
    PureVector.reindex_state, PureVector.prod_state, State.reindex,
    State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply, partialTraceA,
    adhwFQSWMaximallyMixedA2State,
    adhwFQSWSigmaRState_eq_source_marginalB, State.marginalB,
    Fintype.sum_prod_type]
  have hebit :
      (∑ k : et,
        (PureVector.maximallyEntangled pairing).amp (x.1, k) *
          (starRingEnd ℂ) ((PureVector.maximallyEntangled pairing).amp (y.1, k))) =
        (State.maximallyMixed e).matrix x.1 y.1 := by
    have h := congrArg (fun ρ : State e => ρ.matrix x.1 y.1)
      (PureVector.maximallyEntangled_marginalA pairing)
    simpa [State.marginalA, partialTraceB, PureVector.state, rankOneMatrix_apply] using h
  exact
    (fqsw_sum_sum_sum_mul_right
      (fun i : a => fun j : b =>
        ψ.amp ((i, j), x.2) * (starRingEnd ℂ) (ψ.amp ((i, j), y.2)))
      (fun k : et =>
        (PureVector.maximallyEntangled pairing).amp (x.1, k) *
          (starRingEnd ℂ) ((PureVector.maximallyEntangled pairing).amp (y.1, k)))).trans
      (by rw [hebit]; simp [PureVector.state, rankOneMatrix_apply])

/-- Reindexing the computed FQSW output into `A₂R` purification order is the
same pure vector as applying Bob's isometry to the post-Alice purification. -/
theorem fqsw_outputPureVector_reindex_a2r_eq_apply_postAlice
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e))
    (V : ReferenceIsometry (Prod q b) (Prod (Prod a b) et))
    (pairing : e ≃ et) :
    (({ aliceIsometry := U, bobIsometry := V, ebitPairing := pairing } :
        FQSWOneShotProtocol ψ q e et).outputPureVector.reindex
          (fqswIdealTargetToA2RPurificationEquiv a b r e et)) =
      V.applyPureVector
        (adhwFQSWPostAliceA2RPurificationOfIsometry (q := q) (e := e) ψ U) := by
  apply PureVector.ext_amp
  funext x
  simp [FQSWOneShotProtocol.outputPureVector,
    adhwFQSWPostAliceA2RPurificationOfIsometry,
    fqswSourceToAliceInputEquiv, fqswAliceOutputToBobInputEquiv,
    fqswAliceOutputToA2REquiv, fqswBobOutputToFinalEquiv,
    fqswIdealTargetToA2RPurificationEquiv, ReferenceIsometry.applyPureVector,
    ReferenceIsometry.applyAmp, Matrix.mulVec]

/-- Uhlmann assembly for the ADHW one-shot route: a concrete Alice isometry
whose `A₂R` decoupling marginal is close to `I^{A₂}/d_{A₂} ⊗ σ^R` supplies a
computed FQSW one-shot protocol with the corresponding source trace-norm
error bound. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_decoupling
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) (pairing : e ≃ et) (η : ℝ)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) et))
    (hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤ η) :
    ∃ C : FQSWOneShotProtocol ψ q e et,
      C.traceNormError ≤ 2 * Real.sqrt (2 * η) := by
  let post := adhwFQSWPostAliceA2RPurificationOfIsometry (q := q) (e := e) ψ U
  let ideal := adhwFQSWIdealA2RPurification ψ pairing
  let targetState : State (Prod e r) :=
    (adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)
  have hpost : post.Purifies
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U) := by
    simpa [post] using
      (adhwFQSWPostAliceA2RPurificationOfIsometry_purifies
        (q := q) (e := e) ψ U)
  have hideal : ideal.Purifies targetState := by
    simpa [ideal, targetState] using
      (adhwFQSWIdealA2RPurification_purifies ψ pairing)
  obtain ⟨V, hV⟩ :=
    PureVector.exists_referenceIsometry_applyPureVector_normalizedTraceDistance_le_sqrt_two_mul_normalizedTraceDistance
      hpost hideal hcardTarget hcardRef
  let C : FQSWOneShotProtocol ψ q e et :=
    { aliceIsometry := U, bobIsometry := V, ebitPairing := pairing }
  refine ⟨C, ?_⟩
  have hVη :
      (V.applyPureVector post).state.normalizedTraceDistance ideal.state ≤
        Real.sqrt (2 * η) := by
    refine le_trans hV ?_
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdec (by norm_num))
  let E := fqswIdealTargetToA2RPurificationEquiv a b r e et
  have hpure :
      C.outputPureVector.reindex E = V.applyPureVector post := by
    simpa [C, post, E] using
      (fqsw_outputPureVector_reindex_a2r_eq_apply_postAlice ψ U V pairing)
  have hout :
      C.outputState.reindex E = (V.applyPureVector post).state := by
    change C.outputPureVector.state.reindex E = (V.applyPureVector post).state
    exact (PureVector.reindex_state C.outputPureVector E).symm.trans
      (congrArg PureVector.state hpure)
  have htarget :
      C.targetState.reindex E = ideal.state := by
    calc
      C.targetState.reindex E =
          (ψ.state.prod (State.maximallyEntangled pairing)).reindex E := by
        simp [C, FQSWOneShotProtocol.targetState]
      _ = (ψ.state.prod (PureVector.maximallyEntangled pairing).state).reindex E := by
        rfl
      _ = (ψ.prod (PureVector.maximallyEntangled pairing)).state.reindex E := by
        rw [PureVector.prod_state]
      _ = ((ψ.prod (PureVector.maximallyEntangled pairing)).reindex E).state := by
        exact (PureVector.reindex_state (ψ.prod (PureVector.maximallyEntangled pairing)) E).symm
      _ = ideal.state := by
        simp [ideal, E, adhwFQSWIdealA2RPurification]
  have hnorm_eq :
      C.normalizedError =
        (V.applyPureVector post).state.normalizedTraceDistance ideal.state := by
    rw [FQSWOneShotProtocol.normalizedError]
    rw [← State.normalizedTraceDistance_reindex_equiv C.outputState C.targetState E]
    rw [hout, htarget]
  have hnorm_le : C.normalizedError ≤ Real.sqrt (2 * η) := by
    rw [hnorm_eq]
    exact hVη
  have hhalf := C.normalizedError_eq_half_traceNormError
  have htrace_nonneg := C.traceNormError_nonneg
  nlinarith

/-- Purity `Tr[(ψ^{AR})^2]` in the notation of ADHW fqsw.tex lines 580-841. -/
def adhwFQSWARPurity (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  hilbertSchmidtSq ((adhwFQSWARState ψ).matrix)

/-- For a Hermitian PSD matrix, the Hilbert--Schmidt square is its PSD
power trace at `p = 2`. -/
private theorem fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (M : CMatrix α) (hM : M.PosSemidef) :
    hilbertSchmidtSq M = psdTracePower M hM (2 : ℝ) := by
  unfold hilbertSchmidtSq
  rw [psdTracePower_two]
  have hstar : star M = M := by
    simpa [Matrix.star_eq_conjTranspose] using hM.isHermitian.eq
  rw [hstar]

/-- Rectangular reference isometries preserve Hilbert--Schmidt purity under
PSD conjugation. -/
theorem referenceIsometry_hilbertSchmidtSq_conj
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (V : ReferenceIsometry α β) (ρ : State α) :
    hilbertSchmidtSq (V.matrix * ρ.matrix * Matrix.conjTranspose V.matrix) =
      hilbertSchmidtSq ρ.matrix := by
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    (V.matrix * ρ.matrix * Matrix.conjTranspose V.matrix)
    (ρ.pos.mul_mul_conjTranspose_same V.matrix)]
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two ρ.matrix ρ.pos]
  exact psdTracePower_isometry_conj V.matrix ρ.pos V.isometry
    (by norm_num : (0 : ℝ) < 2)

/-- The ADHW `AR` purity equals the complementary source `B` purity.  This is
the pure-state Hilbert--Schmidt bridge used to identify the line-1158 source
purity term in ADHW's i.i.d. proof. -/
theorem adhwFQSWARPurity_eq_systemBPurity
    (ψ : PureVector (Prod (Prod a b) r)) :
    adhwFQSWARPurity ψ =
      hilbertSchmidtSq ψ.state.marginalA.marginalB.matrix := by
  let Ω : PureVector (Prod (Prod a r) b) :=
    ψ.reindex (fqswSourceToARBEquiv a b r)
  have hΩA : Ω.state.marginalA = adhwFQSWARState ψ := by
    apply State.ext
    ext i j
    simp [Ω, adhwFQSWARState, State.coherentTransferReferenceState,
      fqswSourceToARBEquiv, PureVector.reindex_state, State.reindex,
      State.marginalA, partialTraceB, PureVector.state_matrix, rankOneMatrix_apply]
  have hΩB : Ω.state.marginalB = ψ.state.marginalA.marginalB := by
    apply State.ext
    ext i j
    simp [Ω, fqswSourceToARBEquiv, PureVector.reindex_state, State.reindex,
      State.marginalB, State.marginalA, partialTraceA, partialTraceB,
      PureVector.state_matrix, rankOneMatrix_apply, Fintype.sum_prod_type]
  have hdual :=
    PureVector.psdTracePower_marginalA_eq_marginalB
      (Ψ := Ω) (p := (2 : ℝ)) (by norm_num)
  rw [adhwFQSWARPurity]
  rw [← hΩA, ← hΩB]
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    Ω.state.marginalA.matrix Ω.state.marginalA.pos]
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    Ω.state.marginalB.matrix Ω.state.marginalB.pos]
  simpa [PureVector.state, State.marginalA, State.marginalB] using hdual

/-- Purity `Tr[(ψ^A)^2]` in the notation of ADHW fqsw.tex lines 580-841. -/
def adhwFQSWAPurity (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  hilbertSchmidtSq ((adhwFQSWARState ψ).marginalA.matrix)

/-- Purity `Tr[(ψ^R)^2]` in the notation of ADHW fqsw.tex lines 580-841. -/
def adhwFQSWRPurity (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  hilbertSchmidtSq ((adhwFQSWARState ψ).marginalB.matrix)

/-- The overlap `Tr[ψ^{AR}(ψ^A ⊗ ψ^R)]` appearing in the exact
Hilbert--Schmidt calculation of ADHW fqsw.tex lines 682-747. -/
def adhwFQSWARProductOverlap (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  ((adhwFQSWARState ψ).matrix *
      ((adhwFQSWARState ψ).marginalA.prod (adhwFQSWARState ψ).marginalB).matrix).trace.re

/-- The overlap term
`Tr[ψ^{AR}(ψ^A ⊗ ψ^R)]` in ADHW fqsw.tex lines 682-747 is nonnegative:
both factors are positive semidefinite states. -/
theorem adhwFQSWARProductOverlap_nonneg
    (ψ : PureVector (Prod (Prod a b) r)) :
    0 ≤ adhwFQSWARProductOverlap ψ := by
  unfold adhwFQSWARProductOverlap
  exact cMatrix_trace_mul_posSemidef_re_nonneg
    (adhwFQSWARState ψ).pos
    (((adhwFQSWARState ψ).marginalA).prod
      ((adhwFQSWARState ψ).marginalB)).pos

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
/-- The split `A` marginal still has trace one. -/
theorem adhwFQSWASplitMatrix_trace
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (adhwFQSWASplitMatrix ψ split).trace = 1 := by
  unfold adhwFQSWASplitMatrix
  rw [fqsw_trace_submatrix_equiv split.symm]
  exact (adhwFQSWARState ψ).marginalA.trace_eq_one

omit [Nonempty e] in
/-- The split `A` marginal has the same purity as the source `A` marginal. -/
theorem adhwFQSWASplitMatrix_hilbertSchmidtSq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    hilbertSchmidtSq (adhwFQSWASplitMatrix ψ split) = adhwFQSWAPurity ψ := by
  unfold adhwFQSWASplitMatrix adhwFQSWAPurity
  rw [fqsw_hilbertSchmidtSq_submatrix_equiv split]

omit [Nonempty e] in
/-- The split `AR` matrix has the same purity as the source `AR` marginal. -/
theorem adhwFQSWARSplitMatrix_hilbertSchmidtSq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    hilbertSchmidtSq (adhwFQSWARSplitMatrix ψ split) = adhwFQSWARPurity ψ := by
  unfold adhwFQSWARSplitMatrix adhwFQSWARPurity
  rw [fqsw_hilbertSchmidtSq_submatrix_equiv (fqswARSplitEquiv split)]

omit [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] [Nonempty e] in
/-- The split product matrix is the source product state reindexed by the
ADHW split on Alice's register. -/
theorem adhwFQSWARProductSplitMatrix_eq_source_product_submatrix
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    adhwFQSWARProductSplitMatrix ψ split =
      (((adhwFQSWARState ψ).marginalA.prod
        (adhwFQSWARState ψ).marginalB).matrix).submatrix
        (fqswARSplitEquiv split).symm (fqswARSplitEquiv split).symm := by
  ext x y
  simp [adhwFQSWARProductSplitMatrix, adhwFQSWASplitMatrix,
    adhwFQSWSigmaRState, State.prod, fqswARSplitEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply]

omit [Nonempty e] in
/-- The split product matrix has Hilbert--Schmidt square
`Tr[(ψ^A)^2] Tr[(ψ^R)^2]`. -/
theorem adhwFQSWARProductSplitMatrix_hilbertSchmidtSq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    hilbertSchmidtSq (adhwFQSWARProductSplitMatrix ψ split) =
      adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
  unfold adhwFQSWARProductSplitMatrix adhwFQSWRPurity adhwFQSWSigmaRState
  rw [fqsw_hilbertSchmidtSq_kronecker]
  rw [adhwFQSWASplitMatrix_hilbertSchmidtSq]

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
/-- The split overlap is the source overlap
`Tr[ψ^{AR}(ψ^A ⊗ ψ^R)]`. -/
theorem adhwFQSWARProductSplitMatrix_overlap
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (adhwFQSWARSplitMatrix ψ split *
        adhwFQSWARProductSplitMatrix ψ split).trace.re =
      adhwFQSWARProductOverlap ψ := by
  let E : Prod (Prod q e) r ≃ Prod a r :=
    (fqswARSplitEquiv (r := r) split).symm
  have hprod :=
    adhwFQSWARProductSplitMatrix_eq_source_product_submatrix ψ split
  unfold adhwFQSWARProductOverlap adhwFQSWARSplitMatrix
  rw [hprod]
  change (((adhwFQSWARState ψ).matrix.submatrix E E *
        (((adhwFQSWARState ψ).marginalA.prod
          (adhwFQSWARState ψ).marginalB).matrix).submatrix E E).trace).re =
    (((adhwFQSWARState ψ).matrix *
      ((adhwFQSWARState ψ).marginalA.prod
        (adhwFQSWARState ψ).marginalB).matrix).trace).re
  rw [fqsw_mul_submatrix_equiv E]
  rw [fqsw_trace_submatrix_equiv E]

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
/-- Tracing the split `AR` source matrix over `A₁A₂` recovers the fixed
reference marginal `σ^R`. -/
theorem adhwFQSWARSplitMatrix_partialTraceA
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    partialTraceA (a := Prod q e) (b := r)
        (adhwFQSWARSplitMatrix ψ split) =
      (adhwFQSWSigmaRState ψ).matrix := by
  ext i j
  unfold adhwFQSWARSplitMatrix adhwFQSWSigmaRState
  change
    (∑ x : Prod q e,
      (adhwFQSWARState ψ).matrix (split.symm x, i) (split.symm x, j)) =
    ∑ y : a, (adhwFQSWARState ψ).matrix (y, i) (y, j)
  exact Fintype.sum_equiv split.symm
    (fun x : Prod q e =>
      (adhwFQSWARState ψ).matrix (split.symm x, i) (split.symm x, j))
    (fun y : a => (adhwFQSWARState ψ).matrix (y, i) (y, j))
    (fun _ => rfl)

omit [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] [Nonempty e] in
/-- Tracing the split `AR` source matrix over `R` recovers the split
`A₁A₂` source marginal. -/
theorem adhwFQSWARSplitMatrix_partialTraceB
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    partialTraceB (a := Prod q e) (b := r)
        (adhwFQSWARSplitMatrix ψ split) =
      adhwFQSWASplitMatrix ψ split := by
  ext i j
  unfold adhwFQSWARSplitMatrix adhwFQSWASplitMatrix
  rw [State.marginalA_matrix]
  rfl

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
/-- Tracing the split product matrix over `A₁A₂` also recovers the same
reference marginal `σ^R`. -/
theorem adhwFQSWARProductSplitMatrix_partialTraceA
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    partialTraceA (a := Prod q e) (b := r)
        (adhwFQSWARProductSplitMatrix ψ split) =
      (adhwFQSWSigmaRState ψ).matrix := by
  unfold adhwFQSWARProductSplitMatrix
  rw [partialTraceA_kronecker]
  rw [adhwFQSWASplitMatrix_trace]
  exact matrixScale_one (adhwFQSWSigmaRState ψ).matrix

omit [Nonempty e] in
/-- If the split Alice system `A₁ × A₂` is a one-point system, the source
correlation matrix `ψ^{AR} - ψ^A ⊗ ψ^R` is zero. -/
theorem adhwFQSWARCorrelationSplitMatrix_eq_zero_of_subsingleton
    [Subsingleton (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    adhwFQSWARSplitMatrix ψ split -
      adhwFQSWARProductSplitMatrix ψ split = 0 := by
  apply sub_eq_zero.mpr
  let ρsplit : State (Prod (Prod q e) r) :=
    (adhwFQSWARState ψ).reindex (fqswARSplitEquiv split)
  have hprod := state_matrix_eq_prod_marginals_of_subsingleton_left ρsplit
  have hρmatrix : ρsplit.matrix = adhwFQSWARSplitMatrix ψ split := by
    rfl
  have hAmatrix : ρsplit.marginalA.matrix = adhwFQSWASplitMatrix ψ split := by
    rw [State.marginalA_matrix]
    change partialTraceB (a := Prod q e) (b := r)
        (adhwFQSWARSplitMatrix ψ split) =
      adhwFQSWASplitMatrix ψ split
    exact adhwFQSWARSplitMatrix_partialTraceB ψ split
  have hBmatrix : ρsplit.marginalB.matrix = (adhwFQSWSigmaRState ψ).matrix := by
    rw [State.marginalB_matrix]
    change partialTraceA (a := Prod q e) (b := r)
        (adhwFQSWARSplitMatrix ψ split) =
      (adhwFQSWSigmaRState ψ).matrix
    exact adhwFQSWARSplitMatrix_partialTraceA ψ split
  calc
    adhwFQSWARSplitMatrix ψ split = ρsplit.matrix := hρmatrix.symm
    _ = (ρsplit.marginalA.prod ρsplit.marginalB).matrix := hprod
    _ = adhwFQSWARProductSplitMatrix ψ split := by
      ext x y
      simp [State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply,
        adhwFQSWARProductSplitMatrix]
      rw [← State.marginalA_matrix ρsplit, hAmatrix]
      rw [← State.marginalB_matrix ρsplit, hBmatrix]

omit [Nonempty e] in
/-- Source ADHW correlation matrix
`ψ^{AR} - ψ^A ⊗ ψ^R`, reindexed by the split, has the source Hilbert--Schmidt
expansion from fqsw.tex lines 682-747. -/
theorem adhwFQSWARCorrelationSplitMatrix_hilbertSchmidtSq
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    hilbertSchmidtSq
      (adhwFQSWARSplitMatrix ψ split -
        adhwFQSWARProductSplitMatrix ψ split) =
      adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
        adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
  let Rm : CMatrix (Prod (Prod q e) r) := adhwFQSWARSplitMatrix ψ split
  let Pm : CMatrix (Prod (Prod q e) r) := adhwFQSWARProductSplitMatrix ψ split
  have hRm_herm : Rm.IsHermitian := by
    unfold Rm adhwFQSWARSplitMatrix
    exact fqsw_isHermitian_submatrix_equiv (fqswARSplitEquiv split).symm
      (adhwFQSWARState ψ).pos.isHermitian
  have hPm_herm : Pm.IsHermitian := by
    unfold Pm adhwFQSWARProductSplitMatrix
    exact kronecker_isHermitian _ _
      (fqsw_isHermitian_submatrix_equiv split.symm
        (adhwFQSWARState ψ).marginalA.pos.isHermitian)
      (adhwFQSWSigmaRState ψ).pos.isHermitian
  have hRm_sq : (Rm * Rm).trace.re = adhwFQSWARPurity ψ := by
    calc
      (Rm * Rm).trace.re = hilbertSchmidtSq Rm := by
        exact (fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian Rm hRm_herm).symm
      _ = adhwFQSWARPurity ψ := by
        simpa [Rm] using adhwFQSWARSplitMatrix_hilbertSchmidtSq ψ split
  have hPm_sq : hilbertSchmidtSq Pm =
      adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
    simpa [Pm] using adhwFQSWARProductSplitMatrix_hilbertSchmidtSq ψ split
  have hOverlap : (Rm * Pm).trace.re = adhwFQSWARProductOverlap ψ := by
    simpa [Rm, Pm] using adhwFQSWARProductSplitMatrix_overlap ψ split
  rw [show adhwFQSWARSplitMatrix ψ split -
        adhwFQSWARProductSplitMatrix ψ split = Rm - Pm by rfl]
  rw [fqsw_hilbertSchmidtSq_sub_of_isHermitian Rm Pm hRm_herm hPm_herm]
  rw [hRm_sq, hPm_sq, hOverlap]

/-- Schur coefficient `p = (d_A1 + d_A2) / (d_A + 1)` from ADHW fqsw.tex
lines 642-678. -/
def adhwFQSWSchurPCoeff (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ℝ :=
  ((Fintype.card q : ℝ) + (Fintype.card e : ℝ)) /
    (((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) + 1)

/-- Schur coefficient `q = (d_A1 - d_A2) / (d_A - 1)` from ADHW fqsw.tex
lines 642-678. -/
def adhwFQSWSchurQCoeff (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ℝ :=
  ((Fintype.card q : ℝ) - (Fintype.card e : ℝ)) /
    (((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) - 1)

/-- Source Schur coefficient estimate:
`(p + q)/2 ≤ 1/d_{A₂}`. -/
theorem adhwFQSWSchur_half_sum_le_inv_card_e
    (q : Type x) (e : Type y) [Fintype q] [Fintype e]
    [Nonempty q] [Nonempty e] [Nontrivial (Prod q e)] :
    (adhwFQSWSchurPCoeff q e + adhwFQSWSchurQCoeff q e) / 2 ≤
      (1 : ℝ) / (Fintype.card e : ℝ) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hprod_gt : 1 < dq * de := by
    have hnat : 1 < Fintype.card q * Fintype.card e := by
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := Prod q e)
    dsimp [dq, de]
    exact_mod_cast hnat
  have hde_pos : 0 < de := lt_of_lt_of_le zero_lt_one hde_ge_one
  have hden_pos : 0 < (dq * de) ^ 2 - 1 := by nlinarith
  have hden_pos' : 0 < de ^ 2 * dq ^ 2 - 1 := by nlinarith
  have hden_ne_norm : -1 + dq ^ 2 * de ^ 2 ≠ 0 := by
    nlinarith
  unfold adhwFQSWSchurPCoeff adhwFQSWSchurQCoeff
  change ((dq + de) / (dq * de + 1) + (dq - de) / (dq * de - 1)) / 2 ≤ 1 / de
  have hsum :
      ((dq + de) / (dq * de + 1) + (dq - de) / (dq * de - 1)) / 2 =
        de * (dq ^ 2 - 1) / ((dq * de) ^ 2 - 1) := by
    field_simp [ne_of_gt (by nlinarith : (0 : ℝ) < dq * de + 1),
      ne_of_gt (by nlinarith : (0 : ℝ) < dq * de - 1),
      ne_of_gt hden_pos, ne_of_gt hden_pos', hden_ne_norm]
    ring_nf
    field_simp [hden_ne_norm]
    ring
  rw [hsum]
  field_simp [ne_of_gt hde_pos, ne_of_gt hden_pos, ne_of_gt hden_pos']
  nlinarith [sq_nonneg de]

/-- Source Schur coefficient estimate:
`(p - q)/2 ≤ 1/d_{A₁}`. -/
theorem adhwFQSWSchur_half_sub_le_inv_card_q
    (q : Type x) (e : Type y) [Fintype q] [Fintype e]
    [Nonempty q] [Nonempty e] [Nontrivial (Prod q e)] :
    (adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2 ≤
      (1 : ℝ) / (Fintype.card q : ℝ) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hprod_gt : 1 < dq * de := by
    have hnat : 1 < Fintype.card q * Fintype.card e := by
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := Prod q e)
    dsimp [dq, de]
    exact_mod_cast hnat
  have hdq_pos : 0 < dq := lt_of_lt_of_le zero_lt_one hdq_ge_one
  have hden_pos : 0 < (dq * de) ^ 2 - 1 := by nlinarith
  have hden_pos' : 0 < dq ^ 2 * de ^ 2 - 1 := by nlinarith
  have hden_ne_norm : -1 + dq ^ 2 * de ^ 2 ≠ 0 := by
    nlinarith
  unfold adhwFQSWSchurPCoeff adhwFQSWSchurQCoeff
  change ((dq + de) / (dq * de + 1) - (dq - de) / (dq * de - 1)) / 2 ≤ 1 / dq
  have hsub :
      ((dq + de) / (dq * de + 1) - (dq - de) / (dq * de - 1)) / 2 =
        dq * (de ^ 2 - 1) / ((dq * de) ^ 2 - 1) := by
    field_simp [ne_of_gt (by nlinarith : (0 : ℝ) < dq * de + 1),
      ne_of_gt (by nlinarith : (0 : ℝ) < dq * de - 1),
      ne_of_gt hden_pos, ne_of_gt hden_pos', hden_ne_norm]
    ring_nf
  rw [hsub]
  field_simp [ne_of_gt hdq_pos, ne_of_gt hden_pos, ne_of_gt hden_pos']
  nlinarith [sq_nonneg dq]

/-- In the nontrivial Schur case, the source coefficient `(p-q)/2` is exactly
the Hilbert--Schmidt prefactor appearing in ADHW fqsw.tex lines 722-747. -/
theorem adhwFQSWSchur_half_sub_eq_HS_prefactor
    (q : Type x) (e : Type y) [Fintype q] [Fintype e]
    [Nonempty q] [Nonempty e] [Nontrivial (Prod q e)] :
    (adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2 =
      ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ) ^ 2) -
          (Fintype.card q : ℝ)) /
        ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) ^ 2) - 1)) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hprod_gt : 1 < dq * de := by
    have hnat : 1 < Fintype.card q * Fintype.card e := by
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := Prod q e)
    dsimp [dq, de]
    exact_mod_cast hnat
  have hden_pos : 0 < (dq * de) ^ 2 - 1 := by nlinarith
  have hden_pos' : 0 < dq ^ 2 * de ^ 2 - 1 := by nlinarith
  have hden_ne_norm : -1 + dq ^ 2 * de ^ 2 ≠ 0 := by
    nlinarith
  unfold adhwFQSWSchurPCoeff adhwFQSWSchurQCoeff
  change ((dq + de) / (dq * de + 1) - (dq - de) / (dq * de - 1)) / 2 =
    (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1)
  field_simp [ne_of_gt (by nlinarith : (0 : ℝ) < dq * de + 1),
    ne_of_gt (by nlinarith : (0 : ℝ) < dq * de - 1),
    ne_of_gt hden_pos, ne_of_gt hden_pos', hden_ne_norm]
  ring_nf

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
private theorem fqsw_twoCopySideOperator_trace
    (G : CMatrix (TensorPower q 2)) (H : CMatrix (TensorPower e 2)) :
    (twoCopySideOperator (a := q) (e := e) G H).trace = G.trace * H.trace := by
  unfold twoCopySideOperator twoCopyProdReindex
  rw [fqsw_trace_submatrix_equiv (tensorPowerProdEquiv q e 2)]
  exact Matrix.trace_kronecker G H

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
private theorem fqsw_twoCopySideOperator_mul
    (G G' : CMatrix (TensorPower q 2)) (H H' : CMatrix (TensorPower e 2)) :
    twoCopySideOperator (a := q) (e := e) G H *
        twoCopySideOperator (a := q) (e := e) G' H' =
      twoCopySideOperator (a := q) (e := e) (G * G') (H * H') := by
  ext x y
  rw [← twoCopyTensorWord_coords (a := Prod q e) x,
    ← twoCopyTensorWord_coords (a := Prod q e) y]
  simp [twoCopySideOperator, twoCopyProdReindex, Matrix.mul_apply, Matrix.kronecker,
    Finset.mul_sum, Finset.sum_mul]
  let X := tensorPowerProdEquiv q e 2 x
  let Y := tensorPowerProdEquiv q e 2 y
  calc
    (∑ z : TensorPower (Prod q e) 2,
      G X.1 ((tensorPowerProdEquiv q e 2 z).1) *
          H X.2 ((tensorPowerProdEquiv q e 2 z).2) *
        (G' ((tensorPowerProdEquiv q e 2 z).1) Y.1 *
          H' ((tensorPowerProdEquiv q e 2 z).2) Y.2)) =
      ∑ p : TensorPower q 2 × TensorPower e 2,
        G X.1 p.1 * H X.2 p.2 * (G' p.1 Y.1 * H' p.2 Y.2) := by
        exact Fintype.sum_equiv (tensorPowerProdEquiv q e 2)
          (fun z : TensorPower (Prod q e) 2 =>
            G X.1 ((tensorPowerProdEquiv q e 2 z).1) *
                H X.2 ((tensorPowerProdEquiv q e 2 z).2) *
              (G' ((tensorPowerProdEquiv q e 2 z).1) Y.1 *
                H' ((tensorPowerProdEquiv q e 2 z).2) Y.2))
          (fun p : TensorPower q 2 × TensorPower e 2 =>
            G X.1 p.1 * H X.2 p.2 * (G' p.1 Y.1 * H' p.2 Y.2))
          (fun _ => rfl)
    _ = ∑ j : TensorPower e 2, ∑ i : TensorPower q 2,
        G X.1 i * G' i Y.1 * (H X.2 j * H' j Y.2) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        simp [mul_comm, mul_left_comm]

private theorem fqsw_tensorPowerSwapMatrix_two_trace
    {α : Type*} [Fintype α] [DecidableEq α] :
    (tensorPowerSwapMatrix_two (a := α)).trace = (Fintype.card α : ℂ) := by
  calc
    (tensorPowerSwapMatrix_two (a := α)).trace =
        ((1 : CMatrix (TensorPower α 2)) * tensorPowerSwapMatrix_two (a := α)).trace := by
          rw [Matrix.one_mul]
    _ = (tensorPowerKroneckerTwo (a := α) (1 : CMatrix α) *
          tensorPowerSwapMatrix_two (a := α)).trace := by
          rw [fqsw_tensorPowerKroneckerTwo_one]
    _ = (Fintype.card α : ℂ) := by
      have h :=
        tensorPowerKroneckerTwo_mul_tensorPowerSwapMatrix_two_trace
          (a := α) (1 : CMatrix α)
      simpa [Matrix.trace_one] using h

omit [Nonempty e] in
private theorem fqsw_splitObservable_trace :
    (twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))).trace =
      (Fintype.card q : ℂ) ^ 2 * (Fintype.card e : ℂ) := by
  rw [fqsw_twoCopySideOperator_trace]
  rw [Matrix.trace_one, fqsw_tensorPowerSwapMatrix_two_trace (α := e)]
  rw [tensorPower_card]
  rw [Nat.cast_pow]

omit [Nonempty e] in
private theorem fqsw_fullSwap_mul_splitObservable_trace [Nonempty q] :
    (tensorPowerSwapMatrix_two (a := Prod q e) *
      twoCopySideOperator (a := q) (e := e)
        (1 : CMatrix (TensorPower q 2))
        (tensorPowerSwapMatrix_two (a := e))).trace =
      (Fintype.card q : ℂ) * (Fintype.card e : ℂ) ^ 2 := by
  rw [tensorPowerSwapMatrix_two_prod_eq_twoCopySideOperator (a := q) (e := e)]
  rw [fqsw_twoCopySideOperator_mul]
  rw [Matrix.mul_one, tensorPowerSwapMatrix_two_sq]
  rw [fqsw_twoCopySideOperator_trace]
  rw [fqsw_tensorPowerSwapMatrix_two_trace (α := q), Matrix.trace_one]
  rw [tensorPower_card]
  rw [Nat.cast_pow]

/-- Trace of the split FQSW observable `I^{q q'} ⊗ F^e` against the symmetric
two-copy projection on `A = q × e`.  This is the numerator source formula
behind ADHW's Schur coefficient `p = (d_q + d_e) / (d_q d_e + 1)`. -/
theorem adhwFQSW_splitObservable_symmetricProjection_trace
    (q : Type x) (e : Type y) [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] :
    (symmetricProjectionMatrix (a := Prod q e) 2 *
      twoCopySideOperator (a := q) (e := e)
        (1 : CMatrix (TensorPower q 2))
        (tensorPowerSwapMatrix_two (a := e))).trace =
      ((Fintype.card q : ℂ) * (Fintype.card e : ℂ) *
        ((Fintype.card q : ℂ) + (Fintype.card e : ℂ))) / 2 := by
  rw [symmetricProjectionMatrix_two_eq_half_one_add_swap]
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_add]
  rw [fqsw_splitObservable_trace, fqsw_fullSwap_mul_splitObservable_trace]
  ring

/-- Trace of the split FQSW observable `I^{q q'} ⊗ F^e` against the
antisymmetric two-copy projection on `A = q × e`.  This is the numerator source
formula behind ADHW's Schur coefficient `q = (d_q - d_e) / (d_q d_e - 1)`. -/
theorem adhwFQSW_splitObservable_antisymmetricProjection_trace
    (q : Type x) (e : Type y) [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] :
    (antisymmetricProjectionMatrix_two (a := Prod q e) *
      twoCopySideOperator (a := q) (e := e)
        (1 : CMatrix (TensorPower q 2))
        (tensorPowerSwapMatrix_two (a := e))).trace =
      ((Fintype.card q : ℂ) * (Fintype.card e : ℂ) *
        ((Fintype.card q : ℂ) - (Fintype.card e : ℂ))) / 2 := by
  rw [antisymmetricProjectionMatrix_two]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  rw [fqsw_splitObservable_trace, adhwFQSW_splitObservable_symmetricProjection_trace]
  ring

/-- ADHW fqsw.tex lines 642-678: Schur twirling of the split observable
`I^{A₁A₁'} ⊗ F^{A₂}` on `A = A₁ × A₂`. -/
theorem adhwFQSW_splitObservable_unitaryTwirl_eq
    (q : Type x) (e : Type y) [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] [Nontrivial (Prod q e)] :
    unitaryTwirl 2
        (twoCopySideOperator (a := q) (e := e)
          (1 : CMatrix (TensorPower q 2))
          (tensorPowerSwapMatrix_two (a := e))) =
      ((adhwFQSWSchurPCoeff q e : ℂ) • symmetricProjectionMatrix (a := Prod q e) 2) +
        ((adhwFQSWSchurQCoeff q e : ℂ) •
          antisymmetricProjectionMatrix_two (a := Prod q e)) := by
  rw [unitaryTwirl_two_eq_symmetric_antisymmetric_trace_decomposition]
  rw [adhwFQSW_splitObservable_symmetricProjection_trace]
  rw [adhwFQSW_splitObservable_antisymmetricProjection_trace]
  rw [symmetricProjectionMatrix_two_trace]
  rw [antisymmetricProjectionMatrix_two_trace]
  have hqe_ne :
      ((Fintype.card q : ℂ) * (Fintype.card e : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero (α := q))
      (by exact_mod_cast Fintype.card_ne_zero (α := e))
  have hqe_add_ne :
      (Fintype.card q : ℂ) * (Fintype.card e : ℂ) + 1 ≠ 0 := by
    have hnat : Fintype.card q * Fintype.card e + 1 ≠ 0 :=
      Nat.succ_ne_zero (Fintype.card q * Fintype.card e)
    exact_mod_cast hnat
  have hqe_sub_ne :
      (Fintype.card q : ℂ) * (Fintype.card e : ℂ) - 1 ≠ 0 := by
    have hgt : 1 < Fintype.card q * Fintype.card e := by
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := Prod q e)
    have hne : Fintype.card q * Fintype.card e ≠ 1 := ne_of_gt hgt
    intro h
    apply hne
    have hcast : ((Fintype.card q * Fintype.card e : ℕ) : ℂ) = 1 := by
      simpa [sub_eq_zero, ← Nat.cast_mul] using h
    exact_mod_cast hcast
  simp [adhwFQSWSchurPCoeff, adhwFQSWSchurQCoeff, Fintype.card_prod]
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply]
  field_simp [hqe_ne, hqe_add_ne, hqe_sub_ne]

/-- Trace of a two-copy source operator against
`Π₊^A ⊗ F^R`, the symmetric half of ADHW fqsw.tex lines 708-714. -/
theorem fqsw_twoCopy_symmetricProjection_swap_trace
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ρ : CMatrix (Prod α β)) :
    (tensorPowerKroneckerTwo (a := Prod α β) ρ *
      twoCopySideOperator (a := α) (e := β)
        (symmetricProjectionMatrix (a := α) 2)
        (tensorPowerSwapMatrix_two (a := β))).trace =
      ((1 : ℂ) / 2) *
        ((partialTraceA (a := α) (b := β) ρ *
            partialTraceA (a := α) (b := β) ρ).trace +
          (ρ * ρ).trace) := by
  rw [symmetricProjectionMatrix_two_eq_half_one_add_swap]
  rw [twoCopySideOperator_smul_left]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [twoCopySideOperator_add_left]
  rw [Matrix.mul_add, Matrix.trace_add]
  rw [tensorPowerKroneckerTwo_prod_mul_one_swap_trace]
  rw [tensorPowerKroneckerTwo_prod_mul_full_swap_trace]
  ring

/-- Trace of a two-copy source operator against
`Π₋^A ⊗ F^R`, the antisymmetric half of ADHW fqsw.tex lines 708-714. -/
theorem fqsw_twoCopy_antisymmetricProjection_swap_trace
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ρ : CMatrix (Prod α β)) :
    (tensorPowerKroneckerTwo (a := Prod α β) ρ *
      twoCopySideOperator (a := α) (e := β)
        (antisymmetricProjectionMatrix_two (a := α))
        (tensorPowerSwapMatrix_two (a := β))).trace =
      ((1 : ℂ) / 2) *
        ((partialTraceA (a := α) (b := β) ρ *
            partialTraceA (a := α) (b := β) ρ).trace -
          (ρ * ρ).trace) := by
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  rw [twoCopySideOperator_smul_left]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [show twoCopySideOperator (a := α) (e := β)
        ((1 : CMatrix (TensorPower α 2)) - tensorPowerSwapMatrix_two (a := α))
        (tensorPowerSwapMatrix_two (a := β)) =
      twoCopySideOperator (a := α) (e := β)
        (1 : CMatrix (TensorPower α 2))
        (tensorPowerSwapMatrix_two (a := β)) -
      twoCopySideOperator (a := α) (e := β)
        (tensorPowerSwapMatrix_two (a := α))
        (tensorPowerSwapMatrix_two (a := β)) by
    rw [sub_eq_add_neg]
    rw [twoCopySideOperator_add_left]
    rw [show
        -tensorPowerSwapMatrix_two (a := α) =
          ((-1 : ℂ) • tensorPowerSwapMatrix_two (a := α)) by
      ext x y
      simp
      split_ifs <;> simp]
    rw [twoCopySideOperator_smul_left]
    simp [sub_eq_add_neg]]
  rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [tensorPowerKroneckerTwo_prod_mul_one_swap_trace]
  rw [tensorPowerKroneckerTwo_prod_mul_full_swap_trace]
  ring

private noncomputable def fqswTwoCopySideTraceCLM
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ρ : CMatrix (Prod α β)) (H : CMatrix (TensorPower β 2)) :
    CMatrix (TensorPower α 2) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun G =>
        (tensorPowerKroneckerTwo (a := Prod α β) ρ *
          twoCopySideOperator (a := α) (e := β) G H).trace
       map_add' := by
        intro G G'
        rw [twoCopySideOperator_add_left, Matrix.mul_add, Matrix.trace_add]
       map_smul' := by
        intro c G
        change (tensorPowerKroneckerTwo (a := Prod α β) ρ *
            twoCopySideOperator (a := α) (e := β) ((c : ℂ) • G) H).trace =
          c • (tensorPowerKroneckerTwo (a := Prod α β) ρ *
            twoCopySideOperator (a := α) (e := β) G H).trace
        rw [twoCopySideOperator_smul_left, Matrix.mul_smul, Matrix.trace_smul]
        rfl } :
      CMatrix (TensorPower α 2) →ₗ[ℝ] ℂ)

/-- Integral-side bridge for ADHW fqsw.tex lines 708-712: a scalar
two-copy trace of the Haar integrand is the same scalar trace evaluated on
the two-copy unitary twirl. -/
theorem fqsw_unitaryTwirl_twoCopySide_trace_integral_bridge
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β]
    (A : CMatrix (TensorPower α 2)) (ρ : CMatrix (Prod α β))
    (H : CMatrix (TensorPower β 2)) :
    (∫ U : Matrix.unitaryGroup α ℂ,
        (tensorPowerKroneckerTwo (a := Prod α β) ρ *
          twoCopySideOperator (a := α) (e := β)
            (unitaryTwirlIntegrand (a := α) 2 A U) H).trace
        ∂unitaryHaarMeasure (a := α)) =
      (tensorPowerKroneckerTwo (a := Prod α β) ρ *
        twoCopySideOperator (a := α) (e := β)
          (unitaryTwirl 2 A) H).trace := by
  let L := fqswTwoCopySideTraceCLM (α := α) (β := β) ρ H
  have hf : MeasureTheory.Integrable
      (unitaryTwirlIntegrand (a := α) 2 A)
      (unitaryHaarMeasure (a := α)) :=
    unitaryTwirl_integrand_integrable (a := α) 2 A
  change (∫ U : Matrix.unitaryGroup α ℂ,
        L (unitaryTwirlIntegrand (a := α) 2 A U)
        ∂unitaryHaarMeasure (a := α)) =
      L (unitaryTwirl 2 A)
  simpa [L, unitaryTwirl] using
    ((fqswTwoCopySideTraceCLM (α := α) (β := β) ρ H).integral_comp_comm hf)

/-- Trace of a one-system two-copy operator against `Π₊`, used in the
`R = 1` specialization of ADHW fqsw.tex lines 722 and 781-784. -/
theorem fqsw_twoCopy_symmetricProjection_trace
    {α : Type u} [Fintype α] [DecidableEq α] (ρ : CMatrix α) :
    (tensorPowerKroneckerTwo (a := α) ρ *
      symmetricProjectionMatrix (a := α) 2).trace =
      ((1 : ℂ) / 2) * (ρ.trace * ρ.trace + (ρ * ρ).trace) := by
  rw [symmetricProjectionMatrix_two_eq_half_one_add_swap]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [Matrix.mul_add, Matrix.trace_add]
  rw [Matrix.mul_one]
  rw [tensorPowerKroneckerTwo_trace]
  rw [tensorPowerKroneckerTwo_mul_tensorPowerSwapMatrix_two_trace]
  ring

/-- Trace of a one-system two-copy operator against `Π₋`, used in the
`R = 1` specialization of ADHW fqsw.tex lines 722 and 781-784. -/
theorem fqsw_twoCopy_antisymmetricProjection_trace
    {α : Type u} [Fintype α] [DecidableEq α] (ρ : CMatrix α) :
    (tensorPowerKroneckerTwo (a := α) ρ *
      antisymmetricProjectionMatrix_two (a := α)).trace =
      ((1 : ℂ) / 2) * (ρ.trace * ρ.trace - (ρ * ρ).trace) := by
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [Matrix.mul_one]
  rw [tensorPowerKroneckerTwo_trace]
  rw [tensorPowerKroneckerTwo_mul_tensorPowerSwapMatrix_two_trace]
  ring

/-- ADHW fqsw.tex lines 708-714 after Schur twirling: evaluating the twirled
split observable against a source `AR` matrix gives the `R` and `AR` purity
trace terms with coefficients `(p+q)/2` and `(p-q)/2`. -/
theorem fqsw_splitObservable_unitaryTwirl_swap_trace
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype r] [DecidableEq r] [Nontrivial (Prod q e)]
    (ρ : CMatrix (Prod (Prod q e) r)) :
    (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
      twoCopySideOperator (a := Prod q e) (e := r)
        (unitaryTwirl 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e))))
        (tensorPowerSwapMatrix_two (a := r))).trace =
      (((adhwFQSWSchurPCoeff q e : ℂ) + (adhwFQSWSchurQCoeff q e : ℂ)) / 2) *
          (partialTraceA (a := Prod q e) (b := r) ρ *
            partialTraceA (a := Prod q e) (b := r) ρ).trace +
        (((adhwFQSWSchurPCoeff q e : ℂ) - (adhwFQSWSchurQCoeff q e : ℂ)) / 2) *
          (ρ * ρ).trace := by
  rw [adhwFQSW_splitObservable_unitaryTwirl_eq (q := q) (e := e)]
  rw [twoCopySideOperator_add_left]
  rw [twoCopySideOperator_smul_left, twoCopySideOperator_smul_left]
  rw [Matrix.mul_add, Matrix.trace_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  rw [fqsw_twoCopy_symmetricProjection_swap_trace]
  rw [fqsw_twoCopy_antisymmetricProjection_swap_trace]
  ring

/-- ADHW fqsw.tex lines 722 and 781-784 with trivial reference: the twirled
split observable gives the averaged `A₂` purity trace. -/
theorem fqsw_splitObservable_unitaryTwirl_trace
    {q : Type x} {e : Type y}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] [Nontrivial (Prod q e)]
    (ρ : CMatrix (Prod q e)) :
    (tensorPowerKroneckerTwo (a := Prod q e) ρ *
      unitaryTwirl 2
        (twoCopySideOperator (a := q) (e := e)
          (1 : CMatrix (TensorPower q 2))
          (tensorPowerSwapMatrix_two (a := e)))).trace =
      (((adhwFQSWSchurPCoeff q e : ℂ) + (adhwFQSWSchurQCoeff q e : ℂ)) / 2) *
          (ρ.trace * ρ.trace) +
        (((adhwFQSWSchurPCoeff q e : ℂ) - (adhwFQSWSchurQCoeff q e : ℂ)) / 2) *
          (ρ * ρ).trace := by
  rw [adhwFQSW_splitObservable_unitaryTwirl_eq (q := q) (e := e)]
  rw [Matrix.mul_add, Matrix.trace_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  rw [fqsw_twoCopy_symmetricProjection_trace]
  rw [fqsw_twoCopy_antisymmetricProjection_trace]
  ring

private noncomputable def fqswTraceMulCLM
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ : CMatrix α) : CMatrix α →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => (ρ * A).trace
       map_add' := by
        intro A B
        rw [Matrix.mul_add, Matrix.trace_add]
       map_smul' := by
        intro c A
        change (ρ * ((c : ℂ) • A)).trace = c • (ρ * A).trace
        rw [Matrix.mul_smul, Matrix.trace_smul]
        rfl } :
      CMatrix α →ₗ[ℝ] ℂ)

/-- Integral-side bridge for a scalar two-copy trace against the ordinary
Haar twirl. -/
theorem fqsw_unitaryTwirl_trace_integral_bridge
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (A ρ : CMatrix (TensorPower α 2)) :
    (∫ U : Matrix.unitaryGroup α ℂ,
        (ρ * unitaryTwirlIntegrand (a := α) 2 A U).trace
        ∂unitaryHaarMeasure (a := α)) =
      (ρ * unitaryTwirl 2 A).trace := by
  let L := fqswTraceMulCLM (α := TensorPower α 2) ρ
  have hf : MeasureTheory.Integrable
      (unitaryTwirlIntegrand (a := α) 2 A)
      (unitaryHaarMeasure (a := α)) :=
    unitaryTwirl_integrand_integrable (a := α) 2 A
  change (∫ U : Matrix.unitaryGroup α ℂ,
        L (unitaryTwirlIntegrand (a := α) 2 A U)
        ∂unitaryHaarMeasure (a := α)) =
      L (unitaryTwirl 2 A)
  simpa [L, unitaryTwirl] using
    ((fqswTraceMulCLM (α := TensorPower α 2) ρ).integral_comp_comm hf)

/-- Pointwise one-copy flip trick for ADHW fqsw.tex lines 781-784. -/
theorem fqsw_A2_square_trace_eq_twirl_inv_integrand
    {q : Type x} {e : Type y}
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e]
    (ρ : CMatrix (Prod q e)) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) *
      partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e)))).trace =
      (tensorPowerKroneckerTwo (a := Prod q e) ρ *
        unitaryTwirlIntegrand (a := Prod q e) 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e))) U⁻¹).trace := by
  let A : CMatrix (TensorPower (Prod q e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))
  let U₂ : CMatrix (TensorPower (Prod q e) 2) :=
    tensorPowerKroneckerTwo (a := Prod q e) (U : CMatrix (Prod q e))
  let R : CMatrix (TensorPower (Prod q e) 2) :=
    tensorPowerKroneckerTwo (a := Prod q e) ρ
  have htensor :
      tensorPowerKroneckerTwo (a := Prod q e)
          ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) =
        U₂ * R * star U₂ := by
    calc
      tensorPowerKroneckerTwo (a := Prod q e)
          ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) =
        tensorPowerKroneckerTwo (a := Prod q e)
            ((U : CMatrix (Prod q e)) * ρ) *
          tensorPowerKroneckerTwo (a := Prod q e) (star (U : CMatrix (Prod q e))) := by
          exact (tensorPowerKroneckerTwo_mul (a := Prod q e)
            ((U : CMatrix (Prod q e)) * ρ) (star (U : CMatrix (Prod q e)))).symm
      _ = (tensorPowerKroneckerTwo (a := Prod q e) (U : CMatrix (Prod q e)) *
            tensorPowerKroneckerTwo (a := Prod q e) ρ) *
          tensorPowerKroneckerTwo (a := Prod q e) (star (U : CMatrix (Prod q e))) := by
          rw [tensorPowerKroneckerTwo_mul (a := Prod q e) (U : CMatrix (Prod q e)) ρ]
      _ = U₂ * R * star U₂ := by
          rw [fqsw_tensorPowerKroneckerTwo_star]
  rw [← tensorPowerKroneckerTwo_prod_mul_one_swap_trace
    (a := q) (e := e)
    (rho := (U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e)))]
  rw [htensor]
  calc
    ((U₂ * R * star U₂) * A).trace =
        (R * (star U₂ * A * U₂)).trace := by
          have h := Matrix.trace_mul_comm U₂ (R * star U₂ * A)
          simpa [Matrix.mul_assoc] using h
    _ = (R * unitaryTwirlIntegrand (a := Prod q e) 2 A U⁻¹).trace := by
          congr 1
          simp [A, U₂, unitaryTwirlIntegrand,
            fqsw_unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo,
            Matrix.mul_assoc]
    _ = (tensorPowerKroneckerTwo (a := Prod q e) ρ *
        unitaryTwirlIntegrand (a := Prod q e) 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e))) U⁻¹).trace := by
          rfl

/-- Haar-averaged one-copy purity identity from ADHW fqsw.tex lines
781-784. -/
theorem fqsw_A2_square_trace_average_eq
    {q : Type x} {e : Type y}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] [Nontrivial (Prod q e)]
    (ρ : CMatrix (Prod q e)) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        (partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) *
          partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e)))).trace
        ∂unitaryHaarMeasure (a := Prod q e)) =
      (tensorPowerKroneckerTwo (a := Prod q e) ρ *
        unitaryTwirl 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e)))).trace := by
  let A : CMatrix (TensorPower (Prod q e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))
  let R : CMatrix (TensorPower (Prod q e) 2) :=
    tensorPowerKroneckerTwo (a := Prod q e) ρ
  let f : Matrix.unitaryGroup (Prod q e) ℂ → ℂ := fun U =>
    (R * unitaryTwirlIntegrand (a := Prod q e) 2 A U).trace
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        (partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e))) *
          partialTraceA (a := q) (b := e)
            ((U : CMatrix (Prod q e)) * ρ * star (U : CMatrix (Prod q e)))).trace
        ∂unitaryHaarMeasure (a := Prod q e)) =
      ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U⁻¹
        ∂unitaryHaarMeasure (a := Prod q e) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with U
        simpa [f, R, A] using fqsw_A2_square_trace_eq_twirl_inv_integrand
          (q := q) (e := e) ρ U
    _ = ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U
        ∂unitaryHaarMeasure (a := Prod q e) := by
        rw [MeasureTheory.integral_inv_eq_self (f := f)
          (μ := unitaryHaarMeasure (a := Prod q e))]
    _ = (tensorPowerKroneckerTwo (a := Prod q e) ρ *
        unitaryTwirl 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e)))).trace := by
        simpa [f, R, A] using
          fqsw_unitaryTwirl_trace_integral_bridge
            (α := Prod q e) A R

/-- Static flip trick for the `A₂R` marginal after regrouping
`(A₁ × A₂) × R` as `A₁ × (A₂ × R)`.  This is the source-route bridge from the
partial trace square to the two-copy observable
`I^{A₁A₁'} ⊗ F^{A₂} ⊗ F^R`. -/
theorem fqsw_A2R_square_trace_eq_split_observable
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e]
    [Fintype r] [DecidableEq r]
    (ρ : CMatrix (Prod (Prod q e) r)) :
    (partialTraceA (a := q) (b := Prod e r)
        (ρ.submatrix (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) *
      partialTraceA (a := q) (b := Prod e r)
        (ρ.submatrix (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)).trace =
      (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e)))
          (tensorPowerSwapMatrix_two (a := r))).trace := by
  let ρ' : CMatrix (Prod q (Prod e r)) :=
    ρ.submatrix (fqswQERToA2REquiv q e r).symm
      (fqswQERToA2REquiv q e r).symm
  calc
    (partialTraceA (a := q) (b := Prod e r) ρ' *
      partialTraceA (a := q) (b := Prod e r) ρ').trace =
        ∑ i : q, ∑ k : e, ∑ s : r, ∑ j : q, ∑ l : e, ∑ t : r,
          ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s) := by
      rw [← tensorPowerKroneckerTwo_prod_mul_one_swap_trace
        (a := q) (e := Prod e r) (rho := ρ')]
      rw [Matrix.trace, fqsw_sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun t _ => ?_
      change
        (tensorPowerKroneckerTwo (a := Prod q (Prod e r)) ρ' *
          twoCopySideOperator (a := q) (e := Prod e r)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := Prod e r)))
          (twoCopyTensorWord (a := Prod q (Prod e r)) (i, (k, s)) (j, (l, t)))
          (twoCopyTensorWord (a := Prod q (Prod e r)) (i, (k, s)) (j, (l, t))) =
        ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s)
      rw [Matrix.mul_apply, fqsw_sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      simp_rw [Fintype.sum_prod_type]
      simpa [ρ', fqswQERToA2REquiv, Matrix.one_apply,
        permEquiv_twoCopySwapPerm_twoCopyTensorWord, twoCopyTensorWord_eq_iff,
        mul_comm, mul_left_comm, mul_assoc] using
          fqsw_partialTraceA_flip_entry_sum_prod
            (α := q) (β := e) (γ := r) ρ' i j k l s t
    _ = (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrix_two (a := e)))
          (tensorPowerSwapMatrix_two (a := r))).trace := by
      symm
      rw [Matrix.trace, fqsw_sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun t _ => ?_
      change
        (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
          twoCopySideOperator (a := Prod q e) (e := r)
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e)))
            (tensorPowerSwapMatrix_two (a := r)))
          (twoCopyTensorWord (a := Prod (Prod q e) r) ((i, k), s) ((j, l), t))
          (twoCopyTensorWord (a := Prod (Prod q e) r) ((i, k), s) ((j, l), t)) =
        ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s)
      rw [Matrix.mul_apply, fqsw_sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      simp_rw [Fintype.sum_prod_type]
      simpa [Matrix.one_apply, permEquiv_twoCopySwapPerm_twoCopyTensorWord,
        twoCopyTensorWord_eq_iff, mul_comm, mul_left_comm, mul_assoc] using
          fqsw_nested_split_flip_entry_sum
            (α := q) (β := e) (γ := r) ρ i j k l s t

/-- Pointwise `A₂R` flip trick for the split unitary integrand in ADHW
fqsw.tex lines 708-714. -/
theorem fqsw_A2R_square_trace_eq_twirl_inv_integrand
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e]
    [Fintype r] [DecidableEq r]
    (ρ : CMatrix (Prod (Prod q e) r)) (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    (partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) *
      partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)).trace =
      (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (unitaryTwirlIntegrand (a := Prod q e) 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e))) U⁻¹)
          (tensorPowerSwapMatrix_two (a := r))).trace := by
  let A : CMatrix (TensorPower (Prod q e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))
  let H : CMatrix (TensorPower r 2) := tensorPowerSwapMatrix_two (a := r)
  let K : CMatrix (Prod (Prod q e) r) :=
    Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
  let U₂ : CMatrix (TensorPower (Prod q e) 2) :=
    tensorPowerKroneckerTwo (a := Prod q e) (U : CMatrix (Prod q e))
  let K₂ : CMatrix (TensorPower (Prod (Prod q e) r) 2) :=
    tensorPowerKroneckerTwo (a := Prod (Prod q e) r) K
  let R : CMatrix (TensorPower (Prod (Prod q e) r) 2) :=
    tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ
  have htensor :
      tensorPowerKroneckerTwo (a := Prod (Prod q e) r)
          (K * ρ * star K) =
        K₂ * R * star K₂ := by
    calc
      tensorPowerKroneckerTwo (a := Prod (Prod q e) r) (K * ρ * star K) =
          tensorPowerKroneckerTwo (a := Prod (Prod q e) r) (K * ρ) *
            tensorPowerKroneckerTwo (a := Prod (Prod q e) r) (star K) := by
            exact (tensorPowerKroneckerTwo_mul (a := Prod (Prod q e) r)
              (K * ρ) (star K)).symm
      _ = (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) K *
            tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ) *
            tensorPowerKroneckerTwo (a := Prod (Prod q e) r) (star K) := by
            rw [tensorPowerKroneckerTwo_mul (a := Prod (Prod q e) r) K ρ]
      _ = K₂ * R * star K₂ := by
            rw [fqsw_tensorPowerKroneckerTwo_star]
  have hK₂ :
      K₂ = twoCopySideOperator (a := Prod q e) (e := r) U₂
          (1 : CMatrix (TensorPower r 2)) := by
    simpa [K₂, K, U₂] using
      fqsw_tensorPowerKroneckerTwo_kronecker_one
        (α := Prod q e) (β := r) (U : CMatrix (Prod q e))
  have hstarK₂ :
      star K₂ =
        twoCopySideOperator (a := Prod q e) (e := r) (star U₂)
          (1 : CMatrix (TensorPower r 2)) := by
    rw [hK₂]
    ext x y
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      twoCopySideOperator_apply, Matrix.one_apply]
    by_cases hxy :
        ((tensorPowerProdEquiv (Prod q e) r 2) y).2 =
          ((tensorPowerProdEquiv (Prod q e) r 2) x).2
    · have hyx :
          ((tensorPowerProdEquiv (Prod q e) r 2) x).2 =
            ((tensorPowerProdEquiv (Prod q e) r 2) y).2 := hxy.symm
      rw [if_pos hxy, if_pos hyx]
      simp
    · have hyx :
          ¬ ((tensorPowerProdEquiv (Prod q e) r 2) x).2 =
            ((tensorPowerProdEquiv (Prod q e) r 2) y).2 := by
          intro hyx
          exact hxy hyx.symm
      rw [if_neg hxy, if_neg hyx]
      simp
  rw [show
      (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
          ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) =
        K * ρ * star K by rfl]
  rw [fqsw_A2R_square_trace_eq_split_observable
    (q := q) (e := e) (r := r) (ρ := K * ρ * star K)]
  rw [htensor]
  calc
    ((K₂ * R * star K₂) *
        twoCopySideOperator (a := Prod q e) (e := r) A H).trace =
      (R * (star K₂ *
        twoCopySideOperator (a := Prod q e) (e := r) A H * K₂)).trace := by
        have h := Matrix.trace_mul_comm K₂
          (R * star K₂ * twoCopySideOperator (a := Prod q e) (e := r) A H)
        simpa [Matrix.mul_assoc] using h
    _ = (R * twoCopySideOperator (a := Prod q e) (e := r)
        (unitaryTwirlIntegrand (a := Prod q e) 2 A U⁻¹) H).trace := by
        congr 1
        rw [hstarK₂, hK₂]
        rw [fqsw_twoCopySideOperator_mul]
        rw [fqsw_twoCopySideOperator_mul]
        simp [A, H, U₂, unitaryTwirlIntegrand,
          fqsw_unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo,
          Matrix.mul_assoc]
    _ = (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (unitaryTwirlIntegrand (a := Prod q e) 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e))) U⁻¹)
          (tensorPowerSwapMatrix_two (a := r))).trace := by
        rfl

/-- Haar-averaged `A₂R` purity identity from ADHW fqsw.tex lines 708-714. -/
theorem fqsw_A2R_square_trace_average_eq
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype r] [DecidableEq r] [Nontrivial (Prod q e)]
    (ρ : CMatrix (Prod (Prod q e) r)) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      (partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm) *
        partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)).trace
      ∂unitaryHaarMeasure (a := Prod q e)) =
      (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (unitaryTwirl 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e))))
          (tensorPowerSwapMatrix_two (a := r))).trace := by
  let A : CMatrix (TensorPower (Prod q e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrix_two (a := e))
  let H : CMatrix (TensorPower r 2) := tensorPowerSwapMatrix_two (a := r)
  let R : CMatrix (TensorPower (Prod (Prod q e) r) 2) :=
    tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ
  let f : Matrix.unitaryGroup (Prod q e) ℂ → ℂ := fun U =>
    (R *
      twoCopySideOperator (a := Prod q e) (e := r)
        (unitaryTwirlIntegrand (a := Prod q e) 2 A U) H).trace
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      (partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm) *
        partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              ρ * star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)).trace
      ∂unitaryHaarMeasure (a := Prod q e)) =
        ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U⁻¹
          ∂unitaryHaarMeasure (a := Prod q e) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with U
        simpa [f, R, A, H] using
          fqsw_A2R_square_trace_eq_twirl_inv_integrand
            (q := q) (e := e) (r := r) ρ U
    _ = ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U
        ∂unitaryHaarMeasure (a := Prod q e) := by
        rw [MeasureTheory.integral_inv_eq_self (f := f)
          (μ := unitaryHaarMeasure (a := Prod q e))]
    _ = (tensorPowerKroneckerTwo (a := Prod (Prod q e) r) ρ *
        twoCopySideOperator (a := Prod q e) (e := r)
          (unitaryTwirl 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrix_two (a := e))))
          (tensorPowerSwapMatrix_two (a := r))).trace := by
        simpa [f, R, A, H] using
          fqsw_unitaryTwirl_twoCopySide_trace_integral_bridge
            (α := Prod q e) (β := r) A ρ H

/-- Subtracting the maximally mixed state turns the Hilbert--Schmidt square
into the output purity minus `1/d`. -/
theorem fqsw_hilbertSchmidtSq_sub_maximallyMixedState
    {e : Type y} [Fintype e] [DecidableEq e] [Nonempty e] (ρ : State e) :
    hilbertSchmidtSq (ρ.matrix - (State.maximallyMixed e).matrix) =
      (ρ.matrix * ρ.matrix).trace.re - (1 / (Fintype.card e : ℝ)) := by
  have hcard_ne : (Fintype.card e : ℝ) ≠ 0 := by positivity
  have hcross :
      (ρ.matrix * (State.maximallyMixed e).matrix).trace.re =
        1 / (Fintype.card e : ℝ) := by
    simp [State.maximallyMixed, Matrix.trace_smul,
      ρ.trace_eq_one, one_div]
  have hmm :
      hilbertSchmidtSq (State.maximallyMixed e).matrix =
        1 / (Fintype.card e : ℝ) := by
    unfold hilbertSchmidtSq State.maximallyMixed
    simp [Matrix.trace_smul, Matrix.trace_one, one_div]
  rw [fqsw_hilbertSchmidtSq_sub_of_isHermitian
    ρ.matrix (State.maximallyMixed e).matrix
    ρ.pos.isHermitian (State.maximallyMixed e).pos.isHermitian]
  rw [hcross, hmm]
  ring

/-- Exact Hilbert--Schmidt one-shot expression from ADHW fqsw.tex lines
682-747, written in the repository's source-state notation. -/
def adhwFQSWHSOneShotExact
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ℝ :=
  ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ) ^ 2) -
      (Fintype.card q : ℝ)) /
    ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) ^ 2) - 1)) *
    (adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
      adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)

omit [DecidableEq q] [DecidableEq e] in
/-- In the one-point split case, the ADHW Hilbert--Schmidt prefactor is zero,
so the exact one-shot expression is zero. -/
theorem adhwFQSWHSOneShotExact_eq_zero_of_subsingleton
    [Nonempty q] [Subsingleton (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) :
    adhwFQSWHSOneShotExact ψ q e = 0 := by
  classical
  let q0 : q := Classical.choice inferInstance
  let e0 : e := Classical.choice inferInstance
  haveI : Subsingleton q :=
    Function.Injective.subsingleton (f := fun x : q => (x, e0))
      (by intro x y h; exact congrArg Prod.fst h)
  haveI : Subsingleton e :=
    Function.Injective.subsingleton (f := fun y : e => (q0, y))
      (by intro x y h; exact congrArg Prod.snd h)
  have hqcard : (Fintype.card q : ℝ) = 1 := by
    exact_mod_cast
      (Fintype.card_eq_one_iff.mpr ⟨q0, fun y => Subsingleton.elim y q0⟩)
  have hecard : (Fintype.card e : ℝ) = 1 := by
    exact_mod_cast
      (Fintype.card_eq_one_iff.mpr ⟨e0, fun y => Subsingleton.elim y e0⟩)
  unfold adhwFQSWHSOneShotExact
  rw [hqcard, hecard]
  norm_num

/-- ADHW fqsw.tex Eq. (actuallyItsSimple): the Schur/HS prefactor is bounded
by `1/d_{A₁}`. -/
theorem adhwFQSW_HS_prefactor_le_inv_card_q
    (q : Type x) (e : Type y) [Fintype q] [Fintype e] [Nonempty q] [Nonempty e] :
    ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ) ^ 2) -
        (Fintype.card q : ℝ)) /
      ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) ^ 2) - 1)) ≤
      (1 : ℝ) / (Fintype.card q : ℝ) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_pos : 0 < dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_pos : 0 < de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hprod_ge_one : 1 ≤ dq * de := by
    nlinarith
  by_cases hprod_eq : dq * de = 1
  · have hde_eq : de = 1 := by nlinarith
    have hdq_eq : dq = 1 := by nlinarith
    change (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1) ≤ 1 / dq
    rw [hdq_eq, hde_eq]
    norm_num
  have hden_pos : 0 < (dq * de) ^ 2 - 1 := by
    have hprod_gt : 1 < dq * de := lt_of_le_of_ne hprod_ge_one (Ne.symm hprod_eq)
    nlinarith
  have hdq_ne : dq ≠ 0 := ne_of_gt hdq_pos
  change (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1) ≤ 1 / dq
  rw [div_le_iff₀ hden_pos]
  have hdq_sq_ge_one : 1 ≤ dq ^ 2 := by
    nlinarith
  rw [one_div, ← div_eq_inv_mul]
  rw [le_div_iff₀ hdq_pos]
  nlinarith

/-- The ADHW HS prefactor is nonnegative. -/
theorem adhwFQSW_HS_prefactor_nonneg
    (q : Type x) (e : Type y) [Fintype q] [Fintype e] [Nonempty q] [Nonempty e] :
    0 ≤ ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ) ^ 2) -
        (Fintype.card q : ℝ)) /
      ((((Fintype.card q : ℝ) * (Fintype.card e : ℝ)) ^ 2) - 1)) := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  have hdq_ge_one : 1 ≤ dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hde_ge_one : 1 ≤ de := by
    dsimp [de]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card e)
  have hde_sq_ge_one : 1 ≤ de ^ 2 := by nlinarith
  have hnum_nonneg : 0 ≤ dq * de ^ 2 - dq := by
    nlinarith
  have hden_nonneg : 0 ≤ (dq * de) ^ 2 - 1 := by
    nlinarith [sq_nonneg (dq * de), mul_le_mul hdq_ge_one hde_ge_one (by norm_num) (by nlinarith)]
  change 0 ≤ (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1)
  exact div_nonneg hnum_nonneg hden_nonneg

/-- Trace-norm decoupling square bound from ADHW fqsw.tex lines 580-760. -/
def adhwFQSWTraceNormDecouplingSqBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] : ℝ :=
  ((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
      ((Fintype.card q : ℝ) ^ 2)) *
    (adhwFQSWARPurity ψ + adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)

/-- Max-mixed `A₂` square bound from ADHW fqsw.tex lines 767-795. -/
def adhwFQSWMaxMixedA2SqBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] : ℝ :=
  ((Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2)) * adhwFQSWAPurity ψ

/-- ADHW fqsw.tex lines 781-787: in the nontrivial Schur case, the
Haar-averaged Hilbert--Schmidt distance of the `A₂` marginal from maximally
mixed is bounded by the source one-copy purity term. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtAverage_le_of_nontrivial
    [Nonempty q] [Nontrivial (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (Fintype.card e : ℝ) *
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q := by
  let ρA : CMatrix (Prod q e) := adhwFQSWASplitMatrix ψ split
  let f : Matrix.unitaryGroup (Prod q e) ℂ → ℂ := fun U =>
    (partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * ρA * star (U : CMatrix (Prod q e))) *
      partialTraceA (a := q) (b := e)
        ((U : CMatrix (Prod q e)) * ρA * star (U : CMatrix (Prod q e)))).trace
  have hf_cont : Continuous f := by
    unfold f
    continuity
  have hf_int : MeasureTheory.Integrable f (unitaryHaarMeasure (a := Prod q e)) :=
    hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre_integral :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (f U).re
        ∂unitaryHaarMeasure (a := Prod q e)) =
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, f U
          ∂unitaryHaarMeasure (a := Prod q e)).re := by
    simpa [f] using (Complex.reCLM.integral_comp_comm hf_int)
  have hρ_trace : ρA.trace = 1 := by
    simpa [ρA] using adhwFQSWASplitMatrix_trace ψ split
  have hρ_herm : ρA.IsHermitian := by
    unfold ρA adhwFQSWASplitMatrix
    exact fqsw_isHermitian_submatrix_equiv split.symm
      (adhwFQSWARState ψ).marginalA.pos.isHermitian
  have hρ_purity : (ρA * ρA).trace.re = adhwFQSWAPurity ψ := by
    calc
      (ρA * ρA).trace.re = hilbertSchmidtSq ρA := by
        exact (fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian ρA hρ_herm).symm
      _ = adhwFQSWAPurity ψ := by
        simpa [ρA] using adhwFQSWASplitMatrix_hilbertSchmidtSq ψ split
  have hcomplex :=
    (fqsw_A2_square_trace_average_eq (q := q) (e := e) ρA).trans
      (fqsw_splitObservable_unitaryTwirl_trace (q := q) (e := e) ρA)
  have hreal := congrArg Complex.re hcomplex
  have haverage_purity :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (f U).re
        ∂unitaryHaarMeasure (a := Prod q e)) =
        ((adhwFQSWSchurPCoeff q e + adhwFQSWSchurQCoeff q e) / 2) +
          ((adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2) *
            adhwFQSWAPurity ψ := by
    rw [hre_integral]
    simpa [f, ρA, hρ_trace, hρ_purity, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.div_re] using hreal
  have hhs_point : ∀ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U =
        (f U).re - (1 / (Fintype.card e : ℝ)) := by
    intro U
    let σ : State e :=
      adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)
    have hσ :=
      fqsw_hilbertSchmidtSq_sub_maximallyMixedState (e := e) σ
    simpa [adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary,
      adhwFQSWMaximallyMixedA2State, σ, f, ρA,
      adhwFQSWSigmaA2StateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_A]
      using hσ
  have hf_re_int : MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Prod q e) ℂ => (f U).re)
      (unitaryHaarMeasure (a := Prod q e)) :=
    Complex.reCLM.integrable_comp hf_int
  have hhs_average :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) =
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (f U).re
          ∂unitaryHaarMeasure (a := Prod q e)) -
          (1 / (Fintype.card e : ℝ)) := by
    calc
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) =
          ∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
            ((f U).re - (1 / (Fintype.card e : ℝ)))
            ∂unitaryHaarMeasure (a := Prod q e) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with U
            exact hhs_point U
      _ = (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (f U).re
            ∂unitaryHaarMeasure (a := Prod q e)) -
            (1 / (Fintype.card e : ℝ)) := by
            rw [MeasureTheory.integral_sub hf_re_int (MeasureTheory.integrable_const _)]
            rw [MeasureTheory.integral_const]
            simp [MeasureTheory.measureReal_def]
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  let P : ℝ := adhwFQSWAPurity ψ
  have hP_nonneg : 0 ≤ P := by
    simpa [P, adhwFQSWAPurity] using
      hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).marginalA.matrix)
  have hsum_le :
      (adhwFQSWSchurPCoeff q e + adhwFQSWSchurQCoeff q e) / 2 ≤
        1 / de := by
    simpa [de] using adhwFQSWSchur_half_sum_le_inv_card_e q e
  have hsub_le :
      (adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2 ≤
        1 / dq := by
    simpa [dq] using adhwFQSWSchur_half_sub_le_inv_card_q q e
  have hhs_le :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        (1 / dq) * P := by
    rw [hhs_average, haverage_purity]
    nlinarith [mul_le_mul_of_nonneg_right hsub_le hP_nonneg, hsum_le]
  have hde_nonneg : 0 ≤ de := by
    dsimp [de]
    positivity
  have hcard_a : (Fintype.card a : ℝ) = dq * de := by
    have hnat : Fintype.card a = Fintype.card (Prod q e) :=
      Fintype.card_congr split
    rw [Fintype.card_prod] at hnat
    dsimp [dq, de]
    exact_mod_cast hnat
  have hdq_pos : 0 < dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  unfold adhwFQSWMaxMixedA2SqBound
  change de *
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      ((Fintype.card a : ℝ) / dq ^ 2) * P
  calc
    de *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) ≤ de * ((1 / dq) * P) :=
        mul_le_mul_of_nonneg_left hhs_le hde_nonneg
    _ = ((Fintype.card a : ℝ) / dq ^ 2) * P := by
        rw [hcard_a]
        field_simp [ne_of_gt hdq_pos]

omit [Nonempty e] in
/-- Pointwise source-route bridge for ADHW fqsw.tex lines 682-747: the
product-decoupling Hilbert--Schmidt integrand is the `A₂R` marginal of the
conjugated source correlation matrix
`ψ^{AR} - ψ^A ⊗ ψ^R`. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_eq_correlation
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ) :
    adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U =
      hilbertSchmidtSq
        (partialTraceA (a := q) (b := Prod e r)
          (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
              (adhwFQSWARSplitMatrix ψ split -
                adhwFQSWARProductSplitMatrix ψ split) *
              star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)) := by
  let K : CMatrix (Prod (Prod q e) r) :=
    Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
  let Rm : CMatrix (Prod (Prod q e) r) := adhwFQSWARSplitMatrix ψ split
  let Pm : CMatrix (Prod (Prod q e) r) := adhwFQSWARProductSplitMatrix ψ split
  rw [adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary]
  rw [adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_AR_split]
  rw [adhwFQSWProductA2RStateOfSplitUnitary_matrix_eq_partialTraceA_applyMatrix_ARProduct]
  rw [← fqsw_partialTraceA_sub]
  change
    hilbertSchmidtSq
      (partialTraceA (a := q) (b := Prod e r)
        ((K * Rm * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm -
          (K * Pm * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)) =
      hilbertSchmidtSq
        (partialTraceA (a := q) (b := Prod e r)
          ((K * (Rm - Pm) * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm))
  have hsubmatrix :
      (K * Rm * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm -
          (K * Pm * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm =
        (K * (Rm - Pm) * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm := by
    ext x y
    simp [Matrix.mul_sub, Matrix.sub_mul]
  rw [hsubmatrix]

/-- ADHW fqsw.tex lines 682-747 in the nontrivial Schur case: the Haar
average of the product-decoupling Hilbert--Schmidt square is exactly the
source one-shot expression. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtAverage_eq_of_nontrivial
    [Nonempty q] [Nontrivial (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) =
      adhwFQSWHSOneShotExact ψ q e := by
  let Δ : CMatrix (Prod (Prod q e) r) :=
    adhwFQSWARSplitMatrix ψ split -
      adhwFQSWARProductSplitMatrix ψ split
  let g : Matrix.unitaryGroup (Prod q e) ℂ → ℂ := fun U =>
    (partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            Δ *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm) *
      partialTraceA (a := q) (b := Prod e r)
        (((Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)) *
            Δ *
            star (Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r))).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)).trace
  have hg_cont : Continuous g := by
    unfold g
    continuity
  have hg_int : MeasureTheory.Integrable g (unitaryHaarMeasure (a := Prod q e)) :=
    hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre_integral :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (g U).re
        ∂unitaryHaarMeasure (a := Prod q e)) =
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ, g U
          ∂unitaryHaarMeasure (a := Prod q e)).re := by
    simpa [g] using (Complex.reCLM.integral_comp_comm hg_int)
  have hRm_herm : (adhwFQSWARSplitMatrix ψ split).IsHermitian := by
    unfold adhwFQSWARSplitMatrix
    exact fqsw_isHermitian_submatrix_equiv (fqswARSplitEquiv split).symm
      (adhwFQSWARState ψ).pos.isHermitian
  have hPm_herm : (adhwFQSWARProductSplitMatrix ψ split).IsHermitian := by
    unfold adhwFQSWARProductSplitMatrix
    exact kronecker_isHermitian _ _
      (fqsw_isHermitian_submatrix_equiv split.symm
        (adhwFQSWARState ψ).marginalA.pos.isHermitian)
      (adhwFQSWSigmaRState ψ).pos.isHermitian
  have hΔ_herm : Δ.IsHermitian := by
    dsimp [Δ]
    exact Matrix.IsHermitian.sub hRm_herm hPm_herm
  have hΔ_trace :
      partialTraceA (a := Prod q e) (b := r) Δ = 0 := by
    dsimp [Δ]
    rw [fqsw_partialTraceA_sub]
    rw [adhwFQSWARSplitMatrix_partialTraceA, adhwFQSWARProductSplitMatrix_partialTraceA]
    simp
  have hΔ_hs :
      (Δ * Δ).trace.re =
        adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
          adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
    calc
      (Δ * Δ).trace.re = hilbertSchmidtSq Δ := by
        exact (fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian Δ hΔ_herm).symm
      _ = adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
          adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
        simpa [Δ] using adhwFQSWARCorrelationSplitMatrix_hilbertSchmidtSq ψ split
  have hpoint : ∀ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U =
        (g U).re := by
    intro U
    let K : CMatrix (Prod (Prod q e) r) :=
      Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
    let M : CMatrix (Prod e r) :=
      partialTraceA (a := q) (b := Prod e r)
        ((K * Δ * star K).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm)
    have hconj : (K * Δ * star K).IsHermitian := by
      simpa [K, Matrix.star_eq_conjTranspose] using
        Matrix.isHermitian_mul_mul_conjTranspose K hΔ_herm
    have hsub :
        ((K * Δ * star K).submatrix
          (fqswQERToA2REquiv q e r).symm
          (fqswQERToA2REquiv q e r).symm).IsHermitian := by
      exact fqsw_isHermitian_submatrix_equiv
        (fqswQERToA2REquiv q e r).symm hconj
    have hM_herm : M.IsHermitian := by
      exact partialTraceA_isHermitian hsub
    rw [adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_eq_correlation]
    rw [fqsw_hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian M hM_herm]
  have hcomplex :=
    (fqsw_A2R_square_trace_average_eq (q := q) (e := e) (r := r) Δ).trans
      (fqsw_splitObservable_unitaryTwirl_swap_trace (q := q) (e := e) (r := r) Δ)
  have hreal := congrArg Complex.re hcomplex
  have haverage :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) =
        ((adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2) *
          (adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
            adhwFQSWAPurity ψ * adhwFQSWRPurity ψ) := by
    calc
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) =
          ∫ U : Matrix.unitaryGroup (Prod q e) ℂ, (g U).re
            ∂unitaryHaarMeasure (a := Prod q e) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with U
          exact hpoint U
      _ = ((adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2) *
          (adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
            adhwFQSWAPurity ψ * adhwFQSWRPurity ψ) := by
          rw [hre_integral]
          simpa [g, Δ, hΔ_trace, hΔ_hs, Complex.add_re, Complex.sub_re,
            Complex.mul_re, Complex.div_re] using hreal
  rw [haverage]
  unfold adhwFQSWHSOneShotExact
  rw [adhwFQSWSchur_half_sub_eq_HS_prefactor q e]

/-- ADHW fqsw.tex lines 682-747 in the nontrivial Schur case, stated as the
Hilbert--Schmidt average bound consumed by the one-shot assembly. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtAverage_le_of_nontrivial
    [Nonempty q] [Nontrivial (Prod q e)]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWHSOneShotExact ψ q e := by
  exact le_of_eq (adhwFQSWProductDecouplingHilbertSchmidtAverage_eq_of_nontrivial
    ψ split)

/-- ADHW fqsw.tex lines 682-747, including the degenerate one-point split
case, stated as the Hilbert--Schmidt average bound consumed by the one-shot
assembly. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtAverage_le
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWHSOneShotExact ψ q e := by
  by_cases hnt : Nontrivial (Prod q e)
  · exact adhwFQSWProductDecouplingHilbertSchmidtAverage_le_of_nontrivial
      ψ split
  · haveI : Subsingleton (Prod q e) :=
      not_nontrivial_iff_subsingleton.mp hnt
    have hΔzero :=
      adhwFQSWARCorrelationSplitMatrix_eq_zero_of_subsingleton ψ split
    have hfun :
        (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U) =
        fun _ => 0 := by
      funext U
      rw [adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_eq_correlation]
      rw [hΔzero]
      let K : CMatrix (Prod (Prod q e) r) :=
        Matrix.kronecker (U : CMatrix (Prod q e)) (1 : CMatrix r)
      let M : CMatrix (Prod e r) :=
        partialTraceA (a := q) (b := Prod e r)
          ((K * (0 : CMatrix (Prod (Prod q e) r)) * star K).submatrix
            (fqswQERToA2REquiv q e r).symm
            (fqswQERToA2REquiv q e r).symm)
      change hilbertSchmidtSq M = 0
      have hM : M = 0 := by
        ext x y
        simp [M, K, partialTraceA]
      rw [hM]
      simp [hilbertSchmidtSq]
    rw [hfun, MeasureTheory.integral_zero]
    rw [adhwFQSWHSOneShotExact_eq_zero_of_subsingleton (q := q) (e := e) ψ]

/-- ADHW fqsw.tex lines 781-787, including the degenerate one-point split
case, stated as the max-mixed `A₂` Hilbert--Schmidt average bound consumed by
the one-shot assembly. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtAverage_le
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e) :
    (Fintype.card e : ℝ) *
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q := by
  by_cases hnt : Nontrivial (Prod q e)
  · exact adhwFQSWMaxMixedA2HilbertSchmidtAverage_le_of_nontrivial
      ψ split
  · haveI : Subsingleton (Prod q e) :=
      not_nontrivial_iff_subsingleton.mp hnt
    classical
    let q0 : q := Classical.choice inferInstance
    haveI : Subsingleton e :=
      Function.Injective.subsingleton (f := fun y : e => (q0, y))
        (by intro x y h; exact congrArg Prod.snd h)
    have hfun :
        (fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U) =
        fun _ => 0 := by
      funext U
      rw [adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary]
      rw [State.eq_maximallyMixed_of_subsingleton
        (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
          (adhwFQSWAliceIsometryOfSplitUnitary split U))]
      unfold adhwFQSWMaximallyMixedA2State
      rw [sub_self]
      simp [hilbertSchmidtSq]
    rw [hfun, MeasureTheory.integral_zero, mul_zero]
    change 0 ≤ adhwFQSWMaxMixedA2SqBound ψ q
    unfold adhwFQSWMaxMixedA2SqBound
    exact mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (by
        simpa [adhwFQSWAPurity] using
          hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).marginalA.matrix))

/-- Fourth-root argument in the one-shot FQSW theorem of ADHW fqsw.tex
lines 553-568, assembled from the decoupling and max-mixed estimates in
ADHW fqsw.tex lines 580-841. -/
def adhwFQSWOneShotFourthRootArgument
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] : ℝ :=
  (2 * (Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
      ((Fintype.card q : ℝ) ^ 2)) *
    (adhwFQSWARPurity ψ + 2 * adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)

/-- ADHW one-shot FQSW trace-norm error bound from fqsw.tex lines 553-568. -/
def adhwFQSWOneShotErrorBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] : ℝ :=
  2 * Real.sqrt (Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q))

/-- The ADHW one-shot fourth-root argument is nonnegative. -/
theorem adhwFQSWOneShotFourthRootArgument_nonneg
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] :
    0 ≤ adhwFQSWOneShotFourthRootArgument ψ q := by
  have hfactor :
      0 ≤ 2 * (Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
        ((Fintype.card q : ℝ) ^ 2) := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _))
      (sq_nonneg _)
  have hAR : 0 ≤ adhwFQSWARPurity ψ := by
    simpa [adhwFQSWARPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).matrix
  have hA : 0 ≤ adhwFQSWAPurity ψ := by
    simpa [adhwFQSWAPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).marginalA.matrix
  have hR : 0 ≤ adhwFQSWRPurity ψ := by
    simpa [adhwFQSWRPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).marginalB.matrix
  unfold adhwFQSWOneShotFourthRootArgument
  exact mul_nonneg hfactor (by nlinarith)

/-- Scalar fourth-root simplification used by the i.i.d. FQSW bridge. -/
private theorem fqsw_two_sqrt_sqrt_le_sqrt8_mul_of_le_four_mul_fourth
    {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (hxt : x ≤ 4 * t ^ 4) :
    2 * Real.sqrt (Real.sqrt x) ≤ Real.sqrt 8 * t := by
  have ht_sq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have hinner :
      Real.sqrt x ≤ 2 * t ^ 2 := by
    have hright_nonneg : 0 ≤ 2 * t ^ 2 := by nlinarith
    have hsq :
        (Real.sqrt x) ^ 2 ≤ (2 * t ^ 2) ^ 2 := by
      rw [Real.sq_sqrt hx]
      have hright_sq : (2 * t ^ 2) ^ 2 = 4 * t ^ 4 := by ring
      rw [hright_sq]
      exact hxt
    exact (sq_le_sq₀ (Real.sqrt_nonneg x) hright_nonneg).mp hsq
  have hleft_nonneg : 0 ≤ 2 * Real.sqrt (Real.sqrt x) := by positivity
  have hright_nonneg : 0 ≤ Real.sqrt 8 * t := by
    exact mul_nonneg (Real.sqrt_nonneg _) ht
  have hsq :
      (2 * Real.sqrt (Real.sqrt x)) ^ 2 ≤ (Real.sqrt 8 * t) ^ 2 := by
    have hs8 : (Real.sqrt 8) ^ 2 = (8 : ℝ) :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
    have hsinner : (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt x :=
      Real.sq_sqrt (Real.sqrt_nonneg x)
    rw [mul_pow, mul_pow, hs8, hsinner]
    nlinarith
  exact (sq_le_sq₀ hleft_nonneg hright_nonneg).mp hsq

/-- If the one-shot fourth-root argument is bounded by the ADHW i.i.d.
exponential tail, then the one-shot error obeys the simplified i.i.d.
exponent. -/
theorem adhwFQSWOneShotErrorBound_le_iid_entropy_exponent_of_fourthRootArgument_le
    (φ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q]
    (n : ℕ) (δ : ℝ)
    (harg :
      adhwFQSWOneShotFourthRootArgument φ q ≤
        4 * (2 : ℝ) ^ (-(n : ℝ) * δ)) :
    adhwFQSWOneShotErrorBound φ q ≤
      Real.sqrt 8 * (2 : ℝ) ^ (-((n : ℝ) * δ / 4)) := by
  let X : ℝ := adhwFQSWOneShotFourthRootArgument φ q
  let T : ℝ := (2 : ℝ) ^ (-((n : ℝ) * δ / 4))
  have hX_nonneg : 0 ≤ X := by
    simpa [X] using adhwFQSWOneShotFourthRootArgument_nonneg φ q
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hT_four : T ^ 4 = (2 : ℝ) ^ (-(n : ℝ) * δ) := by
    dsimp [T]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hX_le : X ≤ 4 * T ^ 4 := by
    rw [hT_four]
    simpa [X] using harg
  simpa [adhwFQSWOneShotErrorBound, X, T] using
    fqsw_two_sqrt_sqrt_le_sqrt8_mul_of_le_four_mul_fourth hX_nonneg hT_nonneg hX_le

/-- Product-decoupling trace-norm average from the exact Hilbert--Schmidt
average in ADHW fqsw.tex lines 682-747. -/
theorem adhwFQSWProductDecouplingTraceNormAverageSq_le_of_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        adhwFQSWHSOneShotExact ψ q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e := by
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
        ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
          (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
            adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
            ∂unitaryHaarMeasure (a := Prod q e)) :=
          adhwFQSWProductDecouplingTraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
            ψ split
    _ ≤ (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e := by
          exact mul_le_mul_of_nonneg_left hHS
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Max-mixed `A₂` trace-norm average from the exact Hilbert--Schmidt
average in ADHW fqsw.tex lines 781-787. -/
theorem adhwFQSWMaxMixedA2TraceNormAverageSq_le_of_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) ≤
        adhwFQSWMaxMixedA2SqBound ψ q) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q := by
  exact
    (adhwFQSWMaxMixedA2TraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
      ψ split).trans hHS

omit [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] [Nonempty e] in
/-- ADHW fqsw.tex lines 747-760: after the Hilbert--Schmidt average has been
evaluated, Cauchy--Schwarz and the Schur-prefactor estimate imply the
trace-norm square bound.  This is the algebraic tail of the decoupling proof;
the preceding Schur integral identity is supplied separately. -/
theorem adhwFQSW_traceNormSqBound_of_HSOneShotExact
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    [Fintype q] [Fintype e] [Nonempty q] [Nonempty e] :
    (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e ≤
      adhwFQSWTraceNormDecouplingSqBound ψ q := by
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  let dr : ℝ := Fintype.card r
  let c : ℝ :=
    (dq * de ^ 2 - dq) / ((dq * de) ^ 2 - 1)
  let X : ℝ := adhwFQSWARPurity ψ
  let Y : ℝ := adhwFQSWAPurity ψ * adhwFQSWRPurity ψ
  let O : ℝ := adhwFQSWARProductOverlap ψ
  have hc_nonneg : 0 ≤ c := by
    simpa [c, dq, de] using adhwFQSW_HS_prefactor_nonneg q e
  have hc_le : c ≤ 1 / dq := by
    simpa [c, dq, de] using adhwFQSW_HS_prefactor_le_inv_card_q q e
  have hX_nonneg : 0 ≤ X := by
    simpa [X, adhwFQSWARPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).matrix
  have hY_nonneg : 0 ≤ Y := by
    exact mul_nonneg
      (by simpa [Y, adhwFQSWAPurity] using
        hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).marginalA.matrix))
      (by simpa [Y, adhwFQSWRPurity] using
        hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).marginalB.matrix))
  have hO_nonneg : 0 ≤ O := by
    simpa [O] using adhwFQSWARProductOverlap_nonneg ψ
  have hbracket_le : X - 2 * O + Y ≤ X + Y := by
    nlinarith
  have hsum_nonneg : 0 ≤ X + Y := by nlinarith
  have hc_mul :
      c * (X - 2 * O + Y) ≤ (1 / dq) * (X + Y) := by
    calc
      c * (X - 2 * O + Y) ≤ c * (X + Y) :=
        mul_le_mul_of_nonneg_left hbracket_le hc_nonneg
      _ ≤ (1 / dq) * (X + Y) :=
        mul_le_mul_of_nonneg_right hc_le hsum_nonneg
  have hcard_a : (Fintype.card a : ℝ) = dq * de := by
    have hnat : Fintype.card a = Fintype.card (Prod q e) :=
      Fintype.card_congr split
    rw [Fintype.card_prod] at hnat
    dsimp [dq, de]
    exact_mod_cast hnat
  unfold adhwFQSWHSOneShotExact adhwFQSWTraceNormDecouplingSqBound
  change de * dr * (c * (X - 2 * O + Y)) ≤
    ((Fintype.card a : ℝ) * dr / dq ^ 2) * (X + Y)
  rw [hcard_a]
  have hdq_pos : 0 < dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  have hscale_nonneg : 0 ≤ de * dr := by
    dsimp [de, dr]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hc_mul hscale_nonneg
  convert hscaled using 1
  field_simp [ne_of_gt hdq_pos]

/-- Source-route Schur twirling record for ADHW fqsw.tex lines 642-678, the
Schur step inside the decoupling proof of fqsw.tex lines 580-841. -/
structure ADHWSchurTwirling
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] where
  pCoeff : ℝ
  qCoeff : ℝ
  pCoeff_eq : pCoeff = adhwFQSWSchurPCoeff q e
  qCoeff_eq : qCoeff = adhwFQSWSchurQCoeff q e

/-- Source-route Hilbert--Schmidt one-shot bound record for ADHW fqsw.tex
lines 680-747. -/
structure ADHWHSOneShotBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] where
  schur : ADHWSchurTwirling ψ q e
  hsAverage : ℝ
  hsAverage_eq : hsAverage = adhwFQSWHSOneShotExact ψ q e

/-- The source Schur-coefficient record is canonical: its fields are the two
coefficients appearing in ADHW fqsw.tex lines 642-678. -/
def adhwFQSWSchurTwirling
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ADHWSchurTwirling ψ q e where
  pCoeff := adhwFQSWSchurPCoeff q e
  qCoeff := adhwFQSWSchurQCoeff q e
  pCoeff_eq := rfl
  qCoeff_eq := rfl

/-- The source Hilbert--Schmidt one-shot expression record is canonical once
the Schur coefficients have been fixed. -/
def adhwFQSWHSOneShotBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ADHWHSOneShotBound ψ q e where
  schur := adhwFQSWSchurTwirling ψ q e
  hsAverage := adhwFQSWHSOneShotExact ψ q e
  hsAverage_eq := rfl

/-- Source-route ADHW trace-norm decoupling record for fqsw.tex lines 580-760,
including the Schur/HS route from fqsw.tex lines 642-747. -/
structure ADHWTraceNormDecouplingBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    (split : a ≃ Prod q e)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  hs : ADHWHSOneShotBound ψ q e
  traceNormAverageSq_le :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
    adhwFQSWTraceNormDecouplingSqBound ψ q

/-- Source-route max-mixed `A₂` estimate record for ADHW fqsw.tex lines
767-795. -/
structure ADHWMaxMixedA2Estimate
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    (split : a ≃ Prod q e)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  schur : ADHWSchurTwirling ψ q e
  maxMixedAverageSq_le :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
    adhwFQSWMaxMixedA2SqBound ψ q

/-- Split-specific trace-norm square-average tail for the product-decoupling
component.  The explicit hypothesis is the remaining Schur/HS average bridge
for the split unitary integrand; from that bridge the dimension Cauchy--Schwarz
tail and the ADHW `1/d_{A₁}` prefactor estimate give the public square bound. -/
theorem adhwFQSWProductDecouplingTraceNormAverageSq_le
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
    adhwFQSWTraceNormDecouplingSqBound ψ q :=
  hHS.trans (adhwFQSW_traceNormSqBound_of_HSOneShotExact ψ split)

/-- Split-specific trace-norm square-average tail for the max-mixed `A₂`
component.  The explicit hypothesis is exactly the remaining Schur/max-mixed
average estimate for the split unitary integrand. -/
theorem adhwFQSWMaxMixedA2TraceNormAverageSq_le
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hMaxMixed :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
    adhwFQSWMaxMixedA2SqBound ψ q :=
  hMaxMixed

/-- Constructor for the split-specific ADHW trace-norm decoupling component
record, once the product-decoupling Schur/HS average bridge is available. -/
theorem exists_adhwFQSWTraceNormDecouplingBound
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e) :
    Nonempty (ADHWTraceNormDecouplingBound ψ q e split) := by
  refine ⟨?_⟩
  exact
    { hs := adhwFQSWHSOneShotBound ψ q e
      traceNormAverageSq_le :=
        adhwFQSWProductDecouplingTraceNormAverageSq_le ψ split hHS }

/-- Constructor for the split-specific ADHW trace-norm decoupling record from
the exact product-decoupling Hilbert--Schmidt average in fqsw.tex lines
682-747. -/
theorem exists_adhwFQSWTraceNormDecouplingBound_of_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        adhwFQSWHSOneShotExact ψ q e) :
    Nonempty (ADHWTraceNormDecouplingBound ψ q e split) := by
  exact exists_adhwFQSWTraceNormDecouplingBound ψ split
    (adhwFQSWProductDecouplingTraceNormAverageSq_le_of_hilbertSchmidtAverage
      ψ split hHS)

/-- Constructor for the split-specific ADHW max-mixed `A₂` component record,
once the max-mixed Schur average estimate is available. -/
theorem exists_adhwFQSWMaxMixedA2Estimate
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hMaxMixed :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q) :
    Nonempty (ADHWMaxMixedA2Estimate ψ q e split) := by
  refine ⟨?_⟩
  exact
    { schur := adhwFQSWSchurTwirling ψ q e
      maxMixedAverageSq_le :=
        adhwFQSWMaxMixedA2TraceNormAverageSq_le ψ split hMaxMixed }

/-- Constructor for the split-specific ADHW max-mixed `A₂` record from the
exact Hilbert--Schmidt average in fqsw.tex lines 781-787. -/
theorem exists_adhwFQSWMaxMixedA2Estimate_of_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hHS :
      (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := Prod q e)) ≤
        adhwFQSWMaxMixedA2SqBound ψ q) :
    Nonempty (ADHWMaxMixedA2Estimate ψ q e split) := by
  exact exists_adhwFQSWMaxMixedA2Estimate ψ split
    (adhwFQSWMaxMixedA2TraceNormAverageSq_le_of_hilbertSchmidtAverage
      ψ split hHS)

/-- The two source-route component square-average records imply the final ADHW
decoupling square-average bound after the triangle/product-contraction step. -/
theorem adhwFQSWFinalTraceNormAverageSq_le_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q := by
  calc
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
        2 * (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
          ∂unitaryHaarMeasure (a := Prod q e)) +
        2 * (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
          ∂unitaryHaarMeasure (a := Prod q e)) :=
      adhwFQSWCombinedTraceNormAverageSq_le_two_component_averages ψ split
    _ ≤ 2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q := by
      nlinarith [D.traceNormAverageSq_le, M.maxMixedAverageSq_le]

/-- The final ADHW trace-norm average is bounded by the square root of its
source component square-average bounds. -/
theorem adhwFQSWFinalTraceNormAverage_le_sqrt_source_bounds
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      Real.sqrt (2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q) := by
  have hL2 :=
    integral_le_sqrt_integral_sq_of_nonneg
      (μ := unitaryHaarMeasure (a := Prod q e))
      (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (by
        filter_upwards with U
        exact traceNormDistance_nonneg _ _)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
  have hsq := adhwFQSWFinalTraceNormAverageSq_le_component_records ψ split D M
  exact hL2.trans (Real.sqrt_le_sqrt hsq)

/-- Component-record Haar-selection input: if the source algebraic component
bound is below the ADHW fourth-root argument, the averaged final trace-norm
integrand satisfies the one-shot selection radius. -/
theorem adhwFQSWFinalTraceNormAverage_le_oneShotFourthRoot_of_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r))
    (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q) :
    (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := Prod q e)) ≤
      Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q) := by
  exact (adhwFQSWFinalTraceNormAverage_le_sqrt_source_bounds ψ split D M).trans
    (Real.sqrt_le_sqrt hsource)

/-- The two source-route square-average component bounds are absorbed by the
single fourth-root argument in ADHW `thm:trueoneShotMother`.  The only
substantive inequality is the trace-one purity lower bound
`1 ≤ d_R Tr[(ψ^R)^2]`, applied to the reference marginal. -/
theorem adhwFQSW_source_component_bounds_le_oneShotFourthRootArgument
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] :
    2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
      2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
        adhwFQSWOneShotFourthRootArgument ψ q := by
  have hR : (1 : ℝ) ≤ (Fintype.card r : ℝ) * adhwFQSWRPurity ψ := by
    simpa [adhwFQSWRPurity] using
      (State.one_le_card_mul_hilbertSchmidtSq_matrix
        (ρ := (adhwFQSWARState ψ).marginalB))
  have hA_nonneg : 0 ≤ adhwFQSWAPurity ψ := by
    exact hilbertSchmidtSq_nonneg _
  have hfactor_nonneg :
      0 ≤ (Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2) := by
    exact div_nonneg
      (by exact_mod_cast Nat.zero_le (Fintype.card a))
      (sq_nonneg _)
  have hmaxMixed_absorbed :
      ((Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2)) *
          adhwFQSWAPurity ψ ≤
        ((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
            ((Fintype.card q : ℝ) ^ 2)) *
          adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
    have hmul := mul_le_mul_of_nonneg_left hR hfactor_nonneg
    have hmulA := mul_le_mul_of_nonneg_right hmul hA_nonneg
    convert hmulA using 1 <;> ring
  unfold adhwFQSWTraceNormDecouplingSqBound adhwFQSWMaxMixedA2SqBound
    adhwFQSWOneShotFourthRootArgument
  calc
    2 *
          ((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
              (Fintype.card q : ℝ) ^ 2 *
            (adhwFQSWARPurity ψ + adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)) +
        2 * ((Fintype.card a : ℝ) / (Fintype.card q : ℝ) ^ 2 *
            adhwFQSWAPurity ψ) ≤
        2 *
          ((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
              (Fintype.card q : ℝ) ^ 2 *
            (adhwFQSWARPurity ψ + adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)) +
          2 * (((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
              ((Fintype.card q : ℝ) ^ 2)) *
            adhwFQSWAPurity ψ * adhwFQSWRPurity ψ) := by
          nlinarith
    _ = 2 * (Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
          (Fintype.card q : ℝ) ^ 2 *
        (adhwFQSWARPurity ψ + 2 * adhwFQSWAPurity ψ * adhwFQSWRPurity ψ) := by
          ring

/-- The ADHW one-shot RHS is nonnegative. -/
theorem adhwFQSWOneShotErrorBound_nonneg
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) [Fintype q] :
    0 ≤ adhwFQSWOneShotErrorBound ψ q :=
  mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- One-shot ADHW protocol assembly from a selected Alice isometry satisfying
the source decoupling radius.  This is the Uhlmann/protocol part of
`thm:trueoneShotMother` after the Haar-selection step has supplied the
concrete `U`. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
    (ψ : PureVector (Prod (Prod a b) r))
    (U : ReferenceIsometry a (Prod q e)) (pairing : e ≃ et)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) et))
    (hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
          (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ C : FQSWOneShotProtocol ψ q e et,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨C, hC⟩ :=
    exists_fqswOneShotProtocol_traceNormError_le_of_decoupling
      ψ U pairing ((1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q))
      hcardTarget hcardRef hdec
  refine ⟨C, hC.trans ?_⟩
  rw [adhwFQSWOneShotErrorBound]
  ring_nf
  exact le_rfl

/-- Source-split one-shot ADHW assembly after Haar selection: once the
source factorization `A = A₁ × A₂` supplies Alice's isometry and the selected
decoupling estimate holds, the concrete FQSW protocol obeys the source
one-shot trace-norm bound. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_split_selected_decoupling
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplit split)).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
          (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q :=
  exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
    ψ (adhwFQSWAliceIsometryOfSplit split) (Equiv.refl e) hcardTarget hcardRef hdec

/-- Source-split one-shot ADHW assembly from the trace-norm decoupling
integrand used by the Haar-selection step.  This is the bridge from the
selected split-unitary trace-norm estimate to the computed FQSW protocol. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_split_unitary_traceNorm_decoupling
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (U : Matrix.unitaryGroup (Prod q e) ℂ)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (htrace :
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  have hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
          (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q) := by
    rw [adhwFQSWDecoupling_normalizedTraceDistance_eq_half_integrand]
    exact mul_le_mul_of_nonneg_left htrace (by norm_num)
  exact exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
    ψ (adhwFQSWAliceIsometryOfSplitUnitary split U) (Equiv.refl e)
    hcardTarget hcardRef hdec

/-- Haar-selection form of the ADHW one-shot route: an averaged trace-norm
decoupling estimate over unitaries on the split `A₁ × A₂` register selects a
concrete split-unitary FQSW protocol. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_split_unitary_haar_average
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (havg :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨U, hU⟩ :=
    unitaryHaar_exists_le_of_integral_le
      (a := Prod q e)
      (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split) havg
  exact exists_fqswOneShotProtocol_traceNormError_le_of_split_unitary_traceNorm_decoupling
    ψ split U hcardTarget hcardRef hU

/-- Output of the Haar-selection/decoupling stage of the ADHW one-shot proof:
a concrete Alice isometry satisfying the source decoupling radius, together
with the finite-dimensional reference-size side conditions needed by the
Uhlmann assembly step. -/
structure ADHWFQSWSelectedDecouplingIsometry
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  aliceIsometry : ReferenceIsometry a (Prod q e)
  ebitPairing : e ≃ et
  target_ref_card_le : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b)
  bob_ref_card_le : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) et)
  decoupling_le :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ aliceIsometry).normalizedTraceDistance
      ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
        (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)

namespace ADHWFQSWSelectedDecouplingIsometry

variable {ψ : PureVector (Prod (Prod a b) r)}
variable (S : ADHWFQSWSelectedDecouplingIsometry ψ q e et)

/-- The selected ADHW decoupling isometry supplies a concrete one-shot FQSW
protocol. -/
noncomputable def toOneShotProtocol : FQSWOneShotProtocol ψ q e et :=
  Classical.choose
    (exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
      ψ S.aliceIsometry S.ebitPairing S.target_ref_card_le S.bob_ref_card_le S.decoupling_le)

/-- The protocol constructed from the selected decoupling isometry obeys the
ADHW one-shot trace-norm bound. -/
theorem toOneShotProtocol_traceNormError_le :
    S.toOneShotProtocol.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q :=
  (Classical.choose_spec
    (exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
      ψ S.aliceIsometry S.ebitPairing S.target_ref_card_le S.bob_ref_card_le S.decoupling_le))

end ADHWFQSWSelectedDecouplingIsometry

/-- A selected decoupling isometry closes the one-shot ADHW protocol theorem
shape.  The remaining upstream task is to prove such an isometry exists from
the Schur/HS/Haar route. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling
    (ψ : PureVector (Prod (Prod a b) r))
    (S : ADHWFQSWSelectedDecouplingIsometry ψ q e et) :
    ∃ C : FQSWOneShotProtocol ψ q e et,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q :=
  ⟨S.toOneShotProtocol, S.toOneShotProtocol_traceNormError_le⟩

/-- Haar-selection form that produces the selected-decoupling record used by
the source-route one-shot theorem.  The remaining upstream task is the ADHW
Schur/HS calculation proving the averaged trace-norm bound. -/
theorem exists_adhwFQSWSelectedDecouplingIsometry_of_split_unitary_haar_average
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (havg :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ S : ADHWFQSWSelectedDecouplingIsometry ψ q e e,
      S.aliceIsometry =
        adhwFQSWAliceIsometryOfSplitUnitary split
          (Classical.choose
            (unitaryHaar_exists_le_of_integral_le
              (a := Prod q e)
              (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
                adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
              (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split)
              havg)) := by
  let hsel :=
    unitaryHaar_exists_le_of_integral_le
      (a := Prod q e)
      (f := fun U : Matrix.unitaryGroup (Prod q e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split) havg
  let U : Matrix.unitaryGroup (Prod q e) ℂ := Classical.choose hsel
  have hU :
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q) :=
    Classical.choose_spec hsel
  have hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
          (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q) := by
    rw [adhwFQSWDecoupling_normalizedTraceDistance_eq_half_integrand]
    exact mul_le_mul_of_nonneg_left hU (by norm_num)
  refine ⟨{ aliceIsometry := adhwFQSWAliceIsometryOfSplitUnitary split U
            ebitPairing := Equiv.refl e
            target_ref_card_le := hcardTarget
            bob_ref_card_le := hcardRef
            decoupling_le := hdec }, ?_⟩
  rfl

/-- Source-component form of Haar selection: the Schur/HS decoupling record,
the max-mixed `A₂` record, and the source algebraic absorption inequality
select a concrete Alice isometry for the ADHW one-shot protocol route. -/
theorem exists_adhwFQSWSelectedDecouplingIsometry_of_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    Nonempty (ADHWFQSWSelectedDecouplingIsometry ψ q e e) := by
  have havg :=
    adhwFQSWFinalTraceNormAverage_le_oneShotFourthRoot_of_component_records
      ψ split D M hsource
  obtain ⟨S, _hS⟩ :=
    exists_adhwFQSWSelectedDecouplingIsometry_of_split_unitary_haar_average
      ψ split hcardTarget hcardRef havg
  exact ⟨S⟩

/-- Source-component one-shot protocol theorem: once the Schur/HS
decoupling record, max-mixed `A₂` record, source algebraic absorption
inequality, and Uhlmann dimension side conditions are available, the ADHW
one-shot FQSW protocol exists with the source trace-norm error bound. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨S⟩ :=
    exists_adhwFQSWSelectedDecouplingIsometry_of_component_records
      ψ split D M hsource hcardTarget hcardRef
  exact exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling ψ S

/-- Source-closed component-record one-shot theorem: the ADHW source algebra
absorbs the trace-norm decoupling and max-mixed `A₂` component bounds into the
single one-shot fourth-root argument, so callers no longer provide that
inequality as an external hypothesis. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_source_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  exact exists_fqswOneShotProtocol_traceNormError_le_of_component_records
    ψ split D M
    (adhwFQSW_source_component_bounds_le_oneShotFourthRootArgument ψ q)
    hcardTarget hcardRef

/-- One-shot FQSW theorem-shape record for
`thm:trueoneShotMother` in ADHW fqsw.tex lines 553-568.  Its proof route is
the ADHW decoupling, max-mixed `A₂`, Haar-selected Alice isometry, and Uhlmann
assembly in fqsw.tex lines 580-841.  The protocol is computed from the selected
decoupling data rather than stored as an independent field. -/
structure ADHWFQSWOneShotBound
    (ψ : PureVector (Prod (Prod a b) r)) (q : Type x) (e : Type y)
    (split : a ≃ Prod q e)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  traceNormDecoupling : ADHWTraceNormDecouplingBound ψ q e split
  maxMixedA2 : ADHWMaxMixedA2Estimate ψ q e split
  selectedDecoupling : ADHWFQSWSelectedDecouplingIsometry ψ q e e

namespace ADHWFQSWOneShotBound

variable {ψ : PureVector (Prod (Prod a b) r)}
variable {split : a ≃ Prod q e}
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable (H : ADHWFQSWOneShotBound ψ q e split)

/-- The assembled ADHW one-shot bound record computes the concrete one-shot
protocol by delegating to its selected decoupling witness. -/
noncomputable def toOneShotProtocol : FQSWOneShotProtocol ψ q e e :=
  ADHWFQSWSelectedDecouplingIsometry.toOneShotProtocol H.selectedDecoupling

omit [Fintype q] [DecidableEq q] [Nonempty q] [Fintype e] [DecidableEq e] [Nonempty e] in
/-- The computed protocol of an assembled ADHW one-shot bound satisfies the
standard ADHW one-shot trace-norm error bound. -/
theorem toOneShotProtocol_traceNormError_le
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (H : ADHWFQSWOneShotBound ψ q e split) :
    H.toOneShotProtocol.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q :=
  ADHWFQSWSelectedDecouplingIsometry.toOneShotProtocol_traceNormError_le
    H.selectedDecoupling

end ADHWFQSWOneShotBound

/-- Assemble the ADHW one-shot bound record from source-route decoupling and
max-mixed records once the Haar average has selected the concrete split-unitary
decoupling isometry. -/
theorem exists_adhwFQSWOneShotBound_of_split_unitary_haar_average
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e))
    (havg :
      (∫ U : Matrix.unitaryGroup (Prod q e) ℂ,
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := Prod q e)) ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ H : ADHWFQSWOneShotBound ψ q e split,
      H.traceNormDecoupling = D ∧ H.maxMixedA2 = M := by
  obtain ⟨S, _hS⟩ :=
    exists_adhwFQSWSelectedDecouplingIsometry_of_split_unitary_haar_average
      ψ split hcardTarget hcardRef havg
  exact ⟨{ traceNormDecoupling := D
           maxMixedA2 := M
           selectedDecoupling := S }, rfl, rfl⟩

/-- Assemble the ADHW one-shot bound record directly from the source component
records and the algebraic absorption inequality, without taking an averaged
trace-norm bound as an external input. -/
theorem exists_adhwFQSWOneShotBound_of_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ H : ADHWFQSWOneShotBound ψ q e split,
      H.traceNormDecoupling = D ∧ H.maxMixedA2 = M := by
  obtain ⟨S⟩ :=
    exists_adhwFQSWSelectedDecouplingIsometry_of_component_records
      ψ split D M hsource hcardTarget hcardRef
  exact ⟨{ traceNormDecoupling := D
           maxMixedA2 := M
           selectedDecoupling := S }, rfl, rfl⟩

/-- Source-closed assembly of the ADHW one-shot bound record from the two
component records and the Uhlmann dimension side conditions. -/
theorem exists_adhwFQSWOneShotBound_of_source_component_records
    [Nonempty q]
    (ψ : PureVector (Prod (Prod a b) r)) (split : a ≃ Prod q e)
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ H : ADHWFQSWOneShotBound ψ q e split,
      H.traceNormDecoupling = D ∧ H.maxMixedA2 = M := by
  exact exists_adhwFQSWOneShotBound_of_component_records
    ψ split D M
    (adhwFQSW_source_component_bounds_le_oneShotFourthRootArgument ψ q)
    hcardTarget hcardRef



namespace PureVector

variable (ψ : PureVector (Prod (Prod a b) r))

/-- Public one-shot FQSW theorem-shape projection.  The source split
`A = A₁ × A₂`, together with the finite-dimensional side conditions needed by
the Uhlmann/Bob-isometry assembly, produces the protocol promised by
ADHW `thm:trueoneShotMother` (fqsw.tex lines 553-568).  Internally this is
assembled from the Schur twirl, Hilbert--Schmidt calculation, trace-norm
decoupling, max-mixed `A₂` estimate, Haar selection, and Uhlmann step in
fqsw.tex lines 580-841. -/
theorem exists_fqswOneShotProtocol_traceNormError_le
    [Nonempty q]
    (split : a ≃ Prod q e)
    (hcardTarget : Fintype.card (Prod e r) ≤ Fintype.card (Prod q b))
    (hcardRef : Fintype.card (Prod q b) ≤ Fintype.card (Prod (Prod a b) e)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨D⟩ :=
    exists_adhwFQSWTraceNormDecouplingBound_of_hilbertSchmidtAverage ψ split
      (adhwFQSWProductDecouplingHilbertSchmidtAverage_le ψ split)
  obtain ⟨M⟩ :=
    exists_adhwFQSWMaxMixedA2Estimate_of_hilbertSchmidtAverage ψ split
      (adhwFQSWMaxMixedA2HilbertSchmidtAverage_le ψ split)
  exact exists_fqswOneShotProtocol_traceNormError_le_of_source_component_records
    ψ split D M hcardTarget hcardRef

end PureVector

end

end QIT
