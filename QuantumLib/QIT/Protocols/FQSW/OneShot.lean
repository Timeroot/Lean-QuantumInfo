/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.OneShot.Decoupling
public import QuantumLib.QIT.Information.Entropy.EntropyTensorPower
public import QuantumLib.QIT.Protocols.FQSW.Core
public import QuantumLib.QIT.OneShot.GentleMeasurement
public import QuantumLib.QIT.States.Geometry.FuchsVdG
public import QuantumLib.QIT.States.Purification.Schatten
public import QuantumLib.QIT.Channels.Diamond
public import QuantumLib.QIT.Util.MatrixInstances

/-!
# The one-shot FQSW theorem

Given a split `A ≃ A₁ × A₂`, there is a one-shot protocol whose trace-norm error is at most
`adhwFQSWOneShotErrorBound ψ A₁`, the fourth root of `2 d_A d_R / d_{A₁}²` times the purity
combination `Tr[(ψ^{AR})²] + 2 Tr[(ψ^A)²] Tr[(ψ^R)²]`.  This is the mother protocol of
[AbeyesingheDevetakHaydenWinter2006Mother, fqsw.tex:553-568], and
`Ket.exists_fqswOneShotProtocol_traceNormError_le` is the projection of it that the i.i.d. layers
consume.

The proof is the decoupling argument.  Alice's isometry is the split followed by a Haar-random
unitary on `A₁ × A₂`, and one bounds the Haar average of two trace norms: the distance of the `A₂R`
marginal from the product of its own marginals, and the distance of the `A₂` marginal from
maximally mixed.  Both averages are computed exactly in Hilbert--Schmidt norm after a Schur twirl
and then converted by Cauchy--Schwarz; together they say that `A₂R` is close to
`(I/d_{A₂}) ⊗ ψ^R`, so `A₂` is decoupled from the reference.  Uhlmann's theorem then supplies
Bob's isometry, because purifications of nearby states are related by an isometry on the purifying
side.

The intermediate estimates are packaged as records -- `ADHWSchurTwirling`, `ADHWHSOneShotBound`,
`ADHWTraceNormDecouplingBound`, `ADHWMaxMixedA2Estimate`, `ADHWFQSWSelectedDecouplingIsometry` and
`ADHWFQSWOneShotBound` -- each carrying the inequality it stands for.  Every step therefore has an
`exists_..._of_...` form taking the previous record, so a caller holding one of the intermediate
bounds can enter the chain partway along.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker QIT.MatrixL2

noncomputable section
universe u v w x y z p u1 v1 w1

open QIT

namespace QIT

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

/-- Alice/reference marginal `ψ^{AR}` used by the ADHW one-shot FQSW proof
route. -/
def adhwFQSWARState (ψ : Ket ((a × b) × r)) : MState (a × r) :=
  ψ.state.coherentTransferReferenceState

/-- Alice's source split isometry induced by the source assumption
`A = A₁ × A₂` in ADHW `thm:trueoneShotMother` (fqsw.tex lines 553-568). -/
def adhwFQSWAliceIsometryOfSplit (split : a ≃ (q × e)) :
    ReferenceIsometry a (q × e) :=
  ReferenceIsometry.ofEquiv split

/-- Alice's source split followed by a unitary on the split `A₁ × A₂`
register, matching the Haar-random unitary stage in ADHW fqsw.tex
lines 580-841. -/
def adhwFQSWAliceIsometryOfSplitUnitary
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) :
    ReferenceIsometry a (q × e) :=
  (ReferenceUnitary.toReferenceIsometry ({ matrix := U } : ReferenceUnitary (q × e))).comp
    (adhwFQSWAliceIsometryOfSplit split)

/-- The post-Alice state before Bob's isometry, for a concrete Alice isometry
`U : A → A₁A₂`. -/
def adhwFQSWPostAliceStateOfIsometry
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) :
    MState ((q × e) × (b × r)) :=
  let ψA : Ket (a × (b × r)) :=
    ψ.reindex (Equiv.prodAssoc a b r)
  (U.applyKet ψA).state

/-- The post-Alice ket regrouped as a purification of the decoupling
marginal `σ^{A₂R}(U)`, with Bob's side `A₁B` as the purifying reference. -/
def adhwFQSWPostAliceA2RPurificationOfIsometry
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) :
    Ket ((q × b) × (e × r)) :=
  let ψA : Ket (a × (b × r)) :=
    ψ.reindex (Equiv.prodAssoc a b r)
  (U.applyKet ψA).reindex (Equiv.prodProdProdComm q e b r)

/-- The decoupling marginal `σ^{A₂R}(U)` from ADHW fqsw.tex lines 580-841. -/
def adhwFQSWSigmaA2RStateOfIsometry
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) : MState (e × r) :=
  ((adhwFQSWPostAliceStateOfIsometry ψ U).reindex
    (Equiv.prodProdProdComm q e b r)).traceLeft

omit [Nonempty e] in
/-- The regrouped post-Alice ket purifies the ADHW decoupling marginal
`σ^{A₂R}(U)`. -/
theorem adhwFQSWPostAliceA2RPurificationOfIsometry_purifies
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) :
    (adhwFQSWPostAliceA2RPurificationOfIsometry (q := q) (e := e) ψ U).Purifies
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U) := by
  dsimp [adhwFQSWPostAliceA2RPurificationOfIsometry,
    adhwFQSWSigmaA2RStateOfIsometry, adhwFQSWPostAliceStateOfIsometry]
  rw [← Ket.reindex_state]
  exact Ket.purifies_traceLeft _

/-- The `A₂` marginal `σ^{A₂}(U)` in ADHW fqsw.tex lines 767-795. -/
def adhwFQSWSigmaA2StateOfIsometry
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) : MState e :=
  (adhwFQSWSigmaA2RStateOfIsometry (q := q) ψ U).traceRight

/-- The reference marginal `σ^R`, unchanged by Alice's isometry in the ADHW
one-shot proof route. -/
def adhwFQSWSigmaRState (ψ : Ket ((a × b) × r)) : MState r :=
  (adhwFQSWARState ψ).traceLeft

/-- If the left subsystem has only one basis element, every bipartite state is
the product of its two marginals. -/
theorem state_matrix_eq_prod_marginals_of_subsingleton_left
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Subsingleton α] (ρ : MState (α × β)) :
    ρ.m = (ρ.traceRight.prod ρ.traceLeft).m := by
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  have hxy : xa = ya := Subsingleton.elim _ _
  subst ya
  have hA : ρ.traceRight.m xa xa = 1 := by
    have htrace := ρ.traceRight.tr'
    rw [Matrix.trace] at htrace
    have hsum :
        (∑ x : α, ρ.traceRight.m x x) =
          ρ.traceRight.m xa xa := by
      apply Finset.sum_eq_single xa
      · intro b _ hb
        exact False.elim (hb (Subsingleton.elim b xa))
      · intro h
        exact False.elim (h (Finset.mem_univ xa))
    have hsum_diag :
        (∑ x : α, Matrix.diag ρ.traceRight.m x) =
          ρ.traceRight.m xa xa := by
      simpa [Matrix.diag] using hsum
    rw [hsum_diag] at htrace
    exact htrace
  have hB : ρ.traceLeft.m xb yb = ρ.m (xa, xb) (xa, yb) := by
    rw [MState.traceLeft_m]
    simp [Matrix.traceLeft]
    exact Finset.sum_eq_single xa
      (by intro b _ hb; exact False.elim (hb (Subsingleton.elim b xa)))
      (by intro h; exact False.elim (h (Finset.mem_univ xa)))
  rw [MState.prod_m]
  change ρ.m (xa, xb) (xa, yb) =
    ρ.traceRight.m xa xa * ρ.traceLeft.m xb yb
  rw [hA, hB]
  simp

/-- The ADHW notation `σ^R` is the `R` marginal of the original pure source. -/
theorem adhwFQSWSigmaRState_eq_source_traceLeft
    (ψ : Ket ((a × b) × r)) :
    adhwFQSWSigmaRState ψ = ψ.state.traceLeft := by
  apply MState.ext
  ext x y
  simp [adhwFQSWSigmaRState, adhwFQSWARState,
    MState.coherentTransferReferenceState, Matrix.traceLeft, Fintype.sum_prod_type]

omit [Nonempty e] in
/-- Regrouping Alice's post-isometry state into `A₁B × A₂R` and then tracing
down to `R` is the same as tracing the original post-isometry state down to
`BR` and then to `R`.  This is the register-bookkeeping part of the ADHW
one-shot route before the Schur/HS moment calculation. -/
theorem adhwFQSW_traceLeft_traceLeft_reindex_a2r
    (ρ : MState ((q × e) × (b × r))) :
    ((ρ.reindex (Equiv.prodProdProdComm q e b r)).traceLeft).traceLeft =
      ρ.traceLeft.traceLeft := by
  apply MState.ext
  ext x y
  simp [Equiv.prodProdProdComm, Matrix.traceLeft,
    Fintype.sum_prod_type]
  calc
    (∑ ee : e, ∑ qq : q, ∑ bb : b,
      ρ.m ((qq, ee), bb, x) ((qq, ee), bb, y)) =
        (∑ qq : q, ∑ ee : e, ∑ bb : b,
          ρ.m ((qq, ee), bb, x) ((qq, ee), bb, y)) := by
          rw [Finset.sum_comm]
    _ = (∑ qq : q, ∑ bb : b, ∑ ee : e,
          ρ.m ((qq, ee), bb, x) ((qq, ee), bb, y)) := by
          apply Finset.sum_congr rfl
          intro qq _
          rw [Finset.sum_comm]
    _ = (∑ bb : b, ∑ qq : q, ∑ ee : e,
          ρ.m ((qq, ee), bb, x) ((qq, ee), bb, y)) := by
          rw [Finset.sum_comm]

/-- Alice's source-to-input reindexing leaves the final reference marginal
as the `R` marginal used in the ADHW FQSW source route. -/
theorem adhwFQSW_sourceInput_traceLeft_traceLeft
    (ψ : Ket ((a × b) × r)) :
    (ψ.reindex (Equiv.prodAssoc a b r)).state.traceLeft.traceLeft =
      adhwFQSWSigmaRState ψ := by
  apply MState.ext
  ext x y
  simp [adhwFQSWSigmaRState, adhwFQSWARState,
    MState.coherentTransferReferenceState, Ket.state, Equiv.prodAssoc,
    Matrix.traceLeft]
  rw [Finset.sum_comm]

omit [Nonempty e] in
/-- Tracing Bob's register after Alice's isometry is the same as applying the
Alice isometry directly to the source `AR` marginal.  This is the register
bridge that lets the ADHW Schur/HS calculation work on `ψ^{AR}` while the
operational protocol is computed from the full pure source `ψ^{ABR}`. -/
theorem adhwFQSWPostAliceStateOfIsometry_coherentTransferReference_matrix
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) :
    (((adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).reindex
      (Equiv.prodAssoc (q × e) b r).symm).coherentTransferReferenceState).m =
      U.applyMatrix (adhwFQSWARState ψ).m := by
  ext x y
  simp [adhwFQSWPostAliceStateOfIsometry, adhwFQSWARState,
    MState.coherentTransferReferenceState, Ket.state,
    Equiv.prodAssoc, ReferenceIsometry.applyKet,
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
theorem adhwFQSWSigmaA2RStateOfIsometry_eq_postAliceAR_traceLeft
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) :
    adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U =
      ((((adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).reindex
        (Equiv.prodAssoc (q × e) b r).symm).coherentTransferReferenceState).reindex
          (Equiv.prodAssoc q e r)).traceLeft := by
  apply MState.ext
  ext x y
  simp [adhwFQSWSigmaA2RStateOfIsometry, MState.coherentTransferReferenceState,
    Equiv.prodProdProdComm,
    Equiv.prodAssoc, Matrix.traceLeft,
    Fintype.sum_prod_type]

omit [Nonempty e] in
/-- Matrix form of the ADHW decoupling marginal: `σ^{A₂R}(U)` is the
`A₂R` marginal of the source `AR` state after Alice's split isometry.  This is
the exact bridge from the operational full-source protocol state to the
source's Schur/HS one-shot calculation on `ψ^{AR}`. -/
theorem adhwFQSWSigmaA2RStateOfIsometry_matrix_eq_traceLeft_applyMatrix_AR
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).m =
      Matrix.traceLeft
        ((U.applyMatrix (adhwFQSWARState ψ).m).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm) := by
  rw [adhwFQSWSigmaA2RStateOfIsometry_eq_postAliceAR_traceLeft, MState.traceLeft_m,
    MState.reindex_matrix, adhwFQSWPostAliceStateOfIsometry_coherentTransferReference_matrix]

omit [Nonempty e] in
/-- The reference marginal `σ^R` in the ADHW one-shot proof is independent of
Alice's isometry.  This is the formal source-route bridge that justifies using
a fixed `σ^R` in the product term
`σ^{A₂}(U) ⊗ σ^R`. -/
theorem adhwFQSWSigmaA2RStateOfIsometry_traceLeft_eq_sigmaR
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).traceLeft =
      adhwFQSWSigmaRState ψ := by
  have hpost :
      (adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).traceLeft =
        (ψ.reindex (Equiv.prodAssoc a b r)).state.traceLeft := by
    let Ψ : Ket (a × (b × r)) :=
      ψ.reindex (Equiv.prodAssoc a b r)
    have hpur : (U.applyKet Ψ).Purifies Ψ.state.traceLeft := by
      exact U.applyKet_purifies (Ket.purifies_traceLeft Ψ)
    apply MState.ext
    rw [MState.traceLeft_m]
    exact hpur
  calc
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).traceLeft =
        (adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U).traceLeft.traceLeft := by
          exact adhwFQSW_traceLeft_traceLeft_reindex_a2r
            (adhwFQSWPostAliceStateOfIsometry (q := q) (e := e) ψ U)
    _ = (ψ.reindex (Equiv.prodAssoc a b r)).state.traceLeft.traceLeft := by
          rw [hpost]
    _ = adhwFQSWSigmaRState ψ := by
          exact adhwFQSW_sourceInput_traceLeft_traceLeft ψ

/-- The maximally mixed `I^{A₂}/d_{A₂}` state appearing in the ADHW decoupling
target of fqsw.tex lines 580-841. -/
def adhwFQSWMaximallyMixedA2State (e : Type y)
    [Fintype e] [DecidableEq e] [Nonempty e] : MState e :=
  (MState.uniform : MState e)

/-- The source-route trace-norm decoupling integrand for a split Alice system
and a concrete unitary on `A₁ × A₂`, matching the quantity controlled by the
Haar-selection step in ADHW fqsw.tex lines 580-841. -/
def adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) : ℝ :=
  traceNormDistance
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).m
    (((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)).m)

/-- Product-decoupling trace-norm integrand
`||σ^{A₂R}(U) - σ^{A₂}(U) ⊗ σ^R||₁` from ADHW fqsw.tex
lines 580-592 and 806-815. -/
def adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) : ℝ :=
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  traceNormDistance
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).m
    (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
      (adhwFQSWSigmaRState ψ)).m)

/-- Max-mixed `A₂` trace-norm integrand
`||σ^{A₂}(U) - I^{A₂}/d_{A₂}||₁` from ADHW fqsw.tex lines
767-795 and 806-815. -/
def adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) : ℝ :=
  traceNormDistance
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).m
    (adhwFQSWMaximallyMixedA2State e).m

/-- Hilbert--Schmidt-square version of the product-decoupling integrand in
ADHW fqsw.tex lines 682-747. -/
def adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) : ℝ :=
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  hilbertSchmidtSq
    ((adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).m -
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
        (adhwFQSWSigmaRState ψ)).m))

/-- Hilbert--Schmidt-square version of the max-mixed `A₂` integrand in ADHW
fqsw.tex lines 776-787. -/
def adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) : ℝ :=
  hilbertSchmidtSq
    ((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).m -
      (adhwFQSWMaximallyMixedA2State e).m)

/-- Source `A` marginal reindexed by the ADHW split `A ≃ A₁ × A₂`. -/
def adhwFQSWASplitMatrix
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    CMatrix (q × e) :=
  ((adhwFQSWARState ψ).traceRight.m).submatrix split.symm split.symm

/-- Source `AR` marginal reindexed by the ADHW split `A ≃ A₁ × A₂`. -/
def adhwFQSWARSplitMatrix
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    CMatrix ((q × e) × r) :=
  ((adhwFQSWARState ψ).m).submatrix
    (fqswARSplitEquiv split).symm (fqswARSplitEquiv split).symm

/-- Split form of `ψ^A ⊗ ψ^R` on the `A₁A₂R` register. -/
def adhwFQSWARProductSplitMatrix
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    CMatrix ((q × e) × r) :=
  (adhwFQSWASplitMatrix ψ split) ⊗ₖ (adhwFQSWSigmaRState ψ).m

/-- Applying a reference isometry to the left/reference side conjugates the
left marginal by that isometry. -/
theorem referenceIsometry_traceRight_applyKet
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (V : ReferenceIsometry α β) (Ψ : Ket (α × γ)) :
    (V.applyKet Ψ).state.traceRight.m =
      V.matrix * Ψ.state.traceRight.m * Matrix.conjTranspose V.matrix := by
  rw [MState.traceRight_m]
  rw [Ket.state_matrix]
  rw [ReferenceIsometry.applyKet_vec]
  rw [V.rankOne_applyAmp]
  rw [ReferenceIsometry.traceRight_applyMatrix, MState.traceRight_m,
    Ket.state_matrix]

/-- Conjugating a bipartite matrix by a product reference isometry is the same
as applying the right isometry first and then the left isometry. -/
theorem referenceIsometry_prod_conj_eq_applyMatrix_applyMatrixRight
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (V : ReferenceIsometry α β) (W : ReferenceIsometry γ δ)
    (X : CMatrix (α × γ)) :
    (V.matrix ⊗ₖ W.matrix) * X *
        Matrix.conjTranspose (V.matrix ⊗ₖ W.matrix) =
      V.applyMatrix (W.applyMatrixRight X) := by
  ext x y
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.applyMatrixRight,
    ReferenceIsometry.targetBlock, ReferenceIsometry.rightBlock,
    Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_kronecker, Finset.sum_mul, Finset.mul_sum,
    Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm]
  apply Finset.sum_congr rfl
  intro _ _
  rw [Finset.sum_comm]

/-- Taking the right marginal after a product reference-isometry conjugation
leaves only the left isometry conjugating the original left marginal. -/
theorem referenceIsometry_prod_traceRight_conj
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (V : ReferenceIsometry α β) (W : ReferenceIsometry γ δ)
    (X : CMatrix (α × γ)) :
    Matrix.traceRight
        ((V.matrix ⊗ₖ W.matrix) * X *
          Matrix.conjTranspose (V.matrix ⊗ₖ W.matrix)) =
      V.matrix * Matrix.traceRight X *
        Matrix.conjTranspose V.matrix := by
  rw [referenceIsometry_prod_conj_eq_applyMatrix_applyMatrixRight]
  rw [ReferenceIsometry.traceRight_applyMatrix]
  rw [W.traceRight_applyMatrixRight]

/-- Taking the left marginal after a product reference-isometry conjugation
leaves only the right isometry conjugating the original right marginal. -/
theorem referenceIsometry_prod_traceLeft_conj
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (V : ReferenceIsometry α β) (W : ReferenceIsometry γ δ)
    (X : CMatrix (α × γ)) :
    Matrix.traceLeft
        ((V.matrix ⊗ₖ W.matrix) * X *
          Matrix.conjTranspose (V.matrix ⊗ₖ W.matrix)) =
      W.matrix * Matrix.traceLeft X *
        Matrix.conjTranspose W.matrix := by
  rw [referenceIsometry_prod_conj_eq_applyMatrix_applyMatrixRight]
  rw [V.traceLeft_applyMatrix]
  rw [W.traceLeft_applyMatrixRight]

/-- Applying composed reference isometries to a matrix is the same as applying
the right factor first and the left factor second. -/
theorem referenceIsometry_comp_applyMatrix
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type p}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (W : ReferenceIsometry β γ) (V : ReferenceIsometry α β)
    (X : CMatrix (α × δ)) :
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
    (E : α ≃ β) (X : CMatrix (α × γ)) :
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
    (∑ x : α × β, if b0 = x.2 then f x.1 x.2 else 0) =
      ∑ a : α, f a b0 := by
  rw [Fintype.sum_prod_type]
  simp

/-- A product-index finite sum with the symmetric delta orientation on the
right coordinate collapses to the fixed right-coordinate slice. -/
theorem fqsw_sum_prod_right_eq'
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : α → β → ζ) :
    (∑ x : α × β, if x.2 = b0 then f x.1 x.2 else 0) =
      ∑ a : α, f a b0 := by
  rw [Fintype.sum_prod_type]
  simp

/-- Pair-valued variant of `fqsw_sum_prod_right_eq`. -/
theorem fqsw_sum_prod_right_eq_pair
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : α × β → ζ) :
    (∑ x : α × β, if b0 = x.2 then f x else 0) =
      ∑ a : α, f (a, b0) := by
  rw [Fintype.sum_prod_type]
  simp

/-- Pair-valued variant of `fqsw_sum_prod_right_eq'`. -/
theorem fqsw_sum_prod_right_eq_pair'
    {α : Type u} {β : Type v} {ζ : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid ζ]
    (b0 : β) (f : α × β → ζ) :
    (∑ x : α × β, if x.2 = b0 then f x else 0) =
      ∑ a : α, f (a, b0) := by
  rw [Fintype.sum_prod_type]
  simp

/-- Applying a reference isometry to the left factor of a bipartite matrix is
conjugation by `V ⊗ I` on the product register. -/
theorem referenceIsometry_applyMatrix_eq_kronecker_one_conj
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (V : ReferenceIsometry α β) (X : CMatrix (α × γ)) :
    V.applyMatrix X =
      (V.matrix ⊗ₖ (1 : CMatrix γ)) * X *
        Matrix.conjTranspose (V.matrix ⊗ₖ (1 : CMatrix γ)) := by
  ext x y
  simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
    Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.one_apply,
    Finset.sum_mul, mul_assoc]
  rw [fqsw_sum_prod_right_eq_pair' (b0 := y.2)]
  apply Finset.sum_congr rfl
  intro i _
  rw [fqsw_sum_prod_right_eq_pair (b0 := x.2)]

theorem fqsw_traceRight_traceLeft_qer_reindex
    {q : Type x} {e : Type y} {r : Type w}
    [Fintype q] [Fintype e] [Fintype r]
    (M : CMatrix ((q × e) × r)) :
    Matrix.traceRight
      (Matrix.traceLeft
        (M.submatrix (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm)) =
      Matrix.traceLeft
        (Matrix.traceRight M) := by
  ext i j
  simp [Matrix.traceLeft, Matrix.traceRight, Equiv.prodAssoc]
  rw [Finset.sum_comm]

/-- Tracing out `q` after regrouping `(q × e) × r` as `q × (e × r)`
turns a product matrix into the product of the `q`-trace and the untouched
`r` matrix. -/
theorem fqsw_traceLeft_qer_kronecker
    {q : Type x} {e : Type y} {r : Type w}
    [Fintype q] [Fintype e] [Fintype r]
    (A : CMatrix (q × e)) (R : CMatrix r) :
    Matrix.traceLeft
      ((A ⊗ₖ R).submatrix
        (Equiv.prodAssoc q e r).symm
        (Equiv.prodAssoc q e r).symm) =
      (Matrix.traceLeft A) ⊗ₖ R := by
  ext i j
  simp [Matrix.traceLeft, Equiv.prodAssoc, Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- Hilbert--Schmidt square of a Kronecker product factors. -/
theorem fqsw_hilbertSchmidtSq_kronecker
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : CMatrix α) (N : CMatrix β) :
    hilbertSchmidtSq (M ⊗ₖ N) =
      hilbertSchmidtSq M * hilbertSchmidtSq N := by
  unfold hilbertSchmidtSq
  change ((Matrix.conjTranspose (M ⊗ₖ N) *
        (M ⊗ₖ N)).trace).re =
      ((Matrix.conjTranspose M * M).trace).re *
        ((Matrix.conjTranspose N * N).trace).re
  have hct :
      Matrix.conjTranspose (M ⊗ₖ N) =
        (Matrix.conjTranspose M) ⊗ₖ (Matrix.conjTranspose N) := by
    simpa using Matrix.conjTranspose_kronecker M N
  have hmul :
      ((Matrix.conjTranspose M) ⊗ₖ (Matrix.conjTranspose N)) *
          (M ⊗ₖ N) =
        (Matrix.conjTranspose M * M) ⊗ₖ (Matrix.conjTranspose N * N) := by
    simpa using
      (Matrix.mul_kronecker_mul (Matrix.conjTranspose M) M
        (Matrix.conjTranspose N) N).symm
  rw [hct, hmul]
  have htrace :
      ((Matrix.conjTranspose M * M) ⊗ₖ
          (Matrix.conjTranspose N * N)).trace =
        (Matrix.conjTranspose M * M).trace *
          (Matrix.conjTranspose N * N).trace := by
    simpa using
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

omit [Nonempty e] in
/-- Operational/source bridge for the ADHW max-mixed calculation: the `A₂`
marginal produced by the split-unitary FQSW definitions is the partial trace
of the split source `A` marginal after conjugating by the Haar unitary. -/
theorem adhwFQSWSigmaA2StateOfSplitUnitary_matrix_eq_traceLeft_applyMatrix_A
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (U : Matrix.unitaryGroup (q × e) ℂ) :
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).m =
      Matrix.traceLeft
        ((U : CMatrix (q × e)) * adhwFQSWASplitMatrix ψ split *
          star (U : CMatrix (q × e))) := by
  rw [adhwFQSWSigmaA2StateOfIsometry]
  rw [MState.traceRight_m]
  rw [adhwFQSWSigmaA2RStateOfIsometry_matrix_eq_traceLeft_applyMatrix_AR]
  rw [fqsw_traceRight_traceLeft_qer_reindex]
  rw [ReferenceIsometry.traceRight_applyMatrix]
  congr 1
  have hsplit :
      (adhwFQSWAliceIsometryOfSplitUnitary split U).matrix *
          Matrix.traceRight (adhwFQSWARState ψ).m *
          Matrix.conjTranspose (adhwFQSWAliceIsometryOfSplitUnitary split U).matrix =
        (U : CMatrix (q × e)) * adhwFQSWASplitMatrix ψ split *
          star (U : CMatrix (q × e)) := by
    ext i j
    simp [adhwFQSWAliceIsometryOfSplitUnitary, adhwFQSWAliceIsometryOfSplit,
      ReferenceIsometry.comp, ReferenceUnitary.toReferenceIsometry,
      ReferenceIsometry.ofEquiv, adhwFQSWASplitMatrix,
      Matrix.traceRight, Matrix.mul_apply, Matrix.conjTranspose,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    change
      (∑ x : a, ∑ y : a, ∑ rr : r,
        (U : CMatrix (q × e)) i (split y) *
          ((adhwFQSWARState ψ).m (y, rr) (x, rr) *
            star ((U : CMatrix (q × e)) j (split x)))) =
        (∑ x : q × e, ∑ y : q × e, ∑ rr : r,
          (U : CMatrix (q × e)) i y *
            ((adhwFQSWARState ψ).m (split.symm y, rr) (split.symm x, rr) *
              star ((U : CMatrix (q × e)) j x)))
    calc
      (∑ x : a, ∑ y : a, ∑ rr : r,
        (U : CMatrix (q × e)) i (split y) *
          ((adhwFQSWARState ψ).m (y, rr) (x, rr) *
            star ((U : CMatrix (q × e)) j (split x)))) =
        ∑ x : q × e, ∑ y : a, ∑ rr : r,
          (U : CMatrix (q × e)) i (split y) *
            ((adhwFQSWARState ψ).m (y, rr) (split.symm x, rr) *
              star ((U : CMatrix (q × e)) j x)) := by
          exact Fintype.sum_equiv split
            (fun x : a => ∑ y : a, ∑ rr : r,
              (U : CMatrix (q × e)) i (split y) *
                ((adhwFQSWARState ψ).m (y, rr) (x, rr) *
                  star ((U : CMatrix (q × e)) j (split x))))
            (fun x : q × e => ∑ y : a, ∑ rr : r,
              (U : CMatrix (q × e)) i (split y) *
                ((adhwFQSWARState ψ).m (y, rr) (split.symm x, rr) *
                  star ((U : CMatrix (q × e)) j x)))
            (by intro x; simp)
      _ = ∑ x : q × e, ∑ y : q × e, ∑ rr : r,
          (U : CMatrix (q × e)) i y *
            ((adhwFQSWARState ψ).m (split.symm y, rr) (split.symm x, rr) *
              star ((U : CMatrix (q × e)) j x)) := by
          apply Finset.sum_congr rfl
          intro x _
          refine Fintype.sum_equiv split
            (fun y : a => ∑ rr : r,
              (U : CMatrix (q × e)) i (split y) *
                ((adhwFQSWARState ψ).m (y, rr) (split.symm x, rr) *
                  star ((U : CMatrix (q × e)) j x)))
            (fun y : q × e => ∑ rr : r,
              (U : CMatrix (q × e)) i y *
                ((adhwFQSWARState ψ).m (split.symm y, rr) (split.symm x, rr) *
                  star ((U : CMatrix (q × e)) j x)))
            ?_
          intro y
          simp
  exact hsplit

omit [Nonempty e] in
/-- Applying the split-unitary Alice isometry to the source `AR` matrix is the
same as conjugating the split source matrix by `U ⊗ I_R`. -/
theorem adhwFQSWAliceIsometryOfSplitUnitary_applyMatrix_AR_eq
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (U : Matrix.unitaryGroup (q × e) ℂ) :
    (adhwFQSWAliceIsometryOfSplitUnitary split U).applyMatrix
        (adhwFQSWARState ψ).m =
      ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
        adhwFQSWARSplitMatrix ψ split *
        star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) := by
  unfold adhwFQSWAliceIsometryOfSplitUnitary adhwFQSWAliceIsometryOfSplit
  rw [referenceIsometry_comp_applyMatrix]
  have hsplit :
      (ReferenceIsometry.ofEquiv split).applyMatrix (adhwFQSWARState ψ).m =
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
theorem adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_eq_traceLeft_applyMatrix_AR_split
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (U : Matrix.unitaryGroup (q × e) ℂ) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).m =
      Matrix.traceLeft
        ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
            adhwFQSWARSplitMatrix ψ split *
            star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm) := by
  rw [adhwFQSWSigmaA2RStateOfIsometry_matrix_eq_traceLeft_applyMatrix_AR]
  rw [adhwFQSWAliceIsometryOfSplitUnitary_applyMatrix_AR_eq]

omit [Nonempty e] in
/-- The product term `σ^{A₂}(U) ⊗ σ^R` is the same `q` partial trace applied
to the conjugated split product matrix `ψ^A ⊗ ψ^R`. -/
theorem adhwFQSWProductA2RStateOfSplitUnitary_matrix_eq_traceLeft_applyMatrix_ARProduct
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (U : Matrix.unitaryGroup (q × e) ℂ) :
    (MState.prod
      (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U))
      (adhwFQSWSigmaRState ψ)).m =
      Matrix.traceLeft
        ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
            adhwFQSWARProductSplitMatrix ψ split *
            star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm) := by
  let ρA : CMatrix (q × e) := adhwFQSWASplitMatrix ψ split
  let ρR : CMatrix r := (adhwFQSWSigmaRState ψ).m
  have hconj :
      ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
          adhwFQSWARProductSplitMatrix ψ split *
          star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) =
        ((U : CMatrix (q × e)) * ρA * star (U : CMatrix (q × e))) ⊗ₖ
          ρR := by
    unfold adhwFQSWARProductSplitMatrix ρA ρR
    rw [Matrix.star_eq_conjTranspose]
    have hct :
        Matrix.conjTranspose
            ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) =
          (Matrix.conjTranspose (U : CMatrix (q × e))) ⊗ₖ
            (Matrix.conjTranspose (1 : CMatrix r)) := by
      simpa using
        Matrix.conjTranspose_kronecker (U : CMatrix (q × e)) (1 : CMatrix r)
    rw [hct, Matrix.conjTranspose_one]
    have hmul_left :
        ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
            ((adhwFQSWASplitMatrix ψ split) ⊗ₖ
              (adhwFQSWSigmaRState ψ).m) =
          ((U : CMatrix (q × e)) * adhwFQSWASplitMatrix ψ split) ⊗ₖ
            ((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).m) := by
      simpa using
        (Matrix.mul_kronecker_mul (U : CMatrix (q × e))
          (adhwFQSWASplitMatrix ψ split) (1 : CMatrix r)
          (adhwFQSWSigmaRState ψ).m).symm
    rw [hmul_left]
    have hmul_right :
        (((U : CMatrix (q × e)) * adhwFQSWASplitMatrix ψ split) ⊗ₖ
            ((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).m)) *
          ((Matrix.conjTranspose (U : CMatrix (q × e))) ⊗ₖ
            (1 : CMatrix r)) =
        (((U : CMatrix (q × e)) * adhwFQSWASplitMatrix ψ split) *
            Matrix.conjTranspose (U : CMatrix (q × e))) ⊗ₖ
          (((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).m) *
            (1 : CMatrix r)) := by
      simpa using
        (Matrix.mul_kronecker_mul
          ((U : CMatrix (q × e)) * adhwFQSWASplitMatrix ψ split)
          (Matrix.conjTranspose (U : CMatrix (q × e)))
          ((1 : CMatrix r) * (adhwFQSWSigmaRState ψ).m)
          (1 : CMatrix r)).symm
    rw [hmul_right]
    simp [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  calc
    (MState.prod
      (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U))
      (adhwFQSWSigmaRState ψ)).m =
        (Matrix.traceLeft
            ((U : CMatrix (q × e)) * ρA * star (U : CMatrix (q × e)))) ⊗ₖ
          ρR := by
          simp [ρA, ρR,
            adhwFQSWSigmaA2StateOfSplitUnitary_matrix_eq_traceLeft_applyMatrix_A]
    _ = Matrix.traceLeft
        ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
            adhwFQSWARProductSplitMatrix ψ split *
            star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm) := by
          rw [hconj]
          rw [fqsw_traceLeft_qer_kronecker]

/-- The lifted max-mixed product term
`||σ^{A₂}(U) ⊗ σ^R - I^{A₂}/d_{A₂} ⊗ σ^R||₁` appearing between
the triangle-inequality step and the product-with-state contraction in ADHW
fqsw.tex lines 806-815. -/
def adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) : ℝ :=
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  traceNormDistance
    (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
      (adhwFQSWSigmaRState ψ)).m)
    (((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)).m)

/-- Raw triangle-inequality form of ADHW fqsw.tex lines 806-810.  This leaves
the product-with-`σ^R` contraction as a separate subsequent lemma. -/
theorem adhwFQSWDecouplingTraceNormIntegrand_le_product_add_liftedMaxMixed
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) :
    adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ≤
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U +
        adhwFQSWLiftedMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  let ρ : CMatrix (e × r) :=
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).m
  let σ : CMatrix (e × r) :=
    ((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
      (adhwFQSWSigmaRState ψ)).m
  let τ : CMatrix (e × r) :=
    ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)).m
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
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) :
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
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) :
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
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).normalizedTraceDistance
      ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) =
        (1 / 2 : ℝ) *
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U :=
  rfl

/-- Partial trace over the left tensor factor is continuous as a matrix-valued
finite sum. -/
@[fun_prop]
theorem traceLeft_continuous_matrix
    {α : Type*} {β : Type*} [Fintype α] [Fintype β] :
    Continuous (fun M : CMatrix (α × β) => Matrix.traceLeft M) := by
  refine continuous_pi ?_
  intro j
  refine continuous_pi ?_
  intro j'
  simp only [Matrix.traceLeft, Matrix.of_apply]
  refine continuous_finsetSum Finset.univ ?_
  intro i _
  exact (continuous_apply (i, j')).comp (continuous_apply (i, j))

/-- Partial trace over the right tensor factor is continuous as a matrix-valued
finite sum. -/
@[fun_prop]
theorem traceRight_continuous_matrix
    {α : Type*} {β : Type*} [Fintype α] [Fintype β] :
    Continuous (fun M : CMatrix (α × β) => Matrix.traceRight M) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro i'
  simp only [Matrix.traceRight, Matrix.of_apply]
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

private theorem fqsw_traceLeft_flip_entry_sum_prod
    {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (ρ : CMatrix (α × (β × γ)))
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
    traceLeft_flip_entry_sum
      (a := α) (e := β × γ) ρ i j (k, s) (l, t)

private theorem fqsw_nested_split_flip_entry_sum
    {α : Type*} {β : Type*} {γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (ρ : CMatrix ((α × β) × γ))
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
theorem fqsw_traceLeft_one_prod
    {q : Type x} {e : Type y} [Fintype q] [DecidableEq q] [DecidableEq e] :
    Matrix.traceLeft (1 : CMatrix (q × e)) =
      ((Fintype.card q : ℂ) • (1 : CMatrix e)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.traceLeft]
  · simp [Matrix.traceLeft, hij]

/-- Tracing out the right factor of the identity on `q × e` gives
`|e| I_q`. -/
theorem fqsw_traceRight_one_prod
    {q : Type x} {e : Type y} [Fintype e] [DecidableEq q] [DecidableEq e] :
    Matrix.traceRight (1 : CMatrix (q × e)) =
      ((Fintype.card e : ℂ) • (1 : CMatrix q)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.traceRight]
  · simp [Matrix.traceRight, hij]

/-- Source trace term
`Tr(I^{A₁A₁'} ⊗ F^{A₂}) = d_{A₁}² d_{A₂}` from ADHW fqsw.tex
lines 656-666. -/
theorem fqsw_twoCopySideOperator_one_swap_trace
    {q : Type x} {e : Type y} [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] :
    (twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrixTwo (a := e))).trace =
    ((Fintype.card q : ℂ) * (Fintype.card q : ℂ) * (Fintype.card e : ℂ)) := by
  have h := tensorPowerKroneckerTwo_prod_mul_one_swap_trace
    (a := q) (e := e) (rho := (1 : CMatrix (q × e)))
  rw [tensorPowerKroneckerTwo_one, Matrix.one_mul] at h
  rw [h]
  rw [fqsw_traceLeft_one_prod]
  simp [Matrix.trace_smul, Matrix.trace_one]
  ring

/-- Source trace term
`Tr(F^{A₁} ⊗ I^{A₂A₂'}) = d_{A₁} d_{A₂}²` from ADHW fqsw.tex
lines 656-666. -/
theorem fqsw_twoCopySideOperator_swap_one_trace
    {q : Type x} {e : Type y} [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] :
    (twoCopySideOperator (a := q) (e := e)
      (tensorPowerSwapMatrixTwo (a := q))
      (1 : CMatrix (TensorPower e 2))).trace =
    ((Fintype.card q : ℂ) * (Fintype.card e : ℂ) * (Fintype.card e : ℂ)) := by
  have h := tensorPowerKroneckerTwo_prod_mul_swap_one_trace
    (a := q) (e := e) (rho := (1 : CMatrix (q × e)))
  rw [tensorPowerKroneckerTwo_one, Matrix.one_mul] at h
  rw [h]
  rw [fqsw_traceRight_one_prod]
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Continuous fun U : Matrix.unitaryGroup (q × e) ℂ =>
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).m := by
  refine continuous_matrix ?_
  intro x y
  simp only [adhwFQSWSigmaA2RStateOfIsometry, adhwFQSWPostAliceStateOfIsometry,
    MState.traceLeft_m, MState.reindex_matrix, Ket.state_matrix]
  unfold adhwFQSWAliceIsometryOfSplitUnitary
    adhwFQSWAliceIsometryOfSplit
    ReferenceIsometry.comp
    ReferenceUnitary.toReferenceIsometry
    ReferenceIsometry.ofEquiv
    ReferenceIsometry.applyKet
    ReferenceIsometry.applyAmp
    Matrix.traceLeft
    rankOneMatrix
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  continuity

omit [Nonempty e] in
/-- The ADHW marginal `σ^{A₂}(U)` is continuous as a matrix-valued function of
the Haar unitary. -/
theorem adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Continuous fun U : Matrix.unitaryGroup (q × e) ℂ =>
      (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).m := by
  simp only [adhwFQSWSigmaA2StateOfIsometry, MState.traceRight_m]
  exact traceRight_continuous_matrix.comp
    (adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split)

/-- The FQSW split-unitary decoupling integrand is continuous in the Haar
unitary. -/
theorem adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_continuous
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Continuous fun U : Matrix.unitaryGroup (q × e) ℂ =>
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U := by
  unfold adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary traceNormDistance
  exact traceNorm_continuous.comp
    ((adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split).sub continuous_const)

/-- The FQSW split-unitary decoupling integrand is Haar-integrable. -/
theorem adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (q × e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (unitaryHaarMeasure (a := q × e)) :=
  (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_continuous ψ split).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The squared FQSW split-unitary decoupling integrand is Haar-integrable. -/
theorem adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (q × e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2)
      (unitaryHaarMeasure (a := q × e)) :=
  ((adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_continuous ψ split).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [Nonempty e] in
/-- The product-decoupling ADHW integrand is continuous in the Haar unitary. -/
theorem adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_continuous
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Continuous fun U : Matrix.unitaryGroup (q × e) ℂ =>
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U := by
  have hsigmaA2R := adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split
  have hprod : Continuous fun U : Matrix.unitaryGroup (q × e) ℂ =>
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).prod
          (adhwFQSWSigmaRState ψ)).m) := by
    have hsigmaA2 := adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split
    refine continuous_matrix ?_
    intro i j
    simp [Matrix.kroneckerMap_apply]
    continuity
  unfold adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary traceNormDistance
  exact traceNorm_continuous.comp (hsigmaA2R.sub hprod)

/-- The squared product-decoupling ADHW integrand is Haar-integrable. -/
theorem adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (q × e) ℂ =>
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2)
      (unitaryHaarMeasure (a := q × e)) :=
  ((adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_continuous ψ split).pow
      2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The max-mixed `A₂` ADHW integrand is continuous in the Haar unitary. -/
theorem adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_continuous
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Continuous fun U : Matrix.unitaryGroup (q × e) ℂ =>
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U := by
  unfold adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary traceNormDistance
  exact traceNorm_continuous.comp
    ((adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split).sub continuous_const)

/-- The squared max-mixed `A₂` ADHW integrand is Haar-integrable. -/
theorem adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_sq_integrable
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (q × e) ℂ =>
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2)
      (unitaryHaarMeasure (a := q × e)) :=
  ((adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_continuous ψ split).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [Nonempty e] in
/-- The product-decoupling Hilbert--Schmidt integrand is continuous in the
Haar unitary. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_continuous
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Continuous fun U : Matrix.unitaryGroup (q × e) ℂ =>
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  have hsigmaA2R := adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_continuous ψ split
  have hprod : Continuous fun U : Matrix.unitaryGroup (q × e) ℂ =>
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)).prod
          (adhwFQSWSigmaRState ψ)).m) := by
    have hsigmaA2 := adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split
    refine continuous_matrix ?_
    intro i j
    simp [Matrix.kroneckerMap_apply]
    continuity
  unfold adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary
  exact hilbertSchmidtSq_continuous_matrix.comp (hsigmaA2R.sub hprod)

/-- The max-mixed `A₂` Hilbert--Schmidt integrand is continuous in the Haar
unitary. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_continuous
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Continuous fun U : Matrix.unitaryGroup (q × e) ℂ =>
      adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  unfold adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary
  exact hilbertSchmidtSq_continuous_matrix.comp
    ((adhwFQSWSigmaA2StateOfSplitUnitary_matrix_continuous ψ split).sub continuous_const)

/-- The product-decoupling Hilbert--Schmidt integrand is Haar-integrable. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_integrable
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (q × e) ℂ =>
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U)
      (unitaryHaarMeasure (a := q × e)) :=
  (adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_continuous ψ split).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The max-mixed `A₂` Hilbert--Schmidt integrand is Haar-integrable. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_integrable
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (q × e) ℂ =>
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U)
      (unitaryHaarMeasure (a := q × e)) :=
  (adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_continuous ψ split).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [Nonempty e] in
/-- ADHW fqsw.tex lines 751-754: pointwise Cauchy--Schwarz bridge from the
product-decoupling trace norm to the Hilbert--Schmidt square on `A₂R`. -/
theorem adhwFQSWProductDecouplingTraceNormSq_le_card_mul_hilbertSchmidt
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) :
    adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
      ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  let alice := adhwFQSWAliceIsometryOfSplitUnitary split U
  let Δ : CMatrix (e × r) :=
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ alice).m -
      (((adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ alice).prod
        (adhwFQSWSigmaRState ψ)).m)
  have h := traceNorm_sq_le_card_mul_hilbertSchmidtSq Δ
  simpa [adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary,
    adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary,
    traceNormDistance, Δ, alice, Fintype.card_prod] using h

/-- ADHW fqsw.tex lines 776-780: pointwise Cauchy--Schwarz bridge from the
max-mixed `A₂` trace norm to the Hilbert--Schmidt square on `A₂`. -/
theorem adhwFQSWMaxMixedA2TraceNormSq_le_card_mul_hilbertSchmidt
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) :
    adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
      (Fintype.card e : ℝ) *
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
  let Δ : CMatrix e :=
    (adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
      (adhwFQSWAliceIsometryOfSplitUnitary split U)).m -
      (adhwFQSWMaximallyMixedA2State e).m
  have h := traceNorm_sq_le_card_mul_hilbertSchmidtSq Δ
  simpa [adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary,
    adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary,
    traceNormDistance, Δ] using h

/-- Integral form of the ADHW product-decoupling Cauchy--Schwarz tail.  The
remaining source-route task is the exact Hilbert--Schmidt average of
fqsw.tex lines 682-747. -/
theorem adhwFQSWProductDecouplingTraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
      ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
        (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := q × e)) := by
  have hpoint : ∀ᵐ U : Matrix.unitaryGroup (q × e) ℂ
      ∂unitaryHaarMeasure (a := q × e),
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
        ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
    filter_upwards with U
    exact adhwFQSWProductDecouplingTraceNormSq_le_card_mul_hilbertSchmidt ψ split U
  calc
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
      ∫ U : Matrix.unitaryGroup (q × e) ℂ,
        ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e) :=
        MeasureTheory.integral_mono_ae
          (adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
          ((adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_integrable
            ψ split).const_mul ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)))
          hpoint
    _ = ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
        (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := q × e)) := by
          rw [MeasureTheory.integral_const_mul]

/-- Integral form of the ADHW max-mixed `A₂` Cauchy--Schwarz tail.  The
remaining source-route task is the exact one-copy `A₂` Hilbert--Schmidt
average from fqsw.tex lines 781-787. -/
theorem adhwFQSWMaxMixedA2TraceNormAverageSq_le_card_mul_hilbertSchmidtAverage
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
      (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := q × e)) := by
  have hpoint : ∀ᵐ U : Matrix.unitaryGroup (q × e) ℂ
      ∂unitaryHaarMeasure (a := q × e),
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2 ≤
        (Fintype.card e : ℝ) *
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U := by
    filter_upwards with U
    exact adhwFQSWMaxMixedA2TraceNormSq_le_card_mul_hilbertSchmidt ψ split U
  calc
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
      ∫ U : Matrix.unitaryGroup (q × e) ℂ,
        (Fintype.card e : ℝ) *
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e) :=
        MeasureTheory.integral_mono_ae
          (adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary_sq_integrable ψ split)
          ((adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary_integrable
            ψ split).const_mul (Fintype.card e : ℝ))
          hpoint
    _ = (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := q × e)) := by
          rw [MeasureTheory.integral_const_mul]

/-- ADHW fqsw.tex lines 806-815: after the pointwise triangle-inequality
comparison has related the final decoupling integrand to the product-decoupling
and max-mixed integrands, the averaged square is bounded by twice the two
component averaged squares.  The upstream source-route tasks are the pointwise
trace-norm comparison and the two Schur/HS average estimates. -/
theorem adhwFQSWCombinedTraceNormAverageSq_le_two_component_averages
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
      2 * (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
        ∂unitaryHaarMeasure (a := q × e)) +
      2 * (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
        ∂unitaryHaarMeasure (a := q × e)) := by
  exact integral_sq_le_two_add_two_of_ae_le_add
    (μ := unitaryHaarMeasure (a := q × e))
    (f := fun U : Matrix.unitaryGroup (q × e) ℂ =>
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
    (g := fun U : Matrix.unitaryGroup (q × e) ℂ =>
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
    (h := fun U : Matrix.unitaryGroup (q × e) ℂ =>
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

/-- Regroup the ideal FQSW target
`ψ^{R\widehat B} ⊗ Φ^{A₂\widetilde B}` as a purification of the decoupling
target on `A₂R`, with `\widehat B\widetilde B` as the reference. -/
def fqswIdealTargetToA2RPurificationEquiv
    (a : Type u) (b : Type v) (r : Type w) (e : Type y) (et : Type z) :
    (((a × b) × r) × (e × et)) ≃
      (((a × b) × et) × (e × r)) where
  toFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
  invFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- The ideal ADHW target, regrouped as a purification of
`I^{A₂}/d_{A₂} ⊗ σ^R`. -/
def adhwFQSWIdealA2RPurification
    (ψ : Ket ((a × b) × r)) (pairing : e ≃ et) :
    Ket (((a × b) × et) × (e × r)) :=
  (ψ.prod (Ket.maximallyEntangled pairing)).reindex
    (fqswIdealTargetToA2RPurificationEquiv a b r e et)

/-- The ideal ADHW target purifies the decoupling target
`I^{A₂}/d_{A₂} ⊗ σ^R`. -/
theorem adhwFQSWIdealA2RPurification_purifies
    (ψ : Ket ((a × b) × r)) (pairing : e ≃ et) :
    (adhwFQSWIdealA2RPurification ψ pairing).Purifies
      ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) := by
  rw [Ket.purifies_iff]
  ext x y
  simp only [adhwFQSWIdealA2RPurification, fqswIdealTargetToA2RPurificationEquiv,
    Ket.reindex_state, Ket.prod_state, MState.reindex_matrix,
    MState.prod_m, Matrix.kroneckerMap_apply, Matrix.traceLeft, Matrix.of_apply,
    adhwFQSWMaximallyMixedA2State,
    adhwFQSWSigmaRState_eq_source_traceLeft, MState.traceLeft_m,
    Fintype.sum_prod_type, Matrix.submatrix_apply, Equiv.coe_fn_symm_mk,
    Ket.state_matrix, rankOneMatrix_apply]
  have hebit :
      (∑ k : et,
        (Ket.maximallyEntangled pairing).vec (x.1, k) *
          (starRingEnd ℂ) ((Ket.maximallyEntangled pairing).vec (y.1, k))) =
        (MState.uniform : MState e).m x.1 y.1 := by
    have h := congrArg (fun ρ : MState e => ρ.m x.1 y.1)
      (Ket.maximallyEntangled_traceRight pairing)
    simpa [MState.traceRight_m, Matrix.traceRight, Ket.state_matrix,
      rankOneMatrix_apply] using h
  exact
    (sum_sum_sum_mul_right
      (fun i : a => fun j : b =>
        ψ.vec ((i, j), x.2) * (starRingEnd ℂ) (ψ.vec ((i, j), y.2)))
      (fun k : et =>
        (Ket.maximallyEntangled pairing).vec (x.1, k) *
          (starRingEnd ℂ) ((Ket.maximallyEntangled pairing).vec (y.1, k)))).trans
      (by rw [hebit]; simp)

/-- Reindexing the computed FQSW output into `A₂R` purification order is the
same ket as applying Bob's isometry to the post-Alice purification. -/
theorem fqsw_outputKet_reindex_a2r_eq_apply_postAlice
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e))
    (V : ReferenceIsometry (q × b) ((a × b) × et))
    (pairing : e ≃ et) :
    (({ aliceIsometry := U, bobIsometry := V, ebitPairing := pairing } :
        FQSWOneShotProtocol ψ q e et).outputKet.reindex
          (fqswIdealTargetToA2RPurificationEquiv a b r e et)) =
      V.applyKet
        (adhwFQSWPostAliceA2RPurificationOfIsometry (q := q) (e := e) ψ U) := by
  apply Ket.ext_vec
  funext x
  simp [FQSWOneShotProtocol.outputKet,
    adhwFQSWPostAliceA2RPurificationOfIsometry,
    Equiv.prodAssoc, fqswAliceOutputToBobInputEquiv,
    Equiv.prodProdProdComm,
    fqswIdealTargetToA2RPurificationEquiv, ReferenceIsometry.applyKet,
    ReferenceIsometry.applyAmp, Matrix.mulVec]

/-- Uhlmann assembly for the ADHW one-shot route: a concrete Alice isometry
whose `A₂R` decoupling marginal is close to `I^{A₂}/d_{A₂} ⊗ σ^R` supplies a
computed FQSW one-shot protocol with the corresponding source trace-norm
error bound. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_decoupling
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) (pairing : e ≃ et) (η : ℝ)
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × et))
    (hdec :
      (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ U).normalizedTraceDistance
        ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤ η) :
    ∃ C : FQSWOneShotProtocol ψ q e et,
      C.traceNormError ≤ 2 * Real.sqrt (2 * η) := by
  let post := adhwFQSWPostAliceA2RPurificationOfIsometry (q := q) (e := e) ψ U
  let ideal := adhwFQSWIdealA2RPurification ψ pairing
  let targetState : MState (e × r) :=
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
    Ket.exists_referenceIsometry_applyKet_normalizedTraceDistance_le_sqrt_two_mul_normalizedTraceDistance
      hpost hideal hcardTarget hcardRef
  let C : FQSWOneShotProtocol ψ q e et :=
    { aliceIsometry := U, bobIsometry := V, ebitPairing := pairing }
  refine ⟨C, ?_⟩
  have hVη :
      (V.applyKet post).state.normalizedTraceDistance ideal.state ≤
        Real.sqrt (2 * η) := by
    refine le_trans hV ?_
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hdec (by norm_num))
  let E := fqswIdealTargetToA2RPurificationEquiv a b r e et
  have hpure :
      C.outputKet.reindex E = V.applyKet post := by
    simpa [C, post, E] using
      (fqsw_outputKet_reindex_a2r_eq_apply_postAlice ψ U V pairing)
  have hout :
      C.outputState.reindex E = (V.applyKet post).state := by
    change C.outputKet.state.reindex E = (V.applyKet post).state
    exact (Ket.reindex_state C.outputKet E).symm.trans
      (congrArg Ket.state hpure)
  have htarget :
      C.targetState.reindex E = ideal.state := by
    calc
      C.targetState.reindex E =
          (ψ.state.prod (MState.maximallyEntangled pairing)).reindex E := by
        simp [C, FQSWOneShotProtocol.targetState]
      _ = (ψ.state.prod (Ket.maximallyEntangled pairing).state).reindex E := by
        rfl
      _ = (ψ.prod (Ket.maximallyEntangled pairing)).state.reindex E := by
        rw [Ket.prod_state]
      _ = ((ψ.prod (Ket.maximallyEntangled pairing)).reindex E).state := by
        exact (Ket.reindex_state (ψ.prod (Ket.maximallyEntangled pairing)) E).symm
      _ = ideal.state := by
        simp [ideal, E, adhwFQSWIdealA2RPurification]
  have hnorm_eq :
      C.normalizedError =
        (V.applyKet post).state.normalizedTraceDistance ideal.state := by
    rw [FQSWOneShotProtocol.normalizedError]
    rw [← MState.normalizedTraceDistance_reindex_equiv C.outputState C.targetState E]
    rw [hout, htarget]
  have hnorm_le : C.normalizedError ≤ Real.sqrt (2 * η) := by
    rw [hnorm_eq]
    exact hVη
  have hhalf := C.normalizedError_eq_half_traceNormError
  have htrace_nonneg := C.traceNormError_nonneg
  nlinarith

/-- Purity `Tr[(ψ^{AR})^2]` in the notation of ADHW fqsw.tex lines 580-841. -/
def adhwFQSWARPurity (ψ : Ket ((a × b) × r)) : ℝ :=
  hilbertSchmidtSq ((adhwFQSWARState ψ).m)

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
    (V : ReferenceIsometry α β) (ρ : MState α) :
    hilbertSchmidtSq (V.matrix * ρ.m * Matrix.conjTranspose V.matrix) =
      hilbertSchmidtSq ρ.m := by
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    (V.matrix * ρ.m * Matrix.conjTranspose V.matrix)
    (ρ.psd.mul_mul_conjTranspose_same V.matrix)]
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two ρ.m ρ.psd]
  exact psdTracePower_isometry_conj V.matrix ρ.psd V.isometry
    (by norm_num : (0 : ℝ) < 2)

/-- The ADHW `AR` purity equals the complementary source `B` purity.  This is
the pure-state Hilbert--Schmidt bridge used to identify the line-1158 source
purity term in ADHW's i.i.d. proof. -/
theorem adhwFQSWARPurity_eq_systemBPurity
    (ψ : Ket ((a × b) × r)) :
    adhwFQSWARPurity ψ =
      hilbertSchmidtSq ψ.state.traceRight.traceLeft.m := by
  let Ω : Ket ((a × r) × b) :=
    ψ.reindex (prodABCToACBEquiv a b r)
  have hΩA : Ω.state.traceRight = adhwFQSWARState ψ := by
    apply MState.ext
    ext i j
    simp [Ω, adhwFQSWARState, MState.coherentTransferReferenceState,
      prodABCToACBEquiv, Ket.reindex_state,
      Matrix.traceRight, Ket.state_matrix, rankOneMatrix_apply]
  have hΩB : Ω.state.traceLeft = ψ.state.traceRight.traceLeft := by
    apply MState.ext
    ext i j
    simp [Ω, prodABCToACBEquiv, Ket.reindex_state,
      Matrix.traceLeft, Matrix.traceRight,
      Ket.state_matrix, rankOneMatrix_apply, Fintype.sum_prod_type]
  have hdual :=
    Ket.psdTracePower_traceRight_eq_traceLeft
      (Ψ := Ω) (p := (2 : ℝ)) (by norm_num)
  rw [adhwFQSWARPurity]
  rw [← hΩA, ← hΩB]
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    Ω.state.traceRight.m Ω.state.traceRight.psd]
  rw [fqsw_hilbertSchmidtSq_eq_psdTracePower_two
    Ω.state.traceLeft.m Ω.state.traceLeft.psd]
  simpa [Ket.state] using hdual

/-- Purity `Tr[(ψ^A)^2]` in the notation of ADHW fqsw.tex lines 580-841. -/
def adhwFQSWAPurity (ψ : Ket ((a × b) × r)) : ℝ :=
  hilbertSchmidtSq ((adhwFQSWARState ψ).traceRight.m)

/-- Purity `Tr[(ψ^R)^2]` in the notation of ADHW fqsw.tex lines 580-841. -/
def adhwFQSWRPurity (ψ : Ket ((a × b) × r)) : ℝ :=
  hilbertSchmidtSq ((adhwFQSWARState ψ).traceLeft.m)

/-- The overlap `Tr[ψ^{AR}(ψ^A ⊗ ψ^R)]` appearing in the exact
Hilbert--Schmidt calculation of ADHW fqsw.tex lines 682-747. -/
def adhwFQSWARProductOverlap (ψ : Ket ((a × b) × r)) : ℝ :=
  ((adhwFQSWARState ψ).m *
      ((adhwFQSWARState ψ).traceRight.prod (adhwFQSWARState ψ).traceLeft).m).trace.re

/-- The overlap term
`Tr[ψ^{AR}(ψ^A ⊗ ψ^R)]` in ADHW fqsw.tex lines 682-747 is nonnegative:
both factors are positive semidefinite states. -/
theorem adhwFQSWARProductOverlap_nonneg
    (ψ : Ket ((a × b) × r)) :
    0 ≤ adhwFQSWARProductOverlap ψ := by
  unfold adhwFQSWARProductOverlap
  exact cMatrix_trace_mul_posSemidef_re_nonneg
    (adhwFQSWARState ψ).psd
    (((adhwFQSWARState ψ).traceRight).prod
      ((adhwFQSWARState ψ).traceLeft)).psd

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
/-- The split `A` marginal still has trace one. -/
theorem adhwFQSWASplitMatrix_trace
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (adhwFQSWASplitMatrix ψ split).trace = 1 := by
  unfold adhwFQSWASplitMatrix
  rw [Matrix.trace_submatrix _ split.symm]
  exact (adhwFQSWARState ψ).traceRight.tr'

omit [Nonempty e] in
/-- The split `A` marginal has the same purity as the source `A` marginal. -/
theorem adhwFQSWASplitMatrix_hilbertSchmidtSq
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    hilbertSchmidtSq (adhwFQSWASplitMatrix ψ split) = adhwFQSWAPurity ψ := by
  unfold adhwFQSWASplitMatrix adhwFQSWAPurity
  rw [fqsw_hilbertSchmidtSq_submatrix_equiv split]

omit [Nonempty e] in
/-- The split `AR` matrix has the same purity as the source `AR` marginal. -/
theorem adhwFQSWARSplitMatrix_hilbertSchmidtSq
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    hilbertSchmidtSq (adhwFQSWARSplitMatrix ψ split) = adhwFQSWARPurity ψ := by
  unfold adhwFQSWARSplitMatrix adhwFQSWARPurity
  rw [fqsw_hilbertSchmidtSq_submatrix_equiv (fqswARSplitEquiv split)]

omit [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] [Nonempty e] in
/-- The split product matrix is the source product state reindexed by the
ADHW split on Alice's register. -/
theorem adhwFQSWARProductSplitMatrix_eq_source_product_submatrix
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    adhwFQSWARProductSplitMatrix ψ split =
      (((adhwFQSWARState ψ).traceRight.prod
        (adhwFQSWARState ψ).traceLeft).m).submatrix
        (fqswARSplitEquiv split).symm (fqswARSplitEquiv split).symm := by
  ext x y
  simp [adhwFQSWARProductSplitMatrix, adhwFQSWASplitMatrix,
    adhwFQSWSigmaRState, fqswARSplitEquiv, Matrix.kroneckerMap_apply]

omit [Nonempty e] in
/-- The split product matrix has Hilbert--Schmidt square
`Tr[(ψ^A)^2] Tr[(ψ^R)^2]`. -/
theorem adhwFQSWARProductSplitMatrix_hilbertSchmidtSq
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    hilbertSchmidtSq (adhwFQSWARProductSplitMatrix ψ split) =
      adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
  unfold adhwFQSWARProductSplitMatrix adhwFQSWRPurity adhwFQSWSigmaRState
  rw [fqsw_hilbertSchmidtSq_kronecker]
  rw [adhwFQSWASplitMatrix_hilbertSchmidtSq]

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
/-- The split overlap is the source overlap
`Tr[ψ^{AR}(ψ^A ⊗ ψ^R)]`. -/
theorem adhwFQSWARProductSplitMatrix_overlap
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (adhwFQSWARSplitMatrix ψ split *
        adhwFQSWARProductSplitMatrix ψ split).trace.re =
      adhwFQSWARProductOverlap ψ := by
  let E : ((q × e) × r) ≃ (a × r) :=
    (fqswARSplitEquiv (r := r) split).symm
  have hprod :=
    adhwFQSWARProductSplitMatrix_eq_source_product_submatrix ψ split
  unfold adhwFQSWARProductOverlap adhwFQSWARSplitMatrix
  rw [hprod]
  change (((adhwFQSWARState ψ).m.submatrix E E *
        (((adhwFQSWARState ψ).traceRight.prod
          (adhwFQSWARState ψ).traceLeft).m).submatrix E E).trace).re =
    (((adhwFQSWARState ψ).m *
      ((adhwFQSWARState ψ).traceRight.prod
        (adhwFQSWARState ψ).traceLeft).m).trace).re
  rw [Matrix.submatrix_mul_equiv (e₂ := E)]
  rw [Matrix.trace_submatrix _ E]

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
/-- Tracing the split `AR` source matrix over `A₁A₂` recovers the fixed
reference marginal `σ^R`. -/
theorem adhwFQSWARSplitMatrix_traceLeft
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Matrix.traceLeft
        (adhwFQSWARSplitMatrix ψ split) =
      (adhwFQSWSigmaRState ψ).m := by
  ext i j
  unfold adhwFQSWARSplitMatrix adhwFQSWSigmaRState
  rw [MState.traceLeft_m]
  change
    (∑ x : q × e,
      (adhwFQSWARState ψ).m (split.symm x, i) (split.symm x, j)) =
    ∑ y : a, (adhwFQSWARState ψ).m (y, i) (y, j)
  exact Fintype.sum_equiv split.symm
    (fun x : q × e =>
      (adhwFQSWARState ψ).m (split.symm x, i) (split.symm x, j))
    (fun y : a => (adhwFQSWARState ψ).m (y, i) (y, j))
    (fun _ => rfl)

omit [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] [Nonempty e] in
/-- Tracing the split `AR` source matrix over `R` recovers the split
`A₁A₂` source marginal. -/
theorem adhwFQSWARSplitMatrix_traceRight
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Matrix.traceRight
        (adhwFQSWARSplitMatrix ψ split) =
      adhwFQSWASplitMatrix ψ split := by
  ext i j
  unfold adhwFQSWARSplitMatrix adhwFQSWASplitMatrix
  rw [MState.traceRight_m]
  rfl

omit [DecidableEq q] [DecidableEq e] [Nonempty e] in
/-- Tracing the split product matrix over `A₁A₂` also recovers the same
reference marginal `σ^R`. -/
theorem adhwFQSWARProductSplitMatrix_traceLeft
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    Matrix.traceLeft
        (adhwFQSWARProductSplitMatrix ψ split) =
      (adhwFQSWSigmaRState ψ).m := by
  unfold adhwFQSWARProductSplitMatrix
  rw [traceLeft_kronecker]
  rw [adhwFQSWASplitMatrix_trace]
  exact matrixScale_one (adhwFQSWSigmaRState ψ).m

omit [Nonempty e] in
/-- If the split Alice system `A₁ × A₂` is a one-point system, the source
correlation matrix `ψ^{AR} - ψ^A ⊗ ψ^R` is zero. -/
theorem adhwFQSWARCorrelationSplitMatrix_eq_zero_of_subsingleton
    [Subsingleton (q × e)]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    adhwFQSWARSplitMatrix ψ split -
      adhwFQSWARProductSplitMatrix ψ split = 0 := by
  apply sub_eq_zero.mpr
  let ρsplit : MState ((q × e) × r) :=
    (adhwFQSWARState ψ).reindex (fqswARSplitEquiv split)
  have hprod := state_matrix_eq_prod_marginals_of_subsingleton_left ρsplit
  have hρmatrix : ρsplit.m = adhwFQSWARSplitMatrix ψ split :=
    MState.reindex_matrix _ _
  have hAmatrix : ρsplit.traceRight.m = adhwFQSWASplitMatrix ψ split := by
    rw [MState.traceRight_m, hρmatrix]
    exact adhwFQSWARSplitMatrix_traceRight ψ split
  have hBmatrix : ρsplit.traceLeft.m = (adhwFQSWSigmaRState ψ).m := by
    rw [MState.traceLeft_m, hρmatrix]
    exact adhwFQSWARSplitMatrix_traceLeft ψ split
  calc
    adhwFQSWARSplitMatrix ψ split = ρsplit.m := hρmatrix.symm
    _ = (ρsplit.traceRight.prod ρsplit.traceLeft).m := hprod
    _ = adhwFQSWARProductSplitMatrix ψ split := by
      ext x y
      simp [Matrix.kroneckerMap_apply,
        adhwFQSWARProductSplitMatrix]
      rw [← MState.traceRight_m ρsplit, hAmatrix]
      rw [← MState.traceLeft_m ρsplit, hBmatrix]

omit [Nonempty e] in
/-- Source ADHW correlation matrix
`ψ^{AR} - ψ^A ⊗ ψ^R`, reindexed by the split, has the source Hilbert--Schmidt
expansion from fqsw.tex lines 682-747. -/
theorem adhwFQSWARCorrelationSplitMatrix_hilbertSchmidtSq
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    hilbertSchmidtSq
      (adhwFQSWARSplitMatrix ψ split -
        adhwFQSWARProductSplitMatrix ψ split) =
      adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
        adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
  let Rm : CMatrix ((q × e) × r) := adhwFQSWARSplitMatrix ψ split
  let Pm : CMatrix ((q × e) × r) := adhwFQSWARProductSplitMatrix ψ split
  have hRm_herm : Rm.IsHermitian := by
    unfold Rm adhwFQSWARSplitMatrix
    exact (adhwFQSWARState ψ).psd.isHermitian.submatrix (fqswARSplitEquiv split).symm
  have hPm_herm : Pm.IsHermitian := by
    unfold Pm adhwFQSWARProductSplitMatrix
    exact kronecker_isHermitian _ _
      ((adhwFQSWARState ψ).traceRight.psd.isHermitian.submatrix split.symm)
      (adhwFQSWSigmaRState ψ).psd.isHermitian
  have hRm_sq : (Rm * Rm).trace.re = adhwFQSWARPurity ψ := by
    calc
      (Rm * Rm).trace.re = hilbertSchmidtSq Rm := by
        exact (hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian hRm_herm).symm
      _ = adhwFQSWARPurity ψ := by
        simpa [Rm] using adhwFQSWARSplitMatrix_hilbertSchmidtSq ψ split
  have hPm_sq : hilbertSchmidtSq Pm =
      adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
    simpa [Pm] using adhwFQSWARProductSplitMatrix_hilbertSchmidtSq ψ split
  have hOverlap : (Rm * Pm).trace.re = adhwFQSWARProductOverlap ψ := by
    simpa [Rm, Pm] using adhwFQSWARProductSplitMatrix_overlap ψ split
  rw [show adhwFQSWARSplitMatrix ψ split -
        adhwFQSWARProductSplitMatrix ψ split = Rm - Pm by rfl]
  rw [hilbertSchmidtSq_sub_of_isHermitian Rm Pm hRm_herm hPm_herm]
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
    [Nonempty q] [Nonempty e] [Nontrivial (q × e)] :
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
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := q × e)
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
    [Nonempty q] [Nonempty e] [Nontrivial (q × e)] :
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
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := q × e)
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
    [Nonempty q] [Nonempty e] [Nontrivial (q × e)] :
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
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := q × e)
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
  rw [Matrix.trace_submatrix _ (tensorPowerProdEquiv q e 2)]
  exact Matrix.trace_kronecker G H

private theorem fqsw_tensorPowerSwapMatrix_two_trace
    {α : Type*} [Fintype α] [DecidableEq α] :
    (tensorPowerSwapMatrixTwo (a := α)).trace = (Fintype.card α : ℂ) := by
  calc
    (tensorPowerSwapMatrixTwo (a := α)).trace =
        ((1 : CMatrix (TensorPower α 2)) * tensorPowerSwapMatrixTwo (a := α)).trace := by
          rw [Matrix.one_mul]
    _ = (tensorPowerKroneckerTwo (a := α) (1 : CMatrix α) *
          tensorPowerSwapMatrixTwo (a := α)).trace := by
          rw [tensorPowerKroneckerTwo_one]
    _ = (Fintype.card α : ℂ) := by
      have h :=
        tensorPowerKroneckerTwo_mul_tensorPowerSwapMatrix_two_trace
          (a := α) (1 : CMatrix α)
      simpa [Matrix.trace_one] using h

omit [Nonempty e] in
private theorem fqsw_splitObservable_trace :
    (twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrixTwo (a := e))).trace =
      (Fintype.card q : ℂ) ^ 2 * (Fintype.card e : ℂ) := by
  rw [fqsw_twoCopySideOperator_trace]
  rw [Matrix.trace_one, fqsw_tensorPowerSwapMatrix_two_trace (α := e)]
  rw [tensorPower_card]
  rw [Nat.cast_pow]

omit [Nonempty e] in
private theorem fqsw_fullSwap_mul_splitObservable_trace [Nonempty q] :
    (tensorPowerSwapMatrixTwo (a := q × e) *
      twoCopySideOperator (a := q) (e := e)
        (1 : CMatrix (TensorPower q 2))
        (tensorPowerSwapMatrixTwo (a := e))).trace =
      (Fintype.card q : ℂ) * (Fintype.card e : ℂ) ^ 2 := by
  rw [tensorPowerSwapMatrix_two_prod_eq_twoCopySideOperator (a := q) (e := e)]
  rw [twoCopySideOperator_mul]
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
    (symmetricProjectionMatrix (a := q × e) 2 *
      twoCopySideOperator (a := q) (e := e)
        (1 : CMatrix (TensorPower q 2))
        (tensorPowerSwapMatrixTwo (a := e))).trace =
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
    (antisymmetricProjectionMatrixTwo (a := q × e) *
      twoCopySideOperator (a := q) (e := e)
        (1 : CMatrix (TensorPower q 2))
        (tensorPowerSwapMatrixTwo (a := e))).trace =
      ((Fintype.card q : ℂ) * (Fintype.card e : ℂ) *
        ((Fintype.card q : ℂ) - (Fintype.card e : ℂ))) / 2 := by
  rw [antisymmetricProjectionMatrixTwo]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  rw [fqsw_splitObservable_trace, adhwFQSW_splitObservable_symmetricProjection_trace]
  ring

/-- ADHW fqsw.tex lines 642-678: Schur twirling of the split observable
`I^{A₁A₁'} ⊗ F^{A₂}` on `A = A₁ × A₂`. -/
theorem adhwFQSW_splitObservable_unitaryTwirl_eq
    (q : Type x) (e : Type y) [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] [Nontrivial (q × e)] :
    unitaryTwirl 2
        (twoCopySideOperator (a := q) (e := e)
          (1 : CMatrix (TensorPower q 2))
          (tensorPowerSwapMatrixTwo (a := e))) =
      ((adhwFQSWSchurPCoeff q e : ℂ) • symmetricProjectionMatrix (a := q × e) 2) +
        ((adhwFQSWSchurQCoeff q e : ℂ) •
          antisymmetricProjectionMatrixTwo (a := q × e)) := by
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
      simpa [Fintype.card_prod] using Fintype.one_lt_card (α := q × e)
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
    [Fintype β] [DecidableEq β] (ρ : CMatrix (α × β)) :
    (tensorPowerKroneckerTwo (a := α × β) ρ *
      twoCopySideOperator (a := α) (e := β)
        (symmetricProjectionMatrix (a := α) 2)
        (tensorPowerSwapMatrixTwo (a := β))).trace =
      ((1 : ℂ) / 2) *
        ((Matrix.traceLeft ρ *
            Matrix.traceLeft ρ).trace +
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
    [Fintype β] [DecidableEq β] (ρ : CMatrix (α × β)) :
    (tensorPowerKroneckerTwo (a := α × β) ρ *
      twoCopySideOperator (a := α) (e := β)
        (antisymmetricProjectionMatrixTwo (a := α))
        (tensorPowerSwapMatrixTwo (a := β))).trace =
      ((1 : ℂ) / 2) *
        ((Matrix.traceLeft ρ *
            Matrix.traceLeft ρ).trace -
          (ρ * ρ).trace) := by
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  rw [twoCopySideOperator_smul_left]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [show twoCopySideOperator (a := α) (e := β)
        ((1 : CMatrix (TensorPower α 2)) - tensorPowerSwapMatrixTwo (a := α))
        (tensorPowerSwapMatrixTwo (a := β)) =
      twoCopySideOperator (a := α) (e := β)
        (1 : CMatrix (TensorPower α 2))
        (tensorPowerSwapMatrixTwo (a := β)) -
      twoCopySideOperator (a := α) (e := β)
        (tensorPowerSwapMatrixTwo (a := α))
        (tensorPowerSwapMatrixTwo (a := β)) by
    rw [sub_eq_add_neg]
    rw [twoCopySideOperator_add_left]
    rw [show
        -tensorPowerSwapMatrixTwo (a := α) =
          ((-1 : ℂ) • tensorPowerSwapMatrixTwo (a := α)) by
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
    (ρ : CMatrix (α × β)) (H : CMatrix (TensorPower β 2)) :
    CMatrix (TensorPower α 2) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun G =>
        (tensorPowerKroneckerTwo (a := α × β) ρ *
          twoCopySideOperator (a := α) (e := β) G H).trace
       map_add' := by
        intro G G'
        rw [twoCopySideOperator_add_left, Matrix.mul_add, Matrix.trace_add]
       map_smul' := by
        intro c G
        change (tensorPowerKroneckerTwo (a := α × β) ρ *
            twoCopySideOperator (a := α) (e := β) ((c : ℂ) • G) H).trace =
          c • (tensorPowerKroneckerTwo (a := α × β) ρ *
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
    (A : CMatrix (TensorPower α 2)) (ρ : CMatrix (α × β))
    (H : CMatrix (TensorPower β 2)) :
    (∫ U : Matrix.unitaryGroup α ℂ,
        (tensorPowerKroneckerTwo (a := α × β) ρ *
          twoCopySideOperator (a := α) (e := β)
            (unitaryTwirlIntegrand (a := α) 2 A U) H).trace
        ∂unitaryHaarMeasure (a := α)) =
      (tensorPowerKroneckerTwo (a := α × β) ρ *
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
      antisymmetricProjectionMatrixTwo (a := α)).trace =
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
    [Fintype r] [DecidableEq r] [Nontrivial (q × e)]
    (ρ : CMatrix ((q × e) × r)) :
    (tensorPowerKroneckerTwo (a := (q × e) × r) ρ *
      twoCopySideOperator (a := q × e) (e := r)
        (unitaryTwirl 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrixTwo (a := e))))
        (tensorPowerSwapMatrixTwo (a := r))).trace =
      (((adhwFQSWSchurPCoeff q e : ℂ) + (adhwFQSWSchurQCoeff q e : ℂ)) / 2) *
          (Matrix.traceLeft ρ *
            Matrix.traceLeft ρ).trace +
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
    [Fintype e] [DecidableEq e] [Nonempty e] [Nontrivial (q × e)]
    (ρ : CMatrix (q × e)) :
    (tensorPowerKroneckerTwo (a := q × e) ρ *
      unitaryTwirl 2
        (twoCopySideOperator (a := q) (e := e)
          (1 : CMatrix (TensorPower q 2))
          (tensorPowerSwapMatrixTwo (a := e)))).trace =
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
    (ρ : CMatrix (q × e)) (U : Matrix.unitaryGroup (q × e) ℂ) :
    (Matrix.traceLeft
        ((U : CMatrix (q × e)) * ρ * star (U : CMatrix (q × e))) *
      Matrix.traceLeft
        ((U : CMatrix (q × e)) * ρ * star (U : CMatrix (q × e)))).trace =
      (tensorPowerKroneckerTwo (a := q × e) ρ *
        unitaryTwirlIntegrand (a := q × e) 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrixTwo (a := e))) U⁻¹).trace := by
  let A : CMatrix (TensorPower (q × e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrixTwo (a := e))
  let U₂ : CMatrix (TensorPower (q × e) 2) :=
    tensorPowerKroneckerTwo (a := q × e) (U : CMatrix (q × e))
  let R : CMatrix (TensorPower (q × e) 2) :=
    tensorPowerKroneckerTwo (a := q × e) ρ
  have htensor :
      tensorPowerKroneckerTwo (a := q × e)
          ((U : CMatrix (q × e)) * ρ * star (U : CMatrix (q × e))) =
        U₂ * R * star U₂ := by
    calc
      tensorPowerKroneckerTwo (a := q × e)
          ((U : CMatrix (q × e)) * ρ * star (U : CMatrix (q × e))) =
        tensorPowerKroneckerTwo (a := q × e)
            ((U : CMatrix (q × e)) * ρ) *
          tensorPowerKroneckerTwo (a := q × e) (star (U : CMatrix (q × e))) := by
          exact (tensorPowerKroneckerTwo_mul (a := q × e)
            ((U : CMatrix (q × e)) * ρ) (star (U : CMatrix (q × e)))).symm
      _ = (tensorPowerKroneckerTwo (a := q × e) (U : CMatrix (q × e)) *
            tensorPowerKroneckerTwo (a := q × e) ρ) *
          tensorPowerKroneckerTwo (a := q × e) (star (U : CMatrix (q × e))) := by
          rw [tensorPowerKroneckerTwo_mul (a := q × e) (U : CMatrix (q × e)) ρ]
      _ = U₂ * R * star U₂ := by
          rw [tensorPowerKroneckerTwo_star]
  rw [← tensorPowerKroneckerTwo_prod_mul_one_swap_trace
    (a := q) (e := e)
    (rho := (U : CMatrix (q × e)) * ρ * star (U : CMatrix (q × e)))]
  rw [htensor]
  calc
    ((U₂ * R * star U₂) * A).trace =
        (R * (star U₂ * A * U₂)).trace := by
          have h := Matrix.trace_mul_comm U₂ (R * star U₂ * A)
          simpa [Matrix.mul_assoc] using h
    _ = (R * unitaryTwirlIntegrand (a := q × e) 2 A U⁻¹).trace := by
          congr 1
          simp [A, U₂, unitaryTwirlIntegrand,
            unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo,
            Matrix.mul_assoc]
    _ = (tensorPowerKroneckerTwo (a := q × e) ρ *
        unitaryTwirlIntegrand (a := q × e) 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrixTwo (a := e))) U⁻¹).trace := by
          rfl

/-- Haar-averaged one-copy purity identity from ADHW fqsw.tex lines
781-784. -/
theorem fqsw_A2_square_trace_average_eq
    {q : Type x} {e : Type y}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] [Nontrivial (q × e)]
    (ρ : CMatrix (q × e)) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        (Matrix.traceLeft
            ((U : CMatrix (q × e)) * ρ * star (U : CMatrix (q × e))) *
          Matrix.traceLeft
            ((U : CMatrix (q × e)) * ρ * star (U : CMatrix (q × e)))).trace
        ∂unitaryHaarMeasure (a := q × e)) =
      (tensorPowerKroneckerTwo (a := q × e) ρ *
        unitaryTwirl 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrixTwo (a := e)))).trace := by
  let A : CMatrix (TensorPower (q × e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrixTwo (a := e))
  let R : CMatrix (TensorPower (q × e) 2) :=
    tensorPowerKroneckerTwo (a := q × e) ρ
  let f : Matrix.unitaryGroup (q × e) ℂ → ℂ := fun U =>
    (R * unitaryTwirlIntegrand (a := q × e) 2 A U).trace
  calc
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        (Matrix.traceLeft
            ((U : CMatrix (q × e)) * ρ * star (U : CMatrix (q × e))) *
          Matrix.traceLeft
            ((U : CMatrix (q × e)) * ρ * star (U : CMatrix (q × e)))).trace
        ∂unitaryHaarMeasure (a := q × e)) =
      ∫ U : Matrix.unitaryGroup (q × e) ℂ, f U⁻¹
        ∂unitaryHaarMeasure (a := q × e) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with U
        simpa [f, R, A] using fqsw_A2_square_trace_eq_twirl_inv_integrand
          (q := q) (e := e) ρ U
    _ = ∫ U : Matrix.unitaryGroup (q × e) ℂ, f U
        ∂unitaryHaarMeasure (a := q × e) := by
        rw [MeasureTheory.integral_inv_eq_self (f := f)
          (μ := unitaryHaarMeasure (a := q × e))]
    _ = (tensorPowerKroneckerTwo (a := q × e) ρ *
        unitaryTwirl 2
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrixTwo (a := e)))).trace := by
        simpa [f, R, A] using
          fqsw_unitaryTwirl_trace_integral_bridge
            (α := q × e) A R

/-- Static flip trick for the `A₂R` marginal after regrouping
`(A₁ × A₂) × R` as `A₁ × (A₂ × R)`.  This is the source-route bridge from the
partial trace square to the two-copy observable
`I^{A₁A₁'} ⊗ F^{A₂} ⊗ F^R`. -/
theorem fqsw_A2R_square_trace_eq_split_observable
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e]
    [Fintype r] [DecidableEq r]
    (ρ : CMatrix ((q × e) × r)) :
    (Matrix.traceLeft
        (ρ.submatrix (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm) *
      Matrix.traceLeft
        (ρ.submatrix (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm)).trace =
      (tensorPowerKroneckerTwo (a := (q × e) × r) ρ *
        twoCopySideOperator (a := q × e) (e := r)
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrixTwo (a := e)))
          (tensorPowerSwapMatrixTwo (a := r))).trace := by
  let ρ' : CMatrix (q × (e × r)) :=
    ρ.submatrix (Equiv.prodAssoc q e r).symm
      (Equiv.prodAssoc q e r).symm
  calc
    (Matrix.traceLeft ρ' *
      Matrix.traceLeft ρ').trace =
        ∑ i : q, ∑ k : e, ∑ s : r, ∑ j : q, ∑ l : e, ∑ t : r,
          ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s) := by
      rw [← tensorPowerKroneckerTwo_prod_mul_one_swap_trace
        (a := q) (e := e × r) (rho := ρ')]
      rw [Matrix.trace, sum_tensorPower_twoCopyTensorWord (β := ℂ)]
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
        (tensorPowerKroneckerTwo (a := q × (e × r)) ρ' *
          twoCopySideOperator (a := q) (e := e × r)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrixTwo (a := e × r)))
          (twoCopyTensorWord (a := q × (e × r)) (i, (k, s)) (j, (l, t)))
          (twoCopyTensorWord (a := q × (e × r)) (i, (k, s)) (j, (l, t))) =
        ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s)
      rw [Matrix.mul_apply, sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      simp_rw [Fintype.sum_prod_type]
      simpa [ρ', Equiv.prodAssoc, Matrix.one_apply,
        permEquiv_twoCopySwapPerm_twoCopyTensorWord, twoCopyTensorWord_eq_iff,
        mul_comm, mul_left_comm, mul_assoc] using
          fqsw_traceLeft_flip_entry_sum_prod
            (α := q) (β := e) (γ := r) ρ' i j k l s t
    _ = (tensorPowerKroneckerTwo (a := (q × e) × r) ρ *
        twoCopySideOperator (a := q × e) (e := r)
          (twoCopySideOperator (a := q) (e := e)
            (1 : CMatrix (TensorPower q 2))
            (tensorPowerSwapMatrixTwo (a := e)))
          (tensorPowerSwapMatrixTwo (a := r))).trace := by
      symm
      rw [Matrix.trace, sum_tensorPower_twoCopyTensorWord (β := ℂ)]
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
        (tensorPowerKroneckerTwo (a := (q × e) × r) ρ *
          twoCopySideOperator (a := q × e) (e := r)
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrixTwo (a := e)))
            (tensorPowerSwapMatrixTwo (a := r)))
          (twoCopyTensorWord (a := (q × e) × r) ((i, k), s) ((j, l), t))
          (twoCopyTensorWord (a := (q × e) × r) ((i, k), s) ((j, l), t)) =
        ρ ((i, k), s) ((i, l), t) * ρ ((j, l), t) ((j, k), s)
      rw [Matrix.mul_apply, sum_tensorPower_twoCopyTensorWord (β := ℂ)]
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
    (ρ : CMatrix ((q × e) × r)) (U : Matrix.unitaryGroup (q × e) ℂ) :
    (Matrix.traceLeft
        ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
            ρ * star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm) *
      Matrix.traceLeft
        ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
            ρ * star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm)).trace =
      (tensorPowerKroneckerTwo (a := (q × e) × r) ρ *
        twoCopySideOperator (a := q × e) (e := r)
          (unitaryTwirlIntegrand (a := q × e) 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrixTwo (a := e))) U⁻¹)
          (tensorPowerSwapMatrixTwo (a := r))).trace := by
  let A : CMatrix (TensorPower (q × e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrixTwo (a := e))
  let H : CMatrix (TensorPower r 2) := tensorPowerSwapMatrixTwo (a := r)
  let K : CMatrix ((q × e) × r) :=
    (U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)
  let U₂ : CMatrix (TensorPower (q × e) 2) :=
    tensorPowerKroneckerTwo (a := q × e) (U : CMatrix (q × e))
  let K₂ : CMatrix (TensorPower ((q × e) × r) 2) :=
    tensorPowerKroneckerTwo (a := (q × e) × r) K
  let R : CMatrix (TensorPower ((q × e) × r) 2) :=
    tensorPowerKroneckerTwo (a := (q × e) × r) ρ
  have htensor :
      tensorPowerKroneckerTwo (a := (q × e) × r)
          (K * ρ * star K) =
        K₂ * R * star K₂ := by
    calc
      tensorPowerKroneckerTwo (a := (q × e) × r) (K * ρ * star K) =
          tensorPowerKroneckerTwo (a := (q × e) × r) (K * ρ) *
            tensorPowerKroneckerTwo (a := (q × e) × r) (star K) := by
            exact (tensorPowerKroneckerTwo_mul (a := (q × e) × r)
              (K * ρ) (star K)).symm
      _ = (tensorPowerKroneckerTwo (a := (q × e) × r) K *
            tensorPowerKroneckerTwo (a := (q × e) × r) ρ) *
            tensorPowerKroneckerTwo (a := (q × e) × r) (star K) := by
            rw [tensorPowerKroneckerTwo_mul (a := (q × e) × r) K ρ]
      _ = K₂ * R * star K₂ := by
            rw [tensorPowerKroneckerTwo_star]
  have hK₂ :
      K₂ = twoCopySideOperator (a := q × e) (e := r) U₂
          (1 : CMatrix (TensorPower r 2)) := by
    simpa [K₂, K, U₂] using
      tensorPowerKroneckerTwo_kronecker_one
        (a := q × e) (e := r) (U : CMatrix (q × e))
  have hstarK₂ :
      star K₂ =
        twoCopySideOperator (a := q × e) (e := r) (star U₂)
          (1 : CMatrix (TensorPower r 2)) := by
    rw [hK₂]
    ext x y
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      twoCopySideOperator_apply, Matrix.one_apply]
    by_cases hxy :
        ((tensorPowerProdEquiv (q × e) r 2) y).2 =
          ((tensorPowerProdEquiv (q × e) r 2) x).2
    · have hyx :
          ((tensorPowerProdEquiv (q × e) r 2) x).2 =
            ((tensorPowerProdEquiv (q × e) r 2) y).2 := hxy.symm
      rw [if_pos hxy, if_pos hyx]
      simp
    · have hyx :
          ¬ ((tensorPowerProdEquiv (q × e) r 2) x).2 =
            ((tensorPowerProdEquiv (q × e) r 2) y).2 := by
          intro hyx
          exact hxy hyx.symm
      rw [if_neg hxy, if_neg hyx]
      simp
  rw [show
      ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
          ρ * star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) =
        K * ρ * star K by rfl]
  rw [fqsw_A2R_square_trace_eq_split_observable
    (q := q) (e := e) (r := r) (ρ := K * ρ * star K)]
  rw [htensor]
  calc
    ((K₂ * R * star K₂) *
        twoCopySideOperator (a := q × e) (e := r) A H).trace =
      (R * (star K₂ *
        twoCopySideOperator (a := q × e) (e := r) A H * K₂)).trace := by
        have h := Matrix.trace_mul_comm K₂
          (R * star K₂ * twoCopySideOperator (a := q × e) (e := r) A H)
        simpa [Matrix.mul_assoc] using h
    _ = (R * twoCopySideOperator (a := q × e) (e := r)
        (unitaryTwirlIntegrand (a := q × e) 2 A U⁻¹) H).trace := by
        congr 1
        rw [hstarK₂, hK₂]
        rw [twoCopySideOperator_mul]
        rw [twoCopySideOperator_mul]
        simp [A, H, U₂, unitaryTwirlIntegrand,
          unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo,
          Matrix.mul_assoc]
    _ = (tensorPowerKroneckerTwo (a := (q × e) × r) ρ *
        twoCopySideOperator (a := q × e) (e := r)
          (unitaryTwirlIntegrand (a := q × e) 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrixTwo (a := e))) U⁻¹)
          (tensorPowerSwapMatrixTwo (a := r))).trace := by
        rfl

/-- Haar-averaged `A₂R` purity identity from ADHW fqsw.tex lines 708-714. -/
theorem fqsw_A2R_square_trace_average_eq
    {q : Type x} {e : Type y} {r : Type z}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype r] [DecidableEq r] [Nontrivial (q × e)]
    (ρ : CMatrix ((q × e) × r)) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      (Matrix.traceLeft
          ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
              ρ * star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm) *
        Matrix.traceLeft
          ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
              ρ * star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm)).trace
      ∂unitaryHaarMeasure (a := q × e)) =
      (tensorPowerKroneckerTwo (a := (q × e) × r) ρ *
        twoCopySideOperator (a := q × e) (e := r)
          (unitaryTwirl 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrixTwo (a := e))))
          (tensorPowerSwapMatrixTwo (a := r))).trace := by
  let A : CMatrix (TensorPower (q × e) 2) :=
    twoCopySideOperator (a := q) (e := e)
      (1 : CMatrix (TensorPower q 2))
      (tensorPowerSwapMatrixTwo (a := e))
  let H : CMatrix (TensorPower r 2) := tensorPowerSwapMatrixTwo (a := r)
  let R : CMatrix (TensorPower ((q × e) × r) 2) :=
    tensorPowerKroneckerTwo (a := (q × e) × r) ρ
  let f : Matrix.unitaryGroup (q × e) ℂ → ℂ := fun U =>
    (R *
      twoCopySideOperator (a := q × e) (e := r)
        (unitaryTwirlIntegrand (a := q × e) 2 A U) H).trace
  calc
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      (Matrix.traceLeft
          ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
              ρ * star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm) *
        Matrix.traceLeft
          ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
              ρ * star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm)).trace
      ∂unitaryHaarMeasure (a := q × e)) =
        ∫ U : Matrix.unitaryGroup (q × e) ℂ, f U⁻¹
          ∂unitaryHaarMeasure (a := q × e) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with U
        simpa [f, R, A, H] using
          fqsw_A2R_square_trace_eq_twirl_inv_integrand
            (q := q) (e := e) (r := r) ρ U
    _ = ∫ U : Matrix.unitaryGroup (q × e) ℂ, f U
        ∂unitaryHaarMeasure (a := q × e) := by
        rw [MeasureTheory.integral_inv_eq_self (f := f)
          (μ := unitaryHaarMeasure (a := q × e))]
    _ = (tensorPowerKroneckerTwo (a := (q × e) × r) ρ *
        twoCopySideOperator (a := q × e) (e := r)
          (unitaryTwirl 2
            (twoCopySideOperator (a := q) (e := e)
              (1 : CMatrix (TensorPower q 2))
              (tensorPowerSwapMatrixTwo (a := e))))
          (tensorPowerSwapMatrixTwo (a := r))).trace := by
        simpa [f, R, A, H] using
          fqsw_unitaryTwirl_twoCopySide_trace_integral_bridge
            (α := q × e) (β := r) A ρ H

/-- Subtracting the maximally mixed state turns the Hilbert--Schmidt square
into the output purity minus `1/d`. -/
theorem fqsw_hilbertSchmidtSq_sub_uniformState
    {e : Type y} [Fintype e] [DecidableEq e] [Nonempty e] (ρ : MState e) :
    hilbertSchmidtSq (ρ.m - (MState.uniform : MState e).m) =
      (ρ.m * ρ.m).trace.re - (1 / (Fintype.card e : ℝ)) := by
  have hcard_ne : (Fintype.card e : ℝ) ≠ 0 := by positivity
  have hcross :
      (ρ.m * (MState.uniform : MState e).m).trace.re =
        1 / (Fintype.card e : ℝ) := by
    simp [Matrix.trace_smul,
      ρ.tr', one_div]
  have hmm :
      hilbertSchmidtSq (MState.uniform : MState e).m =
        1 / (Fintype.card e : ℝ) := by
    unfold hilbertSchmidtSq
    simp [Matrix.trace_smul, Matrix.trace_one, one_div]
  rw [hilbertSchmidtSq_sub_of_isHermitian
    ρ.m (MState.uniform : MState e).m
    ρ.psd.isHermitian (MState.uniform : MState e).psd.isHermitian]
  rw [hcross, hmm]
  ring

/-- Exact Hilbert--Schmidt one-shot expression from ADHW fqsw.tex lines
682-747, written in the repository's source-state notation. -/
def adhwFQSWHSOneShotExact
    (ψ : Ket ((a × b) × r)) (q : Type x) (e : Type y)
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
    [Nonempty q] [Subsingleton (q × e)]
    (ψ : Ket ((a × b) × r)) :
    adhwFQSWHSOneShotExact ψ q e = 0 := by
  classical
  let q0 : q := Classical.choice inferInstance
  let e0 : e := Classical.choice inferInstance
  have : Subsingleton q :=
    Function.Injective.subsingleton (f := fun x : q => (x, e0))
      (by intro x y h; exact congrArg Prod.fst h)
  have : Subsingleton e :=
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
    (ψ : Ket ((a × b) × r)) (q : Type x) [Fintype q] : ℝ :=
  ((Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
      ((Fintype.card q : ℝ) ^ 2)) *
    (adhwFQSWARPurity ψ + adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)

/-- Max-mixed `A₂` square bound from ADHW fqsw.tex lines 767-795. -/
def adhwFQSWMaxMixedA2SqBound
    (ψ : Ket ((a × b) × r)) (q : Type x) [Fintype q] : ℝ :=
  ((Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2)) * adhwFQSWAPurity ψ

/-- ADHW fqsw.tex lines 781-787: in the nontrivial Schur case, the
Haar-averaged Hilbert--Schmidt distance of the `A₂` marginal from maximally
mixed is bounded by the source one-copy purity term. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtAverage_le_of_nontrivial
    [Nonempty q] [Nontrivial (q × e)]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (Fintype.card e : ℝ) *
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q := by
  let ρA : CMatrix (q × e) := adhwFQSWASplitMatrix ψ split
  let f : Matrix.unitaryGroup (q × e) ℂ → ℂ := fun U =>
    (Matrix.traceLeft
        ((U : CMatrix (q × e)) * ρA * star (U : CMatrix (q × e))) *
      Matrix.traceLeft
        ((U : CMatrix (q × e)) * ρA * star (U : CMatrix (q × e)))).trace
  have hf_cont : Continuous f := by
    unfold f
    continuity
  have hf_int : MeasureTheory.Integrable f (unitaryHaarMeasure (a := q × e)) :=
    hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre_integral :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ, (f U).re
        ∂unitaryHaarMeasure (a := q × e)) =
        (∫ U : Matrix.unitaryGroup (q × e) ℂ, f U
          ∂unitaryHaarMeasure (a := q × e)).re := by
    simpa [f] using (Complex.reCLM.integral_comp_comm hf_int)
  have hρ_trace : ρA.trace = 1 := by
    simpa [ρA] using adhwFQSWASplitMatrix_trace ψ split
  have hρ_herm : ρA.IsHermitian := by
    unfold ρA adhwFQSWASplitMatrix
    exact (adhwFQSWARState ψ).traceRight.psd.isHermitian.submatrix split.symm
  have hρ_purity : (ρA * ρA).trace.re = adhwFQSWAPurity ψ := by
    calc
      (ρA * ρA).trace.re = hilbertSchmidtSq ρA := by
        exact (hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian hρ_herm).symm
      _ = adhwFQSWAPurity ψ := by
        simpa [ρA] using adhwFQSWASplitMatrix_hilbertSchmidtSq ψ split
  have hcomplex :=
    (fqsw_A2_square_trace_average_eq (q := q) (e := e) ρA).trans
      (fqsw_splitObservable_unitaryTwirl_trace (q := q) (e := e) ρA)
  have hreal := congrArg Complex.re hcomplex
  have haverage_purity :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ, (f U).re
        ∂unitaryHaarMeasure (a := q × e)) =
        ((adhwFQSWSchurPCoeff q e + adhwFQSWSchurQCoeff q e) / 2) +
          ((adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2) *
            adhwFQSWAPurity ψ := by
    rw [hre_integral]
    simpa [f, ρA, hρ_trace, hρ_purity, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.div_re] using hreal
  have hhs_point : ∀ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U =
        (f U).re - (1 / (Fintype.card e : ℝ)) := by
    intro U
    let σ : MState e :=
      adhwFQSWSigmaA2StateOfIsometry (q := q) (e := e) ψ
        (adhwFQSWAliceIsometryOfSplitUnitary split U)
    have hσ :=
      fqsw_hilbertSchmidtSq_sub_uniformState (e := e) σ
    simpa [adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary,
      adhwFQSWMaximallyMixedA2State, σ, f, ρA,
      adhwFQSWSigmaA2StateOfSplitUnitary_matrix_eq_traceLeft_applyMatrix_A]
      using hσ
  have hf_re_int : MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (q × e) ℂ => (f U).re)
      (unitaryHaarMeasure (a := q × e)) :=
    Complex.reCLM.integrable_comp hf_int
  have hhs_average :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) =
        (∫ U : Matrix.unitaryGroup (q × e) ℂ, (f U).re
          ∂unitaryHaarMeasure (a := q × e)) -
          (1 / (Fintype.card e : ℝ)) := by
    calc
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) =
          ∫ U : Matrix.unitaryGroup (q × e) ℂ,
            ((f U).re - (1 / (Fintype.card e : ℝ)))
            ∂unitaryHaarMeasure (a := q × e) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with U
            exact hhs_point U
      _ = (∫ U : Matrix.unitaryGroup (q × e) ℂ, (f U).re
            ∂unitaryHaarMeasure (a := q × e)) -
            (1 / (Fintype.card e : ℝ)) := by
            rw [MeasureTheory.integral_sub hf_re_int (MeasureTheory.integrable_const _)]
            rw [MeasureTheory.integral_const]
            simp [MeasureTheory.measureReal_def]
  let dq : ℝ := Fintype.card q
  let de : ℝ := Fintype.card e
  let P : ℝ := adhwFQSWAPurity ψ
  have hP_nonneg : 0 ≤ P := by
    simpa [P, adhwFQSWAPurity] using
      hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).traceRight.m)
  have hsum_le :
      (adhwFQSWSchurPCoeff q e + adhwFQSWSchurQCoeff q e) / 2 ≤
        1 / de := by
    simpa [de] using adhwFQSWSchur_half_sum_le_inv_card_e q e
  have hsub_le :
      (adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2 ≤
        1 / dq := by
    simpa [dq] using adhwFQSWSchur_half_sub_le_inv_card_q q e
  have hhs_le :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) ≤
        (1 / dq) * P := by
    rw [hhs_average, haverage_purity]
    nlinarith [mul_le_mul_of_nonneg_right hsub_le hP_nonneg, hsum_le]
  have hde_nonneg : 0 ≤ de := by
    dsimp [de]
    positivity
  have hcard_a : (Fintype.card a : ℝ) = dq * de := by
    have hnat : Fintype.card a = Fintype.card (q × e) :=
      Fintype.card_congr split
    rw [Fintype.card_prod] at hnat
    dsimp [dq, de]
    exact_mod_cast hnat
  have hdq_pos : 0 < dq := by
    dsimp [dq]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card q)
  unfold adhwFQSWMaxMixedA2SqBound
  change de *
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) ≤
      ((Fintype.card a : ℝ) / dq ^ 2) * P
  calc
    de *
        (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := q × e)) ≤ de * ((1 / dq) * P) :=
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (U : Matrix.unitaryGroup (q × e) ℂ) :
    adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U =
      hilbertSchmidtSq
        (Matrix.traceLeft
          ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
              (adhwFQSWARSplitMatrix ψ split -
                adhwFQSWARProductSplitMatrix ψ split) *
              star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm)) := by
  let K : CMatrix ((q × e) × r) :=
    (U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)
  let Rm : CMatrix ((q × e) × r) := adhwFQSWARSplitMatrix ψ split
  let Pm : CMatrix ((q × e) × r) := adhwFQSWARProductSplitMatrix ψ split
  rw [adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary]
  rw [adhwFQSWSigmaA2RStateOfSplitUnitary_matrix_eq_traceLeft_applyMatrix_AR_split]
  rw [adhwFQSWProductA2RStateOfSplitUnitary_matrix_eq_traceLeft_applyMatrix_ARProduct]
  rw [← Matrix.traceLeft_sub]
  change
    hilbertSchmidtSq
      (Matrix.traceLeft
        ((K * Rm * star K).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm -
          (K * Pm * star K).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm)) =
      hilbertSchmidtSq
        (Matrix.traceLeft
          ((K * (Rm - Pm) * star K).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm))
  have hsubmatrix :
      (K * Rm * star K).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm -
          (K * Pm * star K).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm =
        (K * (Rm - Pm) * star K).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm := by
    ext x y
    simp [Matrix.mul_sub, Matrix.sub_mul]
  rw [hsubmatrix]

/-- ADHW fqsw.tex lines 682-747 in the nontrivial Schur case: the Haar
average of the product-decoupling Hilbert--Schmidt square is exactly the
source one-shot expression. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtAverage_eq_of_nontrivial
    [Nonempty q] [Nontrivial (q × e)]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := q × e)) =
      adhwFQSWHSOneShotExact ψ q e := by
  let Δ : CMatrix ((q × e) × r) :=
    adhwFQSWARSplitMatrix ψ split -
      adhwFQSWARProductSplitMatrix ψ split
  let g : Matrix.unitaryGroup (q × e) ℂ → ℂ := fun U =>
    (Matrix.traceLeft
        ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
            Δ *
            star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm) *
      Matrix.traceLeft
        ((((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)) *
            Δ *
            star ((U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r))).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm)).trace
  have hg_cont : Continuous g := by
    unfold g
    continuity
  have hg_int : MeasureTheory.Integrable g (unitaryHaarMeasure (a := q × e)) :=
    hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre_integral :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ, (g U).re
        ∂unitaryHaarMeasure (a := q × e)) =
        (∫ U : Matrix.unitaryGroup (q × e) ℂ, g U
          ∂unitaryHaarMeasure (a := q × e)).re := by
    simpa [g] using (Complex.reCLM.integral_comp_comm hg_int)
  have hRm_herm : (adhwFQSWARSplitMatrix ψ split).IsHermitian := by
    unfold adhwFQSWARSplitMatrix
    exact (adhwFQSWARState ψ).psd.isHermitian.submatrix (fqswARSplitEquiv split).symm
  have hPm_herm : (adhwFQSWARProductSplitMatrix ψ split).IsHermitian := by
    unfold adhwFQSWARProductSplitMatrix
    exact kronecker_isHermitian _ _
      ((adhwFQSWARState ψ).traceRight.psd.isHermitian.submatrix split.symm)
      (adhwFQSWSigmaRState ψ).psd.isHermitian
  have hΔ_herm : Δ.IsHermitian := by
    dsimp [Δ]
    exact Matrix.IsHermitian.sub hRm_herm hPm_herm
  have hΔ_trace :
      Matrix.traceLeft Δ = 0 := by
    dsimp [Δ]
    rw [Matrix.traceLeft_sub]
    rw [adhwFQSWARSplitMatrix_traceLeft, adhwFQSWARProductSplitMatrix_traceLeft]
    simp
  have hΔ_hs :
      (Δ * Δ).trace.re =
        adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
          adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
    calc
      (Δ * Δ).trace.re = hilbertSchmidtSq Δ := by
        exact (hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian hΔ_herm).symm
      _ = adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
          adhwFQSWAPurity ψ * adhwFQSWRPurity ψ := by
        simpa [Δ] using adhwFQSWARCorrelationSplitMatrix_hilbertSchmidtSq ψ split
  have hpoint : ∀ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U =
        (g U).re := by
    intro U
    let K : CMatrix ((q × e) × r) :=
      (U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)
    let M : CMatrix (e × r) :=
      Matrix.traceLeft
        ((K * Δ * star K).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm)
    have hconj : (K * Δ * star K).IsHermitian := by
      simpa [K, Matrix.star_eq_conjTranspose] using
        Matrix.isHermitian_mul_mul_conjTranspose K hΔ_herm
    have hsub :
        ((K * Δ * star K).submatrix
          (Equiv.prodAssoc q e r).symm
          (Equiv.prodAssoc q e r).symm).IsHermitian := by
      exact hconj.submatrix (Equiv.prodAssoc q e r).symm
    have hM_herm : M.IsHermitian := by
      exact Matrix.IsHermitian.traceLeft hsub
    rw [adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_eq_correlation]
    rw [hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian hM_herm]
  have hcomplex :=
    (fqsw_A2R_square_trace_average_eq (q := q) (e := e) (r := r) Δ).trans
      (fqsw_splitObservable_unitaryTwirl_swap_trace (q := q) (e := e) (r := r) Δ)
  have hreal := congrArg Complex.re hcomplex
  have haverage :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) =
        ((adhwFQSWSchurPCoeff q e - adhwFQSWSchurQCoeff q e) / 2) *
          (adhwFQSWARPurity ψ - 2 * adhwFQSWARProductOverlap ψ +
            adhwFQSWAPurity ψ * adhwFQSWRPurity ψ) := by
    calc
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) =
          ∫ U : Matrix.unitaryGroup (q × e) ℂ, (g U).re
            ∂unitaryHaarMeasure (a := q × e) := by
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
    [Nonempty q] [Nontrivial (q × e)]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := q × e)) ≤
      adhwFQSWHSOneShotExact ψ q e := by
  exact le_of_eq (adhwFQSWProductDecouplingHilbertSchmidtAverage_eq_of_nontrivial
    ψ split)

/-- ADHW fqsw.tex lines 682-747, including the degenerate one-point split
case, stated as the Hilbert--Schmidt average bound consumed by the one-shot
assembly. -/
theorem adhwFQSWProductDecouplingHilbertSchmidtAverage_le
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := q × e)) ≤
      adhwFQSWHSOneShotExact ψ q e := by
  by_cases hnt : Nontrivial (q × e)
  · exact adhwFQSWProductDecouplingHilbertSchmidtAverage_le_of_nontrivial
      ψ split
  · have : Subsingleton (q × e) :=
      not_nontrivial_iff_subsingleton.mp hnt
    have hΔzero :=
      adhwFQSWARCorrelationSplitMatrix_eq_zero_of_subsingleton ψ split
    have hfun :
        (fun U : Matrix.unitaryGroup (q × e) ℂ =>
          adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U) =
        fun _ => 0 := by
      funext U
      rw [adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary_eq_correlation]
      rw [hΔzero]
      let K : CMatrix ((q × e) × r) :=
        (U : CMatrix (q × e)) ⊗ₖ (1 : CMatrix r)
      let M : CMatrix (e × r) :=
        Matrix.traceLeft
          ((K * (0 : CMatrix ((q × e) × r)) * star K).submatrix
            (Equiv.prodAssoc q e r).symm
            (Equiv.prodAssoc q e r).symm)
      change hilbertSchmidtSq M = 0
      have hM : M = 0 := by
        ext x y
        simp [M, K, Matrix.traceLeft]
      rw [hM]
      simp [hilbertSchmidtSq]
    rw [hfun, MeasureTheory.integral_zero]
    rw [adhwFQSWHSOneShotExact_eq_zero_of_subsingleton (q := q) (e := e) ψ]

/-- ADHW fqsw.tex lines 781-787, including the degenerate one-point split
case, stated as the max-mixed `A₂` Hilbert--Schmidt average bound consumed by
the one-shot assembly. -/
theorem adhwFQSWMaxMixedA2HilbertSchmidtAverage_le
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e)) :
    (Fintype.card e : ℝ) *
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q := by
  by_cases hnt : Nontrivial (q × e)
  · exact adhwFQSWMaxMixedA2HilbertSchmidtAverage_le_of_nontrivial
      ψ split
  · have : Subsingleton (q × e) :=
      not_nontrivial_iff_subsingleton.mp hnt
    classical
    let q0 : q := Classical.choice inferInstance
    have : Subsingleton e :=
      Function.Injective.subsingleton (f := fun y : e => (q0, y))
        (by intro x y h; exact congrArg Prod.snd h)
    have hfun :
        (fun U : Matrix.unitaryGroup (q × e) ℂ =>
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U) =
        fun _ => 0 := by
      funext U
      rw [adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary]
      rw [MState.eq_uniform_of_subsingleton
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
          hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).traceRight.m))

/-- Fourth-root argument in the one-shot FQSW theorem of ADHW fqsw.tex
lines 553-568, assembled from the decoupling and max-mixed estimates in
ADHW fqsw.tex lines 580-841. -/
def adhwFQSWOneShotFourthRootArgument
    (ψ : Ket ((a × b) × r)) (q : Type x) [Fintype q] : ℝ :=
  (2 * (Fintype.card a : ℝ) * (Fintype.card r : ℝ) /
      ((Fintype.card q : ℝ) ^ 2)) *
    (adhwFQSWARPurity ψ + 2 * adhwFQSWAPurity ψ * adhwFQSWRPurity ψ)

/-- ADHW one-shot FQSW trace-norm error bound from fqsw.tex lines 553-568. -/
def adhwFQSWOneShotErrorBound
    (ψ : Ket ((a × b) × r)) (q : Type x) [Fintype q] : ℝ :=
  2 * Real.sqrt (Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q))

/-- The ADHW one-shot fourth-root argument is nonnegative. -/
theorem adhwFQSWOneShotFourthRootArgument_nonneg
    (ψ : Ket ((a × b) × r)) (q : Type x) [Fintype q] :
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
    simpa [adhwFQSWARPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).m
  have hA : 0 ≤ adhwFQSWAPurity ψ := by
    simpa [adhwFQSWAPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).traceRight.m
  have hR : 0 ≤ adhwFQSWRPurity ψ := by
    simpa [adhwFQSWRPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).traceLeft.m
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
    (φ : Ket ((a × b) × r)) (q : Type x) [Fintype q]
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hHS :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) ≤
        adhwFQSWHSOneShotExact ψ q e) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
      (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e := by
  calc
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
        ((Fintype.card e : ℝ) * (Fintype.card r : ℝ)) *
          (∫ U : Matrix.unitaryGroup (q × e) ℂ,
            adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
            ∂unitaryHaarMeasure (a := q × e)) :=
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hHS :
      (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := q × e)) ≤
        adhwFQSWMaxMixedA2SqBound ψ q) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
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
    simpa [X, adhwFQSWARPurity] using hilbertSchmidtSq_nonneg (adhwFQSWARState ψ).m
  have hY_nonneg : 0 ≤ Y := by
    exact mul_nonneg
      (by simpa [Y, adhwFQSWAPurity] using
        hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).traceRight.m))
      (by simpa [Y, adhwFQSWRPurity] using
        hilbertSchmidtSq_nonneg ((adhwFQSWARState ψ).traceLeft.m))
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
    have hnat : Fintype.card a = Fintype.card (q × e) :=
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
  have hrhs : dq * de * dr / dq ^ 2 * (X + Y) = de * dr * (1 / dq * (X + Y)) := by
    field_simp
  rw [hrhs]
  exact hscaled

/-- Source-route Schur twirling record for ADHW fqsw.tex lines 642-678, the
Schur step inside the decoupling proof of fqsw.tex lines 580-841. -/
structure ADHWSchurTwirling
    (ψ : Ket ((a × b) × r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] where
  /-- The coefficient of the identity term in the twirl. -/
  pCoeff : ℝ
  /-- The coefficient of the swap term in the twirl. -/
  qCoeff : ℝ
  /-- The identity coefficient is the one determined by the register dimensions. -/
  pCoeff_eq : pCoeff = adhwFQSWSchurPCoeff q e
  /-- The swap coefficient is the one determined by the register dimensions. -/
  qCoeff_eq : qCoeff = adhwFQSWSchurQCoeff q e

/-- Source-route Hilbert--Schmidt one-shot bound record for ADHW fqsw.tex
lines 680-747. -/
structure ADHWHSOneShotBound
    (ψ : Ket ((a × b) × r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] where
  /-- The Schur coefficients used by the Hilbert--Schmidt estimate. -/
  schur : ADHWSchurTwirling ψ q e
  /-- The Haar-average Hilbert--Schmidt norm of the decoupling error. -/
  hsAverage : ℝ
  /-- The average is the exact Schur expression. -/
  hsAverage_eq : hsAverage = adhwFQSWHSOneShotExact ψ q e

/-- The source Schur-coefficient record is canonical: its fields are the two
coefficients appearing in ADHW fqsw.tex lines 642-678. -/
def adhwFQSWSchurTwirling
    (ψ : Ket ((a × b) × r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ADHWSchurTwirling ψ q e where
  pCoeff := adhwFQSWSchurPCoeff q e
  qCoeff := adhwFQSWSchurQCoeff q e
  pCoeff_eq := rfl
  qCoeff_eq := rfl

/-- The source Hilbert--Schmidt one-shot expression record is canonical once
the Schur coefficients have been fixed. -/
def adhwFQSWHSOneShotBound
    (ψ : Ket ((a × b) × r)) (q : Type x) (e : Type y)
    [Fintype q] [Fintype e] : ADHWHSOneShotBound ψ q e where
  schur := adhwFQSWSchurTwirling ψ q e
  hsAverage := adhwFQSWHSOneShotExact ψ q e
  hsAverage_eq := rfl

/-- Source-route ADHW trace-norm decoupling record for fqsw.tex lines 580-760,
including the Schur/HS route from fqsw.tex lines 642-747. -/
structure ADHWTraceNormDecouplingBound
    (ψ : Ket ((a × b) × r)) (q : Type x) (e : Type y)
    (split : a ≃ (q × e))
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  /-- The underlying Hilbert--Schmidt one-shot estimate. -/
  hs : ADHWHSOneShotBound ψ q e
  /-- The Haar average of the squared trace-norm decoupling error is bounded. -/
  traceNormAverageSq_le :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
    adhwFQSWTraceNormDecouplingSqBound ψ q

/-- Source-route max-mixed `A₂` estimate record for ADHW fqsw.tex lines
767-795. -/
structure ADHWMaxMixedA2Estimate
    (ψ : Ket ((a × b) × r)) (q : Type x) (e : Type y)
    (split : a ≃ (q × e))
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  /-- The Schur coefficients used by the estimate. -/
  schur : ADHWSchurTwirling ψ q e
  /-- The Haar average of the squared distance to the maximally mixed `A₂` is bounded. -/
  maxMixedAverageSq_le :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
    adhwFQSWMaxMixedA2SqBound ψ q

/-- Split-specific trace-norm square-average tail for the product-decoupling
component.  The explicit hypothesis is the remaining Schur/HS average bridge
for the split unitary integrand; from that bridge the dimension Cauchy--Schwarz
tail and the ADHW `1/d_{A₁}` prefactor estimate give the public square bound. -/
theorem adhwFQSWProductDecouplingTraceNormAverageSq_le
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hHS :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := q × e)) ≤
      (Fintype.card e : ℝ) * (Fintype.card r : ℝ) *
        adhwFQSWHSOneShotExact ψ q e) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
    adhwFQSWTraceNormDecouplingSqBound ψ q :=
  hHS.trans (adhwFQSW_traceNormSqBound_of_HSOneShotExact ψ split)

/-- Split-specific trace-norm square-average tail for the max-mixed `A₂`
component.  The explicit hypothesis is exactly the remaining Schur/max-mixed
average estimate for the split unitary integrand. -/
theorem adhwFQSWMaxMixedA2TraceNormAverageSq_le
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hMaxMixed :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := q × e)) ≤
      adhwFQSWMaxMixedA2SqBound ψ q) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
        ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
    adhwFQSWMaxMixedA2SqBound ψ q :=
  hMaxMixed

/-- Constructor for the split-specific ADHW trace-norm decoupling component
record, once the product-decoupling Schur/HS average bridge is available. -/
theorem exists_adhwFQSWTraceNormDecouplingBound
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hHS :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := q × e)) ≤
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hHS :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWProductDecouplingHilbertSchmidtIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) ≤
        adhwFQSWHSOneShotExact ψ q e) :
    Nonempty (ADHWTraceNormDecouplingBound ψ q e split) := by
  exact exists_adhwFQSWTraceNormDecouplingBound ψ split
    (adhwFQSWProductDecouplingTraceNormAverageSq_le_of_hilbertSchmidtAverage
      ψ split hHS)

/-- Constructor for the split-specific ADHW max-mixed `A₂` component record,
once the max-mixed Schur average estimate is available. -/
theorem exists_adhwFQSWMaxMixedA2Estimate
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hMaxMixed :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary
          ψ split U ^ 2
        ∂unitaryHaarMeasure (a := q × e)) ≤
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hHS :
      (Fintype.card e : ℝ) *
        (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWMaxMixedA2HilbertSchmidtIntegrandOfSplitUnitary ψ split U
          ∂unitaryHaarMeasure (a := q × e)) ≤
        adhwFQSWMaxMixedA2SqBound ψ q) :
    Nonempty (ADHWMaxMixedA2Estimate ψ q e split) := by
  exact exists_adhwFQSWMaxMixedA2Estimate ψ split
    (adhwFQSWMaxMixedA2TraceNormAverageSq_le_of_hilbertSchmidtAverage
      ψ split hHS)

/-- The two source-route component square-average records imply the final ADHW
decoupling square-average bound after the triangle/product-contraction step. -/
theorem adhwFQSWFinalTraceNormAverageSq_le_component_records
    [Nonempty q]
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e))
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q := by
  calc
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
      adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
      ∂unitaryHaarMeasure (a := q × e)) ≤
        2 * (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWProductDecouplingTraceNormIntegrandOfSplitUnitary ψ split U ^ 2
          ∂unitaryHaarMeasure (a := q × e)) +
        2 * (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWMaxMixedA2TraceNormIntegrandOfSplitUnitary ψ split U ^ 2
          ∂unitaryHaarMeasure (a := q × e)) :=
      adhwFQSWCombinedTraceNormAverageSq_le_two_component_averages ψ split
    _ ≤ 2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q := by
      nlinarith [D.traceNormAverageSq_le, M.maxMixedAverageSq_le]

/-- The final ADHW trace-norm average is bounded by the square root of its
source component square-average bounds. -/
theorem adhwFQSWFinalTraceNormAverage_le_sqrt_source_bounds
    [Nonempty q]
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e))
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := q × e)) ≤
      Real.sqrt (2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q) := by
  have hL2 :=
    integral_le_sqrt_integral_sq_of_nonneg
      (μ := unitaryHaarMeasure (a := q × e))
      (f := fun U : Matrix.unitaryGroup (q × e) ℂ =>
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
    (ψ : Ket ((a × b) × r))
    (split : a ≃ (q × e))
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q) :
    (∫ U : Matrix.unitaryGroup (q × e) ℂ,
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
      ∂unitaryHaarMeasure (a := q × e)) ≤
      Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q) := by
  exact (adhwFQSWFinalTraceNormAverage_le_sqrt_source_bounds ψ split D M).trans
    (Real.sqrt_le_sqrt hsource)

/-- The two source-route square-average component bounds are absorbed by the
single fourth-root argument in ADHW `thm:trueoneShotMother`.  The only
substantive inequality is the trace-one purity lower bound
`1 ≤ d_R Tr[(ψ^R)^2]`, applied to the reference marginal. -/
theorem adhwFQSW_source_component_bounds_le_oneShotFourthRootArgument
    (ψ : Ket ((a × b) × r)) (q : Type x) [Fintype q] :
    2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
      2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
        adhwFQSWOneShotFourthRootArgument ψ q := by
  have hR : (1 : ℝ) ≤ (Fintype.card r : ℝ) * adhwFQSWRPurity ψ := by
    simpa [adhwFQSWRPurity] using
      (MState.one_le_card_mul_hilbertSchmidtSq_matrix
        (ρ := (adhwFQSWARState ψ).traceLeft))
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
    have hlhs :
        (Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2) * adhwFQSWAPurity ψ =
          (Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2) * 1 * adhwFQSWAPurity ψ := by
      ring
    have hrhs :
        (Fintype.card a : ℝ) * (Fintype.card r : ℝ) / ((Fintype.card q : ℝ) ^ 2) *
              adhwFQSWAPurity ψ * adhwFQSWRPurity ψ =
          (Fintype.card a : ℝ) / ((Fintype.card q : ℝ) ^ 2) *
            ((Fintype.card r : ℝ) * adhwFQSWRPurity ψ) * adhwFQSWAPurity ψ := by
      ring
    rw [hlhs, hrhs]
    exact hmulA
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
    (ψ : Ket ((a × b) × r)) (q : Type x) [Fintype q] :
    0 ≤ adhwFQSWOneShotErrorBound ψ q :=
  mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- One-shot ADHW protocol assembly from a selected Alice isometry satisfying
the source decoupling radius.  This is the Uhlmann/protocol part of
`thm:trueoneShotMother` after the Haar-selection step has supplied the
concrete `U`. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling_isometry
    (ψ : Ket ((a × b) × r))
    (U : ReferenceIsometry a (q × e)) (pairing : e ≃ et)
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × et))
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e))
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (U : Matrix.unitaryGroup (q × e) ℂ)
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e))
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e))
    (havg :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨U, hU⟩ :=
    unitaryHaar_exists_le_of_integral_le
      (a := q × e)
      (f := fun U : Matrix.unitaryGroup (q × e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split) havg
  exact exists_fqswOneShotProtocol_traceNormError_le_of_split_unitary_traceNorm_decoupling
    ψ split U hcardTarget hcardRef hU

/-- Output of the Haar-selection/decoupling stage of the ADHW one-shot proof:
a concrete Alice isometry satisfying the source decoupling radius, together
with the finite-dimensional reference-size side conditions needed by the
Uhlmann assembly step. -/
structure ADHWFQSWSelectedDecouplingIsometry
    (ψ : Ket ((a × b) × r)) (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q] [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  /-- The selected Alice isometry. -/
  aliceIsometry : ReferenceIsometry a (q × e)
  /-- The identification of Alice's and Bob's ebit halves. -/
  ebitPairing : e ≃ et
  /-- The Uhlmann target fits inside Bob's input register. -/
  target_ref_card_le : Fintype.card (e × r) ≤ Fintype.card (q × b)
  /-- Bob's input register fits inside his output register. -/
  bob_ref_card_le : Fintype.card (q × b) ≤ Fintype.card ((a × b) × et)
  /-- The selected isometry decouples `A₂` from the reference to within the ADHW radius. -/
  decoupling_le :
    (adhwFQSWSigmaA2RStateOfIsometry (q := q) (e := e) ψ aliceIsometry).normalizedTraceDistance
      ((adhwFQSWMaximallyMixedA2State e).prod (adhwFQSWSigmaRState ψ)) ≤
        (1 / 2 : ℝ) * Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)

namespace ADHWFQSWSelectedDecouplingIsometry

variable {ψ : Ket ((a × b) × r)}
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
    (ψ : Ket ((a × b) × r))
    (S : ADHWFQSWSelectedDecouplingIsometry ψ q e et) :
    ∃ C : FQSWOneShotProtocol ψ q e et,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q :=
  ⟨S.toOneShotProtocol, S.toOneShotProtocol_traceNormError_le⟩

/-- Haar-selection form that produces the selected-decoupling record used by
the source-route one-shot theorem.  The remaining upstream task is the ADHW
Schur/HS calculation proving the averaged trace-norm bound. -/
theorem exists_adhwFQSWSelectedDecouplingIsometry_of_split_unitary_haar_average
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e))
    (havg :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) ≤
        Real.sqrt (adhwFQSWOneShotFourthRootArgument ψ q)) :
    ∃ S : ADHWFQSWSelectedDecouplingIsometry ψ q e e,
      S.aliceIsometry =
        adhwFQSWAliceIsometryOfSplitUnitary split
          (Classical.choose
            (unitaryHaar_exists_le_of_integral_le
              (a := q × e)
              (f := fun U : Matrix.unitaryGroup (q × e) ℂ =>
                adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
              (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split)
              havg)) := by
  let hsel :=
    unitaryHaar_exists_le_of_integral_le
      (a := q × e)
      (f := fun U : Matrix.unitaryGroup (q × e) ℂ =>
        adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U)
      (adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary_integrable ψ split) havg
  let U : Matrix.unitaryGroup (q × e) ℂ := Classical.choose hsel
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q)
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e)) :
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q)
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e)) :
    ∃ C : FQSWOneShotProtocol ψ q e e,
      C.traceNormError ≤ adhwFQSWOneShotErrorBound ψ q := by
  obtain ⟨S⟩ :=
    exists_adhwFQSWSelectedDecouplingIsometry_of_component_records
      ψ split D M hsource hcardTarget hcardRef
  exact exists_fqswOneShotProtocol_traceNormError_le_of_selected_decoupling ψ S

/-- Source-closed component-record one-shot theorem: the ADHW source algebra
absorbs the trace-norm decoupling and max-mixed `A₂` component bounds into the
single one-shot fourth-root argument, so the caller supplies only the component
records. -/
theorem exists_fqswOneShotProtocol_traceNormError_le_of_source_component_records
    [Nonempty q]
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e)) :
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
    (ψ : Ket ((a × b) × r)) (q : Type x) (e : Type y)
    (split : a ≃ (q × e))
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e] where
  /-- The Haar-average trace-norm decoupling estimate. -/
  traceNormDecoupling : ADHWTraceNormDecouplingBound ψ q e split
  /-- The Haar-average max-mixed `A₂` estimate. -/
  maxMixedA2 : ADHWMaxMixedA2Estimate ψ q e split
  /-- One isometry attaining both averages, with its side conditions. -/
  selectedDecoupling : ADHWFQSWSelectedDecouplingIsometry ψ q e e

namespace ADHWFQSWOneShotBound

variable {ψ : Ket ((a × b) × r)}
variable {split : a ≃ (q × e)}
variable [Nonempty q]
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e))
    (havg :
      (∫ U : Matrix.unitaryGroup (q × e) ℂ,
          adhwFQSWDecouplingTraceNormIntegrandOfSplitUnitary ψ split U
        ∂unitaryHaarMeasure (a := q × e)) ≤
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hsource :
      2 * adhwFQSWTraceNormDecouplingSqBound ψ q +
        2 * adhwFQSWMaxMixedA2SqBound ψ q ≤
          adhwFQSWOneShotFourthRootArgument ψ q)
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e)) :
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
    (ψ : Ket ((a × b) × r)) (split : a ≃ (q × e))
    (D : ADHWTraceNormDecouplingBound ψ q e split)
    (M : ADHWMaxMixedA2Estimate ψ q e split)
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e)) :
    ∃ H : ADHWFQSWOneShotBound ψ q e split,
      H.traceNormDecoupling = D ∧ H.maxMixedA2 = M := by
  exact exists_adhwFQSWOneShotBound_of_component_records
    ψ split D M
    (adhwFQSW_source_component_bounds_le_oneShotFourthRootArgument ψ q)
    hcardTarget hcardRef

end QIT

namespace Ket

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

variable (ψ : Ket ((a × b) × r))

/-- Public one-shot FQSW theorem-shape projection.  The source split
`A = A₁ × A₂`, together with the finite-dimensional side conditions needed by
the Uhlmann/Bob-isometry assembly, produces the protocol promised by
ADHW `thm:trueoneShotMother` (fqsw.tex lines 553-568).  Internally this is
assembled from the Schur twirl, Hilbert--Schmidt calculation, trace-norm
decoupling, max-mixed `A₂` estimate, Haar selection, and Uhlmann step in
fqsw.tex lines 580-841. -/
theorem exists_fqswOneShotProtocol_traceNormError_le
    [Nonempty q]
    (split : a ≃ (q × e))
    (hcardTarget : Fintype.card (e × r) ≤ Fintype.card (q × b))
    (hcardRef : Fintype.card (q × b) ≤ Fintype.card ((a × b) × e)) :
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

end Ket

namespace QIT

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

end QIT
