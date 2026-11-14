/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.FQSW.OneShot
public import QIT.Asymptotic.AEP
public import QIT.Coding.Source.SchumacherDirect

/-!
# FQSW IID typicality infrastructure

This file is a dependency-ordered leaf of `QIT.Protocols.FQSW`.  Declaration
names, namespaces, statements, and proof terms are preserved from the original
monolithic module.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p u1 v1 w1

noncomputable section

local instance fqswIIDTypicalCMatrixContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) :=
  SeminormedAddGroup.toContinuousENorm

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

/-- The `n`-fold i.i.d. source regrouped as `(A^n × B^n) × R^n`, matching
the source notation `ψ' = (φ^{ABR})^{⊗ n}` in ADHW fqsw.tex lines 1093-1101. -/
def adhwFQSWIidPureVector (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    PureVector (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  (ψ.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n)

/-- The density state of the regrouped i.i.d. source `ψ'` from ADHW fqsw.tex
lines 1093-1101. -/
def adhwFQSWIidSourceState (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  (adhwFQSWIidPureVector ψ n).state

/-- Alice's one-copy marginal used for the `Π_A` typical projector in ADHW
fqsw.tex lines 1110-1120. -/
def adhwFQSWSystemAState (ψ : PureVector (Prod (Prod a b) r)) : State a :=
  ψ.state.marginalA.marginalA

/-- Bob's one-copy marginal used for the `Π_B` typical projector in ADHW
fqsw.tex lines 1110-1120. -/
def adhwFQSWSystemBState (ψ : PureVector (Prod (Prod a b) r)) : State b :=
  ψ.state.marginalA.marginalB

/-- Reference one-copy marginal used for the `Π_R` typical projector in ADHW
fqsw.tex lines 1110-1120. -/
def adhwFQSWSystemRState (ψ : PureVector (Prod (Prod a b) r)) : State r :=
  ψ.state.marginalB

/-- Entropy `H(A)` in the i.i.d. FQSW source route of ADHW fqsw.tex
lines 1110-1120. -/
def adhwFQSWEntropyA (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  (adhwFQSWSystemAState ψ).vonNeumann

/-- Entropy `H(B)` in the i.i.d. FQSW source route of ADHW fqsw.tex
lines 1110-1120. -/
def adhwFQSWEntropyB (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  (adhwFQSWSystemBState ψ).vonNeumann

/-- Entropy `H(R)` in the i.i.d. FQSW source route of ADHW fqsw.tex
lines 1110-1120. -/
def adhwFQSWEntropyR (ψ : PureVector (Prod (Prod a b) r)) : ℝ :=
  (adhwFQSWSystemRState ψ).vonNeumann

/-- The `A` marginal of the source-route `AR` state is the original source
`A` marginal. -/
theorem adhwFQSWARState_marginalA_eq_systemA
    (ψ : PureVector (Prod (Prod a b) r)) :
    (adhwFQSWARState ψ).marginalA = adhwFQSWSystemAState ψ := by
  apply State.ext
  ext i j
  simp [adhwFQSWARState, adhwFQSWSystemAState, State.coherentTransferReferenceState,
    State.marginalA, partialTraceB]
  rw [Finset.sum_comm]

/-- The `R` marginal of the source-route `AR` state is the original reference
marginal. -/
theorem adhwFQSWARState_marginalB_eq_systemR
    (ψ : PureVector (Prod (Prod a b) r)) :
    (adhwFQSWARState ψ).marginalB = adhwFQSWSystemRState ψ := by
  apply State.ext
  ext i j
  simp [adhwFQSWARState, adhwFQSWSystemRState, State.coherentTransferReferenceState,
    State.marginalB, partialTraceA, Fintype.sum_prod_type]

/-- The `AR` marginal in the ADHW FQSW source route has the same entropy as
the complementary source `B` system. -/
theorem adhwFQSWARState_vonNeumann_eq_entropyB
    (ψ : PureVector (Prod (Prod a b) r)) :
    (adhwFQSWARState ψ).vonNeumann = adhwFQSWEntropyB ψ := by
  let Ω : PureVector (Prod (Prod a r) b) :=
    ψ.reindex (fqswSourceToARBEquiv a b r)
  have hΩA : Ω.state.marginalA = adhwFQSWARState ψ := by
    apply State.ext
    ext i j
    simp [Ω, adhwFQSWARState, State.coherentTransferReferenceState,
      fqswSourceToARBEquiv, PureVector.reindex_state, State.reindex,
      State.marginalA, partialTraceB, PureVector.state_matrix, rankOneMatrix_apply]
  have hΩB : Ω.state.marginalB = adhwFQSWSystemBState ψ := by
    apply State.ext
    ext i j
    simp [Ω, adhwFQSWSystemBState, fqswSourceToARBEquiv,
      PureVector.reindex_state, State.reindex, State.marginalB,
      State.marginalA, partialTraceA, partialTraceB, PureVector.state_matrix,
      rankOneMatrix_apply, Fintype.sum_prod_type]
  have hdual := State.pureVector_marginalA_vonNeumann_eq_marginalB Ω
  rw [hΩA, hΩB] at hdual
  simpa [adhwFQSWEntropyB] using hdual

/-- The source `AB` marginal has the same entropy as the complementary
reference system `R`. -/
theorem adhwFQSWSourceAB_vonNeumann_eq_entropyR
    (ψ : PureVector (Prod (Prod a b) r)) :
    ψ.state.marginalA.vonNeumann = adhwFQSWEntropyR ψ := by
  simpa [adhwFQSWEntropyR, adhwFQSWSystemRState] using
    State.pureVector_marginalA_vonNeumann_eq_marginalB ψ

/-- Source-route mutual information identity
`I(A;R) = H(A) + H(R) - H(B)`. -/
theorem adhwFQSWMutualInformationAR_eq_entropyA_add_entropyR_sub_entropyB
    (ψ : PureVector (Prod (Prod a b) r)) :
    mutualInformation ψ.state.coherentTransferReferenceState =
      adhwFQSWEntropyA ψ + adhwFQSWEntropyR ψ - adhwFQSWEntropyB ψ := by
  rw [← adhwFQSWARState]
  rw [mutualInformation]
  rw [adhwFQSWARState_marginalA_eq_systemA,
    adhwFQSWARState_marginalB_eq_systemR,
    adhwFQSWARState_vonNeumann_eq_entropyB]
  rfl

/-- Source-route mutual information identity
`I(A;B) = H(A) + H(B) - H(R)`. -/
theorem adhwFQSWMutualInformationAB_eq_entropyA_add_entropyB_sub_entropyR
    (ψ : PureVector (Prod (Prod a b) r)) :
    mutualInformation ψ.state.marginalA =
      adhwFQSWEntropyA ψ + adhwFQSWEntropyB ψ - adhwFQSWEntropyR ψ := by
  rw [mutualInformation]
  rw [adhwFQSWSourceAB_vonNeumann_eq_entropyR]
  rfl

/-- Local partial-trace pairing for a right identity factor:
`Tr_B[X (T ⊗ I)] = Tr_B[X] T`. -/
private theorem adhwFQSW_partialTraceB_mul_kronecker_one_left
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (X : CMatrix (Prod α β)) (T : CMatrix α) :
    partialTraceB (a := α) (b := β) (X * Matrix.kronecker T (1 : CMatrix β)) =
      partialTraceB (a := α) (b := β) X * T := by
  ext i i'
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Trace pairing for an observable acting only on the left tensor factor. -/
private theorem adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (M : CMatrix (Prod α β)) (T : CMatrix α) :
    (Matrix.kronecker T (1 : CMatrix β) * M).trace =
      (T * partialTraceB (a := α) (b := β) M).trace := by
  calc
    (Matrix.kronecker T (1 : CMatrix β) * M).trace =
        (M * Matrix.kronecker T (1 : CMatrix β)).trace := by
      rw [Matrix.trace_mul_comm]
    _ = ((partialTraceB (a := α) (b := β) M) * T).trace := by
      rw [← adhwFQSW_partialTraceB_mul_kronecker_one_left
        (α := α) (β := β) M T]
      exact (partialTraceB_trace (a := α) (b := β)
        (M * Matrix.kronecker T (1 : CMatrix β))).symm
    _ = (T * partialTraceB (a := α) (b := β) M).trace := by
      rw [Matrix.trace_mul_comm]

/-- Local partial-trace pairing for a left identity factor:
`Tr_A[X (I ⊗ T)] = Tr_A[X] T`. -/
private theorem adhwFQSW_partialTraceA_mul_kronecker_one_right
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq α]
    (X : CMatrix (Prod α β)) (T : CMatrix β) :
    partialTraceA (a := α) (b := β) (X * Matrix.kronecker (1 : CMatrix α) T) =
      partialTraceA (a := α) (b := β) X * T := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Trace pairing for an observable acting only on the right tensor factor. -/
private theorem adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq α]
    (M : CMatrix (Prod α β)) (T : CMatrix β) :
    (Matrix.kronecker (1 : CMatrix α) T * M).trace =
      (T * partialTraceA (a := α) (b := β) M).trace := by
  calc
    (Matrix.kronecker (1 : CMatrix α) T * M).trace =
        (M * Matrix.kronecker (1 : CMatrix α) T).trace := by
      rw [Matrix.trace_mul_comm]
    _ = ((partialTraceA (a := α) (b := β) M) * T).trace := by
      rw [← adhwFQSW_partialTraceA_mul_kronecker_one_right
        (α := α) (β := β) M T]
      exact (partialTraceA_trace (a := α) (b := β)
        (M * Matrix.kronecker (1 : CMatrix α) T)).symm
    _ = (T * partialTraceA (a := α) (b := β) M).trace := by
      rw [Matrix.trace_mul_comm]

/-- Lift an `A^n` projector to the grouped i.i.d. source register
`A^nB^nR^n`. -/
private def adhwFQSWIidLiftProjectorA
    (n : ℕ) (PA : CMatrix (TensorPower a n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  Matrix.kronecker
    (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
    (1 : CMatrix (TensorPower r n))

/-- Lift a `B^n` projector to the grouped i.i.d. source register
`A^nB^nR^n`. -/
private def adhwFQSWIidLiftProjectorB
    (n : ℕ) (PB : CMatrix (TensorPower b n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  Matrix.kronecker
    (Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
    (1 : CMatrix (TensorPower r n))

/-- Lift an `R^n` projector to the grouped i.i.d. source register
`A^nB^nR^n`. -/
private def adhwFQSWIidLiftProjectorR
    (n : ℕ) (PR : CMatrix (TensorPower r n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  Matrix.kronecker (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n))) PR

/-- The simultaneous lifted `A^nB^nR^n` projector
`Π_A ⊗ Π_B ⊗ Π_R`. -/
def adhwFQSWIidLiftProjectorTriple
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  Matrix.kronecker (Matrix.kronecker PA PB) PR

/-- The simultaneously projected i.i.d. source matrix
`Π_A Π_B Π_R ρ Π_A Π_B Π_R`. -/
def adhwFQSWIidProjectedSourceMatrix
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ)
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  Pi * (adhwFQSWIidSourceState ψ n).matrix * Pi

/-- The lifted triple projector factors as the product of the three
single-register lifted projectors. -/
private theorem adhwFQSWIidLiftProjectorTriple_eq_mul
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA *
        adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB *
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
  ext x y
  simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
    adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type]

-- Algebraic decomposition behind the simultaneous-projector union bound.
omit [Fintype a] [Fintype b] [Fintype r] in
private theorem adhwFQSWIidLiftProjector_union_decomp
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    ((1 - adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) +
        (1 - adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) +
          (1 - adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR)) -
        (1 - adhwFQSWIidLiftProjectorTriple
          (a := a) (b := b) (r := r) n PA PB PR) =
      Matrix.kronecker (Matrix.kronecker (1 - PA) (1 - PB))
          (1 : CMatrix (TensorPower r n)) +
        Matrix.kronecker (1 - Matrix.kronecker PA PB) (1 - PR) := by
  ext x y
  rcases x with ⟨⟨xa, xb⟩, xr⟩
  rcases y with ⟨⟨ya, yb⟩, yr⟩
  by_cases ha : xa = ya
  · subst ya
    by_cases hb : xb = yb
    · subst yb
      by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, hr]
        try ring
    · by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, hb]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, hb, hr]
        try ring
  · by_cases hb : xb = yb
    · subst yb
      by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha, hr]
        try ring
    · by_cases hr : xr = yr
      · subst yr
        simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha, hb]
        try ring
      · simp [adhwFQSWIidLiftProjectorTriple, adhwFQSWIidLiftProjectorA,
          adhwFQSWIidLiftProjectorB, adhwFQSWIidLiftProjectorR, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, ha, hb, hr]
        try ring

/-- Simultaneous-projector union bound on the grouped i.i.d. source register. -/
private theorem adhwFQSWIidLiftProjector_union_bound
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPA : PA.PosSemidef) (hPB : PB.PosSemidef) (hPR : PR.PosSemidef)
    (hPAid : PA * PA = PA) (hPBid : PB * PB = PB) (hPRid : PR * PR = PR) :
    (1 - adhwFQSWIidLiftProjectorTriple
        (a := a) (b := b) (r := r) n PA PB PR) ≤
      (1 - adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) +
        (1 - adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) +
          (1 - adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) := by
  rw [Matrix.le_iff]
  rw [adhwFQSWIidLiftProjector_union_decomp]
  have hAcomp := projector_one_sub_posSemidef PA hPA hPAid
  have hBcomp := projector_one_sub_posSemidef PB hPB hPBid
  have hRcomp := projector_one_sub_posSemidef PR hPR hPRid
  have hAB : (Matrix.kronecker PA PB).PosSemidef := hPA.kronecker hPB
  have hABid : Matrix.kronecker PA PB * Matrix.kronecker PA PB =
      Matrix.kronecker PA PB := by
    simpa [hPAid, hPBid] using (Matrix.mul_kronecker_mul PA PA PB PB).symm
  have hABcomp := projector_one_sub_posSemidef (Matrix.kronecker PA PB) hAB hABid
  exact (hAcomp.kronecker hBcomp).kronecker Matrix.PosSemidef.one |>.add
    (hABcomp.kronecker hRcomp)

/-- The `A^n` marginal of the grouped FQSW i.i.d. source is the tensor power
of the one-copy `A` marginal. -/
private theorem adhwFQSWIidSourceState_marginalA_eq_tensorPower
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    (adhwFQSWIidSourceState ψ n).marginalA.marginalA =
      (adhwFQSWSystemAState ψ).tensorPower n := by
  have hAB :
      (adhwFQSWIidSourceState ψ n).marginalA =
        ψ.state.marginalA.tensorPowerBipartite n := by
    simpa [adhwFQSWIidSourceState, adhwFQSWIidPureVector,
      fqswTensorPowerTripartiteEquiv, PureVector.tensorPowerTripartiteGrouped,
      PureVector.tensorPowerTripartiteGroupedEquiv, PureVector.reindex_state,
      PureVector.tensorPower_state] using
      PureVector.tensorPowerTripartiteGrouped_marginalAB (a := a) (b := b) (c := r) ψ n
  rw [hAB]
  simpa [adhwFQSWSystemAState] using
    State.tensorPowerBipartite_marginalA (rho := ψ.state.marginalA) n

/-- The `B^n` marginal of the grouped FQSW i.i.d. source is the tensor power
of the one-copy `B` marginal. -/
private theorem adhwFQSWIidSourceState_marginalB_eq_tensorPower
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    (adhwFQSWIidSourceState ψ n).marginalA.marginalB =
      (adhwFQSWSystemBState ψ).tensorPower n := by
  have hAB :
      (adhwFQSWIidSourceState ψ n).marginalA =
        ψ.state.marginalA.tensorPowerBipartite n := by
    simpa [adhwFQSWIidSourceState, adhwFQSWIidPureVector,
      fqswTensorPowerTripartiteEquiv, PureVector.tensorPowerTripartiteGrouped,
      PureVector.tensorPowerTripartiteGroupedEquiv, PureVector.reindex_state,
      PureVector.tensorPower_state] using
      PureVector.tensorPowerTripartiteGrouped_marginalAB (a := a) (b := b) (c := r) ψ n
  rw [hAB]
  simpa [adhwFQSWSystemBState] using
    State.tensorPowerBipartite_marginalB (rho := ψ.state.marginalA) n

/-- Tracing the `AC` marginal down to `C` agrees with the direct `C`
marginal for a left-associated tripartite state. -/
private theorem adhwFQSW_marginalAC_marginalB_eq_marginalB
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (ρ : State (Prod (Prod α β) γ)) :
    ρ.marginalAC.marginalB = ρ.marginalB := by
  apply State.ext
  ext x y
  simp [State.marginalAC, State.marginalB, partialTraceA, Fintype.sum_prod_type]

/-- The `R^n` marginal of the grouped FQSW i.i.d. source is the tensor power
of the one-copy reference marginal. -/
private theorem adhwFQSWIidSourceState_marginalR_eq_tensorPower
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) :
    (adhwFQSWIidSourceState ψ n).marginalB =
      (adhwFQSWSystemRState ψ).tensorPower n := by
  let ρ := adhwFQSWIidSourceState ψ n
  have hAC :
      ρ.marginalAC = ψ.state.marginalAC.tensorPowerBipartite n := by
    simpa [ρ, adhwFQSWIidSourceState, adhwFQSWIidPureVector,
      fqswTensorPowerTripartiteEquiv, PureVector.tensorPowerTripartiteGrouped,
      PureVector.tensorPowerTripartiteGroupedEquiv, PureVector.reindex_state,
      PureVector.tensorPower_state] using
      PureVector.tensorPowerTripartiteGrouped_marginalAC (a := a) (b := b) (c := r) ψ n
  calc
    ρ.marginalB = ρ.marginalAC.marginalB := by
      exact (adhwFQSW_marginalAC_marginalB_eq_marginalB ρ).symm
    _ = (ψ.state.marginalAC.tensorPowerBipartite n).marginalB := by
      rw [hAC]
    _ = (ψ.state.marginalAC.marginalB).tensorPower n := by
      exact State.tensorPowerBipartite_marginalB (rho := ψ.state.marginalAC) n
    _ = (adhwFQSWSystemRState ψ).tensorPower n := by
      have hR := adhwFQSW_marginalAC_marginalB_eq_marginalB ψ.state
      simpa [adhwFQSWSystemRState] using congrArg (fun σ : State r => σ.tensorPower n) hR

/-- Acceptance identity for the lifted `A^n` typical projector. -/
private theorem adhwFQSWIid_acceptanceA
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) :
    (((adhwFQSWIidLiftProjectorA (b := b) (r := r) n
        ((adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
      (adhwFQSWSystemAState ψ).typicalSubspaceSpectralWeight n δ := by
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ
  have htraceR :
      (((adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) *
          ρ.matrix).trace).re =
        (((Matrix.kronecker PA (1 : CMatrix (TensorPower b n))) *
            ρ.marginalA.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
      (α := Prod (TensorPower a n) (TensorPower b n)) (β := TensorPower r n)
      (M := ρ.matrix)
      (T := Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
    simpa [adhwFQSWIidLiftProjectorA, ρ, PA, State.marginalA_matrix] using
      congrArg Complex.re h
  have htraceB :
      (((Matrix.kronecker PA (1 : CMatrix (TensorPower b n))) *
            ρ.marginalA.matrix).trace).re =
        ((PA * ρ.marginalA.marginalA.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
      (α := TensorPower a n) (β := TensorPower b n)
      (M := ρ.marginalA.matrix) (T := PA)
    simpa [State.marginalA_matrix] using congrArg Complex.re h
  have hmarg := congrArg (fun σ : State (TensorPower a n) => σ.matrix)
    (adhwFQSWIidSourceState_marginalA_eq_tensorPower ψ n)
  have hmarg' :
      ρ.marginalA.marginalA.matrix =
        ((adhwFQSWSystemAState ψ).tensorPower n).matrix := by
    simpa [ρ] using hmarg
  calc
    (((adhwFQSWIidLiftProjectorA (b := b) (r := r) n
        ((adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
        ((PA * ρ.marginalA.marginalA.matrix).trace).re := by
          rw [htraceR, htraceB]
    _ = (((adhwFQSWSystemAState ψ).tensorPower n).matrix * PA).trace.re := by
          rw [hmarg']
          rw [Matrix.trace_mul_comm]
    _ = (adhwFQSWSystemAState ψ).typicalSubspaceSpectralWeight n δ := by
          simpa [PA] using
            (adhwFQSWSystemAState ψ).typicalSubspaceProjector_trace_mul_re n δ

/-- Acceptance identity for the lifted `B^n` typical projector. -/
private theorem adhwFQSWIid_acceptanceB
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) :
    (((adhwFQSWIidLiftProjectorB (a := a) (r := r) n
        ((adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
      (adhwFQSWSystemBState ψ).typicalSubspaceSpectralWeight n δ := by
  let ρ := adhwFQSWIidSourceState ψ n
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ
  have htraceR :
      (((adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) *
          ρ.matrix).trace).re =
        (((Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB) *
            ρ.marginalA.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
      (α := Prod (TensorPower a n) (TensorPower b n)) (β := TensorPower r n)
      (M := ρ.matrix)
      (T := Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
    simpa [adhwFQSWIidLiftProjectorB, ρ, PB, State.marginalA_matrix] using
      congrArg Complex.re h
  have htraceA :
      (((Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB) *
            ρ.marginalA.matrix).trace).re =
        ((PB * ρ.marginalA.marginalB.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
      (α := TensorPower a n) (β := TensorPower b n)
      (M := ρ.marginalA.matrix) (T := PB)
    simpa [State.marginalB_matrix] using congrArg Complex.re h
  have hmarg := congrArg (fun σ : State (TensorPower b n) => σ.matrix)
    (adhwFQSWIidSourceState_marginalB_eq_tensorPower ψ n)
  have hmarg' :
      ρ.marginalA.marginalB.matrix =
        ((adhwFQSWSystemBState ψ).tensorPower n).matrix := by
    simpa [ρ] using hmarg
  calc
    (((adhwFQSWIidLiftProjectorB (a := a) (r := r) n
        ((adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
        ((PB * ρ.marginalA.marginalB.matrix).trace).re := by
          rw [htraceR, htraceA]
    _ = (((adhwFQSWSystemBState ψ).tensorPower n).matrix * PB).trace.re := by
          rw [hmarg']
          rw [Matrix.trace_mul_comm]
    _ = (adhwFQSWSystemBState ψ).typicalSubspaceSpectralWeight n δ := by
          simpa [PB] using
            (adhwFQSWSystemBState ψ).typicalSubspaceProjector_trace_mul_re n δ

/-- Acceptance identity for the lifted `R^n` typical projector. -/
private theorem adhwFQSWIid_acceptanceR
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ : ℝ) :
    (((adhwFQSWIidLiftProjectorR (a := a) (b := b) n
        ((adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
      (adhwFQSWSystemRState ψ).typicalSubspaceSpectralWeight n δ := by
  let ρ := adhwFQSWIidSourceState ψ n
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ
  have htraceAB :
      (((adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) *
          ρ.matrix).trace).re =
        ((PR * ρ.marginalB.matrix).trace).re := by
    have h := adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
      (α := Prod (TensorPower a n) (TensorPower b n)) (β := TensorPower r n)
      (M := ρ.matrix) (T := PR)
    simpa [adhwFQSWIidLiftProjectorR, ρ, PR, State.marginalB_matrix] using
      congrArg Complex.re h
  have hmarg := congrArg (fun σ : State (TensorPower r n) => σ.matrix)
    (adhwFQSWIidSourceState_marginalR_eq_tensorPower ψ n)
  have hmarg' :
      ρ.marginalB.matrix =
        ((adhwFQSWSystemRState ψ).tensorPower n).matrix := by
    simpa [ρ] using hmarg
  calc
    (((adhwFQSWIidLiftProjectorR (a := a) (b := b) n
        ((adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ)) *
        (adhwFQSWIidSourceState ψ n).matrix).trace).re =
        ((PR * ρ.marginalB.matrix).trace).re := by
          rw [htraceAB]
    _ = (((adhwFQSWSystemRState ψ).tensorPower n).matrix * PR).trace.re := by
          rw [hmarg']
          rw [Matrix.trace_mul_comm]
    _ = (adhwFQSWSystemRState ψ).typicalSubspaceSpectralWeight n δ := by
          simpa [PR] using
            (adhwFQSWSystemRState ψ).typicalSubspaceProjector_trace_mul_re n δ

/-- Selectively projecting the right register cannot increase the left
marginal in Loewner order. -/
private theorem adhwFQSW_partialTraceB_selective_projector_le
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (X : CMatrix (Prod α β)) (hX : X.PosSemidef)
    (Q : CMatrix β) (hQ : Q.PosSemidef) (hQid : Q * Q = Q) :
    partialTraceB (a := α) (b := β)
        (Matrix.kronecker (1 : CMatrix α) Q * X *
          Matrix.kronecker (1 : CMatrix α) Q) ≤
      partialTraceB (a := α) (b := β) X := by
  rw [Matrix.le_iff]
  let D : CMatrix α :=
    partialTraceB (a := α) (b := β) X -
      partialTraceB (a := α) (b := β)
        (Matrix.kronecker (1 : CMatrix α) Q * X *
          Matrix.kronecker (1 : CMatrix α) Q)
  change D.PosSemidef
  have hbranch_psd :
      (Matrix.kronecker (1 : CMatrix α) Q * X *
        Matrix.kronecker (1 : CMatrix α) Q).PosSemidef := by
    let K : CMatrix (Prod α β) := Matrix.kronecker (1 : CMatrix α) Q
    have hK : K.PosSemidef := Matrix.PosSemidef.one.kronecker hQ
    have h := hX.mul_mul_conjTranspose_same K
    rw [hK.isHermitian.eq] at h
    simpa [K, Matrix.mul_assoc] using h
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (partialTraceB_isHermitian hX.isHermitian).sub
      (partialTraceB_isHermitian hbranch_psd.isHermitian)
  rw [cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hDherm]
  intro W hW
  have hQcomp := projector_one_sub_posSemidef Q hQ hQid
  have hWQcomp : (Matrix.kronecker W (1 - Q)).PosSemidef :=
    hW.kronecker hQcomp
  have hnonneg :
      0 ≤ ((Matrix.kronecker W (1 - Q) * X).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hWQcomp hX
  have htrace_full :
      ((W * partialTraceB (a := α) (b := β) X).trace).re =
        ((Matrix.kronecker W (1 : CMatrix β) * X).trace).re := by
    exact congrArg Complex.re
      (adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
        (α := α) (β := β) X W).symm
  have htrace_branch :
      ((W * partialTraceB (a := α) (b := β)
          (Matrix.kronecker (1 : CMatrix α) Q * X *
            Matrix.kronecker (1 : CMatrix α) Q)).trace).re =
        ((Matrix.kronecker W Q * X).trace).re := by
    have hpair := congrArg Complex.re
      (adhwFQSW_trace_kronecker_one_left_mul_eq_trace_mul_partialTraceB
        (α := α) (β := β)
        (Matrix.kronecker (1 : CMatrix α) Q * X *
          Matrix.kronecker (1 : CMatrix α) Q) W).symm
    rw [hpair]
    congr 1
    let K : CMatrix (Prod α β) := Matrix.kronecker (1 : CMatrix α) Q
    let L : CMatrix (Prod α β) := Matrix.kronecker W (1 : CMatrix β)
    have hKLK : K * L * K = Matrix.kronecker W Q := by
      have hKL : K * L = Matrix.kronecker W Q := by
        simpa [K, L, Matrix.one_mul, Matrix.mul_one] using
          (Matrix.mul_kronecker_mul (1 : CMatrix α) W Q (1 : CMatrix β)).symm
      calc
        K * L * K = (Matrix.kronecker W Q) * Matrix.kronecker (1 : CMatrix α) Q := by
          rw [hKL]
        _ = Matrix.kronecker W (Q * Q) := by
          simpa [Matrix.mul_one] using
            (Matrix.mul_kronecker_mul W (1 : CMatrix α) Q Q).symm
        _ = Matrix.kronecker W Q := by rw [hQid]
    calc
      (Matrix.kronecker W (1 : CMatrix β) *
          (Matrix.kronecker (1 : CMatrix α) Q * X *
            Matrix.kronecker (1 : CMatrix α) Q)).trace =
          ((K * L * K) * X).trace := by
            have hassoc :
                Matrix.kronecker W (1 : CMatrix β) *
                    (Matrix.kronecker (1 : CMatrix α) Q * X *
                      Matrix.kronecker (1 : CMatrix α) Q) =
                  L * K * X * K := by
              simp [K, L]
              noncomm_ring
            rw [hassoc]
            rw [Matrix.trace_mul_cycle]
            congr 1
            noncomm_ring
      _ = (Matrix.kronecker W Q * X).trace := by
            rw [hKLK]
  have htrace_decomp :
      ((W * D).trace).re =
        ((Matrix.kronecker W (1 - Q) * X).trace).re := by
    dsimp [D]
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [htrace_full]
    have htrace_branch_expanded := htrace_branch
    simp only [Matrix.kronecker] at htrace_branch_expanded
    rw [htrace_branch_expanded]
    have hsplit :
        Matrix.kronecker W (1 : CMatrix β) - Matrix.kronecker W Q =
          Matrix.kronecker W (1 - Q) := by
      ext x y
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply]
      ring
    have hsplit_expanded := hsplit
    simp only [Matrix.kronecker] at hsplit_expanded
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
    simp only [Matrix.kronecker]
    rw [hsplit_expanded]
  rw [Matrix.trace_mul_comm]
  rw [htrace_decomp]
  exact hnonneg

/-- Selectively projecting the left register cannot increase the right
marginal in Loewner order. -/
private theorem adhwFQSW_partialTraceA_selective_projector_le
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (X : CMatrix (Prod α β)) (hX : X.PosSemidef)
    (Q : CMatrix α) (hQ : Q.PosSemidef) (hQid : Q * Q = Q) :
    partialTraceA (a := α) (b := β)
        (Matrix.kronecker Q (1 : CMatrix β) * X *
          Matrix.kronecker Q (1 : CMatrix β)) ≤
      partialTraceA (a := α) (b := β) X := by
  rw [Matrix.le_iff]
  let D : CMatrix β :=
    partialTraceA (a := α) (b := β) X -
      partialTraceA (a := α) (b := β)
        (Matrix.kronecker Q (1 : CMatrix β) * X *
          Matrix.kronecker Q (1 : CMatrix β))
  change D.PosSemidef
  have hbranch_psd :
      (Matrix.kronecker Q (1 : CMatrix β) * X *
        Matrix.kronecker Q (1 : CMatrix β)).PosSemidef := by
    let K : CMatrix (Prod α β) := Matrix.kronecker Q (1 : CMatrix β)
    have hK : K.PosSemidef := hQ.kronecker Matrix.PosSemidef.one
    have h := hX.mul_mul_conjTranspose_same K
    rw [hK.isHermitian.eq] at h
    simpa [K, Matrix.mul_assoc] using h
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (partialTraceA_isHermitian hX.isHermitian).sub
      (partialTraceA_isHermitian hbranch_psd.isHermitian)
  rw [cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hDherm]
  intro W hW
  have hQcomp := projector_one_sub_posSemidef Q hQ hQid
  have hQcompW : (Matrix.kronecker (1 - Q) W).PosSemidef :=
    hQcomp.kronecker hW
  have hnonneg :
      0 ≤ ((Matrix.kronecker (1 - Q) W * X).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg hQcompW hX
  have htrace_full :
      ((W * partialTraceA (a := α) (b := β) X).trace).re =
        ((Matrix.kronecker (1 : CMatrix α) W * X).trace).re := by
    exact congrArg Complex.re
      (adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
        (α := α) (β := β) X W).symm
  have htrace_branch :
      ((W * partialTraceA (a := α) (b := β)
          (Matrix.kronecker Q (1 : CMatrix β) * X *
            Matrix.kronecker Q (1 : CMatrix β))).trace).re =
        ((Matrix.kronecker Q W * X).trace).re := by
    have hpair := congrArg Complex.re
      (adhwFQSW_trace_kronecker_one_right_mul_eq_trace_mul_partialTraceA
        (α := α) (β := β)
        (Matrix.kronecker Q (1 : CMatrix β) * X *
          Matrix.kronecker Q (1 : CMatrix β)) W).symm
    rw [hpair]
    congr 1
    let K : CMatrix (Prod α β) := Matrix.kronecker Q (1 : CMatrix β)
    let L : CMatrix (Prod α β) := Matrix.kronecker (1 : CMatrix α) W
    have hKLK : K * L * K = Matrix.kronecker Q W := by
      have hKL : K * L = Matrix.kronecker Q W := by
        simpa [K, L, Matrix.one_mul, Matrix.mul_one] using
          (Matrix.mul_kronecker_mul Q (1 : CMatrix α) (1 : CMatrix β) W).symm
      calc
        K * L * K = (Matrix.kronecker Q W) * Matrix.kronecker Q (1 : CMatrix β) := by
          rw [hKL]
        _ = Matrix.kronecker (Q * Q) W := by
          simpa [Matrix.mul_one] using
            (Matrix.mul_kronecker_mul Q Q W (1 : CMatrix β)).symm
        _ = Matrix.kronecker Q W := by rw [hQid]
    calc
      (Matrix.kronecker (1 : CMatrix α) W *
          (Matrix.kronecker Q (1 : CMatrix β) * X *
            Matrix.kronecker Q (1 : CMatrix β))).trace =
          ((K * L * K) * X).trace := by
            have hassoc :
                Matrix.kronecker (1 : CMatrix α) W *
                    (Matrix.kronecker Q (1 : CMatrix β) * X *
                      Matrix.kronecker Q (1 : CMatrix β)) =
                  L * K * X * K := by
              simp [K, L]
              noncomm_ring
            rw [hassoc]
            rw [Matrix.trace_mul_cycle]
            congr 1
            noncomm_ring
      _ = (Matrix.kronecker Q W * X).trace := by
            rw [hKLK]
  have htrace_decomp :
      ((W * D).trace).re =
        ((Matrix.kronecker (1 - Q) W * X).trace).re := by
    dsimp [D]
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [htrace_full]
    have htrace_branch_expanded := htrace_branch
    simp only [Matrix.kronecker] at htrace_branch_expanded
    rw [htrace_branch_expanded]
    have hsplit :
        Matrix.kronecker (1 : CMatrix α) W - Matrix.kronecker Q W =
          Matrix.kronecker (1 - Q) W := by
      ext x y
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply]
      ring
    have hsplit_expanded := hsplit
    simp only [Matrix.kronecker] at hsplit_expanded
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
    simp only [Matrix.kronecker]
    rw [hsplit_expanded]
  rw [Matrix.trace_mul_comm]
  rw [htrace_decomp]
  exact hnonneg

private theorem adhwFQSW_partialTraceB_sub
    {α : Type u} {β : Type v} [Fintype β]
    (X Y : CMatrix (Prod α β)) :
    partialTraceB (a := α) (b := β) (X - Y) =
      partialTraceB (a := α) (b := β) X -
        partialTraceB (a := α) (b := β) Y := by
  ext i j
  simp [partialTraceB, Finset.sum_sub_distrib]

private theorem adhwFQSW_partialTraceA_sub
    {α : Type u} {β : Type v} [Fintype α]
    (X Y : CMatrix (Prod α β)) :
    partialTraceA (a := α) (b := β) (X - Y) =
      partialTraceA (a := α) (b := β) X -
        partialTraceA (a := α) (b := β) Y := by
  ext i j
  simp [partialTraceA, Finset.sum_sub_distrib]

private theorem adhwFQSW_partialTraceB_mono
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    {X Y : CMatrix (Prod α β)} (hXY : X ≤ Y) :
    partialTraceB (a := α) (b := β) X ≤
      partialTraceB (a := α) (b := β) Y := by
  rw [Matrix.le_iff]
  have hdiff : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
  have hpt := partialTraceB_posSemidef (a := α) (b := β) hdiff
  simpa [adhwFQSW_partialTraceB_sub] using hpt

private theorem adhwFQSW_partialTraceA_mono
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    {X Y : CMatrix (Prod α β)} (hXY : X ≤ Y) :
    partialTraceA (a := α) (b := β) X ≤
      partialTraceA (a := α) (b := β) Y := by
  rw [Matrix.le_iff]
  have hdiff : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
  have hpt := partialTraceA_posSemidef (a := α) (b := β) hdiff
  simpa [adhwFQSW_partialTraceA_sub] using hpt

private theorem adhwFQSW_smul_le_smul_of_nonneg
    {α : Type u} [Fintype α] [DecidableEq α]
    {A B : CMatrix α} {c : ℝ} (hc : 0 ≤ c) (hAB : A ≤ B) :
    (((c : ℝ) : ℂ) • A) ≤ (((c : ℝ) : ℂ) • B) := by
  rw [Matrix.le_iff] at hAB ⊢
  have hscaled : (((c : ℝ) : ℂ) • (B - A)).PosSemidef :=
    Matrix.PosSemidef.smul hAB (by exact_mod_cast hc)
  simpa [smul_sub] using hscaled

private theorem adhwFQSW_real_smul_smul
    {α : Type u} (c d : ℝ) (M : CMatrix α) :
    (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • M)) =
      ((((c * d : ℝ) : ℂ) • M)) := by
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc]

private theorem adhwFQSW_complex_smul_smul
    {α : Type u} (c d : ℂ) (M : CMatrix α) :
    c • (d • M) = (c * d) • M := by
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul, mul_assoc]

private theorem adhwFQSW_sum_four_comm
    {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
        = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]

private theorem adhwFQSW_sum_five_comm
    {α β γ δ ε M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [AddCommMonoid M]
    (f : α → β → γ → δ → ε → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ c, ∑ e, ∑ a, ∑ d, ∑ b, f a b c d e := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e)
        = ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, f a b c d e := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, ∑ e, f a b c d e := by
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ e, ∑ d, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ e, ∑ b, ∑ d, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ e, ∑ a, ∑ b, ∑ d, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ e, ∑ a, ∑ d, ∑ b, f a b c d e := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro e _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]

private theorem adhwFQSW_sum_five_comm_leftPair
    {α β γ δ ε M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [AddCommMonoid M]
    (f : α → β → γ → δ → ε → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ d, ∑ a, ∑ e, ∑ c, f a b c d e := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e)
        = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, f a b c d e := by
          rw [Finset.sum_comm]
    _ = ∑ b, ∑ a, ∑ d, ∑ c, ∑ e, f a b c d e := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ b, ∑ d, ∑ a, ∑ c, ∑ e, f a b c d e := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ b, ∑ d, ∑ a, ∑ e, ∑ c, f a b c d e := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro d _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]

private theorem adhwFQSWIidLiftProjectorA_marginalA_marginalA
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) :
    partialTraceB (a := TensorPower a n) (b := TensorPower b n)
      (partialTraceB (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA * ρ.matrix *
          adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA)) =
      PA * ρ.marginalA.marginalA.matrix * PA := by
  ext x y
  simp [adhwFQSWIidLiftProjectorA, State.marginalA_matrix, partialTraceB,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa using
    (adhwFQSW_sum_four_comm
      (fun b0 r0 v0 u0 =>
        PA x u0 * (ρ.matrix ((u0, b0), r0) ((v0, b0), r0) * PA v0 y)))

private theorem adhwFQSWIidLiftProjectorB_marginalA_marginalB
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PB : CMatrix (TensorPower b n)) :
    partialTraceA (a := TensorPower a n) (b := TensorPower b n)
      (partialTraceB (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB * ρ.matrix *
          adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB)) =
      PB * ρ.marginalA.marginalB.matrix * PB := by
  ext x y
  simp [adhwFQSWIidLiftProjectorB, State.marginalA_matrix, State.marginalB_matrix,
    partialTraceA, partialTraceB, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa using
    (adhwFQSW_sum_four_comm
      (fun a0 r0 v0 u0 =>
        PB x u0 * (ρ.matrix ((a0, u0), r0) ((a0, v0), r0) * PB v0 y)))

private theorem adhwFQSWIidLiftProjectorR_marginalB
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PR : CMatrix (TensorPower r n)) :
    partialTraceA (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n)
        (adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * ρ.matrix *
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) =
      PR * ρ.marginalB.matrix * PR := by
  ext x y
  simp [adhwFQSWIidLiftProjectorR, State.marginalB_matrix, partialTraceA,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa using
    (adhwFQSW_sum_four_comm
      (fun a0 b0 v0 u0 =>
        PR x u0 * (ρ.matrix ((a0, b0), u0) ((a0, b0), v0) * PR v0 y)))

omit [DecidableEq a] in
private theorem adhwFQSWIidLiftProjectorA_posSemidef
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (hPA : PA.PosSemidef) :
    (adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA).PosSemidef :=
  (hPA.kronecker Matrix.PosSemidef.one).kronecker Matrix.PosSemidef.one

omit [DecidableEq b] in
private theorem adhwFQSWIidLiftProjectorB_posSemidef
    (n : ℕ) (PB : CMatrix (TensorPower b n)) (hPB : PB.PosSemidef) :
    (adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB).PosSemidef :=
  (Matrix.PosSemidef.one.kronecker hPB).kronecker Matrix.PosSemidef.one

omit [DecidableEq r] in
private theorem adhwFQSWIidLiftProjectorR_posSemidef
    (n : ℕ) (PR : CMatrix (TensorPower r n)) (hPR : PR.PosSemidef) :
    (adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR).PosSemidef :=
  Matrix.PosSemidef.one.kronecker hPR

omit [DecidableEq a] [DecidableEq b] [DecidableEq r] in
private theorem adhwFQSWIidLiftProjectorTriple_posSemidef
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPA : PA.PosSemidef) (hPB : PB.PosSemidef) (hPR : PR.PosSemidef) :
    (adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR).PosSemidef :=
  (hPA.kronecker hPB).kronecker hPR

omit [DecidableEq a] in
private theorem adhwFQSWIidLiftProjectorA_idempotent
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (hPAid : PA * PA = PA) :
    adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA *
      adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA =
        adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA := by
  have hAB :
      Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
          Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) =
        Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) := by
    simpa [hPAid] using
      (Matrix.mul_kronecker_mul PA PA (1 : CMatrix (TensorPower b n))
        (1 : CMatrix (TensorPower b n))).symm
  calc
    adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA *
        adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA =
      Matrix.kronecker
        (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
          Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
        ((1 : CMatrix (TensorPower r n)) * (1 : CMatrix (TensorPower r n))) := by
          simpa [adhwFQSWIidLiftProjectorA] using
            (Matrix.mul_kronecker_mul
              (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
              (Matrix.kronecker PA (1 : CMatrix (TensorPower b n)))
              (1 : CMatrix (TensorPower r n)) (1 : CMatrix (TensorPower r n))).symm
    _ = adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA := by
          rw [hAB]
          simp [adhwFQSWIidLiftProjectorA]

omit [DecidableEq b] in
private theorem adhwFQSWIidLiftProjectorB_idempotent
    (n : ℕ) (PB : CMatrix (TensorPower b n)) (hPBid : PB * PB = PB) :
    adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB *
      adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB =
        adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB := by
  have hAB :
      Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
          Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB =
        Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB := by
    simpa [hPBid] using
      (Matrix.mul_kronecker_mul (1 : CMatrix (TensorPower a n))
        (1 : CMatrix (TensorPower a n)) PB PB).symm
  calc
    adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB *
        adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB =
      Matrix.kronecker
        (Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
          Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
        ((1 : CMatrix (TensorPower r n)) * (1 : CMatrix (TensorPower r n))) := by
          simpa [adhwFQSWIidLiftProjectorB] using
            (Matrix.mul_kronecker_mul
              (Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
              (Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB)
              (1 : CMatrix (TensorPower r n)) (1 : CMatrix (TensorPower r n))).symm
    _ = adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB := by
          rw [hAB]
          simp [adhwFQSWIidLiftProjectorB]

omit [DecidableEq r] in
private theorem adhwFQSWIidLiftProjectorR_idempotent
    (n : ℕ) (PR : CMatrix (TensorPower r n)) (hPRid : PR * PR = PR) :
    adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR *
      adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR =
        adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
  simpa [adhwFQSWIidLiftProjectorR, hPRid] using
    (Matrix.mul_kronecker_mul
      (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
      (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n))) PR PR).symm

omit [DecidableEq a] [DecidableEq b] [DecidableEq r] in
theorem adhwFQSWIidLiftProjectorTriple_idempotent
    (n : ℕ) (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPAid : PA * PA = PA) (hPBid : PB * PB = PB) (hPRid : PR * PR = PR) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
      adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR := by
  have hAB :
      Matrix.kronecker PA PB * Matrix.kronecker PA PB =
        Matrix.kronecker PA PB := by
    simpa [hPAid, hPBid] using (Matrix.mul_kronecker_mul PA PA PB PB).symm
  calc
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      Matrix.kronecker
        (Matrix.kronecker PA PB * Matrix.kronecker PA PB) (PR * PR) := by
          simpa [adhwFQSWIidLiftProjectorTriple] using
            (Matrix.mul_kronecker_mul (Matrix.kronecker PA PB) (Matrix.kronecker PA PB)
              PR PR).symm
    _ = adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR := by
          rw [hAB, hPRid]
          simp [adhwFQSWIidLiftProjectorTriple]

private theorem adhwFQSW_rejection_trace_eq_one_sub_acceptance
    (ρ : State a) (P : CMatrix a) :
    ((ρ.matrix * (1 - P)).trace).re = 1 - ((P * ρ.matrix).trace).re := by
  have hmul : ρ.matrix * (1 - P) = ρ.matrix - ρ.matrix * P := by
    noncomm_ring
  rw [hmul, Matrix.trace_sub, Complex.sub_re, ρ.trace_eq_one, Complex.one_re]
  rw [Matrix.trace_mul_comm]

private theorem adhwFQSWIidLiftProjectorTriple_acceptance_of_single
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (η : ℝ)
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n))
    (hPA : PA.PosSemidef) (hPB : PB.PosSemidef) (hPR : PR.PosSemidef)
    (hPAid : PA * PA = PA) (hPBid : PB * PB = PB) (hPRid : PR * PR = PR)
    (haccA :
      1 - η / 3 ≤
        ((adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA * ρ.matrix).trace).re)
    (haccB :
      1 - η / 3 ≤
        ((adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB * ρ.matrix).trace).re)
    (haccR :
      1 - η / 3 ≤
        ((adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * ρ.matrix).trace).re) :
    1 - η ≤
      ((adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        ρ.matrix).trace).re := by
  let PiA := adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA
  let PiB := adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  have hunion : (1 - Pi) ≤ (1 - PiA) + (1 - PiB) + (1 - PiR) := by
    simpa [Pi, PiA, PiB, PiR] using
      adhwFQSWIidLiftProjector_union_bound (a := a) (b := b) (r := r) n PA PB PR
        hPA hPB hPR hPAid hPBid hPRid
  have htrace_le :=
    cMatrix_trace_mul_le_of_le_posSemidef_left (W := ρ.matrix) ρ.pos hunion
  have hsum :
      ((ρ.matrix * ((1 - PiA) + (1 - PiB) + (1 - PiR))).trace).re =
        (1 - ((PiA * ρ.matrix).trace).re) +
          (1 - ((PiB * ρ.matrix).trace).re) +
            (1 - ((PiR * ρ.matrix).trace).re) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
      Complex.add_re, Complex.add_re]
    rw [adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ PiA]
    rw [adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ PiB]
    rw [adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ PiR]
  have hrejection :
      ((ρ.matrix * (1 - Pi)).trace).re ≤ η := by
    calc
      ((ρ.matrix * (1 - Pi)).trace).re
          ≤ ((ρ.matrix * ((1 - PiA) + (1 - PiB) + (1 - PiR))).trace).re := htrace_le
      _ = (1 - ((PiA * ρ.matrix).trace).re) +
            (1 - ((PiB * ρ.matrix).trace).re) +
              (1 - ((PiR * ρ.matrix).trace).re) := hsum
      _ ≤ η := by linarith
  have hrej_eq := adhwFQSW_rejection_trace_eq_one_sub_acceptance ρ Pi
  linarith

private theorem adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftB_sandwich_partialTraceR
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n)) :
    partialTraceB
        (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n)
        (Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
          ρ.matrix *
          Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))) =
      Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
        partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n)
          (adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA * ρ.matrix *
            adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA) *
        Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB := by
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  simp [adhwFQSWIidLiftProjectorA, partialTraceB, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (adhwFQSW_sum_five_comm
      (fun r0 aR bR aL bL =>
        PA xa aL *
          (PA aR ya *
            (PB xb bL *
              (PB bR yb * ρ.matrix ((aL, bL), r0) ((aR, bR), r0))))))

private theorem adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftA_sandwich_partialTraceR
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n)) :
    partialTraceB
        (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n)
        (Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
          ρ.matrix *
          Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))) =
      Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
        partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n)
          (adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB * ρ.matrix *
            adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB) *
        Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) := by
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  simp [adhwFQSWIidLiftProjectorB, partialTraceB, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (adhwFQSW_sum_five_comm_leftPair
      (fun r0 aR bR aL bL =>
        PA xa aL *
          (PA aR ya *
            (PB xb bL *
              (PB bR yb * ρ.matrix ((aL, bL), r0) ((aR, bR), r0))))))

private theorem adhwFQSW_triple_sandwich_eq_liftR_select_liftAB_sandwich
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        ρ.matrix *
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR *
        (Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
          ρ.matrix *
          Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))) *
        adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
  let K : CMatrix (Prod (TensorPower a n) (TensorPower b n)) := Matrix.kronecker PA PB
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker K (1 : CMatrix (TensorPower r n))
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  have hleft : PiR * PiAB = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
        K PR (1 : CMatrix (TensorPower r n))).symm
  have hright : PiAB * PiR = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul K (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
        (1 : CMatrix (TensorPower r n)) PR).symm
  calc
    Pi * ρ.matrix * Pi = PiR * PiAB * ρ.matrix * (PiAB * PiR) := by
      rw [hleft, hright]
    _ = PiR * (PiAB * ρ.matrix * PiAB) * PiR := by
      noncomm_ring

private theorem adhwFQSW_triple_sandwich_eq_liftAB_select_liftR_sandwich
    (n : ℕ)
    (ρ : State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)))
    (PA : CMatrix (TensorPower a n)) (PB : CMatrix (TensorPower b n))
    (PR : CMatrix (TensorPower r n)) :
    adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR *
        ρ.matrix *
        adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR =
      Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) *
        (adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * ρ.matrix *
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR) *
        Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n)) := by
  let K : CMatrix (Prod (TensorPower a n) (TensorPower b n)) := Matrix.kronecker PA PB
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker K (1 : CMatrix (TensorPower r n))
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  have hleft : PiAB * PiR = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul K (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
        (1 : CMatrix (TensorPower r n)) PR).symm
  have hright : PiR * PiAB = Pi := by
    simpa [PiR, PiAB, Pi, K, adhwFQSWIidLiftProjectorR,
      adhwFQSWIidLiftProjectorTriple] using
      (Matrix.mul_kronecker_mul (1 : CMatrix (Prod (TensorPower a n) (TensorPower b n)))
        K PR (1 : CMatrix (TensorPower r n))).symm
  calc
    Pi * ρ.matrix * Pi = PiAB * PiR * ρ.matrix * (PiR * PiAB) := by
      rw [hleft, hright]
    _ = PiAB * (PiR * ρ.matrix * PiR) * PiAB := by
      noncomm_ring

private theorem adhwFQSW_normalizedTripleSandwich_marginalA_le_envelope
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ' : ℝ) :
    let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
    let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
    let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
    let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
    let τM := Pi * (adhwFQSWIidSourceState ψ n).matrix * Pi
    0 < τM.trace.re →
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤
        (((((τM.trace.re)⁻¹ : ℝ) : ℂ) *
          (((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ'))) : ℝ) : ℂ)) • PA) := by
  dsimp only
  intro htrace_pos
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))
  let PiA := adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA
  let τM : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Pi * ρ.matrix * Pi
  let τAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiAB * ρ.matrix * PiAB
  let τA : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiA * ρ.matrix * PiA
  have hPA_stmt :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPB_stmt :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPR_stmt :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δ'
  rcases hPA_stmt with ⟨hPApsd, _hPAherm, hPAid, hPAle⟩
  rcases hPB_stmt with ⟨hPBpsd, _hPBherm, hPBid, _hPBle⟩
  rcases hPR_stmt with ⟨hPRpsd, _hPRherm, hPRid, _hPRle⟩
  have hPiABpsd : PiAB.PosSemidef := by
    exact (hPApsd.kronecker hPBpsd).kronecker Matrix.PosSemidef.one
  have hτABpsd : τAB.PosSemidef := by
    simpa [τAB, PiAB] using projector_sandwich_posSemidef PiAB hPiABpsd ρ
  have hR :
      partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM ≤
        partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB := by
    have hsel :=
      adhwFQSW_partialTraceB_selective_projector_le
        (X := τAB) hτABpsd PR hPRpsd hPRid
    have hτeq :
        τM =
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * τAB *
            adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
      simpa [τM, τAB, Pi, PiAB, Matrix.mul_assoc] using
        adhwFQSW_triple_sandwich_eq_liftR_select_liftAB_sandwich
          (a := a) (b := b) (r := r) n ρ PA PB PR
    simpa [τAB, hτeq, adhwFQSWIidLiftProjectorR] using hsel
  have hApsd : τA.PosSemidef := by
    have hPiApsd := adhwFQSWIidLiftProjectorA_posSemidef (b := b) (r := r) n PA hPApsd
    simpa [τA, PiA] using projector_sandwich_posSemidef PiA hPiApsd ρ
  have hB :
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB) ≤
        partialTraceB (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA) := by
    have hτA_R_psd :
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA).PosSemidef :=
      partialTraceB_posSemidef (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n) hApsd
    have hsel :=
      adhwFQSW_partialTraceB_selective_projector_le
        (X := partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA)
        hτA_R_psd PB hPBpsd hPBid
    have heq :
        partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB =
          Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB *
            partialTraceB
              (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA *
            Matrix.kronecker (1 : CMatrix (TensorPower a n)) PB := by
      simpa [τAB, τA, PiAB, PiA] using
        adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftB_sandwich_partialTraceR
          (a := a) (b := b) (r := r) n ρ PA PB
    simpa [heq] using hsel
  have hcore₀ :
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM) ≤
        PA * ρ.marginalA.marginalA.matrix * PA := by
    calc
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM)
          ≤ partialTraceB (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB) :=
              adhwFQSW_partialTraceB_mono
                (α := TensorPower a n) (β := TensorPower b n) hR
      _ ≤ partialTraceB (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τA) := hB
      _ = PA * ρ.marginalA.marginalA.matrix * PA := by
            simpa [τA, PiA] using
              adhwFQSWIidLiftProjectorA_marginalA_marginalA
                (a := a) (b := b) (r := r) n ρ PA
  have hmarg :
      ρ.marginalA.marginalA.matrix =
        ((adhwFQSWSystemAState ψ).tensorPower n).matrix := by
    simpa [ρ] using congrArg (fun σ : State (TensorPower a n) => σ.matrix)
      (adhwFQSWIidSourceState_marginalA_eq_tensorPower ψ n)
  have hcompress :
      PA * ρ.marginalA.marginalA.matrix * PA ≤
        (((((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ')))) : ℝ) : ℂ) • PA) := by
    have htyp :=
      State.typicalSubspaceProjector_tensorPower_compress_le
        (adhwFQSWSystemAState ψ) n δ'
    have hexp :
        -((n : ℝ) * (adhwFQSWEntropyA ψ - δ')) =
          -((n : ℝ) * (adhwFQSWSystemAState ψ).vonNeumann - (n : ℝ) * δ') := by
      simp [adhwFQSWEntropyA]
      ring
    rw [hmarg]
    simpa [PA, hexp] using htyp
  have hcore := hcore₀.trans hcompress
  let c : ℝ := (τM.trace.re)⁻¹
  let d : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ')))
  have hinv_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr htrace_pos.le
  have hscaled :=
    adhwFQSW_smul_le_smul_of_nonneg
      (α := TensorPower a n)
      (A := partialTraceB (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n) τM))
      (B := (((d : ℝ) : ℂ) • PA))
      hinv_nonneg hcore
  have hscaled_prod :
      (((c : ℝ) : ℂ) •
          partialTraceB (a := TensorPower a n) (b := TensorPower b n)
            (partialTraceB
              (a := Prod (TensorPower a n) (TensorPower b n))
              (b := TensorPower r n) τM)) ≤
        (((((c : ℝ) : ℂ) * (((d : ℝ) : ℂ)) : ℂ) • PA)) := by
    have hnested :
        (((c : ℝ) : ℂ) •
            partialTraceB (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n))
                (b := TensorPower r n) τM)) ≤
          (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • PA)) := by
      simpa using hscaled
    rw [adhwFQSW_complex_smul_smul (((c : ℝ) : ℂ)) (((d : ℝ) : ℂ)) PA] at hnested
    exact hnested
  simpa [c, d, τM, Pi, ρ, PA, PB, PR, partialTraceB_smul, Matrix.mul_assoc] using hscaled_prod

private theorem adhwFQSW_normalizedTripleSandwich_marginalB_le_envelope
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ' : ℝ) :
    let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
    let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
    let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
    let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
    let τM := Pi * (adhwFQSWIidSourceState ψ n).matrix * Pi
    0 < τM.trace.re →
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤
        (((((τM.trace.re)⁻¹ : ℝ) : ℂ) *
          (((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ'))) : ℝ) : ℂ)) • PB) := by
  dsimp only
  intro htrace_pos
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))
  let PiB := adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB
  let τM : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Pi * ρ.matrix * Pi
  let τAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiAB * ρ.matrix * PiAB
  let τB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiB * ρ.matrix * PiB
  have hPA_stmt :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPB_stmt :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPR_stmt :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δ'
  rcases hPA_stmt with ⟨hPApsd, _hPAherm, hPAid, _hPAle⟩
  rcases hPB_stmt with ⟨hPBpsd, _hPBherm, hPBid, hPBle⟩
  rcases hPR_stmt with ⟨hPRpsd, _hPRherm, hPRid, _hPRle⟩
  have hPiABpsd : PiAB.PosSemidef := by
    exact (hPApsd.kronecker hPBpsd).kronecker Matrix.PosSemidef.one
  have hτABpsd : τAB.PosSemidef := by
    simpa [τAB, PiAB] using projector_sandwich_posSemidef PiAB hPiABpsd ρ
  have hR :
      partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM ≤
        partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB := by
    have hsel :=
      adhwFQSW_partialTraceB_selective_projector_le
        (X := τAB) hτABpsd PR hPRpsd hPRid
    have hτeq :
        τM =
          adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR * τAB *
            adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR := by
      simpa [τM, τAB, Pi, PiAB, Matrix.mul_assoc] using
        adhwFQSW_triple_sandwich_eq_liftR_select_liftAB_sandwich
          (a := a) (b := b) (r := r) n ρ PA PB PR
    simpa [τAB, hτeq, adhwFQSWIidLiftProjectorR] using hsel
  have hBpsd : τB.PosSemidef := by
    have hPiBpsd := adhwFQSWIidLiftProjectorB_posSemidef (a := a) (r := r) n PB hPBpsd
    simpa [τB, PiB] using projector_sandwich_posSemidef PiB hPiBpsd ρ
  have hA :
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB) ≤
        partialTraceA (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB) := by
    have hτB_R_psd :
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB).PosSemidef :=
      partialTraceB_posSemidef (a := Prod (TensorPower a n) (TensorPower b n))
        (b := TensorPower r n) hBpsd
    have hsel :=
      adhwFQSW_partialTraceA_selective_projector_le
        (X := partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB)
        hτB_R_psd PA hPApsd hPAid
    have heq :
        partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB =
          Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) *
            partialTraceB
              (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB *
            Matrix.kronecker PA (1 : CMatrix (TensorPower b n)) := by
      simpa [τAB, τB, PiAB, PiB] using
        adhwFQSW_partialTraceR_liftAB_sandwich_eq_liftA_sandwich_partialTraceR
          (a := a) (b := b) (r := r) n ρ PA PB
    simpa [heq] using hsel
  have hcore₀ :
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM) ≤
        PB * ρ.marginalA.marginalB.matrix * PB := by
    calc
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
          (partialTraceB
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM)
          ≤ partialTraceA (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τAB) :=
              adhwFQSW_partialTraceA_mono
                (α := TensorPower a n) (β := TensorPower b n) hR
      _ ≤ partialTraceA (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τB) := hA
      _ = PB * ρ.marginalA.marginalB.matrix * PB := by
            simpa [τB, PiB] using
              adhwFQSWIidLiftProjectorB_marginalA_marginalB
                (a := a) (b := b) (r := r) n ρ PB
  have hmarg :
      ρ.marginalA.marginalB.matrix =
        ((adhwFQSWSystemBState ψ).tensorPower n).matrix := by
    simpa [ρ] using congrArg (fun σ : State (TensorPower b n) => σ.matrix)
      (adhwFQSWIidSourceState_marginalB_eq_tensorPower ψ n)
  have hcompress :
      PB * ρ.marginalA.marginalB.matrix * PB ≤
        (((((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ')))) : ℝ) : ℂ) • PB) := by
    have htyp :=
      State.typicalSubspaceProjector_tensorPower_compress_le
        (adhwFQSWSystemBState ψ) n δ'
    have hexp :
        -((n : ℝ) * (adhwFQSWEntropyB ψ - δ')) =
          -((n : ℝ) * (adhwFQSWSystemBState ψ).vonNeumann - (n : ℝ) * δ') := by
      simp [adhwFQSWEntropyB]
      ring
    rw [hmarg]
    simpa [PB, hexp] using htyp
  have hcore := hcore₀.trans hcompress
  let c : ℝ := (τM.trace.re)⁻¹
  let d : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ')))
  have hinv_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr htrace_pos.le
  have hscaled :=
    adhwFQSW_smul_le_smul_of_nonneg
      (α := TensorPower b n)
      (A := partialTraceA (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n) τM))
      (B := (((d : ℝ) : ℂ) • PB))
      hinv_nonneg hcore
  have hscaled_prod :
      (((c : ℝ) : ℂ) •
          partialTraceA (a := TensorPower a n) (b := TensorPower b n)
            (partialTraceB
              (a := Prod (TensorPower a n) (TensorPower b n))
              (b := TensorPower r n) τM)) ≤
        (((((c : ℝ) : ℂ) * (((d : ℝ) : ℂ)) : ℂ) • PB)) := by
    have hnested :
        (((c : ℝ) : ℂ) •
            partialTraceA (a := TensorPower a n) (b := TensorPower b n)
              (partialTraceB
                (a := Prod (TensorPower a n) (TensorPower b n))
                (b := TensorPower r n) τM)) ≤
          (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • PB)) := by
      simpa using hscaled
    rw [adhwFQSW_complex_smul_smul (((c : ℝ) : ℂ)) (((d : ℝ) : ℂ)) PB] at hnested
    exact hnested
  simpa [c, d, τM, Pi, ρ, PA, PB, PR, partialTraceA_smul, partialTraceB_smul,
    Matrix.mul_assoc] using hscaled_prod

private theorem adhwFQSW_normalizedTripleSandwich_marginalR_le_envelope
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ' : ℝ) :
    let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
    let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
    let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
    let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
    let τM := Pi * (adhwFQSWIidSourceState ψ n).matrix * Pi
    0 < τM.trace.re →
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM) ≤
        (((((τM.trace.re)⁻¹ : ℝ) : ℂ) *
          (((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ'))) : ℝ) : ℂ)) • PR) := by
  dsimp only
  intro htrace_pos
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δ'
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δ'
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δ'
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let PiAB : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Matrix.kronecker (Matrix.kronecker PA PB) (1 : CMatrix (TensorPower r n))
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  let τM : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Pi * ρ.matrix * Pi
  let τR : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiR * ρ.matrix * PiR
  have hPA_stmt :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPB_stmt :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δ'
  have hPR_stmt :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δ'
  rcases hPA_stmt with ⟨hPApsd, _hPAherm, hPAid, _hPAle⟩
  rcases hPB_stmt with ⟨hPBpsd, _hPBherm, hPBid, _hPBle⟩
  rcases hPR_stmt with ⟨hPRpsd, _hPRherm, _hPRid, hPRle⟩
  have hQpsd : (Matrix.kronecker PA PB).PosSemidef := hPApsd.kronecker hPBpsd
  have hQid : Matrix.kronecker PA PB * Matrix.kronecker PA PB = Matrix.kronecker PA PB := by
    calc
      Matrix.kronecker PA PB * Matrix.kronecker PA PB =
          Matrix.kronecker (PA * PA) (PB * PB) := by
            exact (Matrix.mul_kronecker_mul PA PA PB PB).symm
      _ = Matrix.kronecker PA PB := by rw [hPAid, hPBid]
  have hRpsd : τR.PosSemidef := by
    have hPiRpsd := adhwFQSWIidLiftProjectorR_posSemidef (a := a) (b := b) n PR hPRpsd
    simpa [τR, PiR] using projector_sandwich_posSemidef PiR hPiRpsd ρ
  have hAB :
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM ≤
        partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τR := by
    have hsel :=
      adhwFQSW_partialTraceA_selective_projector_le
        (X := τR) hRpsd (Matrix.kronecker PA PB) hQpsd hQid
    have hτeq :
        τM = PiAB * τR * PiAB := by
      simpa [τM, τR, Pi, PiAB, PiR, Matrix.mul_assoc] using
        adhwFQSW_triple_sandwich_eq_liftAB_select_liftR_sandwich
          (a := a) (b := b) (r := r) n ρ PA PB PR
    simpa [τR, hτeq, PiAB] using hsel
  have hcore₀ :
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM ≤
        PR * ρ.marginalB.matrix * PR := by
    calc
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM
          ≤ partialTraceA
              (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τR := hAB
      _ = PR * ρ.marginalB.matrix * PR := by
            simpa [τR, PiR] using
              adhwFQSWIidLiftProjectorR_marginalB
                (a := a) (b := b) (r := r) n ρ PR
  have hmarg :
      ρ.marginalB.matrix =
        ((adhwFQSWSystemRState ψ).tensorPower n).matrix := by
    simpa [ρ] using congrArg (fun σ : State (TensorPower r n) => σ.matrix)
      (adhwFQSWIidSourceState_marginalR_eq_tensorPower ψ n)
  have hcompress :
      PR * ρ.marginalB.matrix * PR ≤
        (((((2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ')))) : ℝ) : ℂ) • PR) := by
    have htyp :=
      State.typicalSubspaceProjector_tensorPower_compress_le
        (adhwFQSWSystemRState ψ) n δ'
    have hexp :
        -((n : ℝ) * (adhwFQSWEntropyR ψ - δ')) =
          -((n : ℝ) * (adhwFQSWSystemRState ψ).vonNeumann - (n : ℝ) * δ') := by
      simp [adhwFQSWEntropyR]
      ring
    rw [hmarg]
    simpa [PR, hexp] using htyp
  have hcore := hcore₀.trans hcompress
  let c : ℝ := (τM.trace.re)⁻¹
  let d : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ')))
  have hinv_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr htrace_pos.le
  have hscaled :=
    adhwFQSW_smul_le_smul_of_nonneg
      (α := TensorPower r n)
      (A := partialTraceA
        (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM)
      (B := (((d : ℝ) : ℂ) • PR))
      hinv_nonneg hcore
  have hscaled_prod :
      (((c : ℝ) : ℂ) •
          partialTraceA
            (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM) ≤
        (((((c : ℝ) : ℂ) * (((d : ℝ) : ℂ)) : ℂ) • PR)) := by
    have hnested :
        (((c : ℝ) : ℂ) •
            partialTraceA
              (a := Prod (TensorPower a n) (TensorPower b n)) (b := TensorPower r n) τM) ≤
          (((c : ℝ) : ℂ) • (((d : ℝ) : ℂ) • PR)) := by
      simpa using hscaled
    rw [adhwFQSW_complex_smul_smul (((c : ℝ) : ℂ)) (((d : ℝ) : ℂ)) PR] at hnested
    exact hnested
  simpa [c, d, τM, Pi, ρ, PA, PB, PR, partialTraceA_smul, Matrix.mul_assoc] using
    hscaled_prod

/-- AEP high-weight form for one typical projector spectral weight. -/
private theorem adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
    (ρ : State a) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      1 - η ≤ ρ.typicalSubspaceSpectralWeight n δ := by
  have hlim := ρ.tendsto_typicalSubspaceSpectralWeight hδ
  have hball :
      ∀ᶠ n : ℕ in Filter.atTop,
        ρ.typicalSubspaceSpectralWeight n δ ∈ Metric.ball (1 : ℝ) η :=
    hlim.eventually (Metric.ball_mem_nhds _ hη)
  have hev :
      ∀ᶠ n : ℕ in Filter.atTop,
        1 - η ≤ ρ.typicalSubspaceSpectralWeight n δ := by
    filter_upwards [hball] with n hn
    rw [Metric.mem_ball, Real.dist_eq] at hn
    have hlt := abs_lt.mp hn
    linarith
  exact Filter.eventually_atTop.mp hev

/-- Small scalar split used to turn eventual high-weight estimates into an
ADHW-style final trace-error budget. -/
private def adhwFQSWTypicalEta (ε : ℝ) : ℝ :=
  min ((ε / 4) ^ 2) (min (ε / 4) (1 / 2))

private theorem adhwFQSWTypicalEta_pos {ε : ℝ} (hε : 0 < ε) :
    0 < adhwFQSWTypicalEta ε := by
  dsimp [adhwFQSWTypicalEta]
  positivity

private theorem adhwFQSWTypicalEta_error_split {ε : ℝ} (hε : 0 < ε) :
    2 * (Real.sqrt (adhwFQSWTypicalEta ε) + adhwFQSWTypicalEta ε) ≤ ε := by
  have hη_nonneg : 0 ≤ adhwFQSWTypicalEta ε := (adhwFQSWTypicalEta_pos hε).le
  have hη_sq : adhwFQSWTypicalEta ε ≤ (ε / 4) ^ 2 := by
    dsimp [adhwFQSWTypicalEta]
    exact min_le_left _ _
  have hη_quarter : adhwFQSWTypicalEta ε ≤ ε / 4 := by
    dsimp [adhwFQSWTypicalEta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hsqrt : Real.sqrt (adhwFQSWTypicalEta ε) ≤ ε / 4 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, hη_sq⟩
  linarith

private theorem adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
    {t η H δ δtyp : ℝ} (n : ℕ)
    (htrace : 1 - η ≤ t)
    (hη_le_half : η ≤ (1 / 2 : ℝ))
    (hδtyp : δtyp = δ / 2)
    (hn_absorb : 1 ≤ (n : ℝ) * δ / 2) :
    t⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (H - δ))) := by
  have ht_half : (1 / 2 : ℝ) ≤ t := by linarith
  have ht_pos : 0 < t := by linarith
  have hinv_le_two : t⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ ht_pos]
    nlinarith
  have hpow_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  calc
    t⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp)))
        ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) * (H - δtyp))) := by
          exact mul_le_mul_of_nonneg_right hinv_le_two hpow_nonneg
    _ = (2 : ℝ) ^ (1 + -((n : ℝ) * (H - δtyp))) := by
          nth_rw 1 [← Real.rpow_one (2 : ℝ)]
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (H - δ))) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
          rw [hδtyp]
          nlinarith

private theorem adhwFQSW_real_smul_one_le_smul_one
    {α : Type u} [Fintype α] [DecidableEq α]
    {c d : ℝ} (hcd : c ≤ d) :
    (((c : ℝ) : ℂ) • (1 : CMatrix α)) ≤
      (((d : ℝ) : ℂ) • (1 : CMatrix α)) := by
  rw [Matrix.le_iff]
  have hdiff :
      (((d : ℝ) : ℂ) • (1 : CMatrix α) -
          ((c : ℝ) : ℂ) • (1 : CMatrix α)) =
        ((((d - c : ℝ) : ℂ)) • (1 : CMatrix α)) := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Complex.ofReal_sub, sub_mul]
  rw [hdiff]
  exact Matrix.PosSemidef.smul Matrix.PosSemidef.one
    (by exact_mod_cast sub_nonneg.mpr hcd)

private theorem adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ : State α) {P : CMatrix α} {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hP_le : P ≤ (1 : CMatrix α))
    (hcd : c ≤ d) (henv : ρ.matrix ≤ (((c : ℝ) : ℂ) • P)) :
    hilbertSchmidtSq ρ.matrix ≤ d := by
  have hPenv : (((c : ℝ) : ℂ) • P) ≤ (((c : ℝ) : ℂ) • (1 : CMatrix α)) :=
    adhwFQSW_smul_le_smul_of_nonneg hc hP_le
  have hdenv : (((c : ℝ) : ℂ) • (1 : CMatrix α)) ≤
      (((d : ℝ) : ℂ) • (1 : CMatrix α)) :=
    adhwFQSW_real_smul_one_le_smul_one hcd
  exact State.hilbertSchmidtSq_matrix_le_of_le_smul_one ρ hd
    (henv.trans (hPenv.trans hdenv))

private theorem adhwFQSW_traceNormDistance_le_of_normalizedTraceDistance_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ σ : State α) {η ε : ℝ}
    (hdist : ρ.normalizedTraceDistance σ ≤ Real.sqrt η + η)
    (hsplit : 2 * (Real.sqrt η + η) ≤ ε) :
    traceNormDistance ρ.matrix σ.matrix ≤ ε := by
  have hnorm : (1 / 2 : ℝ) * traceNormDistance ρ.matrix σ.matrix ≤
      Real.sqrt η + η := by
    simpa [State.normalizedTraceDistance, normalizedTraceDistance] using hdist
  have hnonneg : 0 ≤ traceNormDistance ρ.matrix σ.matrix :=
    traceNormDistance_nonneg ρ.matrix σ.matrix
  nlinarith

private theorem adhwFQSW_traceNormDistance_triangle_state
    {α : Type u} [Fintype α] [DecidableEq α]
    (ρ σ τ : State α) :
    traceNormDistance ρ.matrix τ.matrix ≤
      traceNormDistance ρ.matrix σ.matrix + traceNormDistance σ.matrix τ.matrix := by
  have htri := State.normalizedTraceDistance_triangle ρ σ τ
  have hscaled :
      (1 / 2 : ℝ) * traceNormDistance ρ.matrix τ.matrix ≤
        (1 / 2 : ℝ) * traceNormDistance ρ.matrix σ.matrix +
          (1 / 2 : ℝ) * traceNormDistance σ.matrix τ.matrix := by
    simpa [State.normalizedTraceDistance, normalizedTraceDistance,
      mul_add] using htri
  have hnonneg : 0 ≤ traceNormDistance ρ.matrix τ.matrix :=
    traceNormDistance_nonneg ρ.matrix τ.matrix
  nlinarith

/-- Simultaneous ADHW i.i.d. typical projectors `Π_A`, `Π_B`, and `Π_R`,
with the no-witness spectral construction, source estimates, marginal purity
bounds, and item iii rank bounds from fqsw.tex lines 1110-1129.

The projectors use the internal typicality window `δ / 2`.  This is the
standard slack split needed by `State.eventually_two_pow_sub_le_typicalSubspaceDimension`:
the constructed projectors are typical at the smaller window while the public
ADHW rank and purity bounds are stated with the advertised `±δ` slack. -/
structure ADHWFQSWSimultaneousTypicalProjectors
    (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ) (δ ε : ℝ) where
  typicalitySlack : ℝ
  typicalitySlack_eq : typicalitySlack = δ / 2
  typicalitySlack_pos : 0 < typicalitySlack
  typicalitySlack_lt_delta : typicalitySlack < δ
  projectorA : CMatrix (TensorPower a n)
  projectorB : CMatrix (TensorPower b n)
  projectorR : CMatrix (TensorPower r n)
  projectorA_eq :
    projectorA = (adhwFQSWSystemAState ψ).typicalSubspaceProjector n typicalitySlack
  projectorB_eq :
    projectorB = (adhwFQSWSystemBState ψ).typicalSubspaceProjector n typicalitySlack
  projectorR_eq :
    projectorR = (adhwFQSWSystemRState ψ).typicalSubspaceProjector n typicalitySlack
  projectorA_statement :
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement n typicalitySlack
  projectorB_statement :
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement n typicalitySlack
  projectorR_statement :
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement n typicalitySlack
  compressedSource :
    State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
  normalizedTypicalSource :
    State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
  normalizedTypicalSource_projected_trace_pos :
    0 < (adhwFQSWIidProjectedSourceMatrix
      (a := a) (b := b) (r := r) ψ n projectorA projectorB projectorR).trace.re
  normalizedTypicalSource_matrix_eq :
    normalizedTypicalSource.matrix =
      ((((adhwFQSWIidProjectedSourceMatrix
        (a := a) (b := b) (r := r) ψ n projectorA projectorB projectorR).trace.re)⁻¹ :
          ℝ) : ℂ) •
        adhwFQSWIidProjectedSourceMatrix
          (a := a) (b := b) (r := r) ψ n projectorA projectorB projectorR
  schumacher_traceNorm_le :
    traceNormDistance compressedSource.matrix (adhwFQSWIidSourceState ψ n).matrix ≤ ε
  schumacher_traceNorm_le_normalizedTypical :
    traceNormDistance compressedSource.matrix normalizedTypicalSource.matrix ≤ ε
  normalized_traceNorm_le :
    traceNormDistance normalizedTypicalSource.matrix (adhwFQSWIidSourceState ψ n).matrix ≤ ε
  purityA_le :
    hilbertSchmidtSq normalizedTypicalSource.marginalA.marginalA.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ)))
  purityB_le :
    hilbertSchmidtSq normalizedTypicalSource.marginalA.marginalB.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
  purityR_le :
    hilbertSchmidtSq normalizedTypicalSource.marginalB.matrix ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ)))
  rankA_lower :
    (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ - δ)) ≤
      (adhwFQSWSystemAState ψ).typicalSubspaceDimension n typicalitySlack
  rankA_upper :
    (adhwFQSWSystemAState ψ).typicalSubspaceDimension n typicalitySlack ≤
      (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyA ψ + δ))
  rankB_lower :
    (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ - δ)) ≤
      (adhwFQSWSystemBState ψ).typicalSubspaceDimension n typicalitySlack
  rankB_upper :
    (adhwFQSWSystemBState ψ).typicalSubspaceDimension n typicalitySlack ≤
      (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyB ψ + δ))
  rankR_lower :
    (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ - δ)) ≤
      (adhwFQSWSystemRState ψ).typicalSubspaceDimension n typicalitySlack
  rankR_upper :
    (adhwFQSWSystemRState ψ).typicalSubspaceDimension n typicalitySlack ≤
      (2 : ℝ) ^ ((n : ℝ) * (adhwFQSWEntropyR ψ + δ))

/-- Upper rank bound after splitting the advertised ADHW slack `δ` into an
internal typicality window `δ / 2`. -/
private theorem adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
    (ρ : State a) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ρ.typicalSubspaceDimension n (δ / 2) ≤
      (2 : ℝ) ^ ((n : ℝ) * (ρ.vonNeumann + δ)) := by
  have hbase : (1 : ℝ) ≤ 2 := by norm_num
  have hdim := ρ.typicalSubspaceDimension_le_two_pow n (δ / 2)
  have hexp :
      (n : ℝ) * (ρ.vonNeumann + δ / 2) ≤
        (n : ℝ) * (ρ.vonNeumann + δ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    nlinarith
  exact hdim.trans (Real.rpow_le_rpow_of_exponent_le hbase hexp)

/-- Construct the simultaneous typical-projector record from local spectral
typical projectors, with no external proof witnesses.

For every positive advertised slack `δ` and tolerance `ε`, all sufficiently
large `n` have the three internal-window projectors, the normalized source
estimates, the three marginal purity estimates, and the ADHW item iii rank
bounds. -/
theorem exists_adhwFQSWSimultaneousTypicalProjectors
    (ψ : PureVector (Prod (Prod a b) r)) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      Nonempty (ADHWFQSWSimultaneousTypicalProjectors ψ n δ ε) := by
  have hhalf_pos : 0 < δ / 2 := by linarith
  have hhalf_lt : δ / 2 < δ := by linarith
  let η : ℝ := adhwFQSWTypicalEta (ε / 2)
  have hε_half_pos : 0 < ε / 2 := by positivity
  have hε_half_le : ε / 2 ≤ ε := by linarith
  have hη_pos : 0 < η := by
    simpa [η] using adhwFQSWTypicalEta_pos hε_half_pos
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hη_le_half : η ≤ (1 / 2 : ℝ) := by
    dsimp [η, adhwFQSWTypicalEta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hη_lt_one : η < 1 := by linarith
  have hη_third_pos : 0 < η / 3 := by linarith
  have hη_error := adhwFQSWTypicalEta_error_split hε_half_pos
  obtain ⟨NA, hNA⟩ :=
    (adhwFQSWSystemAState ψ).eventually_two_pow_sub_le_typicalSubspaceDimension
      hhalf_pos hhalf_lt
  obtain ⟨NB, hNB⟩ :=
    (adhwFQSWSystemBState ψ).eventually_two_pow_sub_le_typicalSubspaceDimension
      hhalf_pos hhalf_lt
  obtain ⟨NR, hNR⟩ :=
    (adhwFQSWSystemRState ψ).eventually_two_pow_sub_le_typicalSubspaceDimension
      hhalf_pos hhalf_lt
  obtain ⟨NwA, hW_A⟩ :=
    adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
      (adhwFQSWSystemAState ψ) hhalf_pos hη_third_pos
  obtain ⟨NwB, hW_B⟩ :=
    adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
      (adhwFQSWSystemBState ψ) hhalf_pos hη_third_pos
  obtain ⟨NwR, hW_R⟩ :=
    adhwFQSW_eventually_one_sub_le_typicalSubspaceSpectralWeight
      (adhwFQSWSystemRState ψ) hhalf_pos hη_third_pos
  let Nabs : ℕ := Nat.ceil (2 / δ)
  let N : ℕ := max NA (max NB (max NR (max NwA (max NwB (max NwR Nabs)))))
  refine ⟨N, ?_⟩
  intro n hn
  have hnA : n ≥ NA := by dsimp [N] at hn; omega
  have hnB : n ≥ NB := by dsimp [N] at hn; omega
  have hnR : n ≥ NR := by dsimp [N] at hn; omega
  have hnWA : n ≥ NwA := by dsimp [N] at hn; omega
  have hnWB : n ≥ NwB := by dsimp [N] at hn; omega
  have hnWR : n ≥ NwR := by dsimp [N] at hn; omega
  have hnAbs : n ≥ Nabs := by dsimp [N] at hn; omega
  have hn_absorb : 1 ≤ (n : ℝ) * δ / 2 := by
    have hceil : 2 / δ ≤ (Nabs : ℝ) := by
      simpa [Nabs] using Nat.le_ceil (2 / δ)
    have hnAbs_real : (Nabs : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnAbs
    have htwo_div_le : 2 / δ ≤ (n : ℝ) := hceil.trans hnAbs_real
    have hmul := mul_le_mul_of_nonneg_right htwo_div_le hδ.le
    have hdiv_mul : (2 / δ) * δ = (2 : ℝ) := by field_simp [hδ.ne']
    nlinarith
  let δtyp : ℝ := δ / 2
  let ρ := adhwFQSWIidSourceState ψ n
  let PA := (adhwFQSWSystemAState ψ).typicalSubspaceProjector n δtyp
  let PB := (adhwFQSWSystemBState ψ).typicalSubspaceProjector n δtyp
  let PR := (adhwFQSWSystemRState ψ).typicalSubspaceProjector n δtyp
  let PiA := adhwFQSWIidLiftProjectorA (b := b) (r := r) n PA
  let Pi := adhwFQSWIidLiftProjectorTriple (a := a) (b := b) (r := r) n PA PB PR
  let τA : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    PiA * ρ.matrix * PiA
  let τM : CMatrix (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    Pi * ρ.matrix * Pi
  have hPAstmt :
      (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement n δtyp :=
    (adhwFQSWSystemAState ψ).typicalSubspaceProjector_statement_proved n δtyp
  have hPBstmt :
      (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement n δtyp :=
    (adhwFQSWSystemBState ψ).typicalSubspaceProjector_statement_proved n δtyp
  have hPRstmt :
      (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement n δtyp :=
    (adhwFQSWSystemRState ψ).typicalSubspaceProjector_statement_proved n δtyp
  have hPAstmt_parts := hPAstmt
  have hPBstmt_parts := hPBstmt
  have hPRstmt_parts := hPRstmt
  rcases hPAstmt_parts with ⟨hPApsd, _hPAherm, hPAid, hPAle⟩
  rcases hPBstmt_parts with ⟨hPBpsd, _hPBherm, hPBid, hPBle⟩
  rcases hPRstmt_parts with ⟨hPRpsd, _hPRherm, hPRid, hPRle⟩
  have hPiApsd : PiA.PosSemidef := by
    simpa [PiA, PA] using
      adhwFQSWIidLiftProjectorA_posSemidef (b := b) (r := r) n PA hPApsd
  have hPiAid : PiA * PiA = PiA := by
    simpa [PiA, PA] using
      adhwFQSWIidLiftProjectorA_idempotent (b := b) (r := r) n PA hPAid
  have hPipsd : Pi.PosSemidef := by
    simpa [Pi, PA, PB, PR] using
      adhwFQSWIidLiftProjectorTriple_posSemidef (a := a) (b := b) (r := r)
        n PA PB PR hPApsd hPBpsd hPRpsd
  have hPiid : Pi * Pi = Pi := by
    simpa [Pi, PA, PB, PR] using
      adhwFQSWIidLiftProjectorTriple_idempotent (a := a) (b := b) (r := r)
        n PA PB PR hPAid hPBid hPRid
  have hτApsd : τA.PosSemidef := by
    simpa [τA] using projector_sandwich_posSemidef PiA hPiApsd ρ
  have hτMpsd : τM.PosSemidef := by
    simpa [τM] using projector_sandwich_posSemidef Pi hPipsd ρ
  have haccA3 :
      1 - η / 3 ≤ ((PiA * ρ.matrix).trace).re := by
    calc
      1 - η / 3 ≤
          (adhwFQSWSystemAState ψ).typicalSubspaceSpectralWeight n δtyp :=
            hW_A n hnWA
      _ = ((PiA * ρ.matrix).trace).re := by
            simpa [PiA, PA, ρ, δtyp] using
              (adhwFQSWIid_acceptanceA (a := a) (b := b) (r := r) ψ n δtyp).symm
  let PiB := adhwFQSWIidLiftProjectorB (a := a) (r := r) n PB
  let PiR := adhwFQSWIidLiftProjectorR (a := a) (b := b) n PR
  have haccB3 :
      1 - η / 3 ≤ ((PiB * ρ.matrix).trace).re := by
    calc
      1 - η / 3 ≤
          (adhwFQSWSystemBState ψ).typicalSubspaceSpectralWeight n δtyp :=
            hW_B n hnWB
      _ = ((PiB * ρ.matrix).trace).re := by
            simpa [PiB, PB, ρ, δtyp] using
              (adhwFQSWIid_acceptanceB (a := a) (b := b) (r := r) ψ n δtyp).symm
  have haccR3 :
      1 - η / 3 ≤ ((PiR * ρ.matrix).trace).re := by
    calc
      1 - η / 3 ≤
          (adhwFQSWSystemRState ψ).typicalSubspaceSpectralWeight n δtyp :=
            hW_R n hnWR
      _ = ((PiR * ρ.matrix).trace).re := by
            simpa [PiR, PR, ρ, δtyp] using
              (adhwFQSWIid_acceptanceR (a := a) (b := b) (r := r) ψ n δtyp).symm
  have haccA : 1 - η ≤ ((PiA * ρ.matrix).trace).re := by
    linarith
  have haccTriple : 1 - η ≤ ((Pi * ρ.matrix).trace).re := by
    simpa [Pi, PiA, PiB, PiR, PA, PB, PR] using
      adhwFQSWIidLiftProjectorTriple_acceptance_of_single
        (a := a) (b := b) (r := r) n ρ η PA PB PR
        hPApsd hPBpsd hPRpsd hPAid hPBid hPRid haccA3 haccB3 haccR3
  have htrA : τA.trace.re ≠ 0 := by
    simpa [τA] using
      projector_sandwich_trace_re_ne_zero_of_acceptance PiA hPiAid ρ hη_lt_one haccA
  have htrM : τM.trace.re ≠ 0 := by
    simpa [τM] using
      projector_sandwich_trace_re_ne_zero_of_acceptance Pi hPiid ρ hη_lt_one haccTriple
  have htraceM_lower : 1 - η ≤ τM.trace.re := by
    calc
      1 - η ≤ ((Pi * ρ.matrix).trace).re := haccTriple
      _ = τM.trace.re := by
            simpa [τM] using
              (projector_sandwich_trace_re_eq_acceptance Pi hPiid ρ).symm
  have htraceM_pos : 0 < τM.trace.re :=
    lt_of_lt_of_le (by linarith : 0 < 1 - η) htraceM_lower
  let compressedSource :
      State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    State.normalizePSD τA hτApsd htrA
  let normalizedTypicalSource :
      State (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n)) :=
    State.normalizePSD τM hτMpsd htrM
  have hdistCompressed_norm :
      compressedSource.normalizedTraceDistance ρ ≤ Real.sqrt η + η := by
    simpa [compressedSource, τA, State.normalizedTraceDistance, normalizedTraceDistance,
      State.normalizePSD_matrix] using
      normalizedTraceDistance_normalize_projector_sandwich_le
        (P := PiA) hPiApsd hPiAid ρ hη_nonneg hη_lt_one haccA
  have hdistNormalized_norm :
      normalizedTypicalSource.normalizedTraceDistance ρ ≤ Real.sqrt η + η := by
    simpa [normalizedTypicalSource, τM, State.normalizedTraceDistance, normalizedTraceDistance,
      State.normalizePSD_matrix] using
      normalizedTraceDistance_normalize_projector_sandwich_le
        (P := Pi) hPipsd hPiid ρ hη_nonneg hη_lt_one haccTriple
  have hdistCompressed_half :
      traceNormDistance compressedSource.matrix ρ.matrix ≤ ε / 2 :=
    adhwFQSW_traceNormDistance_le_of_normalizedTraceDistance_le
      compressedSource ρ hdistCompressed_norm (by simpa [η] using hη_error)
  have hdistNormalized_half :
      traceNormDistance normalizedTypicalSource.matrix ρ.matrix ≤ ε / 2 :=
    adhwFQSW_traceNormDistance_le_of_normalizedTraceDistance_le
      normalizedTypicalSource ρ hdistNormalized_norm (by simpa [η] using hη_error)
  have hdistCompressed :
      traceNormDistance compressedSource.matrix ρ.matrix ≤ ε :=
    hdistCompressed_half.trans hε_half_le
  have hdistNormalized :
      traceNormDistance normalizedTypicalSource.matrix ρ.matrix ≤ ε :=
    hdistNormalized_half.trans hε_half_le
  have hdistCompressedNormalized :
      traceNormDistance compressedSource.matrix normalizedTypicalSource.matrix ≤ ε := by
    have hdistNormalized_half_comm :
        traceNormDistance ρ.matrix normalizedTypicalSource.matrix ≤ ε / 2 := by
      rw [traceNormDistance_comm]
      exact hdistNormalized_half
    calc
      traceNormDistance compressedSource.matrix normalizedTypicalSource.matrix
          ≤ traceNormDistance compressedSource.matrix ρ.matrix +
              traceNormDistance ρ.matrix normalizedTypicalSource.matrix :=
            adhwFQSW_traceNormDistance_triangle_state compressedSource ρ normalizedTypicalSource
      _ ≤ ε / 2 + ε / 2 := by
            exact add_le_add hdistCompressed_half hdistNormalized_half_comm
      _ = ε := by ring
  let cA : ℝ :=
    τM.trace.re⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δtyp)))
  let cB : ℝ :=
    τM.trace.re⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp)))
  let cR : ℝ :=
    τM.trace.re⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δtyp)))
  have hcA_nonneg : 0 ≤ cA := by
    dsimp [cA]
    exact mul_nonneg (inv_nonneg.mpr htraceM_pos.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hcB_nonneg : 0 ≤ cB := by
    dsimp [cB]
    exact mul_nonneg (inv_nonneg.mpr htraceM_pos.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hcR_nonneg : 0 ≤ cR := by
    dsimp [cR]
    exact mul_nonneg (inv_nonneg.mpr htraceM_pos.le)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have htargetA_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have htargetB_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have htargetR_nonneg :
      0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hcA_le :
      cA ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) := by
    change τM.trace.re⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ)))
    exact
      adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
        (n := n) (t := τM.trace.re) (η := η)
        (H := adhwFQSWEntropyA ψ) (δ := δ) (δtyp := δtyp)
        htraceM_lower hη_le_half rfl hn_absorb
  have hcB_le :
      cB ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) := by
    change τM.trace.re⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ)))
    exact
      adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
        (n := n) (t := τM.trace.re) (η := η)
        (H := adhwFQSWEntropyB ψ) (δ := δ) (δtyp := δtyp)
        htraceM_lower hη_le_half rfl hn_absorb
  have hcR_le :
      cR ≤ (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) := by
    change τM.trace.re⁻¹ *
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δtyp))) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ)))
    exact
      adhwFQSW_inv_trace_mul_typicalitySlack_envelope_le
        (n := n) (t := τM.trace.re) (η := η)
        (H := adhwFQSWEntropyR ψ) (δ := δ) (δtyp := δtyp)
        htraceM_lower hη_le_half rfl hn_absorb
  have henvA :
      normalizedTypicalSource.marginalA.marginalA.matrix ≤ (((cA : ℝ) : ℂ) • PA) := by
    have henv :=
      adhwFQSW_normalizedTripleSandwich_marginalA_le_envelope
        (a := a) (b := b) (r := r) ψ n δtyp htraceM_pos
    change
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤ (((cA : ℝ) : ℂ) • PA)
    rw [partialTraceB_smul, partialTraceB_smul]
    have henv' := henv
    rw [partialTraceB_smul, partialTraceB_smul] at henv'
    simpa only [τM, Pi, ρ, PA, PB, PR, cA, Matrix.mul_assoc, Complex.ofReal_mul] using henv'
  have henvB :
      normalizedTypicalSource.marginalA.marginalB.matrix ≤ (((cB : ℝ) : ℂ) • PB) := by
    have henv :=
      adhwFQSW_normalizedTripleSandwich_marginalB_le_envelope
        (a := a) (b := b) (r := r) ψ n δtyp htraceM_pos
    change
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
        (partialTraceB
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM)) ≤ (((cB : ℝ) : ℂ) • PB)
    rw [partialTraceB_smul, partialTraceA_smul]
    have henv' := henv
    rw [partialTraceB_smul, partialTraceA_smul] at henv'
    simpa only [τM, Pi, ρ, PA, PB, PR, cB, Matrix.mul_assoc, Complex.ofReal_mul] using henv'
  have henvR :
      normalizedTypicalSource.marginalB.matrix ≤ (((cR : ℝ) : ℂ) • PR) := by
    have henv :=
      adhwFQSW_normalizedTripleSandwich_marginalR_le_envelope
        (a := a) (b := b) (r := r) ψ n δtyp htraceM_pos
    change
      partialTraceA
          (a := Prod (TensorPower a n) (TensorPower b n))
          (b := TensorPower r n)
          ((((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM) ≤
        (((((τM.trace.re)⁻¹ *
            (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δtyp)))) : ℝ) : ℂ) • PR)
    rw [Complex.ofReal_mul]
    simpa only [τM, Pi, ρ, PA, PB, PR, Matrix.mul_assoc] using henv
  have hpurityA :
      hilbertSchmidtSq normalizedTypicalSource.marginalA.marginalA.matrix ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))) :=
    adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
      (c := cA)
      (d := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyA ψ - δ))))
      normalizedTypicalSource.marginalA.marginalA
      hcA_nonneg htargetA_nonneg hPAle hcA_le henvA
  have hpurityB :
      hilbertSchmidtSq normalizedTypicalSource.marginalA.marginalB.matrix ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))) :=
    adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
      (c := cB)
      (d := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyB ψ - δ))))
      normalizedTypicalSource.marginalA.marginalB
      hcB_nonneg htargetB_nonneg hPBle hcB_le henvB
  have hpurityR :
      hilbertSchmidtSq normalizedTypicalSource.marginalB.matrix ≤
        (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))) :=
    adhwFQSW_hilbertSchmidtSq_le_of_projector_envelope
      (c := cR)
      (d := (2 : ℝ) ^ (-((n : ℝ) * (adhwFQSWEntropyR ψ - δ))))
      normalizedTypicalSource.marginalB
      hcR_nonneg htargetR_nonneg hPRle hcR_le henvR
  exact
    ⟨{ typicalitySlack := δtyp
       typicalitySlack_eq := rfl
       typicalitySlack_pos := hhalf_pos
       typicalitySlack_lt_delta := hhalf_lt
       projectorA := PA
       projectorB := PB
       projectorR := PR
       projectorA_eq := rfl
       projectorB_eq := rfl
       projectorR_eq := rfl
       projectorA_statement := hPAstmt
       projectorB_statement := hPBstmt
       projectorR_statement := hPRstmt
       compressedSource := compressedSource
       normalizedTypicalSource := normalizedTypicalSource
       normalizedTypicalSource_projected_trace_pos := by
        change 0 < τM.trace.re
        exact htraceM_pos
       normalizedTypicalSource_matrix_eq := by
        change normalizedTypicalSource.matrix =
          (((τM.trace.re)⁻¹ : ℝ) : ℂ) • τM
        exact State.normalizePSD_matrix τM hτMpsd htrM
       schumacher_traceNorm_le := by
        simpa [ρ] using hdistCompressed
       schumacher_traceNorm_le_normalizedTypical := by
        simpa using hdistCompressedNormalized
       normalized_traceNorm_le := by
        simpa [ρ] using hdistNormalized
       purityA_le := hpurityA
       purityB_le := hpurityB
       purityR_le := hpurityR
       rankA_lower := by
        simpa [δtyp, adhwFQSWEntropyA] using hNA n hnA
       rankA_upper := by
        simpa [δtyp, adhwFQSWEntropyA] using
          adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
            (adhwFQSWSystemAState ψ) n hδ
       rankB_lower := by
        simpa [δtyp, adhwFQSWEntropyB] using hNB n hnB
       rankB_upper := by
        simpa [δtyp, adhwFQSWEntropyB] using
          adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
            (adhwFQSWSystemBState ψ) n hδ
       rankR_lower := by
        simpa [δtyp, adhwFQSWEntropyR] using hNR n hnR
       rankR_upper := by
        simpa [δtyp, adhwFQSWEntropyR] using
          adhwFQSW_typicalSubspaceDimension_le_two_pow_halfSlack
            (adhwFQSWSystemRState ψ) n hδ }⟩

end

end QIT
