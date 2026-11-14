/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Entropy.Entropy
public import QIT.States.Purification.ReferenceIsometry
public import QIT.Channels.Diamond
public import QIT.States.MaximallyEntangled
public import QIT.States.MaximallyMixed

/-!
# FQSW core operational API

This file is a dependency-ordered leaf of `QIT.Protocols.FQSW`.  Declaration
names, namespaces, statements, and proof terms are preserved from the original
monolithic module.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p u1 v1 w1
universe ua0 ub0 ur0 ua1 ub1 ur1
universe uq0 ue0 ubq0 urq0 uq1 ue1 ubq1 urq1

noncomputable section

variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

namespace State

/-- Marginal state on `A × R` used by coherent state transfer/FQSW. -/
def coherentTransferReferenceState
    (ρ : State (Prod (Prod a b) r)) : State (Prod a r) where
  matrix := fun ar ar' =>
    Finset.univ.sum fun j : b => ρ.matrix ((ar.1, j), ar.2) ((ar'.1, j), ar'.2)
  pos := by
    let block : b → CMatrix (Prod a r) := fun j =>
      ρ.matrix.submatrix
        (fun ar : Prod a r => ((ar.1, j), ar.2))
        (fun ar : Prod a r => ((ar.1, j), ar.2))
    have hsum : (∑ j : b, block j).PosSemidef := by
      classical
      refine Finset.induction_on (s := Finset.univ) ?_ ?_
      · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix (Prod a r)).PosSemidef)
      · intro j s hjs hs
        simpa [Finset.sum_insert hjs, block] using
          (ρ.pos.submatrix (fun ar : Prod a r => ((ar.1, j), ar.2))).add hs
    convert hsum using 1
    ext ar ar'
    simp [block, Matrix.sum_apply]
  trace_eq_one := by
    rw [← ρ.trace_eq_one]
    rw [Matrix.trace]
    change
      (∑ ar : Prod a r, ∑ j : b,
        ρ.matrix ((ar.1, j), ar.2) ((ar.1, j), ar.2)) =
      ∑ x : Prod (Prod a b) r, ρ.matrix x x
    calc
      (∑ ar : Prod a r, ∑ j : b,
          ρ.matrix ((ar.1, j), ar.2) ((ar.1, j), ar.2)) =
          ∑ j : b, ∑ ar : Prod a r,
            ρ.matrix ((ar.1, j), ar.2) ((ar.1, j), ar.2) := by
        rw [Finset.sum_comm]
      _ = ∑ j : b, ∑ i : a, ∑ k : r,
            ρ.matrix ((i, j), k) ((i, j), k) := by
        simp [Fintype.sum_prod_type]
      _ = ∑ i : a, ∑ j : b, ∑ k : r,
            ρ.matrix ((i, j), k) ((i, j), k) := by
        rw [Finset.sum_comm]
      _ = ∑ x : Prod (Prod a b) r, ρ.matrix x x := by
        simp [Fintype.sum_prod_type]

/-- Reference mutual information `I(A;R)` for coherent state transfer/FQSW. -/
def coherentTransferReferenceMutualInformation
    (ρ : State (Prod (Prod a b) r)) : ℝ :=
  mutualInformation ρ.coherentTransferReferenceState

/-- Coherent state-transfer quantum communication rate `(1/2) I(A;R)`. -/
def coherentTransferRate (ρ : State (Prod (Prod a b) r)) : ℝ :=
  (1 / 2 : ℝ) * ρ.coherentTransferReferenceMutualInformation

end State

/-- The canonical equivalence adding a right unit tensor factor. -/
def fqswAppendRightUnitEquiv (α : Type u) : α ≃ Prod α PUnit.{u + 1} where
  toFun x := (x, PUnit.unit)
  invFun x := x.1
  left_inv := by intro x; rfl
  right_inv := by intro x; cases x; rfl

/-- Reindexing along the right-unit equivalence is the same state as tensoring
with the unit-system state. -/
theorem state_reindex_fqswAppendRightUnitEquiv_eq_prod_unit
    {α : Type u} [Fintype α] [DecidableEq α] (ρ : State α) :
    ρ.reindex (fqswAppendRightUnitEquiv α) =
      ρ.prod (State.unit : State PUnit.{u + 1}) := by
  apply State.ext
  ext i j
  simp [fqswAppendRightUnitEquiv, State.reindex, State.prod, State.unit,
    Matrix.kronecker, Matrix.kroneckerMap_apply]

/-- Append a fixed right-hand state by first adjoining the unit system and then
preparing the target state on that factor. -/
def fqswAppendStateRight
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (τ : State β) : Channel α (Prod α β) :=
  ((Channel.idChannel α).prod (Channel.prepare (fun _ : PUnit.{u + 1} => τ))).comp
    (Channel.reindex (fqswAppendRightUnitEquiv α))

/-- The append-state channel sends `ρ` to the product state `ρ ⊗ τ`. -/
theorem fqswAppendStateRight_applyState
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (τ : State β) (ρ : State α) :
    (fqswAppendStateRight (α := α) τ).applyState ρ = ρ.prod τ := by
  unfold fqswAppendStateRight
  rw [Channel.applyState_comp, Channel.reindex_applyState]
  rw [state_reindex_fqswAppendRightUnitEquiv_eq_prod_unit]
  rw [Channel.applyState_prod]
  congr
  · apply State.ext
    change (Channel.idChannel α).map ρ.matrix = ρ.matrix
    simp [Channel.idChannel, MatrixMap.ofKraus]
  · apply State.ext
    ext i j
    simp [Channel.applyState, Channel.prepare_map, State.unit]

/-- Appending a fixed right-hand state is a channel, hence it cannot increase
normalized trace distance. -/
theorem fqswProdRight_normalizedTraceDistance_le
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ σ : State α) (τ : State β) :
    (ρ.prod τ).normalizedTraceDistance (σ.prod τ) ≤
      ρ.normalizedTraceDistance σ := by
  let Φ : Channel α (Prod α β) := fqswAppendStateRight τ
  have hρ : Φ.applyState ρ = ρ.prod τ := by
    simpa [Φ] using fqswAppendStateRight_applyState (α := α) τ ρ
  have hσ : Φ.applyState σ = σ.prod τ := by
    simpa [Φ] using fqswAppendStateRight_applyState (α := α) τ σ
  have h := Channel.normalizedTraceDistance_applyState_le Φ ρ σ
  simpa [hρ, hσ] using h

/-- Appending a fixed right-hand state cannot increase the source trace-norm
distance between density matrices. -/
theorem fqswProdRight_traceNormDistance_le
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ σ : State α) (τ : State β) :
    (ρ.prod τ).traceNormDistance (σ.prod τ) ≤ ρ.traceNormDistance σ := by
  have h := fqswProdRight_normalizedTraceDistance_le ρ σ τ
  unfold State.normalizedTraceDistance normalizedTraceDistance at h
  unfold State.traceNormDistance
  nlinarith

/-- The channel induced by an isometry on a finite system. -/
def fqswChannelOfReferenceIsometry
    {r₁ : Type u} {r₂ : Type v}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) : Channel r₁ r₂ where
  map := MatrixMap.ofReferenceIsometry V
  completelyPositive := MatrixMap.ofReferenceIsometry_isCompletelyPositive V
  tracePreserving := MatrixMap.ofReferenceIsometry_isTracePreserving V
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)

/-- Applying an isometry channel to the left half of a pure bipartite state
agrees with applying the isometry to the underlying pure vector. -/
theorem fqswChannelOfReferenceIsometry_prod_id_applyState_pure
    {r₁ : Type u} {r₂ : Type v} {s : Type w}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    [Fintype s] [DecidableEq s]
    (V : ReferenceIsometry r₁ r₂) (Ψ : PureVector (Prod r₁ s)) :
    ((fqswChannelOfReferenceIsometry V).prod (Channel.idChannel s)).applyState Ψ.state =
      (V.applyPureVector Ψ).state := by
  apply State.ext
  change
    MatrixMap.kron (MatrixMap.ofReferenceIsometry V) (Channel.idChannel s).map
        Ψ.state.matrix =
      rankOneMatrix (V.applyAmp Ψ.amp)
  rw [PureVector.state_matrix]
  rw [MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]
  exact (V.rankOne_applyAmp Ψ.amp).symm

/-- Regroup a left-associated tripartite source `(A × B) × R` so Alice's
system is the left factor. -/
def fqswSourceToAliceInputEquiv (a : Type u) (b : Type v) (r : Type w) :
    Prod (Prod a b) r ≃ Prod a (Prod b r) where
  toFun x := (x.1.1, (x.1.2, x.2))
  invFun x := ((x.1, x.2.1), x.2.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Regroup a left-associated tripartite source `(A × B) × R` as
`(A × R) × B`, exposing the subsystem complementary to Bob. -/
def fqswSourceToARBEquiv (a : Type u) (b : Type v) (r : Type w) :
    Prod (Prod a b) r ≃ Prod (Prod a r) b where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Regroup Alice's output so Bob's input register `A₁ × B` is the left
factor and the untouched reference `R × A₂` is the right factor. -/
def fqswAliceOutputToBobInputEquiv
    (q : Type x) (e : Type y) (b : Type v) (r : Type w) :
    Prod (Prod q e) (Prod b r) ≃ Prod (Prod q b) (Prod r e) where
  toFun x := ((x.1.1, x.2.1), (x.2.2, x.1.2))
  invFun x := ((x.1.1, x.2.2), (x.1.2, x.2.1))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Regroup Alice's one-shot output so the discarded `A₁B` side is separated
from the decoupled `A₂R` side used in ADHW fqsw.tex lines 580-841. -/
def fqswAliceOutputToA2REquiv
    (q : Type x) (e : Type y) (b : Type v) (r : Type w) :
    Prod (Prod q e) (Prod b r) ≃ Prod (Prod q b) (Prod e r) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Apply the source split `A ≃ A₁ × A₂` on the `A` side of the one-shot
`AR` marginal.  This explicit equivalence avoids universe inference issues
from using `Equiv.prodCongr` directly in the FQSW bridge lemmas. -/
def fqswARSplitEquiv (split : a ≃ Prod q e) :
    Prod a r ≃ Prod (Prod q e) r where
  toFun x := (split x.1, x.2)
  invFun x := (split.symm x.1, x.2)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- Regroup a split `AR` marginal from `(A₁ × A₂) × R` into
`A₁ × (A₂ × R)`, the order used by the ADHW decoupling marginal
`σ^{A₂R}` after tracing out `A₁`. -/
def fqswQERToA2REquiv (q : Type x) (e : Type y) (r : Type w) :
    Prod (Prod q e) r ≃ Prod q (Prod e r) where
  toFun x := (x.1.1, (x.1.2, x.2))
  invFun x := ((x.1, x.2.1), x.2.2)
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Regroup Bob's output into the final FQSW comparison order:
transferred source against the distilled ebit. -/
def fqswBobOutputToFinalEquiv
    (a : Type u) (b : Type v) (et : Type z) (r : Type w) (e : Type y) :
    Prod (Prod (Prod a b) et) (Prod r e) ≃
      Prod (Prod (Prod a b) r) (Prod e et) where
  toFun x := ((x.1.1, x.2.1), (x.2.2, x.1.2))
  invFun x := ((x.1.1, x.2.2), (x.1.2, x.2.1))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r]
    [Fintype e] [DecidableEq e] [Nonempty e] [Fintype et] [DecidableEq et] in
@[simp]
theorem fqswBobOutputToFinalEquiv_apply
    (x : Prod (Prod (Prod a b) et) (Prod r e)) :
    fqswBobOutputToFinalEquiv a b et r e x =
      ((x.1.1, x.2.1), (x.2.2, x.1.2)) :=
  rfl

/-- Regroup the tensor power of a left-associated tripartite system as
`(A^n × B^n) × R^n`. -/
def fqswTensorPowerTripartiteEquiv (a : Type u) (b : Type v) (r : Type w)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r] (n : ℕ) :
    TensorPower (Prod (Prod a b) r) n ≃
      Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n) :=
  (tensorPowerProdEquiv (Prod a b) r n).trans
    (Equiv.prodCongr (tensorPowerProdEquiv a b n) (Equiv.refl (TensorPower r n)))

/-- One-shot FQSW protocol data.  The final states are intentionally not
fields: they are computed from the source and the two source operations below. -/
structure FQSWOneShotProtocol (ψ : PureVector (Prod (Prod a b) r))
    (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  aliceIsometry : ReferenceIsometry a (Prod q e)
  bobIsometry : ReferenceIsometry (Prod q b) (Prod (Prod a b) et)
  ebitPairing : e ≃ et

namespace FQSWOneShotProtocol

variable {ψ : PureVector (Prod (Prod a b) r)}
variable (C : FQSWOneShotProtocol ψ q e et)

/-- Computed FQSW output for an explicit source state.  This is the mixed-state
counterpart of `outputPureVector`: Alice applies her isometry, the registers
are regrouped so `A₁B` is Bob's input, Bob applies his isometry, and the final
state is compared in the source order `ABR × A₂B~`. -/
def outputStateOfState (C : FQSWOneShotProtocol ψ q e et)
    (ρ : State (Prod (Prod a b) r)) :
    State (Prod (Prod (Prod a b) r) (Prod e et)) :=
  let ρA : State (Prod a (Prod b r)) :=
    ρ.reindex (fqswSourceToAliceInputEquiv a b r)
  let ρU : State (Prod (Prod q e) (Prod b r)) :=
    ((fqswChannelOfReferenceIsometry C.aliceIsometry).prod
      (Channel.idChannel (Prod b r))).applyState ρA
  let ρBobIn : State (Prod (Prod q b) (Prod r e)) :=
    ρU.reindex (fqswAliceOutputToBobInputEquiv q e b r)
  let ρV : State (Prod (Prod (Prod a b) et) (Prod r e)) :=
    ((fqswChannelOfReferenceIsometry C.bobIsometry).prod
      (Channel.idChannel (Prod r e))).applyState ρBobIn
  ρV.reindex (fqswBobOutputToFinalEquiv a b et r e)

/-- The pure output state obtained by applying Alice's isometry, transmitting
`A₁`, and applying Bob's isometry. -/
def outputPureVector :
    PureVector (Prod (Prod (Prod a b) r) (Prod e et)) :=
  let ψA : PureVector (Prod a (Prod b r)) :=
    ψ.reindex (fqswSourceToAliceInputEquiv a b r)
  let ψU : PureVector (Prod (Prod q e) (Prod b r)) :=
    C.aliceIsometry.applyPureVector ψA
  let ψBobIn : PureVector (Prod (Prod q b) (Prod r e)) :=
    ψU.reindex (fqswAliceOutputToBobInputEquiv q e b r)
  let ψV : PureVector (Prod (Prod (Prod a b) et) (Prod r e)) :=
    C.bobIsometry.applyPureVector ψBobIn
  ψV.reindex (fqswBobOutputToFinalEquiv a b et r e)

/-- Computed FQSW output state. -/
def outputState : State (Prod (Prod (Prod a b) r) (Prod e et)) :=
  C.outputPureVector.state

/-- The mixed-state operational path on the source pure state agrees with the
pure-vector definition of the computed one-shot output. -/
theorem outputStateOfState_source_eq_outputState :
    C.outputStateOfState ψ.state = C.outputState := by
  unfold outputStateOfState outputState outputPureVector
  dsimp only
  rw [← PureVector.reindex_state]
  rw [fqswChannelOfReferenceIsometry_prod_id_applyState_pure]
  rw [← PureVector.reindex_state]
  rw [fqswChannelOfReferenceIsometry_prod_id_applyState_pure]
  rw [PureVector.reindex_state]

/-- Source-shaped target: transferred `ABR` source tensor a canonical ebit. -/
def targetState : State (Prod (Prod (Prod a b) r) (Prod e et)) :=
  ψ.state.prod (State.maximallyEntangled C.ebitPairing)

/-- Normalized trace-distance protocol error, matching existing Lean protocol
conventions. -/
def normalizedError : ℝ :=
  C.outputState.normalizedTraceDistance C.targetState

/-- Source trace-norm error `||ρ_out - ρ_target||₁`. -/
def traceNormError : ℝ :=
  traceNormDistance C.outputState.matrix C.targetState.matrix

/-- Source trace-norm error against `C.targetState` for an explicit source
state argument. -/
def traceNormErrorOfState (C : FQSWOneShotProtocol ψ q e et)
    (ρ : State (Prod (Prod a b) r)) : ℝ :=
  traceNormDistance (C.outputStateOfState ρ).matrix C.targetState.matrix

/-- Number of qubits communicated in the one-shot protocol. -/
def communicationCost (_C : FQSWOneShotProtocol ψ q e et) : ℝ :=
  log2 (Fintype.card q : ℝ)

/-- Number of ebits distilled in the one-shot protocol. -/
def ebitYield (_C : FQSWOneShotProtocol ψ q e et) : ℝ :=
  log2 (Fintype.card e : ℝ)

theorem normalizedError_nonneg : 0 ≤ C.normalizedError :=
  State.normalizedTraceDistance_nonneg _ _

theorem traceNormError_nonneg : 0 ≤ C.traceNormError :=
  traceNormDistance_nonneg _ _

theorem normalizedError_eq_half_traceNormError :
    C.normalizedError = (1 / 2 : ℝ) * C.traceNormError := by
  rfl

end FQSWOneShotProtocol

/-- A physical block FQSW protocol on the original IID registers.

Unlike the one-shot layer, the Alice operation is a channel rather than an
isometry: Schumacher compression maps the full `A^n` register into its smaller
typical register and therefore needs a trace-preserving completion away from
the typical support.  Output and error states are computed from these two
operations and the source; they are not protocol fields. -/
structure FQSWBlockProtocol (ψ : PureVector (Prod (Prod a b) r)) (n : ℕ)
    (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  aliceOperation : Channel (TensorPower a n) (Prod q e)
  bobOperation :
    Channel (Prod q (TensorPower b n))
      (Prod (Prod (TensorPower a n) (TensorPower b n)) et)
  ebitPairing : e ≃ et

namespace FQSWBlockProtocol

variable {ψ : PureVector (Prod (Prod a b) r)} {n : ℕ}
variable (C : FQSWBlockProtocol ψ n q e et)

/-- Run a block protocol on an explicit state of the grouped block source. -/
def outputStateOfBlockState (C : FQSWBlockProtocol ψ n q e et)
    (ρ : State
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))) :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e et)) :=
  let ρA : State
      (Prod (TensorPower a n) (Prod (TensorPower b n) (TensorPower r n))) :=
    ρ.reindex
      (fqswSourceToAliceInputEquiv
        (TensorPower a n) (TensorPower b n) (TensorPower r n))
  let ρU : State
      (Prod (Prod q e) (Prod (TensorPower b n) (TensorPower r n))) :=
    (C.aliceOperation.prod
      (Channel.idChannel (Prod (TensorPower b n) (TensorPower r n)))).applyState ρA
  let ρBobIn : State
      (Prod (Prod q (TensorPower b n)) (Prod (TensorPower r n) e)) :=
    ρU.reindex
      (fqswAliceOutputToBobInputEquiv q e (TensorPower b n) (TensorPower r n))
  let ρV : State
      (Prod
        (Prod (Prod (TensorPower a n) (TensorPower b n)) et)
        (Prod (TensorPower r n) e)) :=
    (C.bobOperation.prod
      (Channel.idChannel (Prod (TensorPower r n) e))).applyState ρBobIn
  ρV.reindex
    (fqswBobOutputToFinalEquiv
      (TensorPower a n) (TensorPower b n) et (TensorPower r n) e)

/-- Run a block protocol on the tensor power of an explicit single-copy
source state. -/
def outputStateOfState (C : FQSWBlockProtocol ψ n q e et)
    (ρ : State (Prod (Prod a b) r)) :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e et)) :=
  C.outputStateOfBlockState
    ((ρ.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n))

/-- Computed output on the IID source `ψ^{⊗n}`. -/
def outputState :
    State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e et)) :=
  C.outputStateOfState ψ.state

def targetState :
  State (Prod
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))
      (Prod e et)) :=
  ((ψ.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n)).state.prod
    (State.maximallyEntangled C.ebitPairing)

def normalizedError : ℝ :=
  C.outputState.normalizedTraceDistance C.targetState

def traceNormError : ℝ :=
  traceNormDistance C.outputState.matrix C.targetState.matrix

def traceNormErrorOfState (C : FQSWBlockProtocol ψ n q e et)
    (ρ : State (Prod (Prod a b) r)) : ℝ :=
  traceNormDistance (C.outputStateOfState ρ).matrix C.targetState.matrix

def communicationRate (_C : FQSWBlockProtocol ψ n q e et) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card q : ℝ) / (n : ℝ)

def ebitYieldRate (_C : FQSWBlockProtocol ψ n q e et) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card e : ℝ) / (n : ℝ)

theorem normalizedError_nonneg : 0 ≤ C.normalizedError :=
  State.normalizedTraceDistance_nonneg _ _

theorem traceNormError_nonneg : 0 ≤ C.traceNormError :=
  traceNormDistance_nonneg _ _

theorem normalizedError_eq_half_traceNormError :
    C.normalizedError = (1 / 2 : ℝ) * C.traceNormError := by
  rfl

private theorem fqswChannel_reindex_map
    {alpha : Type*} {beta : Type*}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (E : alpha ≃ beta) (X : CMatrix alpha) :
    (Channel.reindex E).map X = X.submatrix E.symm E.symm := by
  ext i j
  simp [Channel.reindex, MatrixMap.ofReferenceIsometry_apply,
    ReferenceIsometry.ofEquiv, Matrix.mul_apply]
  rw [Finset.sum_eq_single (E.symm j)]
  · rw [Finset.sum_eq_single (E.symm i)]
    · simp
    · intro x _ hx
      have hne : i ≠ E x := by
        intro hi
        apply hx
        simp [hi]
      simp [hne]
    · simp
  · intro x _ hx
    have hne : j ≠ E x := by
      intro hj
      apply hx
      simp [hj]
    simp [hne]
  · simp

private theorem fqswChannel_reindex_map_single
    {alpha : Type*} {beta : Type*}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (E : alpha ≃ beta) (i j : alpha) :
    (Channel.reindex E).map (Matrix.single i j (1 : Complex)) =
      Matrix.single (E i) (E j) (1 : Complex) := by
  rw [fqswChannel_reindex_map]
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.single_apply]
  have hx : i = E.symm x ↔ E i = x := by
    constructor
    · intro h
      rw [h, E.apply_symm_apply]
    · intro h
      apply E.injective
      rw [E.apply_symm_apply, h]
  have hy : j = E.symm y ↔ E j = y := by
    constructor
    · intro h
      rw [h, E.apply_symm_apply]
    · intro h
      apply E.injective
      rw [E.apply_symm_apply, h]
  simp only [hx, hy]

/-- Regrouping a tripartite source commutes with independent local channels. -/
public theorem fqswSourceToAliceInput_naturality
    {alpha : Type ua0} {beta : Type ub0} {gamma : Type ur0}
    {alpha' : Type ua1} {beta' : Type ub1} {gamma' : Type ur1}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma]
    [Fintype alpha'] [DecidableEq alpha']
    [Fintype beta'] [DecidableEq beta']
    [Fintype gamma'] [DecidableEq gamma']
    (PhiA : Channel alpha alpha') (PhiB : Channel beta beta')
    (PhiR : Channel gamma gamma') :
    (PhiA.prod (PhiB.prod PhiR)).comp
        (Channel.reindex (fqswSourceToAliceInputEquiv alpha beta gamma)) =
      (Channel.reindex (fqswSourceToAliceInputEquiv alpha' beta' gamma')).comp
        ((PhiA.prod PhiB).prod PhiR) := by
  rw [Channel.mk.injEq]
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    ((PhiA.prod (PhiB.prod PhiR)).comp
      (Channel.reindex (fqswSourceToAliceInputEquiv alpha beta gamma))).map X]
  rw [MatrixMap.map_eq_sum_single
    ((Channel.reindex (fqswSourceToAliceInputEquiv alpha' beta' gamma')).comp
      ((PhiA.prod PhiB).prod PhiR)).map X]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change MatrixMap.kron PhiA.map (MatrixMap.kron PhiB.map PhiR.map)
      ((Channel.reindex (fqswSourceToAliceInputEquiv alpha beta gamma)).map
        (Matrix.single i j (1 : Complex))) =
    (Channel.reindex (fqswSourceToAliceInputEquiv alpha' beta' gamma')).map
      (MatrixMap.kron (MatrixMap.kron PhiA.map PhiB.map) PhiR.map
        (Matrix.single i j (1 : Complex)))
  rw [fqswChannel_reindex_map_single]
  rw [show Matrix.single
      (fqswSourceToAliceInputEquiv alpha beta gamma i)
      (fqswSourceToAliceInputEquiv alpha beta gamma j) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : Complex))
          (Matrix.single (i.1.2, i.2) (j.1.2, j.2) (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single (i.1.2, i.2) (j.1.2, j.2) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1.2 j.1.2 (1 : Complex))
          (Matrix.single i.2 j.2 (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single i j (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1 j.1 (1 : Complex))
          (Matrix.single i.2 j.2 (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single i.1 j.1 (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : Complex))
          (Matrix.single i.1.2 j.1.2 (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker, fqswChannel_reindex_map]
  ext k l
  simp [fqswSourceToAliceInputEquiv, Matrix.kronecker, mul_assoc]

/-- Regrouping Alice's output into Bob's input commutes with independent local
channels on the four registers. -/
public theorem fqswAliceOutputToBobInput_naturality
    {q0 : Type uq0} {e0 : Type ue0} {b0 : Type ubq0} {r0 : Type urq0}
    {q1 : Type uq1} {e1 : Type ue1} {b1 : Type ubq1} {r1 : Type urq1}
    [Fintype q0] [DecidableEq q0]
    [Fintype e0] [DecidableEq e0]
    [Fintype b0] [DecidableEq b0]
    [Fintype r0] [DecidableEq r0]
    [Fintype q1] [DecidableEq q1]
    [Fintype e1] [DecidableEq e1]
    [Fintype b1] [DecidableEq b1]
    [Fintype r1] [DecidableEq r1]
    (PhiQ : Channel q0 q1) (PhiE : Channel e0 e1)
    (PhiB : Channel b0 b1) (PhiR : Channel r0 r1) :
    ((PhiQ.prod PhiB).prod (PhiR.prod PhiE)).comp
        (Channel.reindex (fqswAliceOutputToBobInputEquiv q0 e0 b0 r0)) =
      (Channel.reindex (fqswAliceOutputToBobInputEquiv q1 e1 b1 r1)).comp
        ((PhiQ.prod PhiE).prod (PhiB.prod PhiR)) := by
  rw [Channel.mk.injEq]
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    (((PhiQ.prod PhiB).prod (PhiR.prod PhiE)).comp
      (Channel.reindex (fqswAliceOutputToBobInputEquiv q0 e0 b0 r0))).map X]
  rw [MatrixMap.map_eq_sum_single
    ((Channel.reindex (fqswAliceOutputToBobInputEquiv q1 e1 b1 r1)).comp
      ((PhiQ.prod PhiE).prod (PhiB.prod PhiR))).map X]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  change MatrixMap.kron (MatrixMap.kron PhiQ.map PhiB.map)
      (MatrixMap.kron PhiR.map PhiE.map)
      ((Channel.reindex (fqswAliceOutputToBobInputEquiv q0 e0 b0 r0)).map
        (Matrix.single i j (1 : Complex))) =
    (Channel.reindex (fqswAliceOutputToBobInputEquiv q1 e1 b1 r1)).map
      (MatrixMap.kron (MatrixMap.kron PhiQ.map PhiE.map)
        (MatrixMap.kron PhiB.map PhiR.map)
        (Matrix.single i j (1 : Complex)))
  rw [fqswChannel_reindex_map_single]
  rw [show Matrix.single
      (fqswAliceOutputToBobInputEquiv q0 e0 b0 r0 i)
      (fqswAliceOutputToBobInputEquiv q0 e0 b0 r0 j) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (i.1.1, i.2.1) (j.1.1, j.2.1) (1 : Complex))
          (Matrix.single (i.2.2, i.1.2) (j.2.2, j.1.2) (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single (i.1.1, i.2.1) (j.1.1, j.2.1) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : Complex))
          (Matrix.single i.2.1 j.2.1 (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single (i.2.2, i.1.2) (j.2.2, j.1.2) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.2.2 j.2.2 (1 : Complex))
          (Matrix.single i.1.2 j.1.2 (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single i j (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1 j.1 (1 : Complex))
          (Matrix.single i.2 j.2 (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single i.1 j.1 (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : Complex))
          (Matrix.single i.1.2 j.1.2 (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single i.2 j.2 (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.2.1 j.2.1 (1 : Complex))
          (Matrix.single i.2.2 j.2.2 (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_apply_kronecker, fqswChannel_reindex_map]
  ext k l
  simp [fqswAliceOutputToBobInputEquiv, Matrix.kronecker, mul_assoc, mul_comm,
    mul_left_comm]

/-- Regard an isometric one-shot protocol on the grouped IID source as a
physical block protocol. -/
def ofOneShot
    (C : FQSWOneShotProtocol
      ((ψ.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n))
      q e et) :
    FQSWBlockProtocol ψ n q e et where
  aliceOperation := fqswChannelOfReferenceIsometry C.aliceIsometry
  bobOperation := fqswChannelOfReferenceIsometry C.bobIsometry
  ebitPairing := C.ebitPairing

theorem outputStateOfBlockState_ofOneShot
    (C : FQSWOneShotProtocol
      ((ψ.tensorPower n).reindex (fqswTensorPowerTripartiteEquiv a b r n))
      q e et)
    (ρ : State
      (Prod (Prod (TensorPower a n) (TensorPower b n)) (TensorPower r n))) :
    (ofOneShot C).outputStateOfBlockState ρ = C.outputStateOfState ρ := by
  rfl

end FQSWBlockProtocol

namespace PureVector

variable (ψ : PureVector (Prod (Prod a b) r))

/-- FQSW communication rate `(1/2) I(A;R)_ψ`. -/
def fqswCommunicationRate : ℝ :=
  (1 / 2 : ℝ) * mutualInformation ψ.state.coherentTransferReferenceState

/-- FQSW ebit-yield rate `(1/2) I(A;B)_ψ`. -/
def fqswEbitYieldRate : ℝ :=
  (1 / 2 : ℝ) * mutualInformation ψ.state.marginalA

/-- Operational FQSW achievability with computed protocols: for every positive
rate slack and error tolerance, all sufficiently large block lengths have an
`FQSWBlockProtocol` whose communication rate is at most `1/2 I(A;R) + δ`,
whose ebit yield is at least `1/2 I(A;B) - δ`, and whose computed normalized
trace-distance error is at most `ε`. -/
def IsAchievableFQSW : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ εerr : ℝ, 0 < εerr →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ (q : Type x), ∃ (_ : Fintype q), ∃ (_ : DecidableEq q),
          ∃ (e : Type y), ∃ (_ : Fintype e), ∃ (_ : DecidableEq e), ∃ (_ : Nonempty e),
            ∃ (et : Type z), ∃ (_ : Fintype et), ∃ (_ : DecidableEq et),
              ∃ C : FQSWBlockProtocol ψ n q e et,
                C.communicationRate ≤ ψ.fqswCommunicationRate + δ ∧
                  ψ.fqswEbitYieldRate - δ ≤ C.ebitYieldRate ∧
                    C.normalizedError ≤ εerr

end PureVector

end

end QIT
