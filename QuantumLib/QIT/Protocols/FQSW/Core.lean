/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Information.Entropy.Entropy
public import QuantumLib.QIT.States.Purification.ReferenceIsometry
public import QuantumLib.QIT.Channels.Diamond
public import QuantumLib.QIT.States.MaximallyEntangled
public import QuantumLib.QIT.States.MaximallyMixed

/-!
# Fully quantum Slepian--Wolf: protocol data, errors, and rates

An FQSW protocol starts from a pure tripartite source `ψ_ABR`, with `A` at Alice, `B` at Bob and
`R` an untouched reference.  Alice splits `A` into a message register `A₁` and a local register
`A₂`, sends `A₁` to Bob, and Bob applies an isometry to `A₁B`; the protocol succeeds when the
result is the source state, with Alice's share now held by Bob, tensored with a maximally entangled
pair between `A₂` and Bob's fresh register.  `FQSWOneShotProtocol` records only that data -- the
two isometries and the pairing of the ebit registers -- and computes `outputState` and
`targetState` from it, so `normalizedError`, `traceNormError`, `communicationCost` and `ebitYield`
are functions of the protocol alone.

`FQSWBlockProtocol` is the `n`-copy counterpart.  There Alice's operation is a channel rather than
an isometry, because Schumacher compression of `A^n` into its typical register needs a
trace-preserving completion off that subspace, and costs are replaced by rates.  `ofOneShot` reads
a one-shot protocol on `ψ^{⊗n}` as a block protocol.

The two rates in play are `fqswCommunicationRate = I(A;R)_ψ / 2` and
`fqswEbitYieldRate = I(A;B)_ψ / 2`, both computed from `coherentTransferReferenceState`, the `AR`
marginal of the source.  `Ket.IsAchievableFQSW` is the operational statement they enter: for every
rate slack and error tolerance, all sufficiently long blocks carry a protocol meeting those rates
up to the slack with error below the tolerance.  It is proved in `IIDDirect.lean`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

noncomputable section
universe u v w x y z p u1 v1 w1
universe ua0 ub0 ur0 ua1 ub1 ur1
universe uq0 ue0 ubq0 urq0 uq1 ue1 ubq1 urq1
variable {a : Type u} {b : Type v} {r : Type w}
variable {q : Type x} {e : Type y} {et : Type z}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable [Fintype q] [DecidableEq q]
variable [Fintype e] [DecidableEq e] [Nonempty e]
variable [Fintype et] [DecidableEq et]

open QIT

namespace MState

/-- Marginal state on `A × R` used by coherent state transfer/FQSW. -/
def coherentTransferReferenceState
    (ρ : MState ((a × b) × r)) : MState (a × r) := .ofMatrix
  (matrix := Matrix.of fun ar ar' =>
    Finset.univ.sum fun j : b => ρ.m ((ar.1, j), ar.2) ((ar'.1, j), ar'.2))
  (pos := by
    let block : b → CMatrix (a × r) := fun j =>
      ρ.m.submatrix
        (fun ar : a × r => ((ar.1, j), ar.2))
        (fun ar : a × r => ((ar.1, j), ar.2))
    have hsum : (∑ j : b, block j).PosSemidef := by
      classical
      refine Finset.induction_on (s := Finset.univ) ?_ ?_
      · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix (a × r)).PosSemidef)
      · intro j s hjs hs
        simpa [Finset.sum_insert hjs, block] using
          (ρ.psd.submatrix (fun ar : a × r => ((ar.1, j), ar.2))).add hs
    convert hsum using 1
    ext ar ar'
    simp [block, Matrix.of_apply, Matrix.sum_apply])
  (trace_eq_one := by
    rw [← ρ.tr']
    rw [Matrix.trace]
    change
      (∑ ar : a × r, ∑ j : b,
        ρ.m ((ar.1, j), ar.2) ((ar.1, j), ar.2)) =
      ∑ x : (a × b) × r, ρ.m x x
    calc
      (∑ ar : a × r, ∑ j : b,
          ρ.m ((ar.1, j), ar.2) ((ar.1, j), ar.2)) =
          ∑ j : b, ∑ ar : a × r,
            ρ.m ((ar.1, j), ar.2) ((ar.1, j), ar.2) := by
        rw [Finset.sum_comm]
      _ = ∑ j : b, ∑ i : a, ∑ k : r,
            ρ.m ((i, j), k) ((i, j), k) := by
        simp [Fintype.sum_prod_type]
      _ = ∑ i : a, ∑ j : b, ∑ k : r,
            ρ.m ((i, j), k) ((i, j), k) := by
        rw [Finset.sum_comm]
      _ = ∑ x : (a × b) × r, ρ.m x x := by
        simp [Fintype.sum_prod_type])

/-- Reference mutual information `I(A;R)` for coherent state transfer/FQSW. -/
def coherentTransferReferenceMutualInformation
    (ρ : MState ((a × b) × r)) : ℝ :=
  mutualInformation ρ.coherentTransferReferenceState

/-- Coherent state-transfer quantum communication rate `(1/2) I(A;R)`. -/
def coherentTransferRate (ρ : MState ((a × b) × r)) : ℝ :=
  (1 / 2 : ℝ) * ρ.coherentTransferReferenceMutualInformation

end MState

namespace QIT

/-- Reindexing along the right-unit equivalence is the same state as tensoring
with the unit-system state. -/
theorem state_reindex_prodPUnit_symm_eq_prod_unit
    {α : Type u} [Fintype α] [DecidableEq α] (ρ : MState α) :
    ρ.reindex (Equiv.prodPUnit α).symm =
      ρ.prod (MState.unit : MState PUnit.{u + 1}) := by
  apply MState.ext
  ext i j
  simp [MState.unit, Matrix.kroneckerMap_apply]

/-- Append a fixed right-hand state by first adjoining the unit system and then
preparing the target state on that factor. -/
def fqswAppendStateRight
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (τ : MState β) : CPTPMap α (α × β) :=
  ((CPTPOp.id (dIn := α)).prod (CPTPOp.prepare (fun _ : PUnit.{u + 1} => τ))) ∘ₘ
    (CPTPOp.reindex (Equiv.prodPUnit α).symm)

/-- The append-state channel sends `ρ` to the product state `ρ ⊗ τ`. -/
theorem fqswAppendStateRight_applyState
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (τ : MState β) (ρ : MState α) :
    (fqswAppendStateRight (α := α) τ) ρ = ρ.prod τ := by
  unfold fqswAppendStateRight
  rw [CPTPOp.compose_eq, CPTPOp.reindex_applyState]
  rw [state_reindex_prodPUnit_symm_eq_prod_unit]
  rw [CPTPOp.prod_apply_prod]
  congr
  · apply MState.ext
    rw [CPTPOp.mat_coe_eq_apply_mat]
    simp [CPTPOp.id_map]
  · apply MState.ext
    ext i j
    simp [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prepare_map]

/-- Appending a fixed right-hand state is a channel, hence it cannot increase
normalized trace distance. -/
theorem fqswProdRight_normalizedTraceDistance_le
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ σ : MState α) (τ : MState β) :
    (ρ.prod τ).normalizedTraceDistance (σ.prod τ) ≤
      ρ.normalizedTraceDistance σ := by
  let Φ : CPTPMap α (α × β) := fqswAppendStateRight τ
  have hρ : Φ ρ = ρ.prod τ := by
    simpa [Φ] using fqswAppendStateRight_applyState (α := α) τ ρ
  have hσ : Φ σ = σ.prod τ := by
    simpa [Φ] using fqswAppendStateRight_applyState (α := α) τ σ
  have h := CPTPOp.normalizedTraceDistance_applyState_le Φ ρ σ
  simpa [hρ, hσ] using h

/-- Appending a fixed right-hand state cannot increase the source trace-norm
distance between density matrices. -/
theorem fqswProdRight_traceNormDistance_le
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ σ : MState α) (τ : MState β) :
    (ρ.prod τ).traceNormDistance (σ.prod τ) ≤ ρ.traceNormDistance σ := by
  have h := fqswProdRight_normalizedTraceDistance_le ρ σ τ
  unfold MState.normalizedTraceDistance normalizedTraceDistance at h
  unfold MState.traceNormDistance
  nlinarith

/-- The channel induced by an isometry on a finite system. -/
def fqswChannelOfReferenceIsometry
    {r₁ : Type u} {r₂ : Type v}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) : CPTPMap r₁ r₂ :=
  CPTPOp.ofMat
    (MatrixMap.ofReferenceIsometry V)
    (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)
    (MatrixMap.ofReferenceIsometry_isTracePreserving V)

/-- The isometry channel acts by the isometry's matrix map. -/
@[simp]
theorem fqswChannelOfReferenceIsometry_map
    {r₁ : Type u} {r₂ : Type v}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) :
    (fqswChannelOfReferenceIsometry V).map = MatrixMap.ofReferenceIsometry V :=
  CPTPOp.map_ofMat _ _ _

/-- Applying an isometry channel to the left half of a pure bipartite state
agrees with applying the isometry to the underlying ket. -/
theorem fqswChannelOfReferenceIsometry_prod_id_applyState_pure
    {r₁ : Type u} {r₂ : Type v} {s : Type w}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    [Fintype s] [DecidableEq s]
    (V : ReferenceIsometry r₁ r₂) (Ψ : Ket (r₁ × s)) :
    ((fqswChannelOfReferenceIsometry V).prod (CPTPOp.id (dIn := s))) Ψ.state =
      (V.applyKet Ψ).state := by
  apply MState.ext
  rw [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map,
    fqswChannelOfReferenceIsometry_map, Ket.state_matrix, Ket.state_matrix,
    MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft]
  exact (V.rankOne_applyAmp Ψ.vec).symm

/-- Regroup Alice's output so Bob's input register `A₁ × B` is the left
factor and the untouched reference `R × A₂` is the right factor. -/
def fqswAliceOutputToBobInputEquiv
    (q : Type x) (e : Type y) (b : Type v) (r : Type w) :
    ((q × e) × (b × r)) ≃ ((q × b) × (r × e)) where
  toFun x := ((x.1.1, x.2.1), (x.2.2, x.1.2))
  invFun x := ((x.1.1, x.2.2), (x.1.2, x.2.1))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

@[simp]
theorem fqswAliceOutputToBobInputEquiv_apply
    {q : Type x} {e : Type y} {b : Type v} {r : Type w}
    (z : (q × e) × (b × r)) :
    fqswAliceOutputToBobInputEquiv q e b r z = ((z.1.1, z.2.1), (z.2.2, z.1.2)) :=
  rfl

/-- Apply the source split `A ≃ A₁ × A₂` on the `A` side of the one-shot
`AR` marginal.  This explicit equivalence avoids universe inference issues
from using `Equiv.prodCongr` directly in the FQSW bridge lemmas. -/
def fqswARSplitEquiv (split : a ≃ (q × e)) :
    (a × r) ≃ ((q × e) × r) where
  toFun x := (split x.1, x.2)
  invFun x := (split.symm x.1, x.2)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- One-shot FQSW protocol data.  The final states are intentionally not
fields: they are computed from the source and the two source operations below. -/
structure FQSWOneShotProtocol (ψ : Ket ((a × b) × r))
    (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  /-- Alice's isometry, splitting her register into the part she sends and her ebit half. -/
  aliceIsometry : ReferenceIsometry a (q × e)
  /-- Bob's isometry, acting on what he receives together with his own register. -/
  bobIsometry : ReferenceIsometry (q × b) ((a × b) × et)
  /-- The identification of Alice's and Bob's ebit halves. -/
  ebitPairing : e ≃ et

namespace FQSWOneShotProtocol

variable {ψ : Ket ((a × b) × r)}
variable (C : FQSWOneShotProtocol ψ q e et)

/-- Computed FQSW output for an explicit source state.  This is the mixed-state
counterpart of `outputKet`: Alice applies her isometry, the registers
are regrouped so `A₁B` is Bob's input, Bob applies his isometry, and the final
state is compared in the source order `ABR × A₂B~`. -/
def outputStateOfState (C : FQSWOneShotProtocol ψ q e et)
    (ρ : MState ((a × b) × r)) :
    MState (((a × b) × r) × (e × et)) :=
  let ρA : MState (a × (b × r)) :=
    ρ.reindex (Equiv.prodAssoc a b r)
  let ρU : MState ((q × e) × (b × r)) :=
    ((fqswChannelOfReferenceIsometry C.aliceIsometry).prod
      (CPTPOp.id (dIn := b × r))) ρA
  let ρBobIn : MState ((q × b) × (r × e)) :=
    ρU.reindex (fqswAliceOutputToBobInputEquiv q e b r)
  let ρV : MState (((a × b) × et) × (r × e)) :=
    ((fqswChannelOfReferenceIsometry C.bobIsometry).prod
      (CPTPOp.id (dIn := r × e))) ρBobIn
  ρV.reindex (fqswAliceOutputToBobInputEquiv (a × b) et r e)

/-- The pure output state obtained by applying Alice's isometry, transmitting
`A₁`, and applying Bob's isometry. -/
def outputKet :
    Ket (((a × b) × r) × (e × et)) :=
  let ψA : Ket (a × (b × r)) :=
    ψ.reindex (Equiv.prodAssoc a b r)
  let ψU : Ket ((q × e) × (b × r)) :=
    C.aliceIsometry.applyKet ψA
  let ψBobIn : Ket ((q × b) × (r × e)) :=
    ψU.reindex (fqswAliceOutputToBobInputEquiv q e b r)
  let ψV : Ket (((a × b) × et) × (r × e)) :=
    C.bobIsometry.applyKet ψBobIn
  ψV.reindex (fqswAliceOutputToBobInputEquiv (a × b) et r e)

/-- Computed FQSW output state. -/
def outputState : MState (((a × b) × r) × (e × et)) :=
  C.outputKet.state

/-- The mixed-state operational path on the source pure state agrees with the
ket definition of the computed one-shot output. -/
theorem outputStateOfState_source_eq_outputState :
    C.outputStateOfState ψ.state = C.outputState := by
  unfold outputStateOfState outputState outputKet
  dsimp only
  rw [← Ket.reindex_state]
  rw [fqswChannelOfReferenceIsometry_prod_id_applyState_pure]
  rw [← Ket.reindex_state]
  rw [fqswChannelOfReferenceIsometry_prod_id_applyState_pure]
  rw [Ket.reindex_state]

/-- Source-shaped target: transferred `ABR` source tensor a canonical ebit. -/
def targetState : MState (((a × b) × r) × (e × et)) :=
  ψ.state.prod (MState.maximallyEntangled C.ebitPairing)

/-- Normalized trace-distance protocol error, matching existing Lean protocol
conventions. -/
def normalizedError : ℝ :=
  C.outputState.normalizedTraceDistance C.targetState

/-- Source trace-norm error `||ρ_out - ρ_target||₁`. -/
def traceNormError : ℝ :=
  traceNormDistance C.outputState.m C.targetState.m

/-- Source trace-norm error against `C.targetState` for an explicit source
state argument. -/
def traceNormErrorOfState (C : FQSWOneShotProtocol ψ q e et)
    (ρ : MState ((a × b) × r)) : ℝ :=
  traceNormDistance (C.outputStateOfState ρ).m C.targetState.m

/-- Number of qubits communicated in the one-shot protocol. -/
def communicationCost (_C : FQSWOneShotProtocol ψ q e et) : ℝ :=
  log2 (Fintype.card q : ℝ)

/-- Number of ebits distilled in the one-shot protocol. -/
def ebitYield (_C : FQSWOneShotProtocol ψ q e et) : ℝ :=
  log2 (Fintype.card e : ℝ)

theorem normalizedError_nonneg : 0 ≤ C.normalizedError :=
  MState.normalizedTraceDistance_nonneg _ _

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
structure FQSWBlockProtocol (ψ : Ket ((a × b) × r)) (n : ℕ)
    (q : Type x) (e : Type y) (et : Type z)
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    [Fintype et] [DecidableEq et] where
  /-- Alice's channel, compressing `A^n` into what she sends and her ebit half. -/
  aliceOperation : CPTPMap (TensorPower a n) (q × e)
  /-- Bob's channel, acting on what he receives together with his own registers. -/
  bobOperation :
    CPTPMap (q × TensorPower b n)
      ((TensorPower a n × TensorPower b n) × et)
  /-- The identification of Alice's and Bob's ebit halves. -/
  ebitPairing : e ≃ et

namespace FQSWBlockProtocol

variable {ψ : Ket ((a × b) × r)} {n : ℕ}
variable (C : FQSWBlockProtocol ψ n q e et)

/-- Run a block protocol on an explicit state of the grouped block source. -/
def outputStateOfBlockState (C : FQSWBlockProtocol ψ n q e et)
    (ρ : MState
      ((TensorPower a n × TensorPower b n) × TensorPower r n)) :
    MState (((TensorPower a n × TensorPower b n) × TensorPower r n) ×
      (e × et)) :=
  let ρA : MState
      (TensorPower a n × (TensorPower b n × TensorPower r n)) :=
    ρ.reindex
      (Equiv.prodAssoc
        (TensorPower a n) (TensorPower b n) (TensorPower r n))
  let ρU : MState
      ((q × e) × (TensorPower b n × TensorPower r n)) :=
    (C.aliceOperation.prod
      (CPTPOp.id (dIn := TensorPower b n × TensorPower r n))) ρA
  let ρBobIn : MState
      ((q × TensorPower b n) × (TensorPower r n × e)) :=
    ρU.reindex
      (fqswAliceOutputToBobInputEquiv q e (TensorPower b n) (TensorPower r n))
  let ρV : MState
      (((TensorPower a n × TensorPower b n) × et) ×
        (TensorPower r n × e)) :=
    (C.bobOperation.prod
      (CPTPOp.id (dIn := TensorPower r n × e))) ρBobIn
  ρV.reindex
    (fqswAliceOutputToBobInputEquiv
      (TensorPower a n × TensorPower b n) et (TensorPower r n) e)

/-- Run a block protocol on the tensor power of an explicit single-copy
source state. -/
def outputStateOfState (C : FQSWBlockProtocol ψ n q e et)
    (ρ : MState ((a × b) × r)) :
    MState (((TensorPower a n × TensorPower b n) × TensorPower r n) ×
      (e × et)) :=
  C.outputStateOfBlockState
    ((ρ.tensorPower n).reindex (tensorPowerProdProdEquiv a b r n))

/-- Computed output on the IID source `ψ^{⊗n}`. -/
def outputState :
    MState (((TensorPower a n × TensorPower b n) × TensorPower r n) ×
      (e × et)) :=
  C.outputStateOfState ψ.state

/-- The ideal output the protocol is compared against: the source `ψ^{⊗n}` regrouped so that the
`B` registers sit with Bob, tensored with a maximally entangled state on the ebit registers. -/
def targetState :
  MState (((TensorPower a n × TensorPower b n) × TensorPower r n) ×
      (e × et)) :=
  ((ψ.tensorPower n).reindex (tensorPowerProdProdEquiv a b r n)).state.prod
    (MState.maximallyEntangled C.ebitPairing)

/-- The protocol error, as the normalized trace distance between the output and the target. -/
def normalizedError : ℝ :=
  C.outputState.normalizedTraceDistance C.targetState

/-- The protocol error in the unnormalized trace norm, which is twice `normalizedError`. -/
def traceNormError : ℝ :=
  traceNormDistance C.outputState.m C.targetState.m

/-- The trace-norm error incurred when the protocol is run on an arbitrary input state `ρ` rather
than on the IID source. -/
def traceNormErrorOfState (C : FQSWBlockProtocol ψ n q e et)
    (ρ : MState ((a × b) × r)) : ℝ :=
  traceNormDistance (C.outputStateOfState ρ).m C.targetState.m

/-- Qubits of quantum communication per copy of the source, `log₂ |q| / n`, and `0` when `n = 0`. -/
def communicationRate (_C : FQSWBlockProtocol ψ n q e et) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card q : ℝ) / (n : ℝ)

/-- Ebits generated per copy of the source, `log₂ |e| / n`, and `0` when `n = 0`. -/
def ebitYieldRate (_C : FQSWBlockProtocol ψ n q e et) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card e : ℝ) / (n : ℝ)

theorem normalizedError_nonneg : 0 ≤ C.normalizedError :=
  MState.normalizedTraceDistance_nonneg _ _

theorem traceNormError_nonneg : 0 ≤ C.traceNormError :=
  traceNormDistance_nonneg _ _

theorem normalizedError_eq_half_traceNormError :
    C.normalizedError = (1 / 2 : ℝ) * C.traceNormError := by
  rfl

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
    (PhiA : CPTPMap alpha alpha') (PhiB : CPTPMap beta beta')
    (PhiR : CPTPMap gamma gamma') :
    (PhiA.prod (PhiB.prod PhiR)) ∘ₘ
        (CPTPOp.reindex (Equiv.prodAssoc alpha beta gamma)) =
      (CPTPOp.reindex (Equiv.prodAssoc alpha' beta' gamma')) ∘ₘ
        ((PhiA.prod PhiB).prod PhiR) := by
  refine CPTPOp.ext_map ?_
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    ((PhiA.prod (PhiB.prod PhiR)) ∘ₘ
      (CPTPOp.reindex (Equiv.prodAssoc alpha beta gamma))).map X]
  rw [MatrixMap.map_eq_sum_single
    ((CPTPOp.reindex (Equiv.prodAssoc alpha' beta' gamma')) ∘ₘ
      ((PhiA.prod PhiB).prod PhiR)).map X]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [CPTPOp.compose_map, CPTPOp.prod_map,
    LinearMap.comp_apply]
  rw [CPTPOp.reindex_map_single]
  rw [show Matrix.single
      (Equiv.prodAssoc alpha beta gamma i)
      (Equiv.prodAssoc alpha beta gamma j) (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.1.1 j.1.1 (1 : ℂ))
          (Matrix.single (i.1.2, i.2) (j.1.2, j.2) (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single (i.1.2, i.2) (j.1.2, j.2) (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.1.2 j.1.2 (1 : ℂ))
          (Matrix.single i.2 j.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single i j (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.1 j.1 (1 : ℂ))
          (Matrix.single i.2 j.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single i.1 j.1 (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.1.1 j.1.1 (1 : ℂ))
          (Matrix.single i.1.2 j.1.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state, CPTPOp.reindex_map]
  ext k l
  simp [Equiv.prodAssoc, mul_assoc]

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
    (PhiQ : CPTPMap q0 q1) (PhiE : CPTPMap e0 e1)
    (PhiB : CPTPMap b0 b1) (PhiR : CPTPMap r0 r1) :
    ((PhiQ.prod PhiB).prod (PhiR.prod PhiE)) ∘ₘ
        (CPTPOp.reindex (fqswAliceOutputToBobInputEquiv q0 e0 b0 r0)) =
      (CPTPOp.reindex (fqswAliceOutputToBobInputEquiv q1 e1 b1 r1)) ∘ₘ
        ((PhiQ.prod PhiE).prod (PhiB.prod PhiR)) := by
  refine CPTPOp.ext_map ?_
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    (((PhiQ.prod PhiB).prod (PhiR.prod PhiE)) ∘ₘ
      (CPTPOp.reindex (fqswAliceOutputToBobInputEquiv q0 e0 b0 r0))).map X]
  rw [MatrixMap.map_eq_sum_single
    ((CPTPOp.reindex (fqswAliceOutputToBobInputEquiv q1 e1 b1 r1)) ∘ₘ
      ((PhiQ.prod PhiE).prod (PhiB.prod PhiR))).map X]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [CPTPOp.compose_map, CPTPOp.prod_map,
    LinearMap.comp_apply]
  rw [CPTPOp.reindex_map_single]
  rw [show Matrix.single
      (fqswAliceOutputToBobInputEquiv q0 e0 b0 r0 i)
      (fqswAliceOutputToBobInputEquiv q0 e0 b0 r0 j) (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single (i.1.1, i.2.1) (j.1.1, j.2.1) (1 : ℂ))
          (Matrix.single (i.2.2, i.1.2) (j.2.2, j.1.2) (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single (i.1.1, i.2.1) (j.1.1, j.2.1) (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.1.1 j.1.1 (1 : ℂ))
          (Matrix.single i.2.1 j.2.1 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single (i.2.2, i.1.2) (j.2.2, j.1.2) (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.2.2 j.2.2 (1 : ℂ))
          (Matrix.single i.1.2 j.1.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single i j (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.1 j.1 (1 : ℂ))
          (Matrix.single i.2 j.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single i.1 j.1 (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.1.1 j.1.1 (1 : ℂ))
          (Matrix.single i.1.2 j.1.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single i.2 j.2 (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.2.1 j.2.1 (1 : ℂ))
          (Matrix.single i.2.2 j.2.2 (1 : ℂ)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  rw [MatrixMap.kron_map_of_kron_state, CPTPOp.reindex_map]
  ext k l
  simp [fqswAliceOutputToBobInputEquiv, mul_assoc, mul_comm, mul_left_comm]

/-- Regard an isometric one-shot protocol on the grouped IID source as a
physical block protocol. -/
def ofOneShot
    (C : FQSWOneShotProtocol
      ((ψ.tensorPower n).reindex (tensorPowerProdProdEquiv a b r n))
      q e et) :
    FQSWBlockProtocol ψ n q e et where
  aliceOperation := fqswChannelOfReferenceIsometry C.aliceIsometry
  bobOperation := fqswChannelOfReferenceIsometry C.bobIsometry
  ebitPairing := C.ebitPairing

theorem outputStateOfBlockState_ofOneShot
    (C : FQSWOneShotProtocol
      ((ψ.tensorPower n).reindex (tensorPowerProdProdEquiv a b r n))
      q e et)
    (ρ : MState
      ((TensorPower a n × TensorPower b n) × TensorPower r n)) :
    (ofOneShot C).outputStateOfBlockState ρ = C.outputStateOfState ρ := by
  simp only [outputStateOfBlockState, ofOneShot, FQSWOneShotProtocol.outputStateOfState]

end FQSWBlockProtocol

end QIT

namespace Ket

variable (ψ : Ket ((a × b) × r))

/-- FQSW communication rate `(1/2) I(A;R)_ψ`. -/
def fqswCommunicationRate : ℝ :=
  (1 / 2 : ℝ) * mutualInformation ψ.state.coherentTransferReferenceState

/-- FQSW ebit-yield rate `(1/2) I(A;B)_ψ`. -/
def fqswEbitYieldRate : ℝ :=
  (1 / 2 : ℝ) * mutualInformation ψ.state.traceRight

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

end Ket
