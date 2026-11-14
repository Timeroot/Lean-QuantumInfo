/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Asymptotic.Typicality
public import QIT.Channels.Diamond
public import QIT.Core.Channel
public import QIT.States.Purification.Canonical
public import QIT.States.TraceNorm.Distance

/-!
# Schumacher compression code interface

This module records the finite-dimensional compression-code interface for
Schumacher quantum data compression.  The operational fidelity criterion is
the *purification joint trace distance* `jointError`, matching the success
criterion of the Wilde converse route
[Wilde2011Qst, qit-notes.tex:31610-31690].  The direct achievability,
converse, and limit-equality theorems live in sibling modules
`SchumacherDirect`, `SchumacherConverse`, and `SchumacherLimit`.

The earlier A-only marginal fidelity is intentionally not used as the
operational notion: a dephasing channel in the `ρ^{⊗ n}` eigenbasis attains
zero A-marginal error at rate `0 < S(ρ)`, so the A-only criterion does not
support any converse.  The joint (purification) criterion is the one under
which the optimal compression rate equals the von Neumann entropy.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Register rate for an `n`-block compression register `W`.

For the degenerate `n = 0` block the rate is set to zero; all asymptotic
coding statements consume this only for sufficiently large positive block
lengths. -/
def schumacherRegisterRate (W : Type u) [Fintype W] (n : ℕ) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card W : ℝ) / (n : ℝ)

/-- A finite-dimensional Schumacher compression code for `n` copies of `ρ`.

The compressed register is `W`; the encoder maps the tensor-power source into
`W`, and the decoder maps `W` back to the original tensor-power system. -/
structure SchumacherCompressionCode (ρ : State a) (n : ℕ)
    (W : Type u) [Fintype W] [DecidableEq W] where
  encoder : Channel (TensorPower a n) W
  decoder : Channel W (TensorPower a n)

namespace SchumacherCompressionCode

variable {ρ : State a} {n : ℕ} {W : Type u} [Fintype W] [DecidableEq W]

/-- The pure tensor-power purification used in the Schumacher joint-error
criterion, with reference and source tensor powers regrouped as `R^n × A^n`. -/
def tensorPowerCanonicalPurification (ρ : State a) (n : ℕ) :
    PureVector (Prod (TensorPower a n) (TensorPower a n)) :=
  (ρ.canonicalPurification.tensorPower n).reindex (tensorPowerProdEquiv a a n)

/-- The tensor-power canonical purification has the state used by
`SchumacherCompressionCode.jointError`. -/
theorem tensorPowerCanonicalPurification_state (ρ : State a) (n : ℕ) :
    (tensorPowerCanonicalPurification ρ n).state =
      (State.canonicalPurification ρ).state.tensorPowerBipartite n := by
  rw [tensorPowerCanonicalPurification, PureVector.reindex_state,
    PureVector.tensorPower_state]
  rfl

/-- The tensor-power canonical purification purifies `ρ^{⊗ n}`. -/
theorem tensorPowerCanonicalPurification_purifies (ρ : State a) (n : ℕ) :
    (tensorPowerCanonicalPurification ρ n).Purifies (ρ.tensorPower n) := by
  rw [PureVector.purifies_iff, tensorPowerCanonicalPurification_state]
  have htarget :
      (State.canonicalPurification ρ).state.marginalB = ρ := by
    apply State.ext
    simpa [State.marginalB] using State.canonicalPurification_purifies ρ
  have h :=
    State.tensorPowerBipartite_marginalB (State.canonicalPurification ρ).state n
  rw [htarget] at h
  exact congrArg State.matrix h

private def referenceIsometryChannel
    {r₁ : Type u} {r₂ : Type v}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    (V : ReferenceIsometry r₁ r₂) : Channel r₁ r₂ where
  map := MatrixMap.ofReferenceIsometry V
  completelyPositive := MatrixMap.ofReferenceIsometry_isCompletelyPositive V
  tracePreserving := MatrixMap.ofReferenceIsometry_isTracePreserving V
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)

private theorem referenceIsometryChannel_prod_id_applyState
    {r₁ : Type u} {r₂ : Type v} {α : Type u}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    [Fintype α] [DecidableEq α]
    (V : ReferenceIsometry r₁ r₂) (σ : State (Prod r₁ α)) :
    (((referenceIsometryChannel V).prod (Channel.idChannel α)).applyState σ).matrix =
      V.applyMatrix σ.matrix := by
  change MatrixMap.kron (MatrixMap.ofReferenceIsometry V) (Channel.idChannel α).map
      σ.matrix = V.applyMatrix σ.matrix
  exact MatrixMap.kron_ofReferenceIsometry_idChannel_apply_eq_applyMatrixLeft V σ.matrix

private theorem referenceIsometryChannel_prod_id_applyPureVector_state
    {r₁ : Type u} {r₂ : Type v} {α : Type u}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    [Fintype α] [DecidableEq α]
    (V : ReferenceIsometry r₁ r₂) (Ψ : PureVector (Prod r₁ α)) :
    ((referenceIsometryChannel V).prod (Channel.idChannel α)).applyState Ψ.state =
      (V.applyPureVector Ψ).state := by
  apply State.ext
  rw [referenceIsometryChannel_prod_id_applyState]
  rw [PureVector.state_matrix, PureVector.state_matrix]
  exact (V.rankOne_applyAmp Ψ.amp).symm

private theorem kron_idChannel_apply_applyMatrix
    {r₁ : Type u} {r₂ : Type v} {α : Type u}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    [Fintype α] [DecidableEq α]
    (Φ : MatrixMap α α) (V : ReferenceIsometry r₁ r₂)
    (X : CMatrix (Prod r₁ α)) :
    MatrixMap.kron (Channel.idChannel r₂).map Φ (V.applyMatrix X) =
      V.applyMatrix (MatrixMap.kron (Channel.idChannel r₁).map Φ X) := by
  ext ra ra'
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (fun i i' => V.applyMatrix X (ra.1, i) (ra'.1, i')) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix ra.1 x * star (V.matrix ra'.1 y)) •
            (fun i i' => X (x, i) (y, i')) := by
    ext i i'
    simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
      Matrix.mul_apply, Finset.sum_mul, mul_assoc, mul_comm]
  rw [hslice]
  have hmap :
      Φ (∑ y : r₁, ∑ x : r₁,
          (V.matrix ra.1 x * star (V.matrix ra'.1 y)) •
            (fun i i' => X (x, i) (y, i'))) =
        ∑ y : r₁, ∑ x : r₁,
          (V.matrix ra.1 x * star (V.matrix ra'.1 y)) •
            Φ (fun i i' => X (x, i) (y, i')) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact LinearMap.map_smul Φ (V.matrix ra.1 x * star (V.matrix ra'.1 y))
      (fun i i' => X (x, i) (y, i'))
  have hmapEntry := congrFun (congrFun hmap ra.2) ra'.2
  calc
    Φ (∑ y : r₁, ∑ x : r₁,
        (V.matrix ra.1 x * star (V.matrix ra'.1 y)) •
          (fun i i' => X (x, i) (y, i'))) ra.2 ra'.2
        = (∑ y : r₁, ∑ x : r₁,
            (V.matrix ra.1 x * star (V.matrix ra'.1 y)) •
              Φ (fun i i' => X (x, i) (y, i'))) ra.2 ra'.2 := hmapEntry
    _ = V.applyMatrix (MatrixMap.kron (Channel.idChannel r₁).map Φ X) ra ra' := by
      simp [ReferenceIsometry.applyMatrix, ReferenceIsometry.targetBlock,
        Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        MatrixMap.kron_idChannel_left_apply_slice, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]

private theorem referenceIsometryChannel_prod_id_comm_id_prod_applyState
    {r₁ : Type u} {r₂ : Type v} {α : Type u}
    [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]
    [Fintype α] [DecidableEq α]
    (V : ReferenceIsometry r₁ r₂) (N : Channel α α) (σ : State (Prod r₁ α)) :
    ((Channel.idChannel r₂).prod N).applyState
        (((referenceIsometryChannel V).prod (Channel.idChannel α)).applyState σ) =
      ((referenceIsometryChannel V).prod (Channel.idChannel α)).applyState
        (((Channel.idChannel r₁).prod N).applyState σ) := by
  apply State.ext
  rw [referenceIsometryChannel_prod_id_applyState]
  change MatrixMap.kron (Channel.idChannel r₂).map N.map
      ((((referenceIsometryChannel V).prod (Channel.idChannel α)).applyState σ).matrix) =
    V.applyMatrix (MatrixMap.kron (Channel.idChannel r₁).map N.map σ.matrix)
  rw [referenceIsometryChannel_prod_id_applyState]
  exact kron_idChannel_apply_applyMatrix N.map V σ.matrix

/-- Decoded system-side output state of a Schumacher compression code. -/
def outputState (C : SchumacherCompressionCode ρ n W) : State (TensorPower a n) :=
  C.decoder.applyState (C.encoder.applyState (ρ.tensorPower n))

/-- Joint (purification) trace-distance error of a Schumacher code.

This is the operational fidelity criterion for quantum data compression.
Purify the source `ρ` canonically to `φ_{RA}` (system on `marginalB`,
reference `R ≅ A` on `marginalA`), take the `n`-fold bipartite tensor power
`φ_{RA}^{⊗ n}` on `R^{n} A^{n}`, apply the compression map `D ∘ E` to the
system side and the identity channel to the reference, and measure the
normalized trace distance of the resulting joint state `ω_{R^{n}Â^{n}}` from
`φ_{RA}^{⊗ n}`. The tensor-power purification (rather than a single canonical
purification of `ρ^{⊗ n}`) is used so that the quantum mutual information
`I(A^{n};R^{n})` decomposes additively, as required by the Wilde converse
[Wilde2011Qst, qit-notes.tex:31610-31690]. -/
def jointError (C : SchumacherCompressionCode ρ n W) : ℝ :=
  let φ : State (Prod (TensorPower a n) (TensorPower a n)) :=
    (State.canonicalPurification ρ).state.tensorPowerBipartite n
  let N : Channel (TensorPower a n) (TensorPower a n) :=
    C.decoder.comp C.encoder
  let ω : State (Prod (TensorPower a n) (TensorPower a n)) :=
    ((Channel.idChannel (TensorPower a n)).prod N).applyState φ
  ω.normalizedTraceDistance φ

/-- Transport Schumacher's canonical joint-error bound through a supplied
reference isometry identifying another purification with the tensor-power
canonical purification.

This witness form avoids adding a false dimension/cardinality assumption:
callers provide the concrete reference-side isometry when their purification is
known to be a reference-isometric image of the canonical tensor-power
purification. -/
theorem normalizedTraceDistance_apply_purification_le_jointError_of_referenceIsometry
    (C : SchumacherCompressionCode ρ n W)
    {r : Type v} [Fintype r] [DecidableEq r]
    (Ω : PureVector (Prod r (TensorPower a n)))
    (V : ReferenceIsometry (TensorPower a n) r)
    (hΩ :
      Ω = V.applyPureVector (tensorPowerCanonicalPurification ρ n)) :
    let N : Channel (TensorPower a n) (TensorPower a n) := C.decoder.comp C.encoder
    (((Channel.idChannel r).prod N).applyState Ω.state).normalizedTraceDistance Ω.state ≤
      C.jointError := by
  classical
  let Ψ : PureVector (Prod (TensorPower a n) (TensorPower a n)) :=
    tensorPowerCanonicalPurification ρ n
  let N : Channel (TensorPower a n) (TensorPower a n) := C.decoder.comp C.encoder
  let Γ : Channel (TensorPower a n) r := referenceIsometryChannel V
  have hΩstate : Ω.state = (Γ.prod (Channel.idChannel (TensorPower a n))).applyState Ψ.state := by
    rw [hΩ]
    exact (referenceIsometryChannel_prod_id_applyPureVector_state V Ψ).symm
  have hΩout :
      ((Channel.idChannel r).prod N).applyState Ω.state =
        (Γ.prod (Channel.idChannel (TensorPower a n))).applyState
          (((Channel.idChannel (TensorPower a n)).prod N).applyState Ψ.state) := by
    rw [hΩstate]
    simpa [Γ, N] using
      (referenceIsometryChannel_prod_id_comm_id_prod_applyState
        (α := TensorPower a n) V N Ψ.state)
  have hcontract :=
    Channel.normalizedTraceDistance_applyState_le
      (Γ.prod (Channel.idChannel (TensorPower a n)))
      (((Channel.idChannel (TensorPower a n)).prod N).applyState Ψ.state)
      Ψ.state
  have hcanon_state :
      Ψ.state = (State.canonicalPurification ρ).state.tensorPowerBipartite n := by
    simpa [Ψ] using tensorPowerCanonicalPurification_state ρ n
  have hcanon :
      ((((Channel.idChannel (TensorPower a n)).prod N).applyState Ψ.state).normalizedTraceDistance
          Ψ.state) = C.jointError := by
    rw [hcanon_state]
    rfl
  change (((Channel.idChannel r).prod N).applyState Ω.state).normalizedTraceDistance Ω.state ≤
    C.jointError
  calc
    (((Channel.idChannel r).prod N).applyState Ω.state).normalizedTraceDistance Ω.state =
        ((Γ.prod (Channel.idChannel (TensorPower a n))).applyState
            (((Channel.idChannel (TensorPower a n)).prod N).applyState Ψ.state)).normalizedTraceDistance
          ((Γ.prod (Channel.idChannel (TensorPower a n))).applyState Ψ.state) := by
          rw [hΩout, hΩstate]
    _ ≤ (((Channel.idChannel (TensorPower a n)).prod N).applyState Ψ.state).normalizedTraceDistance
          Ψ.state := hcontract
    _ = C.jointError := hcanon

/-- Register rate of the compressed system. -/
def rate (_C : SchumacherCompressionCode ρ n W) : ℝ :=
  schumacherRegisterRate W n

end SchumacherCompressionCode

/-- Source-shaped witness for one block of the direct Schumacher coding proof.

The witness packages an explicit compression code together with the two
estimates used by the direct theorem: register rate bounded by `S(ρ)+δ` and
joint (purification) trace-distance error bounded by `ε`. -/
structure TypicalCompressionWitness (ρ : State a) (n : ℕ) (δ ε : ℝ)
    (W : Type u) [Fintype W] [DecidableEq W] where
  code : SchumacherCompressionCode ρ n W
  rate_le : code.rate ≤ ρ.schumacherRate + δ
  jointError_le : code.jointError ≤ ε

namespace State

/-- Direct achievability of a Schumacher compression rate (joint fidelity).

For every rate slack `δ > 0` and joint-error tolerance `ε > 0`, all
sufficiently large block lengths have a finite compression register and a code
of rate at most `R + δ` and joint error at most `ε`. -/
def IsAchievableSchumacherRate (ρ : State a) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
        ∃ C : SchumacherCompressionCode ρ n W, C.rate ≤ R + δ ∧ C.jointError ≤ ε

/-- A family of joint-fidelity typical-compression witnesses proves the direct
achievability of the Schumacher rate `S(ρ)`.

This is the reusable Lean interface from a witness family to achievability; it
is an internal bridge, not the public direct-achievability node (which
discharges the witness existence unconditionally in `SchumacherDirect`). -/
theorem schumacher_direct_achievable_of_typicalCompressionWitness
    (ρ : State a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
            Nonempty (TypicalCompressionWitness ρ n δ ε W)) :
    ρ.IsAchievableSchumacherRate ρ.schumacherRate := by
  intro δ hδ ε hε
  obtain ⟨N, hN⟩ := h δ hδ ε hε
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨W, hWfin, hWdec, ⟨witness⟩⟩ := hN n hn
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  exact ⟨W, inferInstance, inferInstance, witness.code, witness.rate_le,
    witness.jointError_le⟩

end State

end

end QIT
