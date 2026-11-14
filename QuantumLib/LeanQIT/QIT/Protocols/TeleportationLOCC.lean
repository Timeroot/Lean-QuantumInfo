/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.LOCC.Construction
public import QIT.Protocols.LOCC.Measurement
public import QIT.Protocols.Teleportation

/-!
# Qudit teleportation as a finite one-way LOCC protocol

This module packages the generalized Bell measurement and Bob's
outcome-conditioned Weyl correction as a physical `OneWayLOCC`. The identity
channel theorem remains a derived calculation after adjoining the shared
maximally entangled resource.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

/-- Regroup an input qudit and the two halves of its teleportation resource
as Alice's Bell-measurement input and Bob's local input. -/
def teleportationLOCCInputEquiv (d : Type u) :
    Prod d (Prod d d) ≃ Prod (Prod d d) d where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun x := (x.1.1, (x.1.2, x.2))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Remove the one-dimensional output left after Alice discards her measured
registers. -/
def teleportationLOCCOutputEquiv (d : Type u) : Prod PUnit.{u + 1} d ≃ d where
  toFun x := x.2
  invFun x := (PUnit.unit, x)
  left_inv := by intro x; cases x.1; rfl
  right_inv := by intro x; rfl

/-- Alice's generalized Bell measurement as a finite instrument whose quantum
output is the unit system. -/
def teleportationBellInstrument
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    FiniteInstrument (Prod d d) PUnit.{u + 1} (TeleportationOutcome d) :=
  (generalizedBellPOVM d).discardInstrument

@[simp]
theorem teleportationBellInstrument_branch
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (result : TeleportationOutcome d) :
    (teleportationBellInstrument d).branch result =
      MatrixMap.traceEffectToUnit ((generalizedBellPOVM d).effects result) :=
  rfl

/-- The physical one-way LOCC operation for qudit teleportation before the
shared maximally entangled resource is fixed. -/
def teleportationLOCC
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    OneWayLOCC (Prod d d) PUnit.{u + 1} d d (TeleportationOutcome d) :=
  OneWayLOCC.ofFiniteInstrument
    (teleportationBellInstrument d) (teleportationCorrection d)

@[simp]
theorem teleportationLOCC_toChannel_map
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    (teleportationLOCC d).toChannel.map =
      ∑ result : TeleportationOutcome d,
        MatrixMap.kron
          (MatrixMap.traceEffectToUnit
            ((generalizedBellPOVM d).effects result))
          (teleportationCorrection d result).map :=
  rfl

def teleportationAppendRightUnitEquiv (d : Type u) :
    d ≃ Prod d PUnit.{u + 1} where
  toFun x := (x, PUnit.unit)
  invFun x := x.1
  left_inv := by intro x; rfl
  right_inv := by intro x; cases x.2; rfl

/-- Adjoin the actual shared rank-`d` maximally entangled resource to the
teleported input. -/
def teleportationAppendResourceChannel
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    Channel d (Prod d (Prod d d)) :=
  ((Channel.idChannel d).prod
      (Channel.prepare (fun _ : PUnit.{u + 1} =>
        (teleportationEntanglementResource d).state))).comp
    (Channel.reindex (teleportationAppendRightUnitEquiv d))

theorem teleportationAppendResourceChannel_map
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (X : CMatrix d) :
    (teleportationAppendResourceChannel d).map X =
      Matrix.kronecker X
        (teleportationEntanglementResource d).state.matrix := by
  have hunit :
      (Channel.reindex (teleportationAppendRightUnitEquiv d)).map X =
        Matrix.kronecker X (1 : CMatrix PUnit.{u + 1}) := by
    ext i j
    cases i.2
    cases j.2
    simp only [Channel.reindex, MatrixMap.ofReferenceIsometry_apply,
      ReferenceIsometry.ofEquiv, teleportationAppendRightUnitEquiv,
      Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
    rw [Finset.sum_eq_single j.1]
    · rw [Finset.sum_eq_single i.1]
      · simp
      · intro x _ hx
        have hne : i ≠ (x, PUnit.unit) := by
          intro hi
          exact hx (congrArg Prod.fst hi).symm
        simp [hne]
      · simp
    · intro x _ hx
      have hne : j ≠ (x, PUnit.unit) := by
        intro hj
        exact hx (congrArg Prod.fst hj).symm
      simp [hne]
    · simp
  change
    MatrixMap.kron (Channel.idChannel d).map
      (Channel.prepare (fun _ : PUnit.{u + 1} =>
        (teleportationEntanglementResource d).state)).map
      ((Channel.reindex (teleportationAppendRightUnitEquiv d)).map X) = _
  rw [hunit, MatrixMap.kron_apply_kronecker]
  have hid : (Channel.idChannel d).map X = X := by
    ext i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  have hprepare :
      (Channel.prepare (fun _ : PUnit.{u + 1} =>
        (teleportationEntanglementResource d).state)).map
          (1 : CMatrix PUnit.{u + 1}) =
        (teleportationEntanglementResource d).state.matrix := by
    rw [Channel.prepare_map]
    simp
  rw [hid, hprepare]

/-- The end-to-end channel computed by the physical Bell instrument, the
shared entangled resource, and Bob's conditional correction. -/
def teleportationLOCCResourceChannel
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] : Channel d d :=
  (Channel.reindex (teleportationLOCCOutputEquiv d)).comp <|
    (teleportationLOCC d).toChannel.comp <|
      (Channel.reindex (teleportationLOCCInputEquiv d)).comp <|
        teleportationAppendResourceChannel d

private theorem teleportationReindex_map
    {a : Type u} {b : Type u}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) (X : CMatrix a) :
    (Channel.reindex e).map X = X.submatrix e.symm e.symm := by
  ext i j
  simp [Channel.reindex, MatrixMap.ofReferenceIsometry_apply,
    ReferenceIsometry.ofEquiv, Matrix.mul_apply]
  rw [Finset.sum_eq_single (e.symm j)]
  · rw [Finset.sum_eq_single (e.symm i)]
    · simp
    · intro x _ hx
      have hne : i ≠ e x := by
        intro hi
        apply hx
        simp [hi]
      simp [hne]
    · simp
  · intro x _ hx
    have hne : j ≠ e x := by
      intro hj
      apply hx
      simp [hj]
    simp [hne]
  · simp

private theorem teleportationBellEffect_single
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (result : TeleportationOutcome d) (i j : Prod d d) :
    MatrixMap.traceEffectToUnit
        ((generalizedBellPOVM d).effects result)
        (Matrix.single i j (1 : Complex))
          (PUnit.unit : PUnit.{u + 1}) (PUnit.unit : PUnit.{u + 1}) =
      (generalizedBellPureVector d result).amp j *
        star ((generalizedBellPureVector d result).amp i) := by
  rw [MatrixMap.traceEffectToUnit_apply_of_posSemidef
    ((generalizedBellPOVM d).pos result)]
  simp [generalizedBellPOVM, rankOneMatrix_apply, Matrix.trace_single_mul]

private theorem teleportationBellRankOneEffect_single
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (result : TeleportationOutcome d) (i j : Prod d d) :
    MatrixMap.traceEffectToUnit
        (rankOneMatrix (generalizedBellPureVector d result).amp)
        (Matrix.single i j (1 : Complex))
          (PUnit.unit : PUnit.{u + 1}) (PUnit.unit : PUnit.{u + 1}) =
      (generalizedBellPureVector d result).amp j *
        star ((generalizedBellPureVector d result).amp i) := by
  simpa [generalizedBellPOVM] using
    teleportationBellEffect_single d result i j

private theorem teleportationCorrection_map_single
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (result : TeleportationOutcome d) (i j bob bob' : d) :
    (teleportationCorrection d result).map
        (Matrix.single i j (1 : Complex)) bob bob' =
      teleportationWeyl d result bob i *
        star (teleportationWeyl d result bob' j) := by
  simp only [teleportationCorrection, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Finset.univ_unique, Finset.sum_singleton,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx
      have hne : i ≠ x := Ne.symm hx
      simp [Matrix.single, hne]
    · simp
  · intro x _ hx
    have hne : j ≠ x := Ne.symm hx
    simp [Matrix.single, hne]
  · simp

private theorem sum_six_teleportation_permute {α : Type*} [Fintype α]
    (f : α → α → α → α → α → α → ℂ) :
    (∑ resourceBob, ∑ resourceBob', ∑ input, ∑ alice, ∑ input', ∑ alice',
        f resourceBob resourceBob' input alice input' alice') =
      ∑ input', ∑ input, ∑ resourceBob, ∑ alice, ∑ resourceBob', ∑ alice',
        f resourceBob resourceBob' input alice input' alice' := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  conv_rhs =>
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
  let e : (((((α × α) × α) × α) × α) × α) ≃
      (((((α × α) × α) × α) × α) × α) := {
    toFun := fun t =>
      (((((t.1.2, t.1.1.1.2), t.1.1.1.1.1), t.1.1.2),
        t.1.1.1.1.2), t.2)
    invFun := fun s =>
      (((((s.1.1.1.2, s.1.2), s.1.1.1.1.2), s.1.1.2),
        s.1.1.1.1.1), s.2)
    left_inv := by intro t; rcases t with ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, g⟩; rfl
    right_inv := by intro s; rcases s with ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, g⟩; rfl }
  simpa [e] using
    (Finset.sum_equiv e (s := Finset.univ) (t := Finset.univ)
      (fun _ => by simp)
      (fun t _ => by
        rcases t with ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, g⟩
        rfl))

/-- The physical one-way-LOCC realization with its shared resource computes
the corrected teleportation channel. -/
theorem teleportationLOCCResourceChannel_eq_teleportationChannel
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    teleportationLOCCResourceChannel d = teleportationChannel d := by
  rw [Channel.mk.injEq]
  apply LinearMap.ext
  intro X
  change
    (Channel.reindex (teleportationLOCCOutputEquiv d)).map
      ((teleportationLOCC d).toChannel.map
        ((Channel.reindex (teleportationLOCCInputEquiv d)).map
          ((teleportationAppendResourceChannel d).map X))) =
      (teleportationChannel d).map X
  rw [teleportationAppendResourceChannel_map,
    teleportationLOCC_toChannel_map, LinearMap.sum_apply,
    teleportationReindex_map, teleportationReindex_map]
  ext bob bob'
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]
  simp only [MatrixMap.kron]
  simp only [generalizedBellPOVM]
  simp only [teleportationLOCCInputEquiv, teleportationLOCCOutputEquiv,
    teleportationChannel, MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun result _ => ?_
  simp_rw [teleportationBellRankOneEffect_single d result,
    teleportationCorrection_map_single d result]
  simp only [correctedTeleportationKraus, bellContractionKraus,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [star_sum, star_mul, star_star]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [sum_six_teleportation_permute]
  simp only [TeleportationEntanglementResource.state, PureVector.state_matrix,
    rankOneMatrix_apply, mul_assoc, mul_left_comm, mul_comm]

/-- The explicit finite one-way-LOCC protocol, after adjoining its shared
maximally entangled resource, implements the identity channel. -/
theorem teleportationLOCCResourceChannel_eq_idChannel
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    teleportationLOCCResourceChannel d = Channel.idChannel d :=
  (teleportationLOCCResourceChannel_eq_teleportationChannel d).trans
    (teleportationChannel_eq_idChannel d)

/-- The resource-augmented physical LOCC realization preserves entanglement
with every inaccessible reference system. -/
theorem teleportationLOCCResourceChannel_preserves_reference
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (r : Type v) [Fintype r] [DecidableEq r]
    (rho : State (Prod r d)) :
    ((Channel.idChannel r).prod (teleportationLOCCResourceChannel d)).applyState rho = rho := by
  rw [teleportationLOCCResourceChannel_eq_teleportationChannel]
  exact teleportation_preserves_reference d r rho

end

end QIT
