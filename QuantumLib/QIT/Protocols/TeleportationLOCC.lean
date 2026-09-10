/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.LOCC.Construction
public import QuantumLib.QIT.Protocols.LOCC.Measurement
public import QuantumLib.QIT.Protocols.Teleportation

/-!
# Qudit teleportation as a finite one-way LOCC protocol

This module packages the generalized Bell measurement and Bob's
outcome-conditioned Weyl correction as a physical `OneWayLOCC`. The
identity-channel property is then derived from it, with the shared maximally
entangled resource adjoined.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

/-- Alice's generalized Bell measurement as a finite instrument whose quantum
output is the unit system. -/
def teleportationBellInstrument
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    FiniteInstrument (d × d) PUnit.{u + 1} (TeleportationOutcome d) :=
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
    OneWayLOCC (d × d) PUnit.{u + 1} d d (TeleportationOutcome d) :=
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
          (teleportationCorrection d result).map := by
  simp only [teleportationLOCC, OneWayLOCC.ofFiniteInstrument_toChannel_map,
    teleportationBellInstrument_branch]

/-- Adjoin the actual shared rank-`d` maximally entangled resource to the
teleported input. -/
def teleportationAppendResourceChannel
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    CPTPMap d (d × (d × d)) :=
  ((CPTPOp.id (dIn := d)).prod
      (CPTPOp.prepare (fun _ : PUnit.{u + 1} =>
        (teleportationEntanglementResource d).state))) ∘ₘ
    (CPTPOp.reindex (Equiv.prodPUnit d).symm)

theorem teleportationAppendResourceChannel_map
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (X : CMatrix d) :
    (teleportationAppendResourceChannel d).map X =
      Matrix.kronecker X
        (teleportationEntanglementResource d).state.m := by
  have hunit :
      (CPTPOp.reindex (Equiv.prodPUnit d).symm).map X =
        Matrix.kronecker X (1 : CMatrix PUnit.{u + 1}) := by
    ext i j
    cases i.2
    cases j.2
    simp only [CPTPOp.reindex, CPTPOp.map_ofMat,
      MatrixMap.ofReferenceIsometry_apply,
      ReferenceIsometry.ofEquiv, Equiv.prodPUnit_symm_apply,
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
  simp only [teleportationAppendResourceChannel, CPTPOp.compose_map,
    LinearMap.comp_apply, CPTPOp.prod_map]
  rw [hunit]
  simp only [Matrix.kronecker]
  rw [MatrixMap.kron_map_of_kron_state]
  have hid : (CPTPOp.id (dIn := d)).map X = X := by
    simp
  have hprepare :
      (CPTPOp.prepare (fun _ : PUnit.{u + 1} =>
        (teleportationEntanglementResource d).state)).map
          (1 : CMatrix PUnit.{u + 1}) =
        (teleportationEntanglementResource d).state.m := by
    rw [CPTPOp.prepare_map]
    simp
  rw [hid, hprepare]

/-- The end-to-end channel computed by the physical Bell instrument, the
shared entangled resource, and Bob's conditional correction. -/
def teleportationLOCCResourceChannel
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] : CPTPMap d d :=
  (CPTPOp.reindex (Equiv.punitProd d)) ∘ₘ
    ((teleportationLOCC d).toChannel ∘ₘ
      ((CPTPOp.reindex (Equiv.prodAssoc d d d).symm) ∘ₘ
        teleportationAppendResourceChannel d))

private theorem teleportationBellEffect_single
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (result : TeleportationOutcome d) (i j : d × d) :
    MatrixMap.traceEffectToUnit
        ((generalizedBellPOVM d).effects result)
        (Matrix.single i j (1 : ℂ))
          (PUnit.unit : PUnit.{u + 1}) (PUnit.unit : PUnit.{u + 1}) =
      (generalizedBellKet d result).vec j *
        star ((generalizedBellKet d result).vec i) := by
  rw [MatrixMap.traceEffectToUnit_apply_of_posSemidef
    ((generalizedBellPOVM d).pos result)]
  simp [generalizedBellPOVM, rankOneMatrix_apply, Matrix.trace_single_mul]

private theorem teleportationBellRankOneEffect_single
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (result : TeleportationOutcome d) (i j : d × d) :
    MatrixMap.traceEffectToUnit
        (rankOneMatrix (generalizedBellKet d result).vec)
        (Matrix.single i j (1 : ℂ))
          (PUnit.unit : PUnit.{u + 1}) (PUnit.unit : PUnit.{u + 1}) =
      (generalizedBellKet d result).vec j *
        star ((generalizedBellKet d result).vec i) := by
  simpa [generalizedBellPOVM] using
    teleportationBellEffect_single d result i j

private theorem teleportationCorrection_map_single
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (result : TeleportationOutcome d) (i j bob bob' : d) :
    (teleportationCorrection d result).map
        (Matrix.single i j (1 : ℂ)) bob bob' =
      teleportationWeyl d result bob i *
        star (teleportationWeyl d result bob' j) := by
  simp only [teleportationCorrection, CPTPOp.map_ofMat, MatrixMap.ofKraus,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.univ_unique, Finset.sum_singleton,
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
    (∑ input, ∑ resourceAlice, ∑ input', ∑ resourceAlice', ∑ bellBob, ∑ bellBob',
        f input resourceAlice input' resourceAlice' bellBob bellBob') =
      ∑ input', ∑ input, ∑ bellBob, ∑ resourceAlice, ∑ bellBob', ∑ resourceAlice',
        f input resourceAlice input' resourceAlice' bellBob bellBob' := by
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
      (((((t.1.1.1.2, t.1.1.1.1.1), t.1.2), t.1.1.1.1.2),
        t.2), t.1.1.2)
    invFun := fun s =>
      (((((s.1.1.1.1.2, s.1.1.2), s.1.1.1.1.1), s.2),
        s.1.1.1.2), s.1.2)
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
  refine CPTPOp.ext_map ?_
  apply LinearMap.ext
  intro X
  simp only [teleportationLOCCResourceChannel, CPTPOp.compose_map,
    LinearMap.comp_apply]
  rw [teleportationAppendResourceChannel_map,
    teleportationLOCC_toChannel_map, LinearMap.sum_apply,
    CPTPOp.reindex_map, CPTPOp.reindex_map]
  ext bob bob'
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]
  simp only [Equiv.punitProd_symm_apply]
  simp only [MatrixMap.kron_def]
  simp only [generalizedBellPOVM]
  simp only [Equiv.symm_symm,
    teleportationChannel, CPTPOp.map_ofMat, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply]
  simp [Matrix.kronecker]
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
  simp only [TeleportationEntanglementResource.state, Ket.state_matrix,
    rankOneMatrix_apply, mul_assoc, mul_left_comm, mul_comm]

/-- The explicit finite one-way-LOCC protocol, after adjoining its shared
maximally entangled resource, implements the identity channel. -/
theorem teleportationLOCCResourceChannel_eq_idChannel
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d] :
    teleportationLOCCResourceChannel d = CPTPOp.id (dIn := d) :=
  (teleportationLOCCResourceChannel_eq_teleportationChannel d).trans
    (teleportationChannel_eq_idChannel d)

/-- The resource-augmented physical LOCC realization preserves entanglement
with every inaccessible reference system. -/
theorem teleportationLOCCResourceChannel_preserves_reference
    (d : Type u) [Fintype d] [DecidableEq d] [Nonempty d]
    (r : Type v) [Fintype r] [DecidableEq r]
    (rho : MState (r × d)) :
    ((CPTPOp.id (dIn := r)).prod (teleportationLOCCResourceChannel d)) rho = rho := by
  rw [teleportationLOCCResourceChannel_eq_teleportationChannel]
  exact teleportation_preserves_reference d r rho

end

end QIT
