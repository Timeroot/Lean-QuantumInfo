/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.LOCC.Core

/-!
# Reference lifts for finite one-way LOCC operations

This module lifts a one-way LOCC operation by an untouched finite reference
register. The reference is grouped with Alice in the physical protocol, while
the channel law identifies the lift with the original realization tensored
with the identity channel after explicit register regrouping.
-/

@[expose] public section

noncomputable section
universe u v w x y z

open QIT

namespace QIT

namespace MatrixMap

private theorem sum_comp
    {A : Type u} {B : Type v} {C : Type w} {I : Type x}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype I]
    (Phi : I → MatrixMap B C) (Psi : MatrixMap A B) :
    (∑ i, Phi i).comp Psi = ∑ i, (Phi i).comp Psi :=
  LinearMap.ext fun X => by simp [LinearMap.sum_apply]

private theorem comp_sum
    {A : Type u} {B : Type v} {C : Type w} {I : Type x}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype I]
    (Phi : MatrixMap B C) (Psi : I → MatrixMap A B) :
    Phi.comp (∑ i, Psi i) = ∑ i, Phi.comp (Psi i) :=
  LinearMap.ext fun X => by simp [LinearMap.sum_apply]

end MatrixMap

end QIT
end

noncomputable section

namespace QIT

open QIT

private theorem regroup_kron_id_apply_single
    {A : Type u} {A' : Type v} {B : Type w} {B' : Type x} {R : Type y}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    [Fintype R] [DecidableEq R]
    (PhiA : MatrixMap A A') (PhiB : MatrixMap B B')
    (i j : (A × R) × B) :
    (CPTPOp.reindex (prodABCToACBEquiv A' B' R)).map
        (MatrixMap.kron (MatrixMap.kron PhiA PhiB) (CPTPOp.id (dIn := R)).map
          ((CPTPOp.reindex (prodABCToACBEquiv A B R).symm).map
            (Matrix.single i j (1 : ℂ)))) =
      MatrixMap.kron (MatrixMap.kron PhiA (CPTPOp.id (dIn := R)).map) PhiB
        (Matrix.single i j (1 : ℂ)) := by
  rw [CPTPOp.reindex_map_single]
  rw [show Matrix.single
      ((prodABCToACBEquiv A B R).symm i)
      ((prodABCToACBEquiv A B R).symm j) (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single (i.1.1, i.2) (j.1.1, j.2) (1 : ℂ))
          (Matrix.single i.1.2 j.1.2 (1 : ℂ)) by
      simpa [prodABCToACBEquiv] using
        (single_prod_eq_kronecker_single
          (i.1.1, i.2) (j.1.1, j.2) i.1.2 j.1.2)]
  rw [MatrixMap.kron_map_of_kron_state]
  rw [show Matrix.single (i.1.1, i.2) (j.1.1, j.2) (1 : ℂ) =
        Matrix.kroneckerMap (· * ·)
          (Matrix.single i.1.1 j.1.1 (1 : ℂ))
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
  simp [prodABCToACBEquiv, mul_assoc, mul_comm]

private theorem regroup_kron_id
    {A : Type u} {A' : Type v} {B : Type w} {B' : Type x} {R : Type y}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    [Fintype R] [DecidableEq R]
    (PhiA : MatrixMap A A') (PhiB : MatrixMap B B') :
    (CPTPOp.reindex (prodABCToACBEquiv A' B' R)).map.comp
        ((MatrixMap.kron (MatrixMap.kron PhiA PhiB) (CPTPOp.id (dIn := R)).map).comp
          (CPTPOp.reindex (prodABCToACBEquiv A B R).symm).map) =
      MatrixMap.kron (MatrixMap.kron PhiA (CPTPOp.id (dIn := R)).map) PhiB := by
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    ((CPTPOp.reindex (prodABCToACBEquiv A' B' R)).map.comp
      ((MatrixMap.kron (MatrixMap.kron PhiA PhiB) (CPTPOp.id (dIn := R)).map).comp
        (CPTPOp.reindex (prodABCToACBEquiv A B R).symm).map)) X]
  rw [MatrixMap.map_eq_sum_single
    (MatrixMap.kron (MatrixMap.kron PhiA (CPTPOp.id (dIn := R)).map) PhiB) X]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simpa [LinearMap.comp_apply] using regroup_kron_id_apply_single PhiA PhiB i j

private theorem regroup_sum_kron_id
    {A : Type u} {A' : Type v} {B : Type w} {B' : Type x}
    {R : Type y} {I : Type z}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    [Fintype R] [DecidableEq R] [Fintype I]
    (PhiA : I → MatrixMap A A') (PhiB : I → MatrixMap B B') :
    (CPTPOp.reindex (prodABCToACBEquiv A' B' R)).map.comp
        ((MatrixMap.kron (∑ i, MatrixMap.kron (PhiA i) (PhiB i))
          (CPTPOp.id (dIn := R)).map).comp
          (CPTPOp.reindex (prodABCToACBEquiv A B R).symm).map) =
      ∑ i, MatrixMap.kron (MatrixMap.kron (PhiA i) (CPTPOp.id (dIn := R)).map) (PhiB i) := by
  rw [MatrixMap.kron_sum_left, MatrixMap.sum_comp, MatrixMap.comp_sum]
  exact Finset.sum_congr rfl fun i _ => regroup_kron_id (PhiA i) (PhiB i)

namespace FiniteInstrument

variable {A : Type u} {A' : Type v} {X : Type w} {R : Type x}
variable [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
variable [Fintype X] [Fintype R] [DecidableEq R]

/-- Tensor every branch of a finite instrument with the identity on a right reference. -/
def prodIdRight (M : FiniteInstrument A A' X) :
    FiniteInstrument (A × R) (A' × R) X where
  branch result := MatrixMap.kron (M.branch result) (CPTPOp.id (dIn := R)).map
  branchTraceNonincreasingCP result :=
    MatrixMap.traceNonincreasingCP_kron_id (a := R)
      (M.branchTraceNonincreasingCP result)
  total := M.total.prod (CPTPOp.id (dIn := R))
  sum_branch_eq_total := by
    rw [CPTPOp.prod_map, ← M.sum_branch_eq_total,
      MatrixMap.kron_sum_left]

@[simp]
theorem prodIdRight_branch (M : FiniteInstrument A A' X) (result : X) :
    (M.prodIdRight (R := R)).branch result =
      MatrixMap.kron (M.branch result) (CPTPOp.id (dIn := R)).map := rfl

theorem prodIdRight_totalChannel (M : FiniteInstrument A A' X) :
    (M.prodIdRight (R := R)).totalChannel =
      M.totalChannel.prod (CPTPOp.id (dIn := R)) := rfl

end FiniteInstrument

namespace OneWayLOCC

variable {A : Type u} {A' : Type v} {B : Type w} {B' : Type x}
variable {X : Type y} {R : Type z}
variable [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
variable [Fintype X] [Fintype R] [DecidableEq R]

/-- Lift a finite one-way LOCC operation by an untouched reference grouped with Alice. -/
def prodIdRight (L : OneWayLOCC A A' B B' X) :
    OneWayLOCC (A × R) (A' × R) B B' X where
  aliceInstrument := L.aliceInstrument.prodIdRight
  bobChannel := L.bobChannel
  realization :=
    (CPTPOp.reindex (prodABCToACBEquiv A' B' R)) ∘ₘ
      ((L.toChannel.prod (CPTPOp.id (dIn := R))) ∘ₘ
        (CPTPOp.reindex (prodABCToACBEquiv A B R).symm))
  realization_map := by
    rw [CPTPOp.compose_map, CPTPOp.compose_map, CPTPOp.prod_map, L.toChannel_map]
    exact regroup_sum_kron_id
      (fun result => L.aliceInstrument.branch result)
      (fun result => (L.bobChannel result).map)

/-- The lifted realization is the original realization tensored with the reference identity,
with explicit input and output regrouping. -/
theorem prodIdRight_toChannel (L : OneWayLOCC A A' B B' X) :
    (L.prodIdRight (R := R)).toChannel =
      (CPTPOp.reindex (prodABCToACBEquiv A' B' R)) ∘ₘ
        ((L.toChannel.prod (CPTPOp.id (dIn := R))) ∘ₘ
          (CPTPOp.reindex (prodABCToACBEquiv A B R).symm)) := rfl

/-- On a pure input, regrouping the reference with Alice before the lifted LOCC gives the
regrouped output of the original LOCC tensored with the identity on the reference. -/
theorem prodIdRight_applyState_reindex_pure
    (L : OneWayLOCC A A' B B' X) (psi : Ket ((A × B) × R)) :
    (L.prodIdRight (R := R)).toChannel
        (psi.state.reindex (prodABCToACBEquiv A B R)) =
      MState.reindex ((L.toChannel.prod (CPTPOp.id (dIn := R))) psi.state)
        (prodABCToACBEquiv A' B' R) := by
  rw [prodIdRight_toChannel, CPTPOp.compose_eq, CPTPOp.compose_eq,
    CPTPOp.reindex_applyState, CPTPOp.reindex_applyState]
  rw [MState.reindex_reindex_symm]

end OneWayLOCC

end QIT
