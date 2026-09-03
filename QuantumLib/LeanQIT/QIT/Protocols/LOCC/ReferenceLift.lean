/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.LOCC.Core

/-!
# Reference lifts for finite one-way LOCC operations

This module lifts a one-way LOCC operation by an untouched finite reference
register. The reference is grouped with Alice in the physical protocol, while
the channel law identifies the lift with the original realization tensored
with the identity channel after explicit register regrouping.
-/

@[expose] public section

namespace QIT

universe u v w x y z

noncomputable section

/-- Regroup an untouched right reference with the left subsystem. -/
def loccReferenceRegroupEquiv (A : Type u) (B : Type v) (R : Type w) :
    Prod (Prod A B) R ≃ Prod (Prod A R) B where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

namespace MatrixMap

private theorem kron_add_left
    {A : Type u} {A' : Type v} {C : Type w} {C' : Type x}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype C] [DecidableEq C] [Fintype C'] [DecidableEq C']
    (Phi Gamma : MatrixMap A A') (Psi : MatrixMap C C') :
    kron (Phi + Gamma) Psi = kron Phi Psi + kron Gamma Psi := by
  apply LinearMap.ext
  intro X
  ext i j
  simp [kron, mul_add, add_mul, Finset.sum_add_distrib]

private theorem kron_sum_left
    {A : Type u} {A' : Type v} {C : Type w} {C' : Type x} {I : Type y}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype C] [DecidableEq C] [Fintype C'] [DecidableEq C'] [Fintype I]
    (Phi : I → MatrixMap A A') (Psi : MatrixMap C C') :
    kron (∑ i, Phi i) Psi = ∑ i, kron (Phi i) Psi := by
  classical
  have hsum : ∀ s : Finset I,
      kron (∑ i ∈ s, Phi i) Psi = ∑ i ∈ s, kron (Phi i) Psi := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        apply LinearMap.ext
        intro X
        ext i j
        simp [kron]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        rw [kron_add_left, ih]
  simpa using hsum Finset.univ

end MatrixMap

namespace Channel

private theorem reindex_map
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (X : CMatrix A) :
    (reindex e).map X = X.submatrix e.symm e.symm := by
  ext i j
  simp [reindex, MatrixMap.ofReferenceIsometry_apply,
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

private theorem reindex_map_single
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (i j : A) :
    (reindex e).map (Matrix.single i j (1 : Complex)) =
      Matrix.single (e i) (e j) (1 : Complex) := by
  rw [reindex_map]
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.single_apply]
  have hx : i = e.symm x ↔ e i = x := by
    constructor
    · intro h
      rw [h, e.apply_symm_apply]
    · intro h
      apply e.injective
      rw [e.apply_symm_apply, h]
  have hy : j = e.symm y ↔ e j = y := by
    constructor
    · intro h
      rw [h, e.apply_symm_apply]
    · intro h
      apply e.injective
      rw [e.apply_symm_apply, h]
  simp only [hx, hy]

end Channel

private theorem regroup_kron_id_apply_single
    {A : Type u} {A' : Type v} {B : Type w} {B' : Type x} {R : Type y}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    [Fintype R] [DecidableEq R]
    (PhiA : MatrixMap A A') (PhiB : MatrixMap B B')
    (i j : Prod (Prod A R) B) :
    (Channel.reindex (loccReferenceRegroupEquiv A' B' R)).map
        (MatrixMap.kron (MatrixMap.kron PhiA PhiB) (Channel.idChannel R).map
          ((Channel.reindex (loccReferenceRegroupEquiv A B R).symm).map
            (Matrix.single i j (1 : Complex)))) =
      MatrixMap.kron (MatrixMap.kron PhiA (Channel.idChannel R).map) PhiB
        (Matrix.single i j (1 : Complex)) := by
  rw [Channel.reindex_map_single]
  rw [show Matrix.single
      ((loccReferenceRegroupEquiv A B R).symm i)
      ((loccReferenceRegroupEquiv A B R).symm j) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (i.1.1, i.2) (j.1.1, j.2) (1 : Complex))
          (Matrix.single i.1.2 j.1.2 (1 : Complex)) by
      simpa [loccReferenceRegroupEquiv] using
        (single_prod_eq_kronecker_single
          (i.1.1, i.2) (j.1.1, j.2) i.1.2 j.1.2)]
  rw [MatrixMap.kron_apply_kronecker]
  rw [show Matrix.single (i.1.1, i.2) (j.1.1, j.2) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : Complex))
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
  rw [MatrixMap.kron_apply_kronecker, Channel.reindex_map]
  ext k l
  simp [loccReferenceRegroupEquiv, Matrix.kronecker, mul_assoc, mul_comm, mul_left_comm]

private theorem regroup_kron_id
    {A : Type u} {A' : Type v} {B : Type w} {B' : Type x} {R : Type y}
    [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
    [Fintype R] [DecidableEq R]
    (PhiA : MatrixMap A A') (PhiB : MatrixMap B B') :
    (Channel.reindex (loccReferenceRegroupEquiv A' B' R)).map.comp
        ((MatrixMap.kron (MatrixMap.kron PhiA PhiB) (Channel.idChannel R).map).comp
          (Channel.reindex (loccReferenceRegroupEquiv A B R).symm).map) =
      MatrixMap.kron (MatrixMap.kron PhiA (Channel.idChannel R).map) PhiB := by
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    ((Channel.reindex (loccReferenceRegroupEquiv A' B' R)).map.comp
      ((MatrixMap.kron (MatrixMap.kron PhiA PhiB) (Channel.idChannel R).map).comp
        (Channel.reindex (loccReferenceRegroupEquiv A B R).symm).map)) X]
  rw [MatrixMap.map_eq_sum_single
    (MatrixMap.kron (MatrixMap.kron PhiA (Channel.idChannel R).map) PhiB) X]
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
    (Channel.reindex (loccReferenceRegroupEquiv A' B' R)).map.comp
        ((MatrixMap.kron (∑ i, MatrixMap.kron (PhiA i) (PhiB i))
          (Channel.idChannel R).map).comp
          (Channel.reindex (loccReferenceRegroupEquiv A B R).symm).map) =
      ∑ i, MatrixMap.kron (MatrixMap.kron (PhiA i) (Channel.idChannel R).map) (PhiB i) := by
  rw [MatrixMap.kron_sum_left]
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply]
  let input := (Channel.reindex (loccReferenceRegroupEquiv A B R).symm).map X
  let leftMap : I → MatrixMap (Prod (Prod A B) R) (Prod (Prod A' B') R) :=
    fun i => MatrixMap.kron (MatrixMap.kron (PhiA i) (PhiB i))
      (Channel.idChannel R).map
  let rightMap : I → MatrixMap (Prod (Prod A R) B) (Prod (Prod A' R) B') :=
    fun i => MatrixMap.kron
      (MatrixMap.kron (PhiA i) (Channel.idChannel R).map) (PhiB i)
  change
    (Channel.reindex (loccReferenceRegroupEquiv A' B' R)).map
        ((∑ i, leftMap i) input) =
      (∑ i, rightMap i) X
  rw [show (∑ i, leftMap i) input = ∑ i, leftMap i input from by
    simp]
  rw [map_sum]
  rw [show (∑ i, rightMap i) X = ∑ i, rightMap i X from by
    simp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa [input, leftMap, rightMap, LinearMap.comp_apply] using
    LinearMap.congr_fun (regroup_kron_id (PhiA i) (PhiB i)) X

namespace FiniteInstrument

variable {A : Type u} {A' : Type v} {X : Type w} {R : Type x}
variable [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
variable [Fintype X] [Fintype R] [DecidableEq R]

/-- Tensor every branch of a finite instrument with the identity on a right reference. -/
def prodIdRight (M : FiniteInstrument A A' X) :
    FiniteInstrument (Prod A R) (Prod A' R) X where
  branch result := MatrixMap.kron (M.branch result) (Channel.idChannel R).map
  branchTraceNonincreasingCP result :=
    MatrixMap.traceNonincreasingCP_kron_id (a := R)
      (M.branchTraceNonincreasingCP result)
  total := M.total.prod (Channel.idChannel R)
  sum_branch_eq_total := by
    change (∑ result, MatrixMap.kron (M.branch result) (Channel.idChannel R).map) =
      MatrixMap.kron M.total.map (Channel.idChannel R).map
    rw [← M.sum_branch_eq_total, MatrixMap.kron_sum_left]

@[simp]
theorem prodIdRight_branch (M : FiniteInstrument A A' X) (result : X) :
    (M.prodIdRight (R := R)).branch result =
      MatrixMap.kron (M.branch result) (Channel.idChannel R).map := rfl

theorem prodIdRight_totalChannel (M : FiniteInstrument A A' X) :
    (M.prodIdRight (R := R)).totalChannel =
      M.totalChannel.prod (Channel.idChannel R) := rfl

end FiniteInstrument

namespace State

private theorem reindex_symm_reindex
    {A : Type u} {B : Type v}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : State A) (e : A ≃ B) :
    (rho.reindex e).reindex e.symm = rho := by
  ext i j
  simp [State.reindex]

end State

namespace OneWayLOCC

variable {A : Type u} {A' : Type v} {B : Type w} {B' : Type x}
variable {X : Type y} {R : Type z}
variable [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
variable [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
variable [Fintype X] [Fintype R] [DecidableEq R]

/-- Lift a finite one-way LOCC operation by an untouched reference grouped with Alice. -/
def prodIdRight (L : OneWayLOCC A A' B B' X) :
    OneWayLOCC (Prod A R) (Prod A' R) B B' X where
  aliceInstrument := L.aliceInstrument.prodIdRight
  bobChannel := L.bobChannel
  realization :=
    (Channel.reindex (loccReferenceRegroupEquiv A' B' R)).comp
      ((L.toChannel.prod (Channel.idChannel R)).comp
        (Channel.reindex (loccReferenceRegroupEquiv A B R).symm))
  realization_map := by
    change
      (Channel.reindex (loccReferenceRegroupEquiv A' B' R)).map.comp
          ((MatrixMap.kron L.toChannel.map (Channel.idChannel R).map).comp
            (Channel.reindex (loccReferenceRegroupEquiv A B R).symm).map) =
        ∑ result,
          MatrixMap.kron
            (MatrixMap.kron (L.aliceInstrument.branch result)
              (Channel.idChannel R).map)
            (L.bobChannel result).map
    rw [L.toChannel_map]
    exact regroup_sum_kron_id
      (fun result => L.aliceInstrument.branch result)
      (fun result => (L.bobChannel result).map)

/-- The lifted realization is the original realization tensored with the reference identity,
with explicit input and output regrouping. -/
theorem prodIdRight_toChannel (L : OneWayLOCC A A' B B' X) :
    (L.prodIdRight (R := R)).toChannel =
      (Channel.reindex (loccReferenceRegroupEquiv A' B' R)).comp
        ((L.toChannel.prod (Channel.idChannel R)).comp
          (Channel.reindex (loccReferenceRegroupEquiv A B R).symm)) := rfl

/-- On a pure input, regrouping the reference with Alice before the lifted LOCC gives the
regrouped output of the original LOCC tensored with the identity on the reference. -/
theorem prodIdRight_applyState_reindex_pure
    (L : OneWayLOCC A A' B B' X) (psi : PureVector (Prod (Prod A B) R)) :
    (L.prodIdRight (R := R)).toChannel.applyState
        (psi.state.reindex (loccReferenceRegroupEquiv A B R)) =
      ((L.toChannel.prod (Channel.idChannel R)).applyState psi.state).reindex
        (loccReferenceRegroupEquiv A' B' R) := by
  rw [prodIdRight_toChannel, Channel.applyState_comp, Channel.applyState_comp,
    Channel.reindex_applyState, Channel.reindex_applyState]
  rw [State.reindex_symm_reindex]

end OneWayLOCC

end

end QIT
