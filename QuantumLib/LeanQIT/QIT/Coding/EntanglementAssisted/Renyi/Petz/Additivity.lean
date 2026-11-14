/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.Lower.Petz
public import QIT.Symmetry.DeFinetti

/-!
# Petz-Renyi tensor-power lower bound

This module proves the tensor-power lower bound for the barred Petz--Renyi
channel mutual information used by the entanglement-assisted capacity proof.
It realizes the tensor-product candidate step inside the source proof
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:894-982].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace PureVector

def tensorPowerBipartite (psi : PureVector (Prod a b)) (n : Nat) :
    PureVector (Prod (TensorPower a n) (TensorPower b n)) :=
  (psi.tensorPower n).reindex (tensorPowerProdEquiv a b n)

theorem tensorPowerBipartite_state (psi : PureVector (Prod a b)) (n : Nat) :
    (psi.tensorPowerBipartite n).state = psi.state.tensorPowerBipartite n := by
  unfold tensorPowerBipartite State.tensorPowerBipartite
  rw [PureVector.reindex_state, PureVector.tensorPower_state]

end PureVector

namespace State

theorem prod_punit_ext (rho sigma : State (Prod PUnit PUnit)) :
    rho = sigma := by
  apply State.ext
  ext x y
  rcases x with ⟨xA, xB⟩
  rcases y with ⟨yA, yB⟩
  cases xA
  cases xB
  cases yA
  cases yB
  have hrho : rho.matrix (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) = 1 := by
    simpa [Matrix.trace, Fintype.sum_prod_type] using rho.trace_eq_one
  have hsigma : sigma.matrix (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) = 1 := by
    simpa [Matrix.trace, Fintype.sum_prod_type] using sigma.trace_eq_one
  rw [hrho, hsigma]

def tensorPowerBipartiteSuccEquiv (a : Type u) (b : Type v) (n : Nat) :
    Prod (Prod a b) (Prod (TensorPower a n) (TensorPower b n)) ≃
      Prod (TensorPower a (n + 1)) (TensorPower b (n + 1)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl

theorem tensorPowerBipartite_succ (rho : State (Prod a b)) (n : Nat) :
    rho.tensorPowerBipartite (n + 1) =
      (rho.prod (rho.tensorPowerBipartite n)).reindex
        (tensorPowerBipartiteSuccEquiv a b n) := by
  apply State.ext
  ext x y
  rcases x with ⟨xA, xB⟩
  rcases y with ⟨yA, yB⟩
  rcases xA with ⟨xA0, xAs⟩
  rcases xB with ⟨xB0, xBs⟩
  rcases yA with ⟨yA0, yAs⟩
  rcases yB with ⟨yB0, yBs⟩
  simp [State.tensorPowerBipartite, State.tensorPower,
    State.prod, State.reindex, tensorPowerProdEquiv,
    tensorPowerBipartiteSuccEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply]

theorem reindex_posDef {alpha : Type u} {beta : Type v}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (rho : State alpha) (e : alpha ≃ beta) (h : rho.matrix.PosDef) :
    (rho.reindex e).matrix.PosDef := by
  rw [State.reindex_matrix]
  exact h.submatrix e.symm.injective

theorem tensorPowerBipartite_posDef (rho : State (Prod a b)) (h : rho.matrix.PosDef) (n : Nat) :
    (rho.tensorPowerBipartite n).matrix.PosDef := by
  unfold State.tensorPowerBipartite
  exact State.reindex_posDef (rho.tensorPower n) (tensorPowerProdEquiv a b n)
    (rho.tensorPower_posDef h n)

theorem prod_tensorPowerBipartite (rho : State a) (sigma : State b) :
    (n : Nat) ->
      (rho.prod sigma).tensorPowerBipartite n =
        (rho.tensorPower n).prod (sigma.tensorPower n)
  | 0 => by
      exact State.prod_punit_ext _ _
  | n + 1 => by
      have ih := prod_tensorPowerBipartite rho sigma n
      apply State.ext
      ext x y
      rcases x with ⟨xA, xB⟩
      rcases y with ⟨yA, yB⟩
      rcases xA with ⟨xA0, xAs⟩
      rcases xB with ⟨xB0, xBs⟩
      rcases yA with ⟨yA0, yAs⟩
      rcases yB with ⟨yB0, yBs⟩
      have ih_entry := congrArg
        (fun tau : State (Prod (TensorPower a n) (TensorPower b n)) =>
          tau.matrix (xAs, xBs) (yAs, yBs)) ih
      simp [State.tensorPowerBipartite_succ, State.tensorPower, State.prod,
        State.reindex, State.tensorPowerBipartiteSuccEquiv, Matrix.kronecker,
        Matrix.kroneckerMap_apply] at ih_entry ⊢
      rw [ih_entry]
      ring

end State

noncomputable def cMatrixReindexStarAlgEquiv {alpha : Type u} {beta : Type v}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (e : alpha ≃ beta) :
    CMatrix alpha ≃⋆ₐ[ℂ] CMatrix beta where
  __ := Matrix.reindexAlgEquiv ℂ ℂ e
  map_smul' r A := by
    ext i j
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  map_star' A := by
    ext i j
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem cMatrix_rpow_reindex_posDef {alpha : Type u} {beta : Type v}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (e : alpha ≃ beta) (A : CMatrix alpha) (hA : A.PosDef) (s : ℝ) :
    CFC.rpow (Matrix.reindex e e A) s =
      Matrix.reindex e e (CFC.rpow A s) := by
  change (Matrix.reindex e e A) ^ s = Matrix.reindex e e (A ^ s)
  have hmap_nonneg : 0 ≤ Matrix.reindex e e A := by
    exact Matrix.nonneg_iff_posSemidef.mpr (hA.posSemidef.submatrix e.symm)
  have hA_nonneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  rw [CFC.rpow_eq_cfc_real (a := Matrix.reindex e e A) (y := s) hmap_nonneg]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := s) hA_nonneg]
  simpa [cMatrixReindexStarAlgEquiv, Matrix.reindexAlgEquiv_apply] using
    (StarAlgHomClass.map_cfc
      (cMatrixReindexStarAlgEquiv e)
      (fun x : ℝ => x ^ s) A
      (hf := by
        intro x hx
        exact (Real.continuousAt_rpow_const x s
          (.inl (ne_of_gt ((Matrix.PosDef.isStrictlyPositive hA).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous (Matrix.reindex e e : CMatrix alpha -> CMatrix beta)
        fun_prop)).symm

theorem cMatrix_trace_reindex {alpha : Type u} {beta : Type v}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (e : alpha ≃ beta) (A : CMatrix alpha) :
    (Matrix.reindex e e A).trace = A.trace := by
  rw [Matrix.trace, Matrix.trace]
  exact Fintype.sum_equiv e.symm
    (fun i : beta => Matrix.reindex e e A i i)
    (fun i : alpha => A i i)
    (by intro i; simp [Matrix.reindex_apply, Matrix.submatrix_apply])

namespace State

theorem petzRenyi_reindex {alpha : Type u} {beta : Type v}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (rho sigma : State alpha) (e : alpha ≃ beta)
    (hrho : rho.matrix.PosDef) (hsigma : sigma.matrix.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1) :
    (rho.reindex e).petzRenyi (sigma.reindex e)
        (State.reindex_posDef rho e hrho) (State.reindex_posDef sigma e hsigma)
        alphaR halpha_pos halpha_ne_one =
      rho.petzRenyi sigma hrho hsigma alphaR halpha_pos halpha_ne_one := by
  unfold State.petzRenyi
  rw [State.reindex_matrix, State.reindex_matrix]
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (Matrix.reindex e e rho.matrix) alphaR *
        CFC.rpow (Matrix.reindex e e sigma.matrix) (1 - alphaR)).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow rho.matrix alphaR *
        CFC.rpow sigma.matrix (1 - alphaR)).trace).re)
  rw [cMatrix_rpow_reindex_posDef e rho.matrix hrho alphaR]
  rw [cMatrix_rpow_reindex_posDef e sigma.matrix hsigma (1 - alphaR)]
  change (1 / (alphaR - 1)) *
      log2 ((((Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow rho.matrix alphaR) *
        (Matrix.reindexAlgEquiv ℂ ℂ e)
          (CFC.rpow sigma.matrix (1 - alphaR))).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow rho.matrix alphaR *
        CFC.rpow sigma.matrix (1 - alphaR)).trace).re)
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e
    (CFC.rpow rho.matrix alphaR) (CFC.rpow sigma.matrix (1 - alphaR))]
  change (1 / (alphaR - 1)) *
      log2 ((((Matrix.reindex e e
        (CFC.rpow rho.matrix alphaR *
          CFC.rpow sigma.matrix (1 - alphaR))).trace).re)) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow rho.matrix alphaR *
        CFC.rpow sigma.matrix (1 - alphaR)).trace).re)
  rw [cMatrix_trace_reindex e]

theorem tensorPowerBipartite_marginalA_posDef (rho : State (Prod a b))
    (hA : rho.marginalA.matrix.PosDef) (n : Nat) :
    (rho.tensorPowerBipartite n).marginalA.matrix.PosDef := by
  rw [rho.tensorPowerBipartite_marginalA n]
  exact State.tensorPower_posDef hA n

theorem tensorPowerBipartite_marginalB_posDef (rho : State (Prod a b))
    (hB : rho.marginalB.matrix.PosDef) (n : Nat) :
    (rho.tensorPowerBipartite n).marginalB.matrix.PosDef := by
  rw [rho.tensorPowerBipartite_marginalB n]
  exact State.tensorPower_posDef hB n

theorem barPetzRenyiMutualInformation_tensorPowerBipartite
    (rhoAB : State (Prod a b))
    (hrho : rhoAB.matrix.PosDef)
    (hA : rhoAB.marginalA.matrix.PosDef)
    (hB : rhoAB.marginalB.matrix.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1)
    (n : Nat) :
    (rhoAB.tensorPowerBipartite n).barPetzRenyiMutualInformation
        (rhoAB.tensorPowerBipartite_posDef hrho n)
        (rhoAB.tensorPowerBipartite_marginalA_posDef hA n)
        (rhoAB.tensorPowerBipartite_marginalB_posDef hB n)
        alphaR halpha_pos halpha_ne_one =
      (n : ℝ) *
        rhoAB.barPetzRenyiMutualInformation hrho hA hB
          alphaR halpha_pos halpha_ne_one := by
  have hcomp :
      (rhoAB.tensorPowerBipartite n).marginalA.prod
          (rhoAB.tensorPowerBipartite n).marginalB =
        (rhoAB.marginalA.prod rhoAB.marginalB).tensorPowerBipartite n := by
    calc
      (rhoAB.tensorPowerBipartite n).marginalA.prod
          (rhoAB.tensorPowerBipartite n).marginalB =
        (rhoAB.marginalA.tensorPower n).prod
          (rhoAB.marginalB.tensorPower n) := by
          rw [rhoAB.tensorPowerBipartite_marginalA n,
            rhoAB.tensorPowerBipartite_marginalB n]
      _ = (rhoAB.marginalA.prod rhoAB.marginalB).tensorPowerBipartite n :=
          (State.prod_tensorPowerBipartite rhoAB.marginalA rhoAB.marginalB n).symm
  unfold State.barPetzRenyiMutualInformation
  calc
    (rhoAB.tensorPowerBipartite n).petzRenyi
        ((rhoAB.tensorPowerBipartite n).marginalA.prod
          (rhoAB.tensorPowerBipartite n).marginalB)
        _ _ alphaR halpha_pos halpha_ne_one =
      (rhoAB.tensorPowerBipartite n).petzRenyi
        ((rhoAB.marginalA.prod rhoAB.marginalB).tensorPowerBipartite n)
        _ _ alphaR halpha_pos halpha_ne_one := by
        unfold State.petzRenyi
        rw [congrArg State.matrix hcomp]
    _ =
      (n : ℝ) *
        rhoAB.petzRenyi (rhoAB.marginalA.prod rhoAB.marginalB)
          hrho (State.prod_posDef hA hB) alphaR halpha_pos halpha_ne_one := by
        change ((rhoAB.tensorPower n).reindex (tensorPowerProdEquiv a b n)).petzRenyi
            (((rhoAB.marginalA.prod rhoAB.marginalB).tensorPower n).reindex
              (tensorPowerProdEquiv a b n))
            _ _ alphaR halpha_pos halpha_ne_one =
          (n : ℝ) *
            rhoAB.petzRenyi (rhoAB.marginalA.prod rhoAB.marginalB)
              hrho (State.prod_posDef hA hB) alphaR halpha_pos halpha_ne_one
        rw [State.petzRenyi_reindex]
        exact State.petzRenyi_tensorPower rhoAB (rhoAB.marginalA.prod rhoAB.marginalB)
          hrho (State.prod_posDef hA hB) alphaR halpha_pos halpha_ne_one n

theorem barPetzRenyiMutualInformation_congr
    {rho sigma : State (Prod a b)} (h : rho = sigma)
    (hrho : rho.matrix.PosDef) (hA : rho.marginalA.matrix.PosDef)
    (hB : rho.marginalB.matrix.PosDef)
    (hsigma : sigma.matrix.PosDef) (hsA : sigma.marginalA.matrix.PosDef)
    (hsB : sigma.marginalB.matrix.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1) :
    rho.barPetzRenyiMutualInformation hrho hA hB
        alphaR halpha_pos halpha_ne_one =
      sigma.barPetzRenyiMutualInformation hsigma hsA hsB
        alphaR halpha_pos halpha_ne_one := by
  cases h
  rfl

end State

namespace Channel

set_option maxHeartbeats 800000 in
theorem applyState_hypothesisTensor_succ_reindex
    (N : Channel a b) (n : Nat)
    (rho : State (Prod a a))
    (sigma : State (Prod (QIT.TensorPower a n) (QIT.TensorPower a n))) :
    (((Channel.idChannel (QIT.TensorPower a (n + 1))).prod (N.tensorPower (n + 1))).applyState
        ((rho.prod sigma).reindex (State.tensorPowerBipartiteSuccEquiv a a n))) =
      ((((Channel.idChannel a).prod N).applyState rho).prod
          (((Channel.idChannel (QIT.TensorPower a n)).prod (N.tensorPower n)).applyState sigma)).reindex
        (State.tensorPowerBipartiteSuccEquiv a b n) := by
  apply State.ext
  ext x y
  rcases x with ⟨xR, xB⟩
  rcases y with ⟨yR, yB⟩
  rcases xR with ⟨xR0, xRs⟩
  rcases xB with ⟨xB0, xBs⟩
  rcases yR with ⟨yR0, yRs⟩
  rcases yB with ⟨yB0, yBs⟩
  simp only [Channel.applyState, Channel.prod, State.reindex_matrix,
    State.prod_matrix_kronecker, Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (fun j j' =>
          (Matrix.kronecker rho.matrix sigma.matrix).submatrix
            (State.tensorPowerBipartiteSuccEquiv a a n).symm
            (State.tensorPowerBipartiteSuccEquiv a a n).symm
            (((xR0, xRs), (xB0, xBs)).1, j)
            (((yR0, yRs), (yB0, yBs)).1, j')) =
        Matrix.kronecker
          (fun i i' => rho.matrix (xR0, i) (yR0, i'))
          (fun is is' => sigma.matrix (xRs, is) (yRs, is')) := by
    ext z z'
    rcases z with ⟨z0, zs⟩
    rcases z' with ⟨z0', zs'⟩
    simp [State.tensorPowerBipartiteSuccEquiv, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
  rw [hslice]
  rw [Channel.tensorPower_succ]
  change MatrixMap.kron N.map (N.tensorPower n).map
      (Matrix.kronecker
        (fun i i' => rho.matrix (xR0, i) (yR0, i'))
        (fun is is' => sigma.matrix (xRs, is) (yRs, is')))
      (xB0, xBs) (yB0, yBs) = _
  rw [MatrixMap.kron_apply_kronecker]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply,
    State.tensorPowerBipartiteSuccEquiv]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_left_apply_slice]

theorem hypothesisTestingOutputState_tensorPowerBipartite
    (N : Channel a b) (psi : PureVector (Prod a a)) (n : Nat) :
      (N.tensorPower n).hypothesisTestingOutputState (psi.tensorPowerBipartite n) =
        (N.hypothesisTestingOutputState psi).tensorPowerBipartite n := by
  induction n with
  | zero =>
      exact State.prod_punit_ext _ _
  | succ n ih =>
      have ih_state :
          (((Channel.idChannel (QIT.TensorPower a n)).prod (N.tensorPower n)).applyState
              (psi.state.tensorPowerBipartite n)) =
            (N.hypothesisTestingOutputState psi).tensorPowerBipartite n := by
        rw [← PureVector.tensorPowerBipartite_state psi n]
        exact ih
      rw [Channel.hypothesisTestingOutputState, PureVector.tensorPowerBipartite_state]
      rw [State.tensorPowerBipartite_succ]
      rw [Channel.applyState_hypothesisTensor_succ_reindex]
      rw [ih_state]
      change ((N.hypothesisTestingOutputState psi).prod
          ((N.hypothesisTestingOutputState psi).tensorPowerBipartite n)).reindex
        (State.tensorPowerBipartiteSuccEquiv a b n) =
          (N.hypothesisTestingOutputState psi).tensorPowerBipartite (n + 1)
      rw [← State.tensorPowerBipartite_succ]

theorem hypothesisTestingOutputState_tensorPowerBipartite_posDef
    (N : Channel a b) (psi : PureVector (Prod a a))
    (homega : (N.hypothesisTestingOutputState psi).matrix.PosDef) (n : Nat) :
    ((N.tensorPower n).hypothesisTestingOutputState
      (psi.tensorPowerBipartite n)).matrix.PosDef := by
  rw [Channel.hypothesisTestingOutputState_tensorPowerBipartite]
  exact State.tensorPowerBipartite_posDef (N.hypothesisTestingOutputState psi) homega n

theorem hypothesisTestingOutputState_tensorPowerBipartite_marginalA_posDef
    (N : Channel a b) (psi : PureVector (Prod a a))
    (hR : (N.hypothesisTestingOutputState psi).marginalA.matrix.PosDef) (n : Nat) :
    ((N.tensorPower n).hypothesisTestingOutputState
      (psi.tensorPowerBipartite n)).marginalA.matrix.PosDef := by
  rw [Channel.hypothesisTestingOutputState_tensorPowerBipartite]
  exact State.tensorPowerBipartite_marginalA_posDef
    (N.hypothesisTestingOutputState psi) hR n

theorem hypothesisTestingOutputState_tensorPowerBipartite_marginalB_posDef
    (N : Channel a b) (psi : PureVector (Prod a a))
    (hB : (N.hypothesisTestingOutputState psi).marginalB.matrix.PosDef) (n : Nat) :
    ((N.tensorPower n).hypothesisTestingOutputState
      (psi.tensorPowerBipartite n)).marginalB.matrix.PosDef := by
  rw [Channel.hypothesisTestingOutputState_tensorPowerBipartite]
  exact State.tensorPowerBipartite_marginalB_posDef
    (N.hypothesisTestingOutputState psi) hB n

theorem inputBarPetzRenyiMutualInformation_tensorPowerBipartite
    (N : Channel a b) (psi : PureVector (Prod a a))
    (homega : (N.hypothesisTestingOutputState psi).matrix.PosDef)
    (hR : (N.hypothesisTestingOutputState psi).marginalA.matrix.PosDef)
    (hB : (N.hypothesisTestingOutputState psi).marginalB.matrix.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1)
    (n : Nat) :
    (N.tensorPower n).inputBarPetzRenyiMutualInformation
        (psi.tensorPowerBipartite n)
        (N.hypothesisTestingOutputState_tensorPowerBipartite_posDef
          psi homega n)
        (N.hypothesisTestingOutputState_tensorPowerBipartite_marginalA_posDef
          psi hR n)
        (N.hypothesisTestingOutputState_tensorPowerBipartite_marginalB_posDef
          psi hB n)
        alphaR halpha_pos halpha_ne_one =
      (n : ℝ) *
        N.inputBarPetzRenyiMutualInformation psi homega hR hB
          alphaR halpha_pos halpha_ne_one := by
  unfold Channel.inputBarPetzRenyiMutualInformation
  calc
    ((N.tensorPower n).hypothesisTestingOutputState
        (psi.tensorPowerBipartite n)).barPetzRenyiMutualInformation
        _ _ _ alphaR halpha_pos halpha_ne_one =
      (((N.hypothesisTestingOutputState psi).tensorPowerBipartite n).barPetzRenyiMutualInformation
          _ _ _ alphaR halpha_pos halpha_ne_one) := by
        exact State.barPetzRenyiMutualInformation_congr
          (Channel.hypothesisTestingOutputState_tensorPowerBipartite N psi n)
          _ _ _
          ((N.hypothesisTestingOutputState psi).tensorPowerBipartite_posDef homega n)
          ((N.hypothesisTestingOutputState psi).tensorPowerBipartite_marginalA_posDef hR n)
          ((N.hypothesisTestingOutputState psi).tensorPowerBipartite_marginalB_posDef hB n)
          alphaR halpha_pos halpha_ne_one
    _ =
      (n : ℝ) *
        (N.hypothesisTestingOutputState psi).barPetzRenyiMutualInformation
          homega hR hB alphaR halpha_pos halpha_ne_one := by
        exact State.barPetzRenyiMutualInformation_tensorPowerBipartite
          (N.hypothesisTestingOutputState psi) homega hR hB
          alphaR halpha_pos halpha_ne_one n

theorem barPetzRenyiMutualInformation_tensorPower_lower_bound
    (N : Channel a b) {n : Nat} (hn : 0 < n)
    {alphaR : ℝ} (halpha_pos : 0 < alphaR) (halpha_lt_one : alphaR < 1)
    (hne :
      (N.barPetzRenyiMutualInformationValueSet alphaR halpha_pos
        (ne_of_lt halpha_lt_one)).Nonempty)
    (hbddTensor :
      BddAbove ((N.tensorPower n).barPetzRenyiMutualInformationValueSet
        alphaR halpha_pos (ne_of_lt halpha_lt_one))) :
    (n : ℝ) * N.barPetzRenyiMutualInformation
        alphaR halpha_pos (ne_of_lt halpha_lt_one) ≤
      (N.tensorPower n).barPetzRenyiMutualInformation
        alphaR halpha_pos (ne_of_lt halpha_lt_one) := by
  rw [N.barPetzRenyiMutualInformation_eq_sSup,
    (N.tensorPower n).barPetzRenyiMutualInformation_eq_sSup]
  let S := N.barPetzRenyiMutualInformationValueSet
    alphaR halpha_pos (ne_of_lt halpha_lt_one)
  let T := (N.tensorPower n).barPetzRenyiMutualInformationValueSet
    alphaR halpha_pos (ne_of_lt halpha_lt_one)
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hsSup :
      sSup S ≤ sSup T / (n : ℝ) := by
    refine csSup_le hne ?_
    intro x hx
    rcases hx with ⟨psi, homega, hR, hB, rfl⟩
    have hmemT :
        (n : ℝ) *
            N.inputBarPetzRenyiMutualInformation psi homega hR hB
              alphaR halpha_pos (ne_of_lt halpha_lt_one) ∈ T := by
      refine ⟨psi.tensorPowerBipartite n,
        N.hypothesisTestingOutputState_tensorPowerBipartite_posDef
          psi homega n,
        N.hypothesisTestingOutputState_tensorPowerBipartite_marginalA_posDef
          psi hR n,
        N.hypothesisTestingOutputState_tensorPowerBipartite_marginalB_posDef
          psi hB n,
        ?_⟩
      exact (Channel.inputBarPetzRenyiMutualInformation_tensorPowerBipartite
        N psi homega hR hB alphaR halpha_pos
        (ne_of_lt halpha_lt_one) n).symm
    have hleT :
        (n : ℝ) *
            N.inputBarPetzRenyiMutualInformation psi homega hR hB
              alphaR halpha_pos (ne_of_lt halpha_lt_one) ≤ sSup T :=
      le_csSup hbddTensor hmemT
    exact (le_div_iff₀ hnR).mpr (by simpa [mul_comm] using hleT)
  calc
    (n : ℝ) * sSup S ≤ (n : ℝ) * (sSup T / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsSup (le_of_lt hnR)
    _ = sSup T := by
      field_simp [ne_of_gt hnR]

end Channel

end

end QIT
