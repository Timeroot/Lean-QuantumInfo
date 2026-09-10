/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.OneShot.Lower.Petz
public import QuantumLib.QIT.Symmetry.DeFinetti

/-!
# Petz-Renyi tensor-power lower bound

This module proves the tensor-power lower bound for the barred Petz--Renyi
channel mutual information used by the entanglement-assisted capacity proof.
It realizes the tensor-product candidate step inside the source proof
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:894-982].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

noncomputable section
universe u v
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

open QIT

namespace Ket

/-- The `n`-fold tensor power of a bipartite pure state, regrouped so that the `a` factors and the
`b` factors each form a tensor power of their own. -/
def tensorPowerBipartite (psi : Ket (a × b)) (n : ℕ) :
    Ket (TensorPower a n × TensorPower b n) :=
  (psi.tensorPower n).reindex (tensorPowerProdEquiv a b n)

theorem tensorPowerBipartite_state (psi : Ket (a × b)) (n : ℕ) :
    (psi.tensorPowerBipartite n).state = psi.state.tensorPowerBipartite n := by
  unfold tensorPowerBipartite MState.tensorPowerBipartite
  rw [Ket.reindex_state, Ket.tensorPower_state]

end Ket

namespace MState

theorem prod_punit_ext (rho sigma : MState (PUnit × PUnit)) :
    rho = sigma := by
  apply MState.ext
  ext x y
  rcases x with ⟨xA, xB⟩
  rcases y with ⟨yA, yB⟩
  cases xA
  cases xB
  cases yA
  cases yB
  have hrho : rho.m (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) = 1 := by
    simpa [Matrix.trace, Fintype.sum_prod_type] using rho.tr'
  have hsigma : sigma.m (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) = 1 := by
    simpa [Matrix.trace, Fintype.sum_prod_type] using sigma.tr'
  rw [hrho, hsigma]

/-- Splitting one copy off a bipartite tensor power:
`(a × b) × (a^⊗n × b^⊗n) ≃ a^⊗(n+1) × b^⊗(n+1)`. -/
def tensorPowerBipartiteSuccEquiv (a : Type u) (b : Type v) (n : ℕ) :
    ((a × b) × (TensorPower a n × TensorPower b n)) ≃
      (TensorPower a (n + 1) × TensorPower b (n + 1)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl

theorem tensorPowerBipartite_succ (rho : MState (a × b)) (n : ℕ) :
    rho.tensorPowerBipartite (n + 1) =
      (rho.prod (rho.tensorPowerBipartite n)).reindex
        (tensorPowerBipartiteSuccEquiv a b n) := by
  apply MState.ext
  simp only [MState.tensorPowerBipartite_matrix, MState.reindex_matrix, MState.prod_m,
    MState.tensorPower_succ_matrix]
  ext x y
  rfl

theorem prod_tensorPowerBipartite (rho : MState a) (sigma : MState b) :
    (n : ℕ) →
      (rho.prod sigma).tensorPowerBipartite n =
        (rho.tensorPower n).prod (sigma.tensorPower n)
  | 0 => by
      exact MState.prod_punit_ext _ _
  | n + 1 => by
      have ih := prod_tensorPowerBipartite rho sigma n
      rw [MState.tensorPowerBipartite_succ, ih]
      apply MState.ext
      simp only [MState.reindex_matrix, MState.prod_m, MState.tensorPower_succ_matrix]
      ext x y
      show rho.m x.1.1 y.1.1 * sigma.m x.2.1 y.2.1 *
          ((rho.tensorPower n).m x.1.2 y.1.2 *
            (sigma.tensorPower n).m x.2.2 y.2.2) =
        rho.m x.1.1 y.1.1 * (rho.tensorPower n).m x.1.2 y.1.2 *
          (sigma.m x.2.1 y.2.1 * (sigma.tensorPower n).m x.2.2 y.2.2)
      ring

end MState

namespace QIT

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
  simpa [cMatrixReindexStarAlgEquiv, Matrix.coe_reindexAlgEquiv] using
    (StarAlgHomClass.map_cfc
      (cMatrixReindexStarAlgEquiv e)
      (fun x : ℝ => x ^ s) A
      (hf := by
        intro x hx
        exact (Real.continuousAt_rpow_const x s
          (.inl (ne_of_gt ((Matrix.PosDef.isStrictlyPositive hA).spectrum_pos hx)))).continuousWithinAt)
      (hφ := by
        change Continuous (Matrix.reindex e e : CMatrix alpha → CMatrix beta)
        fun_prop)).symm

end QIT

namespace MState

theorem petzRenyi_reindex {alpha : Type u} {beta : Type v}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (rho sigma : MState alpha) (e : alpha ≃ beta)
    (hrho : rho.m.PosDef) (hsigma : sigma.m.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1) :
    (rho.reindex e).petzRenyi (sigma.reindex e)
        (MState.reindex_posDef rho e hrho) (MState.reindex_posDef sigma e hsigma)
        alphaR halpha_pos halpha_ne_one =
      rho.petzRenyi sigma hrho hsigma alphaR halpha_pos halpha_ne_one := by
  unfold MState.petzRenyi
  rw [MState.reindex_matrix, MState.reindex_matrix]
  change (1 / (alphaR - 1)) *
      log2 (((CFC.rpow (Matrix.reindex e e rho.m) alphaR *
        CFC.rpow (Matrix.reindex e e sigma.m) (1 - alphaR)).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow rho.m alphaR *
        CFC.rpow sigma.m (1 - alphaR)).trace).re)
  rw [cMatrix_rpow_reindex_posDef e rho.m hrho alphaR]
  rw [cMatrix_rpow_reindex_posDef e sigma.m hsigma (1 - alphaR)]
  change (1 / (alphaR - 1)) *
      log2 ((((Matrix.reindexAlgEquiv ℂ ℂ e) (CFC.rpow rho.m alphaR) *
        (Matrix.reindexAlgEquiv ℂ ℂ e)
          (CFC.rpow sigma.m (1 - alphaR))).trace).re) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow rho.m alphaR *
        CFC.rpow sigma.m (1 - alphaR)).trace).re)
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
    (CFC.rpow rho.m alphaR) (CFC.rpow sigma.m (1 - alphaR))]
  change (1 / (alphaR - 1)) *
      log2 ((((Matrix.reindex e e
        (CFC.rpow rho.m alphaR *
          CFC.rpow sigma.m (1 - alphaR))).trace).re)) =
    (1 / (alphaR - 1)) *
      log2 (((CFC.rpow rho.m alphaR *
        CFC.rpow sigma.m (1 - alphaR)).trace).re)
  rw [cMatrix_trace_reindex e]

theorem barPetzRenyiMutualInformation_tensorPowerBipartite
    (rhoAB : MState (a × b))
    (hrho : rhoAB.m.PosDef)
    (hA : rhoAB.traceRight.m.PosDef)
    (hB : rhoAB.traceLeft.m.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1)
    (n : ℕ) :
    (rhoAB.tensorPowerBipartite n).barPetzRenyiMutualInformation
        (rhoAB.tensorPowerBipartite_posDef hrho n)
        (rhoAB.tensorPowerBipartite_traceRight_posDef hA n)
        (rhoAB.tensorPowerBipartite_traceLeft_posDef hB n)
        alphaR halpha_pos halpha_ne_one =
      (n : ℝ) *
        rhoAB.barPetzRenyiMutualInformation hrho hA hB
          alphaR halpha_pos halpha_ne_one := by
  have hcomp :
      (rhoAB.tensorPowerBipartite n).traceRight.prod
          (rhoAB.tensorPowerBipartite n).traceLeft =
        (rhoAB.traceRight.prod rhoAB.traceLeft).tensorPowerBipartite n := by
    calc
      (rhoAB.tensorPowerBipartite n).traceRight.prod
          (rhoAB.tensorPowerBipartite n).traceLeft =
        (rhoAB.traceRight.tensorPower n).prod
          (rhoAB.traceLeft.tensorPower n) := by
          rw [rhoAB.tensorPowerBipartite_traceRight n,
            rhoAB.tensorPowerBipartite_traceLeft n]
      _ = (rhoAB.traceRight.prod rhoAB.traceLeft).tensorPowerBipartite n :=
          (MState.prod_tensorPowerBipartite rhoAB.traceRight rhoAB.traceLeft n).symm
  unfold MState.barPetzRenyiMutualInformation
  calc
    (rhoAB.tensorPowerBipartite n).petzRenyi
        ((rhoAB.tensorPowerBipartite n).traceRight.prod
          (rhoAB.tensorPowerBipartite n).traceLeft)
        _ _ alphaR halpha_pos halpha_ne_one =
      (rhoAB.tensorPowerBipartite n).petzRenyi
        ((rhoAB.traceRight.prod rhoAB.traceLeft).tensorPowerBipartite n)
        _ _ alphaR halpha_pos halpha_ne_one := by
        unfold MState.petzRenyi
        rw [congrArg DensityOp.m hcomp]
    _ =
      (n : ℝ) *
        rhoAB.petzRenyi (rhoAB.traceRight.prod rhoAB.traceLeft)
          hrho (MState.PosDef.kron hA hB) alphaR halpha_pos halpha_ne_one := by
        have hreindex := MState.petzRenyi_reindex (rhoAB.tensorPower n)
          ((rhoAB.traceRight.prod rhoAB.traceLeft).tensorPower n)
          (tensorPowerProdEquiv a b n)
          (MState.tensorPower_posDef hrho n)
          (MState.tensorPower_posDef (MState.PosDef.kron hA hB) n)
          alphaR halpha_pos halpha_ne_one
        exact hreindex.trans (MState.petzRenyi_tensorPower rhoAB
          (rhoAB.traceRight.prod rhoAB.traceLeft)
          hrho (MState.PosDef.kron hA hB) alphaR halpha_pos halpha_ne_one n)

theorem barPetzRenyiMutualInformation_congr
    {rho sigma : MState (a × b)} (h : rho = sigma)
    (hrho : rho.m.PosDef) (hA : rho.traceRight.m.PosDef)
    (hB : rho.traceLeft.m.PosDef)
    (hsigma : sigma.m.PosDef) (hsA : sigma.traceRight.m.PosDef)
    (hsB : sigma.traceLeft.m.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1) :
    rho.barPetzRenyiMutualInformation hrho hA hB
        alphaR halpha_pos halpha_ne_one =
      sigma.barPetzRenyiMutualInformation hsigma hsA hsB
        alphaR halpha_pos halpha_ne_one := by
  cases h
  rfl

end MState

end

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem applyState_hypothesisTensor_succ_reindex
    (N : CPTPMap a b) (n : ℕ)
    (rho : MState (a × a))
    (sigma : MState (QIT.TensorPower a n × QIT.TensorPower a n)) :
    (((CPTPOp.id (dIn := QIT.TensorPower a (n + 1))).prod (N.tensorPower (n + 1)))
        ((rho.prod sigma).reindex (MState.tensorPowerBipartiteSuccEquiv a a n))) =
      (MState.prod (((CPTPOp.id (dIn := a)).prod N) rho)
          (((CPTPOp.id (dIn := QIT.TensorPower a n)).prod (N.tensorPower n)) sigma)).reindex
        (MState.tensorPowerBipartiteSuccEquiv a b n) := by
  apply MState.ext
  ext x y
  rcases x with ⟨xR, xB⟩
  rcases y with ⟨yR, yB⟩
  rcases xR with ⟨xR0, xRs⟩
  rcases xB with ⟨xB0, xBs⟩
  rcases yR with ⟨yR0, yRs⟩
  rcases yB with ⟨yB0, yBs⟩
  simp only [CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map,
    MState.reindex_matrix, MState.prod_m, Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (Matrix.of fun j j' =>
          (Matrix.kronecker rho.m sigma.m).submatrix
            (MState.tensorPowerBipartiteSuccEquiv a a n).symm
            (MState.tensorPowerBipartiteSuccEquiv a a n).symm
            (((xR0, xRs), (xB0, xBs)).1, j)
            (((yR0, yRs), (yB0, yBs)).1, j')) =
        Matrix.kronecker
          (Matrix.of fun i i' => rho.m (xR0, i) (yR0, i'))
          (Matrix.of fun is is' => sigma.m (xRs, is) (yRs, is')) := by
    ext z z'
    rcases z with ⟨z0, zs⟩
    rcases z' with ⟨z0', zs'⟩
    simp [MState.tensorPowerBipartiteSuccEquiv, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.of_apply]
    rfl
  rw [← Matrix.kronecker, hslice]
  rw [CPTPOp.tensorPower_succ]
  refine Eq.trans (CPTPOp.prod_map_kronecker_apply N (N.tensorPower n) _ _ _ _ _ _) ?_
  simp [-CPTPOp.id_map, Matrix.kroneckerMap_apply,
    MState.tensorPowerBipartiteSuccEquiv]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_left_apply_slice]

theorem hypothesisTestingOutputState_tensorPowerBipartite
    (N : CPTPMap a b) (psi : Ket (a × a)) (n : ℕ) :
      (N.tensorPower n).hypothesisTestingOutputState (psi.tensorPowerBipartite n) =
        (N.hypothesisTestingOutputState psi).tensorPowerBipartite n := by
  induction n with
  | zero =>
      exact MState.prod_punit_ext _ _
  | succ n ih =>
      have ih_state :
          (((CPTPOp.id (dIn := QIT.TensorPower a n)).prod (N.tensorPower n))
              (psi.state.tensorPowerBipartite n)) =
            (N.hypothesisTestingOutputState psi).tensorPowerBipartite n := by
        rw [← Ket.tensorPowerBipartite_state psi n]
        exact ih
      rw [CPTPOp.hypothesisTestingOutputState, Ket.tensorPowerBipartite_state]
      rw [MState.tensorPowerBipartite_succ]
      rw [CPTPOp.applyState_hypothesisTensor_succ_reindex]
      rw [ih_state]
      change ((N.hypothesisTestingOutputState psi).prod
          ((N.hypothesisTestingOutputState psi).tensorPowerBipartite n)).reindex
        (MState.tensorPowerBipartiteSuccEquiv a b n) =
          (N.hypothesisTestingOutputState psi).tensorPowerBipartite (n + 1)
      rw [← MState.tensorPowerBipartite_succ]

theorem hypothesisTestingOutputState_tensorPowerBipartite_posDef
    (N : CPTPMap a b) (psi : Ket (a × a))
    (homega : (N.hypothesisTestingOutputState psi).m.PosDef) (n : ℕ) :
    ((N.tensorPower n).hypothesisTestingOutputState
      (psi.tensorPowerBipartite n)).m.PosDef := by
  rw [CPTPOp.hypothesisTestingOutputState_tensorPowerBipartite]
  exact MState.tensorPowerBipartite_posDef (N.hypothesisTestingOutputState psi) homega n

theorem hypothesisTestingOutputState_tensorPowerBipartite_traceRight_posDef
    (N : CPTPMap a b) (psi : Ket (a × a))
    (hR : (N.hypothesisTestingOutputState psi).traceRight.m.PosDef) (n : ℕ) :
    ((N.tensorPower n).hypothesisTestingOutputState
      (psi.tensorPowerBipartite n)).traceRight.m.PosDef := by
  rw [CPTPOp.hypothesisTestingOutputState_tensorPowerBipartite]
  exact MState.tensorPowerBipartite_traceRight_posDef
    (N.hypothesisTestingOutputState psi) hR n

theorem hypothesisTestingOutputState_tensorPowerBipartite_traceLeft_posDef
    (N : CPTPMap a b) (psi : Ket (a × a))
    (hB : (N.hypothesisTestingOutputState psi).traceLeft.m.PosDef) (n : ℕ) :
    ((N.tensorPower n).hypothesisTestingOutputState
      (psi.tensorPowerBipartite n)).traceLeft.m.PosDef := by
  rw [CPTPOp.hypothesisTestingOutputState_tensorPowerBipartite]
  exact MState.tensorPowerBipartite_traceLeft_posDef
    (N.hypothesisTestingOutputState psi) hB n

theorem inputBarPetzRenyiMutualInformation_tensorPowerBipartite
    (N : CPTPMap a b) (psi : Ket (a × a))
    (homega : (N.hypothesisTestingOutputState psi).m.PosDef)
    (hR : (N.hypothesisTestingOutputState psi).traceRight.m.PosDef)
    (hB : (N.hypothesisTestingOutputState psi).traceLeft.m.PosDef)
    (alphaR : ℝ) (halpha_pos : 0 < alphaR) (halpha_ne_one : alphaR ≠ 1)
    (n : ℕ) :
    (N.tensorPower n).inputBarPetzRenyiMutualInformation
        (psi.tensorPowerBipartite n)
        (N.hypothesisTestingOutputState_tensorPowerBipartite_posDef
          psi homega n)
        (N.hypothesisTestingOutputState_tensorPowerBipartite_traceRight_posDef
          psi hR n)
        (N.hypothesisTestingOutputState_tensorPowerBipartite_traceLeft_posDef
          psi hB n)
        alphaR halpha_pos halpha_ne_one =
      (n : ℝ) *
        N.inputBarPetzRenyiMutualInformation psi homega hR hB
          alphaR halpha_pos halpha_ne_one := by
  unfold CPTPOp.inputBarPetzRenyiMutualInformation
  calc
    ((N.tensorPower n).hypothesisTestingOutputState
        (psi.tensorPowerBipartite n)).barPetzRenyiMutualInformation
        _ _ _ alphaR halpha_pos halpha_ne_one =
      (((N.hypothesisTestingOutputState psi).tensorPowerBipartite n).barPetzRenyiMutualInformation
          _ _ _ alphaR halpha_pos halpha_ne_one) := by
        exact MState.barPetzRenyiMutualInformation_congr
          (CPTPOp.hypothesisTestingOutputState_tensorPowerBipartite N psi n)
          _ _ _
          ((N.hypothesisTestingOutputState psi).tensorPowerBipartite_posDef homega n)
          ((N.hypothesisTestingOutputState psi).tensorPowerBipartite_traceRight_posDef hR n)
          ((N.hypothesisTestingOutputState psi).tensorPowerBipartite_traceLeft_posDef hB n)
          alphaR halpha_pos halpha_ne_one
    _ =
      (n : ℝ) *
        (N.hypothesisTestingOutputState psi).barPetzRenyiMutualInformation
          homega hR hB alphaR halpha_pos halpha_ne_one := by
        exact MState.barPetzRenyiMutualInformation_tensorPowerBipartite
          (N.hypothesisTestingOutputState psi) homega hR hB
          alphaR halpha_pos halpha_ne_one n

theorem barPetzRenyiMutualInformation_tensorPower_lower_bound
    (N : CPTPMap a b) {n : ℕ} (hn : 0 < n)
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
        N.hypothesisTestingOutputState_tensorPowerBipartite_traceRight_posDef
          psi hR n,
        N.hypothesisTestingOutputState_tensorPowerBipartite_traceLeft_posDef
          psi hB n,
        ?_⟩
      exact (CPTPOp.inputBarPetzRenyiMutualInformation_tensorPowerBipartite
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

end CPTPOp

end
