/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.StateMerging.DirectProtocol
public import QuantumLib.QIT.OneShot.SmoothNormalizedExtension

/-!
# Operational FQSW-to-state-merging bridge

This module proves that exact finite-dimensional teleportation transports the
physical FQSW output without changing it, up to the declared register
reindexing. It then converts the FQSW normalized trace-distance error into the
state-merging squared-fidelity error by Fuchs--van de Graaf.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u v w x y p u₁ v₁

noncomputable section

private def fqswTeleportationCoreInputEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    (((q × e) × (s × r)) × (q × q)) ≃
      ((((q × q) × e) × (s × q)) × r) where
  toFun t := ((((t.1.1.1, t.2.1), t.1.1.2), (t.1.2.1, t.2.2)), t.1.2.2)
  invFun t := (((t.1.1.1.1, t.1.1.2), (t.1.2.1, t.2)),
    (t.1.1.1.2, t.1.2.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationCoreOutputEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    ((q × e) × (s × r)) ≃ ((e × (q × s)) × r) where
  toFun t := ((t.1.2, (t.1.1, t.2.1)), t.2.2)
  invFun t := ((t.1.2.1, t.1.1), (t.1.2.2, t.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationToReferenceEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    ((q × e) × (s × r)) ≃ ((e × (s × r)) × q) where
  toFun t := ((t.1.2, t.2), t.1.1)
  invFun t := ((t.2, t.1.1), t.1.2)
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationFromReferenceEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    ((e × (s × r)) × q) ≃ ((e × (q × s)) × r) where
  toFun t := ((t.1.1, (t.2, t.1.2.1)), t.1.2.2)
  invFun t := ((t.1.1, (t.1.2.2, t.2)), t.1.2.1)
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private theorem fqswSum_pair_single
    {a : Type x} {b : Type y} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (i : a) (j : b) (f : a → b → ℂ) :
    (∑ x : a, ∑ y : b, if x = i ∧ y = j then f x y else 0) = f i j := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro y _ hy
      simp [hy]
    · simp
  · intro x _ hx
    simp [hx]
  · simp

private theorem fqswSum_four_pair_single
    {a : Type x} {b : Type y} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (i j : b → a) (f : a → a → b → b → ℂ) :
    (∑ x : a, ∑ y : a, ∑ u : b, ∑ v : b,
      if x = i u ∧ y = j v then f x y u v else 0) =
      ∑ u : b, ∑ v : b, f (i u) (j v) u v := by
  calc
    _ = ∑ x : a, ∑ u : b, ∑ y : a, ∑ v : b,
          if x = i u ∧ y = j v then f x y u v else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
    _ = ∑ u : b, ∑ x : a, ∑ y : a, ∑ v : b,
          if x = i u ∧ y = j v then f x y u v else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ u : b, ∑ x : a, ∑ v : b, ∑ y : a,
          if x = i u ∧ y = j v then f x y u v else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
    _ = ∑ u : b, ∑ v : b, ∑ x : a, ∑ y : a,
          if x = i u ∧ y = j v then f x y u v else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        exact fqswSum_pair_single (i u) (j v) _

private def fqswTeleportationSpectatorInputEquiv (q : Type x) (e : Type y) (s : Type v) :
    (((q × q) × e) × (s × q)) ≃
      (((q × q) × (e × s)) × q) where
  toFun t := ((t.1.1, (t.1.2, t.2.1)), t.2.2)
  invFun t := ((t.1.1, t.1.2.1), (t.1.2.2, t.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationSpectatorOutputEquiv (q : Type x) (e : Type y) (s : Type v) :
    ((PUnit.{x + 1} × (e × s)) × q) ≃ (e × (q × s)) where
  toFun t := (t.1.2.1, (t.2, t.1.2.2))
  invFun t := ((PUnit.unit, (t.1, t.2.2)), t.2.1)
  left_inv := by intro t; cases t.1.1; rfl
  right_inv := by intro t; rfl

private theorem fqswTeleportation_spectators_channel
    (q : Type x) (e : Type y) (s : Type v)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    [Fintype s] [DecidableEq s] :
    (fqswStateMergingTeleportationLOCC q e s).toChannel =
      (CPTPOp.reindex (fqswTeleportationSpectatorOutputEquiv q e s)) ∘ₘ
        (((teleportationLOCC q).prodIdRight (R := e × s)).toChannel ∘ₘ
          (CPTPOp.reindex (fqswTeleportationSpectatorInputEquiv q e s))) := by
  refine CPTPOp.ext_map ?_
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    (fqswStateMergingTeleportationLOCC q e s).toChannel.map X]
  rw [MatrixMap.map_eq_sum_single
    ((CPTPOp.reindex (fqswTeleportationSpectatorOutputEquiv q e s)) ∘ₘ
      (((teleportationLOCC q).prodIdRight (R := e × s)).toChannel ∘ₘ
        (CPTPOp.reindex (fqswTeleportationSpectatorInputEquiv q e s)))).map X]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [fqswStateMergingTeleportationLOCC,
    OneWayLOCC.ofFiniteInstrument_toChannel_map,
    OneWayLOCC.prodIdRight_toChannel,
    fqswStateMergingTeleportationAliceInstrument,
    fqswStateMergingTeleportationBobChannel,
    FiniteInstrument.postcompChannel_branch,
    FiniteInstrument.prodIdRight_branch,
    teleportationBellInstrument_branch,
    CPTPOp.compose_map, LinearMap.comp_apply, LinearMap.sum_apply]
  simp_rw [CPTPOp.reindex_map_single]
  simp only [show Matrix.single i j (1 : ℂ) =
      Matrix.single i.1 j.1 (1 : ℂ) ⊗ₖ
        Matrix.single i.2 j.2 (1 : ℂ) by
    exact single_prod_eq_kronecker_single _ _ _ _]
  simp only [MatrixMap.kron_map_of_kron_state]
  have hAlice : Matrix.single i.1 j.1 (1 : ℂ) =
      Matrix.single i.1.1 j.1.1 (1 : ℂ) ⊗ₖ
        Matrix.single i.1.2 j.1.2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  have hBob : Matrix.single i.2 j.2 (1 : ℂ) =
      Matrix.single i.2.1 j.2.1 (1 : ℂ) ⊗ₖ
        Matrix.single i.2.2 j.2.2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  have hLift :
      Matrix.single ((i.1.1, i.2.2), (i.1.2, i.2.1))
          ((j.1.1, j.2.2), (j.1.2, j.2.1)) (1 : ℂ) =
        Matrix.single (i.1.1, i.2.2) (j.1.1, j.2.2) (1 : ℂ) ⊗ₖ
          Matrix.single (i.1.2, i.2.1) (j.1.2, j.2.1) (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  have hBase :
      Matrix.single (i.1.1, i.2.2) (j.1.1, j.2.2) (1 : ℂ) =
        Matrix.single i.1.1 j.1.1 (1 : ℂ) ⊗ₖ
          Matrix.single i.2.2 j.2.2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hAlice]
  rw [hBob]
  have hInI :
      (prodABCToACBEquiv (q × q) q (e × s)).symm
          (fqswTeleportationSpectatorInputEquiv q e s i) =
        ((i.1.1, i.2.2), (i.1.2, i.2.1)) := rfl
  have hInJ :
      (prodABCToACBEquiv (q × q) q (e × s)).symm
          (fqswTeleportationSpectatorInputEquiv q e s j) =
        ((j.1.1, j.2.2), (j.1.2, j.2.1)) := rfl
  rw [hInI, hInJ]
  rw [hLift]
  rw [CPTPOp.prod_map, MatrixMap.kron_map_of_kron_state]
  simp only [CPTPOp.id_map, LinearMap.id_apply]
  rw [teleportationLOCC_toChannel_map, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply]
  simp_rw [hBase]
  simp_rw [MatrixMap.kron_map_of_kron_state]
  simp_rw [CPTPOp.prod_map, MatrixMap.kron_map_of_kron_state]
  simp only [CPTPOp.id_map, LinearMap.id_apply]
  simp_rw [CPTPOp.reindex_map]
  ext k l
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
  by_cases hiE : i.1.2 = k.1
  · by_cases hjE : j.1.2 = l.1
    · by_cases hiS : i.2.1 = k.2.2
      · by_cases hjS : j.2.1 = l.2.2
        · simp [hiE, hjE, hiS, hjS, fqswTeleportationSpectatorOutputEquiv,
            prodABCToACBEquiv, Equiv.punitProd,
            Equiv.prodComm]
          simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
        · simp [hiE, hjE, hiS, hjS, fqswTeleportationSpectatorOutputEquiv,
            prodABCToACBEquiv, Equiv.punitProd,
            Equiv.prodComm]
      · simp [hiE, hjE, hiS, fqswTeleportationSpectatorOutputEquiv,
          prodABCToACBEquiv, Equiv.punitProd,
          Equiv.prodComm]
    · simp [hiE, hjE, fqswTeleportationSpectatorOutputEquiv,
        prodABCToACBEquiv, Equiv.punitProd,
        Equiv.prodComm, Matrix.single_apply]
  · simp [hiE, fqswTeleportationSpectatorOutputEquiv, prodABCToACBEquiv,
      Equiv.punitProd, Equiv.prodComm,
      Matrix.single_apply]

private def fqswTeleportationResourceInputEquiv (q : Type x) (ref : Type y) :
    ((ref × q) × (q × q)) ≃ (((q × q) × ref) × q) where
  toFun t := (((t.1.2, t.2.1), t.1.1), t.2.2)
  invFun t := ((t.1.2, t.1.1.1), (t.1.1.2, t.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationResourceOutputEquiv (q : Type x) (ref : Type y) :
    ((PUnit.{x + 1} × ref) × q) ≃ (ref × q) where
  toFun t := (t.1.2, t.2)
  invFun t := ((PUnit.unit, t.1), t.2)
  left_inv := by intro t; cases t.1.1; rfl
  right_inv := by intro t; rfl

private theorem fqswTeleportation_liftedResource_preserves
    (q : Type x) (ref : Type y)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype ref] [DecidableEq ref]
    (rho : MState (ref × q)) :
    ((CPTPOp.reindex (fqswTeleportationResourceOutputEquiv q ref))
      (((teleportationLOCC q).prodIdRight (R := ref)).toChannel
        ((rho.prod (teleportationEntanglementResource q).state).reindex
          (fqswTeleportationResourceInputEquiv q ref)))) = rho := by
  have htele := teleportationLOCCResourceChannel_preserves_reference q ref rho
  calc
    _ = ((CPTPOp.id (dIn := ref)).prod
          (teleportationLOCCResourceChannel q)) rho := by
      rw [OneWayLOCC.prodIdRight_toChannel]
      simp only [CPTPOp.compose_eq, CPTPOp.reindex_applyState]
      apply MState.ext
      simp only [CPTPOp.mat_coe_eq_apply_mat, MState.reindex_matrix,
        MState.prod_m, teleportationLOCCResourceChannel]
      funext i j
      rcases i with ⟨ri, qi⟩
      rcases j with ⟨rj, qj⟩
      simp only [Matrix.submatrix_apply, fqswTeleportationResourceInputEquiv,
        fqswTeleportationResourceOutputEquiv, prodABCToACBEquiv]
      simp only [CPTPOp.prod_map, MatrixMap.kron_apply,
        CPTPOp.compose_map, LinearMap.comp_apply,
        CPTPOp.id_map, LinearMap.id_apply]
      simp_rw [teleportationAppendResourceChannel_map]
      simp_rw [CPTPOp.reindex_map]
      simp [Equiv.prodAssoc, Equiv.punitProd,
        Matrix.single_apply]
      rw [fqswSum_pair_single ri rj]
      simp_rw [fqswSum_pair_single ri rj]
      have hPhi (m m' : q) :
          (∑ result : TeleportationOutcome q,
              MatrixMap.kron
                (MatrixMap.traceEffectToUnit
                  ((generalizedBellPOVM q).effects result))
                (teleportationCorrection q result).map)
              ((Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
                (Matrix.single m m' (1 : ℂ))
                (rankOneMatrix
                  (teleportationEntanglementResource q).ket.vec)).submatrix
                    (fun x => (x.1.1, x.1.2, x.2))
                    (fun x => (x.1.1, x.1.2, x.2)))
              (PUnit.unit, qi) (PUnit.unit, qj) =
            ∑ full : (q × q) × q, ∑ full' : (q × q) × q,
              (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
                (Matrix.single m m' (1 : ℂ))
                (rankOneMatrix
                  (teleportationEntanglementResource q).ket.vec)).submatrix
                    (fun x => (x.1.1, x.1.2, x.2))
                    (fun x => (x.1.1, x.1.2, x.2)) full full' *
                (∑ result : TeleportationOutcome q,
                    MatrixMap.kron
                      (MatrixMap.traceEffectToUnit
                        ((generalizedBellPOVM q).effects result))
                      (teleportationCorrection q result).map)
                  (Matrix.single full full' (1 : ℂ))
                  (PUnit.unit, qi) (PUnit.unit, qj) := by
        rw [MatrixMap.map_eq_sum_single]
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        rfl
      have hInput (m m' : q) (full full' : (q × q) × q) :
          (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
            (Matrix.single m m' (1 : ℂ))
            (rankOneMatrix
              (teleportationEntanglementResource q).ket.vec)).submatrix
                (fun x => (x.1.1, x.1.2, x.2))
                (fun x => (x.1.1, x.1.2, x.2)) full full' =
            if m = full.1.1 ∧ m' = full'.1.1 then
              (teleportationEntanglementResource q).ket.vec
                  (full.1.2, full.2) *
                star ((teleportationEntanglementResource q).ket.vec
                  (full'.1.2, full'.2))
            else 0 := by
        simp [Matrix.kroneckerMap_apply, Matrix.submatrix_apply,
          rankOneMatrix_apply, Matrix.single_apply]
      symm
      calc
        _ = ∑ m : q, ∑ m' : q, rho.m (ri, m) (rj, m') *
              (∑ full : (q × q) × q,
                ∑ full' : (q × q) × q,
                  (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
                    (Matrix.single m m' (1 : ℂ))
                    (rankOneMatrix
                      (teleportationEntanglementResource q).ket.vec)).submatrix
                        (fun x => (x.1.1, x.1.2, x.2))
                        (fun x => (x.1.1, x.1.2, x.2)) full full' *
                    (∑ result : TeleportationOutcome q,
                        MatrixMap.kron
                          (MatrixMap.traceEffectToUnit
                            ((generalizedBellPOVM q).effects result))
                          (teleportationCorrection q result).map)
                      (Matrix.single full full' (1 : ℂ))
                        (PUnit.unit, qi) (PUnit.unit, qj)) := by
            apply Finset.sum_congr rfl
            intro m _
            apply Finset.sum_congr rfl
            intro m' _
            apply congrArg
              (fun z : ℂ => rho.m (ri, m) (rj, m') * z)
            simpa only [LinearMap.sum_apply, TeleportationEntanglementResource.state,
              Ket.state_matrix] using hPhi m m'
        _ = _ := by
          simp_rw [hInput]
          simp only [Finset.mul_sum, mul_ite, ite_mul, mul_zero, zero_mul]
          calc
            _ = ∑ full : (q × q) × q,
                  ∑ full' : (q × q) × q,
                    rho.m (ri, full.1.1) (rj, full'.1.1) *
                      (((teleportationEntanglementResource q).ket.vec
                          (full.1.2, full.2) *
                        star ((teleportationEntanglementResource q).ket.vec
                          (full'.1.2, full'.2))) *
                        (∑ c : TeleportationOutcome q,
                            MatrixMap.kron
                              (MatrixMap.traceEffectToUnit
                                ((generalizedBellPOVM q).effects c))
                              (teleportationCorrection q c).map)
                          (Matrix.single full full' (1 : ℂ))
                            (PUnit.unit, qi) (PUnit.unit, qj)) :=
                fqswSum_four_pair_single
                  (fun full : (q × q) × q => full.1.1)
                  (fun full : (q × q) × q => full.1.1)
                  (fun m m' full full' =>
                    rho.m (ri, m) (rj, m') *
                      (((teleportationEntanglementResource q).ket.vec
                          (full.1.2, full.2) *
                        star ((teleportationEntanglementResource q).ket.vec
                          (full'.1.2, full'.2))) *
                        (∑ c : TeleportationOutcome q,
                            MatrixMap.kron
                              (MatrixMap.traceEffectToUnit
                                ((generalizedBellPOVM q).effects c))
                              (teleportationCorrection q c).map)
                          (Matrix.single full full' (1 : ℂ))
                            (PUnit.unit, qi) (PUnit.unit, qj)))
            _ = _ := by
              apply Finset.sum_congr rfl
              intro full _
              apply Finset.sum_congr rfl
              intro full' _
              simp only [teleportationEntanglementResource_state, Ket.state_matrix,
                rankOneMatrix_apply, LinearMap.sum_apply, mul_assoc]
    _ = rho := htele

private def fqswTeleportationCoreToLiftInputEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    ((((q × q) × e) × (s × q)) × r) ≃
      (((q × q) × (e × (s × r))) × q) where
  toFun t := ((t.1.1.1, (t.1.1.2, (t.1.2.1, t.2))), t.1.2.2)
  invFun t := (((t.1.1, t.1.2.1), (t.1.2.2.1, t.2)), t.1.2.2.2)
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationLiftToCoreOutputEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    ((PUnit.{x + 1} × (e × (s × r))) × q) ≃
      ((e × (q × s)) × r) where
  toFun t := ((t.1.2.1, (t.2, t.1.2.2.1)), t.1.2.2.2)
  invFun t := ((PUnit.unit, (t.1.1, (t.1.2.2, t.2))), t.1.2.1)
  left_inv := by intro t; cases t.1.1; rfl
  right_inv := by intro t; rfl

private theorem fqswTeleportation_coreChannel
    (q : Type x) (e : Type y) (s : Type v) (r : Type w)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    [Fintype s] [DecidableEq s]
    [Fintype r] [DecidableEq r] :
    (fqswStateMergingTeleportationLOCC q e s).toChannel.prod
        (CPTPOp.id (dIn := r)) =
      (CPTPOp.reindex (fqswTeleportationLiftToCoreOutputEquiv q e s r)) ∘ₘ
        (((teleportationLOCC q).prodIdRight
          (R := e × (s × r))).toChannel ∘ₘ
            (CPTPOp.reindex (fqswTeleportationCoreToLiftInputEquiv q e s r))) := by
  rw [fqswTeleportation_spectators_channel]
  rw [OneWayLOCC.prodIdRight_toChannel,
    OneWayLOCC.prodIdRight_toChannel]
  refine CPTPOp.ext_map ?_
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single]
  rw [MatrixMap.map_eq_sum_single]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  conv_lhs =>
    rw [show Matrix.single i j (1 : ℂ) =
        Matrix.single i.1 j.1 (1 : ℂ) ⊗ₖ
          Matrix.single i.2 j.2 (1 : ℂ) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  simp only [CPTPOp.prod_map]
  rw [MatrixMap.kron_map_of_kron_state]
  simp only [CPTPOp.compose_map, LinearMap.comp_apply, CPTPOp.prod_map]
  simp only [CPTPOp.id_map, LinearMap.id_apply]
  simp only [CPTPOp.reindex_map_single]
  have hLhsI :
      (prodABCToACBEquiv (q × q) q (e × s)).symm
          (fqswTeleportationSpectatorInputEquiv q e s i.1) =
        ((i.1.1.1, i.1.2.2), (i.1.1.2, i.1.2.1)) := rfl
  have hLhsJ :
      (prodABCToACBEquiv (q × q) q (e × s)).symm
          (fqswTeleportationSpectatorInputEquiv q e s j.1) =
        ((j.1.1.1, j.1.2.2), (j.1.1.2, j.1.2.1)) := rfl
  have hRhsI :
      (prodABCToACBEquiv (q × q) q
          (e × (s × r))).symm
          (fqswTeleportationCoreToLiftInputEquiv q e s r i) =
        ((i.1.1.1, i.1.2.2), (i.1.1.2, (i.1.2.1, i.2))) := rfl
  have hRhsJ :
      (prodABCToACBEquiv (q × q) q
          (e × (s × r))).symm
          (fqswTeleportationCoreToLiftInputEquiv q e s r j) =
        ((j.1.1.1, j.1.2.2), (j.1.1.2, (j.1.2.1, j.2))) := rfl
  rw [hLhsI, hLhsJ, hRhsI, hRhsJ]
  have hLhsInput :
      Matrix.single
          ((i.1.1.1, i.1.2.2), (i.1.1.2, i.1.2.1))
          ((j.1.1.1, j.1.2.2), (j.1.1.2, j.1.2.1))
          (1 : ℂ) =
        Matrix.single (i.1.1.1, i.1.2.2)
            (j.1.1.1, j.1.2.2) (1 : ℂ) ⊗ₖ
          Matrix.single (i.1.1.2, i.1.2.1)
            (j.1.1.2, j.1.2.1) (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  have hRhsInput :
      Matrix.single
          ((i.1.1.1, i.1.2.2), (i.1.1.2, (i.1.2.1, i.2)))
          ((j.1.1.1, j.1.2.2), (j.1.1.2, (j.1.2.1, j.2)))
          (1 : ℂ) =
        Matrix.single (i.1.1.1, i.1.2.2)
            (j.1.1.1, j.1.2.2) (1 : ℂ) ⊗ₖ
          Matrix.single (i.1.1.2, (i.1.2.1, i.2))
            (j.1.1.2, (j.1.2.1, j.2)) (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhsInput, hRhsInput]
  simp_rw [MatrixMap.kron_map_of_kron_state]
  simp only [LinearMap.id_apply]
  simp_rw [CPTPOp.reindex_map]
  ext k l
  simp [fqswTeleportationSpectatorOutputEquiv,
    fqswTeleportationLiftToCoreOutputEquiv,
    prodABCToACBEquiv,
    Matrix.kroneckerMap_apply, Matrix.single_apply]
  split_ifs <;> simp_all

set_option maxRecDepth 4000 in
private theorem fqswTeleportation_core_preserves
    (q : Type x) (e : Type y) (s : Type v) (r : Type w)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    [Fintype s] [DecidableEq s]
    [Fintype r] [DecidableEq r]
    (rho : MState ((q × e) × (s × r))) :
    (((fqswStateMergingTeleportationLOCC q e s).toChannel.prod
          (CPTPOp.id (dIn := r)))
      ((rho.prod (teleportationEntanglementResource q).state).reindex
        (fqswTeleportationCoreInputEquiv q e s r))) =
      rho.reindex (fqswTeleportationCoreOutputEquiv q e s r) := by
  have hinput :
      (((rho.prod (teleportationEntanglementResource q).state).reindex
          (fqswTeleportationCoreInputEquiv q e s r)).reindex
            (fqswTeleportationCoreToLiftInputEquiv q e s r)) =
        (((rho.reindex (fqswTeleportationToReferenceEquiv q e s r)).prod
            (teleportationEntanglementResource q).state).reindex
              (fqswTeleportationResourceInputEquiv q (e × (s × r)))) := by
    apply MState.ext
    simp only [MState.reindex_matrix, MState.prod_m]
    ext x y
    rfl
  have htele := fqswTeleportation_liftedResource_preserves q (e × (s × r))
    (rho.reindex (fqswTeleportationToReferenceEquiv q e s r))
  rw [fqswTeleportation_coreChannel]
  simp only [CPTPOp.compose_eq, CPTPOp.reindex_applyState]
  rw [hinput]
  calc
    _ = ((MState.reindex
          (((teleportationLOCC q).prodIdRight
            (R := e × (s × r))).toChannel
              (((rho.reindex (fqswTeleportationToReferenceEquiv q e s r)).prod
                (teleportationEntanglementResource q).state).reindex
                  (fqswTeleportationResourceInputEquiv q (e × (s × r)))))
          (fqswTeleportationResourceOutputEquiv q (e × (s × r)))).reindex
            (fqswTeleportationFromReferenceEquiv q e s r)) := by
        apply MState.ext
        simp only [MState.reindex_matrix]
        ext x y
        rfl
    _ = (rho.reindex (fqswTeleportationToReferenceEquiv q e s r)).reindex
          (fqswTeleportationFromReferenceEquiv q e s r) := by
        simpa only [CPTPOp.reindex_applyState] using congrArg
          (fun tau =>
            MState.reindex tau (fqswTeleportationFromReferenceEquiv q e s r)) htele
    _ = rho.reindex (fqswTeleportationCoreOutputEquiv q e s r) := by
        apply MState.ext
        simp only [MState.reindex_matrix]
        ext x y
        rfl

private theorem fqswProdCompId
    {alpha : Type u} {beta : Type v} {gamma : Type w} {ref : Type x}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma]
    [Fintype ref] [DecidableEq ref]
    (Phi : CPTPMap beta gamma) (Psi : CPTPMap alpha beta) :
    (Phi ∘ₘ Psi).prod (CPTPOp.id (dIn := ref)) =
      (Phi.prod (CPTPOp.id (dIn := ref))) ∘ₘ
        (Psi.prod (CPTPOp.id (dIn := ref))) := by
  rw [CPTPOp.prod_comp_prod, CPTPOp.id_compose]

private def fqswStateMergingPreparationInputEquiv
    (a : Type u) (b : Type v) (r : Type w) (q : Type x) :
    ((a × (b × r)) × (q × q)) ≃
      (((a × q) × (b × q)) × r) where
  toFun t := (((t.1.1, t.2.1), (t.1.2.1, t.2.2)), t.1.2.2)
  invFun t := ((t.1.1.1, (t.1.2.1, t.2)), (t.1.1.2, t.1.2.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private theorem fqswStateMergingPreparationChannel
    {a : Type u} {b : Type v} {r : Type w} {q : Type x} {e : Type y}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (Phi : CPTPMap a (q × e)) :
    ((((CPTPOp.reindex (prodABCToACBEquiv q e q)) ∘ₘ
          (Phi.prod (CPTPOp.id (dIn := q)))).prod
        (CPTPOp.id (dIn := b × q))).prod (CPTPOp.id (dIn := r))) ∘ₘ
          (CPTPOp.reindex (fqswStateMergingPreparationInputEquiv a b r q)) =
      (CPTPOp.reindex (fqswTeleportationCoreInputEquiv q e b r)) ∘ₘ
        ((Phi.prod (CPTPOp.id (dIn := b × r))).prod
          (CPTPOp.id (dIn := q × q))) := by
  refine CPTPOp.ext_map ?_
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single]
  rw [MatrixMap.map_eq_sum_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [CPTPOp.compose_map, CPTPOp.prod_map, LinearMap.comp_apply]
  simp_rw [CPTPOp.reindex_map_single]
  simp_rw [CPTPOp.reindex_map]
  have hLhs0 :
      Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i)
          (fqswStateMergingPreparationInputEquiv a b r q j) (1 : ℂ) =
        Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1
            (fqswStateMergingPreparationInputEquiv a b r q j).1 (1 : ℂ) ⊗ₖ
          Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).2
            (fqswStateMergingPreparationInputEquiv a b r q j).2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs0, MatrixMap.kron_map_of_kron_state]
  have hLhs1 :
      Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1
          (fqswStateMergingPreparationInputEquiv a b r q j).1 (1 : ℂ) =
        Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1.1
            (fqswStateMergingPreparationInputEquiv a b r q j).1.1 (1 : ℂ) ⊗ₖ
          Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1.2
            (fqswStateMergingPreparationInputEquiv a b r q j).1.2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs1, MatrixMap.kron_map_of_kron_state]
  have hLhs2 :
      Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1.1
          (fqswStateMergingPreparationInputEquiv a b r q j).1.1 (1 : ℂ) =
        Matrix.single i.1.1 j.1.1 (1 : ℂ) ⊗ₖ
          Matrix.single i.2.1 j.2.1 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs2]
  simp only [LinearMap.comp_apply]
  rw [MatrixMap.kron_map_of_kron_state]
  have hRhs0 : Matrix.single i j (1 : ℂ) =
      Matrix.single i.1 j.1 (1 : ℂ) ⊗ₖ
        Matrix.single i.2 j.2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hRhs0]
  rw [MatrixMap.kron_map_of_kron_state]
  have hRhs1 : Matrix.single i.1 j.1 (1 : ℂ) =
      Matrix.single i.1.1 j.1.1 (1 : ℂ) ⊗ₖ
        Matrix.single i.1.2 j.1.2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hRhs1]
  rw [MatrixMap.kron_map_of_kron_state]
  simp only [CPTPOp.id_map, LinearMap.id_apply]
  ext k l
  rcases i with ⟨⟨ia, ⟨ib, ir⟩⟩, ⟨iq₁, iq₂⟩⟩
  rcases j with ⟨⟨ja, ⟨jb, jr⟩⟩, ⟨jq₁, jq₂⟩⟩
  rcases k with ⟨⟨⟨⟨kq₁, kq₂⟩, ke⟩, ⟨kb, kq₃⟩⟩, kr⟩
  rcases l with ⟨⟨⟨⟨lq₁, lq₂⟩, le⟩, ⟨lb, lq₃⟩⟩, lr⟩
  rw [CPTPOp.reindex_map]
  simp [fqswStateMergingPreparationInputEquiv, fqswTeleportationCoreInputEquiv,
    prodABCToACBEquiv,
    Matrix.kroneckerMap_apply, Matrix.single_apply]
  split_ifs <;> simp_all

private def fqswStateMergingDecoderFinalEquiv (d : Type u) (e : Type y) (r : Type w) :
    (d × (r × e)) ≃ ((e × d) × r) where
  toFun t := ((t.2.2, t.1), t.2.1)
  invFun t := (t.1.2, (t.2, t.1.1))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private theorem fqswStateMergingDecoderChannel
    {q : Type x} {e : Type y} {s : Type v} {r : Type w} {d : Type u}
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    [Fintype s] [DecidableEq s]
    [Fintype r] [DecidableEq r]
    [Fintype d] [DecidableEq d]
    (Phi : CPTPMap (q × s) d) :
    ((((CPTPOp.id (dIn := e)).prod Phi).prod (CPTPOp.id (dIn := r))) ∘ₘ
          (CPTPOp.reindex (fqswTeleportationCoreOutputEquiv q e s r))) =
      (CPTPOp.reindex (fqswStateMergingDecoderFinalEquiv d e r)) ∘ₘ
        ((Phi.prod (CPTPOp.id (dIn := r × e))) ∘ₘ
          (CPTPOp.reindex (fqswAliceOutputToBobInputEquiv q e s r))) := by
  refine CPTPOp.ext_map ?_
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single]
  rw [MatrixMap.map_eq_sum_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [CPTPOp.compose_map, CPTPOp.prod_map, LinearMap.comp_apply]
  simp_rw [CPTPOp.reindex_map_single]
  have hLhs0 :
      Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i)
          (fqswTeleportationCoreOutputEquiv q e s r j) (1 : ℂ) =
        Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).1
            (fqswTeleportationCoreOutputEquiv q e s r j).1 (1 : ℂ) ⊗ₖ
          Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).2
            (fqswTeleportationCoreOutputEquiv q e s r j).2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs0, MatrixMap.kron_map_of_kron_state]
  have hLhs1 :
      Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).1
          (fqswTeleportationCoreOutputEquiv q e s r j).1 (1 : ℂ) =
        Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).1.1
            (fqswTeleportationCoreOutputEquiv q e s r j).1.1 (1 : ℂ) ⊗ₖ
          Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).1.2
            (fqswTeleportationCoreOutputEquiv q e s r j).1.2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs1, MatrixMap.kron_map_of_kron_state]
  have hRhs0 :
      Matrix.single (fqswAliceOutputToBobInputEquiv q e s r i)
          (fqswAliceOutputToBobInputEquiv q e s r j) (1 : ℂ) =
        Matrix.single (fqswAliceOutputToBobInputEquiv q e s r i).1
            (fqswAliceOutputToBobInputEquiv q e s r j).1 (1 : ℂ) ⊗ₖ
          Matrix.single (fqswAliceOutputToBobInputEquiv q e s r i).2
            (fqswAliceOutputToBobInputEquiv q e s r j).2 (1 : ℂ) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hRhs0, MatrixMap.kron_map_of_kron_state]
  simp only [CPTPOp.id_map, LinearMap.id_apply]
  rw [CPTPOp.reindex_map]
  ext k l
  rcases i with ⟨⟨iq, ie⟩, ⟨is, ir⟩⟩
  rcases j with ⟨⟨jq, je⟩, ⟨js, jr⟩⟩
  rcases k with ⟨⟨ke, kd⟩, kr⟩
  rcases l with ⟨⟨le, ld⟩, lr⟩
  simp [fqswTeleportationCoreOutputEquiv, fqswStateMergingDecoderFinalEquiv,
    fqswAliceOutputToBobInputEquiv,
    Matrix.kroneckerMap_apply, Matrix.single_apply]
  split_ifs <;> simp_all

private theorem fqswStateMergingDecoderFinalReindex
    {a : Type u} {b : Type v} {e : Type y} {r : Type w}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype e] [DecidableEq e]
    [Fintype r] [DecidableEq r]
    (rho : MState (((a × b) × e) × (r × e))) :
    rho.reindex (fqswStateMergingDecoderFinalEquiv ((a × b) × e) e r) =
      (rho.reindex (fqswAliceOutputToBobInputEquiv (a × b) e r e)).reindex
        (stateMergingTargetEquiv a b r e e) := by
  apply MState.ext
  simp only [MState.reindex_matrix]
  ext i j
  rfl

set_option synthInstance.maxSize 512 in
set_option maxRecDepth 4000 in
theorem FQSWBlockProtocol.toStateMergingProtocol_outputState_eq_reindex
    {a : Type u} {b : Type v} {r : Type w}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r]
    {psi : Ket ((a × b) × r)} {n : ℕ}
    {q : Type x} {e : Type y}
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (C : FQSWBlockProtocol psi n q e e) :
    C.toStateMergingProtocol.outputState =
      C.outputState.reindex
        (stateMergingTargetEquiv
          (TensorPower a n) (TensorPower b n) (TensorPower r n) e e) := by
  unfold StateMergingBlockProtocol.outputState
  change
    (C.stateMergingLOCC.toChannel.prod
        (CPTPOp.id (dIn := TensorPower r n)))
      C.toStateMergingProtocol.initialState = _
  rw [C.stateMergingLOCC_toChannel_eq_encoder_teleportation_decoder]
  rw [fqswProdCompId, fqswProdCompId]
  simp only [CPTPOp.compose_eq]
  let rhoU : MState
      ((q × e) ×
        (TensorPower b n × TensorPower r n)) :=
    (C.aliceOperation.prod
      (CPTPOp.id (dIn := TensorPower b n × TensorPower r n)))
      ((stateMergingBlockSource psi n).state.reindex
        (Equiv.prodAssoc
          (TensorPower a n) (TensorPower b n) (TensorPower r n)))
  have hprep :
      (((C.stateMergingAlicePreparation.prod
            (CPTPOp.id (dIn := TensorPower b n × q))).prod
          (CPTPOp.id (dIn := TensorPower r n)))
        C.toStateMergingProtocol.initialState) =
        ((rhoU.prod (teleportationEntanglementResource q).state).reindex
          (fqswTeleportationCoreInputEquiv q e (TensorPower b n) (TensorPower r n))) := by
    have hinitial :
        C.toStateMergingProtocol.initialState =
          (((stateMergingBlockSource psi n).state.reindex
              (Equiv.prodAssoc
                (TensorPower a n) (TensorPower b n) (TensorPower r n))).prod
            (teleportationEntanglementResource q).state).reindex
              (fqswStateMergingPreparationInputEquiv
                (TensorPower a n) (TensorPower b n) (TensorPower r n) q) := by
      simp [FQSWBlockProtocol.toStateMergingProtocol,
        StateMergingBlockProtocol.initialState,
        fqswStateMergingPreparationInputEquiv, stateMergingInputEquiv,
        Equiv.prodAssoc,
        teleportationEntanglementResource_state]
      apply MState.ext
      simp only [MState.reindex_matrix, MState.prod_m]
      ext i j
      rfl
    rw [hinitial]
    change
      (((((CPTPOp.reindex (prodABCToACBEquiv q e q)) ∘ₘ
            (C.aliceOperation.prod (CPTPOp.id (dIn := q)))).prod
          (CPTPOp.id (dIn := TensorPower b n × q))).prod
            (CPTPOp.id (dIn := TensorPower r n)))
        _) = _
    rw [← CPTPOp.reindex_applyState]
    rw [← CPTPOp.compose_eq]
    rw [fqswStateMergingPreparationChannel]
    rw [CPTPOp.compose_eq, CPTPOp.reindex_applyState,
      CPTPOp.prod_apply_prod]
    have hresource :
        (CPTPOp.id (dIn := q × q))
            (teleportationEntanglementResource q).state =
          (teleportationEntanglementResource q).state := by
      apply MState.ext
      rw [CPTPOp.mat_coe_eq_apply_mat]
      simp [CPTPOp.id_map]
    rw [hresource]
  rw [hprep]
  rw [fqswTeleportation_core_preserves]
  unfold FQSWBlockProtocol.outputState FQSWBlockProtocol.outputStateOfState
  unfold FQSWBlockProtocol.outputStateOfBlockState
  dsimp only
  dsimp only [rhoU]
  rw [← CPTPOp.reindex_applyState]
  rw [← CPTPOp.compose_eq]
  rw [fqswStateMergingDecoderChannel]
  simp only [CPTPOp.compose_eq, CPTPOp.reindex_applyState]
  rw [fqswStateMergingDecoderFinalReindex]
  have hsource :
      (stateMergingBlockSource psi n).state =
        (psi.state.tensorPower n).reindex
          (tensorPowerProdProdEquiv a b r n) := by
    rw [stateMergingBlockSource, Ket.reindex_state,
      Ket.tensorPower_state]
  rw [hsource]

namespace FQSWBlockProtocol

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : Ket ((a × b) × r)} {n : ℕ}
variable {q : Type x} {e : Type y}
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]

/-- Teleporting the FQSW message changes the source error criterion by at most
the standard Fuchs--van de Graaf factor of two. -/
theorem toStateMergingProtocol_fidelityError_le
    (C : FQSWBlockProtocol psi n q e e) :
    C.toStateMergingProtocol.fidelityError ≤ 2 * C.normalizedError := by
  unfold StateMergingBlockProtocol.fidelityError
  unfold FQSWBlockProtocol.normalizedError
  rw [C.toStateMergingProtocol_outputState_eq_reindex,
    C.toStateMergingProtocol_targetState_eq_reindex,
    MState.squaredFidelity_reindex]
  exact MState.one_sub_squaredFidelity_le_two_mul_normalizedTraceDistance
    C.outputState C.targetState

end FQSWBlockProtocol

namespace ADHWFQSWIidMixedBlockConstruction

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : Ket ((a × b) × r)} {n : ℕ}
variable {deltaTypical deltaRate epsilon : ℝ}
variable {atyp : Type p} {btyp : Type u₁} {rtyp : Type v₁}
variable {q : Type x} {e : Type y}
variable [Fintype atyp] [DecidableEq atyp]
variable [Fintype btyp] [DecidableEq btyp]
variable [Fintype rtyp] [DecidableEq rtyp]
variable [Fintype q] [DecidableEq q] [Nonempty q]
variable [Fintype e] [DecidableEq e] [Nonempty e]

/-- The concrete mixed-slack state-merging protocol inherits the realized
FQSW trace-distance error through exact teleportation. -/
theorem stateMergingProtocol_fidelityError_le
    (C : ADHWFQSWIidMixedBlockConstruction
      psi n deltaTypical deltaRate epsilon atyp btyp rtyp q e) :
    C.stateMergingProtocol.fidelityError ≤
      2 * C.physicalProtocol.normalizedError :=
  C.physicalProtocol.toStateMergingProtocol_fidelityError_le

end ADHWFQSWIidMixedBlockConstruction

end
end QIT
