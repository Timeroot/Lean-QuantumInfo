/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Protocols.StateMerging.DirectProtocol
public import QIT.OneShot.SmoothNormalizedExtension

/-!
# Operational FQSW-to-state-merging bridge

This module proves that exact finite-dimensional teleportation transports the
physical FQSW output without changing it, up to the declared register
reindexing. It then converts the FQSW normalized trace-distance error into the
state-merging squared-fidelity error by Fuchs--van de Graaf.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y p u₁ v₁

noncomputable section

private def fqswTeleportationCoreInputEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    Prod (Prod (Prod q e) (Prod s r)) (Prod q q) ≃
      Prod (Prod (Prod (Prod q q) e) (Prod s q)) r where
  toFun t := ((((t.1.1.1, t.2.1), t.1.1.2), (t.1.2.1, t.2.2)), t.1.2.2)
  invFun t := (((t.1.1.1.1, t.1.1.2), (t.1.2.1, t.2)),
    (t.1.1.1.2, t.1.2.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationCoreOutputEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    Prod (Prod q e) (Prod s r) ≃ Prod (Prod e (Prod q s)) r where
  toFun t := ((t.1.2, (t.1.1, t.2.1)), t.2.2)
  invFun t := ((t.1.2.1, t.1.1), (t.1.2.2, t.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationToReferenceEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    Prod (Prod q e) (Prod s r) ≃ Prod (Prod e (Prod s r)) q where
  toFun t := ((t.1.2, t.2), t.1.1)
  invFun t := ((t.2, t.1.1), t.1.2)
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationFromReferenceEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    Prod (Prod e (Prod s r)) q ≃ Prod (Prod e (Prod q s)) r where
  toFun t := ((t.1.1, (t.2, t.1.2.1)), t.1.2.2)
  invFun t := ((t.1.1, (t.1.2.2, t.2)), t.1.2.1)
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private theorem fqswReindexChannel_map
    {a : Type x} {b : Type y}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) (X : CMatrix a) :
    (Channel.reindex e).map X = X.submatrix e.symm e.symm := by
  ext i j
  simp [Channel.reindex, MatrixMap.ofReferenceIsometry_apply,
    ReferenceIsometry.ofEquiv, Matrix.mul_apply]
  rw [Finset.sum_eq_single (e.symm j)]
  · rw [Finset.sum_eq_single (e.symm i)]
    · simp
    · intro z _ hz
      have hne : i ≠ e z := by
        intro hi
        apply hz
        simp [hi]
      simp [hne]
    · simp
  · intro z _ hz
    have hne : j ≠ e z := by
      intro hj
      apply hz
      simp [hj]
    simp [hne]
  · simp

private theorem fqswReindexChannel_map_single
    {a : Type x} {b : Type y}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) (i j : a) :
    (Channel.reindex e).map (Matrix.single i j (1 : Complex)) =
      Matrix.single (e i) (e j) (1 : Complex) := by
  rw [fqswReindexChannel_map]
  ext k l
  simp only [Matrix.submatrix_apply, Matrix.single_apply]
  have hi : i = e.symm k ↔ e i = k := by
    constructor
    · intro h
      rw [h, e.apply_symm_apply]
    · intro h
      apply e.injective
      rw [e.apply_symm_apply, h]
  have hj : j = e.symm l ↔ e j = l := by
    constructor
    · intro h
      rw [h, e.apply_symm_apply]
    · intro h
      apply e.injective
      rw [e.apply_symm_apply, h]
  simp only [hi, hj]

private theorem fqswSum_pair_single
    {a : Type x} {b : Type y} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (i : a) (j : b) (f : a → b → Complex) :
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
    (i j : b → a) (f : a → a → b → b → Complex) :
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
    Prod (Prod (Prod q q) e) (Prod s q) ≃
      Prod (Prod (Prod q q) (Prod e s)) q where
  toFun t := ((t.1.1, (t.1.2, t.2.1)), t.2.2)
  invFun t := ((t.1.1, t.1.2.1), (t.1.2.2, t.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationSpectatorOutputEquiv (q : Type x) (e : Type y) (s : Type v) :
    Prod (Prod PUnit.{x + 1} (Prod e s)) q ≃ Prod e (Prod q s) where
  toFun t := (t.1.2.1, (t.2, t.1.2.2))
  invFun t := ((PUnit.unit, (t.1, t.2.2)), t.2.1)
  left_inv := by intro t; cases t.1.1; rfl
  right_inv := by intro t; rfl

set_option maxHeartbeats 800000 in
private theorem fqswTeleportation_spectators_channel
    (q : Type x) (e : Type y) (s : Type v)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    [Fintype s] [DecidableEq s] :
    (fqswStateMergingTeleportationLOCC q e s).toChannel =
      (Channel.reindex (fqswTeleportationSpectatorOutputEquiv q e s)).comp
        (((teleportationLOCC q).prodIdRight (R := Prod e s)).toChannel.comp
          (Channel.reindex (fqswTeleportationSpectatorInputEquiv q e s))) := by
  rw [Channel.mk.injEq]
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single
    (fqswStateMergingTeleportationLOCC q e s).toChannel.map X]
  rw [MatrixMap.map_eq_sum_single
    ((Channel.reindex (fqswTeleportationSpectatorOutputEquiv q e s)).comp
      (((teleportationLOCC q).prodIdRight (R := Prod e s)).toChannel.comp
        (Channel.reindex (fqswTeleportationSpectatorInputEquiv q e s)))).map X]
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
    Channel.comp, LinearMap.comp_apply, LinearMap.sum_apply]
  simp_rw [fqswReindexChannel_map_single]
  simp only [show Matrix.single i j (1 : Complex) =
      Matrix.kronecker (Matrix.single i.1 j.1 (1 : Complex))
        (Matrix.single i.2 j.2 (1 : Complex)) by
    exact single_prod_eq_kronecker_single _ _ _ _]
  simp only [MatrixMap.kron_apply_kronecker]
  have hAlice : Matrix.single i.1 j.1 (1 : Complex) =
      Matrix.kronecker
        (Matrix.single i.1.1 j.1.1 (1 : Complex))
        (Matrix.single i.1.2 j.1.2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  have hBob : Matrix.single i.2 j.2 (1 : Complex) =
      Matrix.kronecker
        (Matrix.single i.2.1 j.2.1 (1 : Complex))
        (Matrix.single i.2.2 j.2.2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  have hLift :
      Matrix.single ((i.1.1, i.2.2), (i.1.2, i.2.1))
          ((j.1.1, j.2.2), (j.1.2, j.2.1)) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (i.1.1, i.2.2) (j.1.1, j.2.2) (1 : Complex))
          (Matrix.single (i.1.2, i.2.1) (j.1.2, j.2.1) (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  have hBase :
      Matrix.single (i.1.1, i.2.2) (j.1.1, j.2.2) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : Complex))
          (Matrix.single i.2.2 j.2.2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hAlice]
  rw [hBob]
  have hInI :
      (loccReferenceRegroupEquiv (Prod q q) q (Prod e s)).symm
          (fqswTeleportationSpectatorInputEquiv q e s i) =
        ((i.1.1, i.2.2), (i.1.2, i.2.1)) := rfl
  have hInJ :
      (loccReferenceRegroupEquiv (Prod q q) q (Prod e s)).symm
          (fqswTeleportationSpectatorInputEquiv q e s j) =
        ((j.1.1, j.2.2), (j.1.2, j.2.1)) := rfl
  rw [hInI, hInJ]
  rw [hLift]
  rw [Channel.prod_map_kronecker]
  simp only [Channel.idChannel_map_eq_linearMap_id, LinearMap.id_apply]
  rw [teleportationLOCC_toChannel_map, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply]
  simp_rw [hBase]
  simp_rw [MatrixMap.kron_apply_kronecker]
  simp_rw [Channel.prod_map_kronecker]
  simp only [Channel.idChannel_map_eq_linearMap_id, LinearMap.id_apply]
  simp_rw [fqswReindexChannel_map]
  ext k l
  simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  by_cases hiE : i.1.2 = k.1
  · by_cases hjE : j.1.2 = l.1
    · by_cases hiS : i.2.1 = k.2.2
      · by_cases hjS : j.2.1 = l.2.2
        · simp [hiE, hjE, hiS, hjS, fqswTeleportationSpectatorOutputEquiv,
            loccReferenceRegroupEquiv, fqswStateMergingAliceOutputEquiv,
            Equiv.prodComm]
          simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
        · simp [hiE, hjE, hiS, hjS, fqswTeleportationSpectatorOutputEquiv,
            loccReferenceRegroupEquiv, fqswStateMergingAliceOutputEquiv,
            Equiv.prodComm]
      · simp [hiE, hjE, hiS, fqswTeleportationSpectatorOutputEquiv,
          loccReferenceRegroupEquiv, fqswStateMergingAliceOutputEquiv,
          Equiv.prodComm]
    · simp [hiE, hjE, fqswTeleportationSpectatorOutputEquiv,
        loccReferenceRegroupEquiv, fqswStateMergingAliceOutputEquiv,
        Equiv.prodComm, Matrix.single_apply]
  · simp [hiE, fqswTeleportationSpectatorOutputEquiv, loccReferenceRegroupEquiv,
      fqswStateMergingAliceOutputEquiv, Equiv.prodComm,
      Matrix.single_apply]

private def fqswTeleportationResourceInputEquiv (q : Type x) (ref : Type y) :
    Prod (Prod ref q) (Prod q q) ≃ Prod (Prod (Prod q q) ref) q where
  toFun t := (((t.1.2, t.2.1), t.1.1), t.2.2)
  invFun t := ((t.1.2, t.1.1.1), (t.1.1.2, t.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationResourceOutputEquiv (q : Type x) (ref : Type y) :
    Prod (Prod PUnit.{x + 1} ref) q ≃ Prod ref q where
  toFun t := (t.1.2, t.2)
  invFun t := ((PUnit.unit, t.1), t.2)
  left_inv := by intro t; cases t.1.1; rfl
  right_inv := by intro t; rfl

set_option maxHeartbeats 400000 in
private theorem fqswTeleportation_liftedResource_preserves
    (q : Type x) (ref : Type y)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype ref] [DecidableEq ref]
    (rho : State (Prod ref q)) :
    ((Channel.reindex (fqswTeleportationResourceOutputEquiv q ref)).applyState
      (((teleportationLOCC q).prodIdRight (R := ref)).toChannel.applyState
        ((rho.prod (teleportationEntanglementResource q).state).reindex
          (fqswTeleportationResourceInputEquiv q ref)))) = rho := by
  have htele := teleportationLOCCResourceChannel_preserves_reference q ref rho
  calc
    _ = ((Channel.idChannel ref).prod
          (teleportationLOCCResourceChannel q)).applyState rho := by
      rw [OneWayLOCC.prodIdRight_toChannel]
      simp only [Channel.applyState_comp, Channel.reindex_applyState]
      apply State.ext
      simp only [Channel.applyState, State.reindex_matrix,
        State.prod_matrix_kronecker, teleportationLOCCResourceChannel,
        Channel.comp]
      funext i j
      rcases i with ⟨ri, qi⟩
      rcases j with ⟨rj, qj⟩
      simp only [Matrix.submatrix_apply, fqswTeleportationResourceInputEquiv,
        fqswTeleportationResourceOutputEquiv, loccReferenceRegroupEquiv]
      simp only [Channel.prod, MatrixMap.kron, LinearMap.comp_apply,
        Channel.idChannel_map_eq_linearMap_id, LinearMap.id_apply]
      simp_rw [teleportationAppendResourceChannel_map]
      simp_rw [fqswReindexChannel_map]
      simp [teleportationLOCCInputEquiv, teleportationLOCCOutputEquiv,
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
                (Matrix.single m m' (1 : Complex))
                (rankOneMatrix
                  (teleportationEntanglementResource q).pureVector.amp)).submatrix
                    (fun x => (x.1.1, x.1.2, x.2))
                    (fun x => (x.1.1, x.1.2, x.2)))
              (PUnit.unit, qi) (PUnit.unit, qj) =
            ∑ full : Prod (Prod q q) q, ∑ full' : Prod (Prod q q) q,
              (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
                (Matrix.single m m' (1 : Complex))
                (rankOneMatrix
                  (teleportationEntanglementResource q).pureVector.amp)).submatrix
                    (fun x => (x.1.1, x.1.2, x.2))
                    (fun x => (x.1.1, x.1.2, x.2)) full full' *
                (∑ result : TeleportationOutcome q,
                    MatrixMap.kron
                      (MatrixMap.traceEffectToUnit
                        ((generalizedBellPOVM q).effects result))
                      (teleportationCorrection q result).map)
                  (Matrix.single full full' (1 : Complex))
                  (PUnit.unit, qi) (PUnit.unit, qj) := by
        rw [MatrixMap.map_eq_sum_single]
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        rfl
      have hInput (m m' : q) (full full' : Prod (Prod q q) q) :
          (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
            (Matrix.single m m' (1 : Complex))
            (rankOneMatrix
              (teleportationEntanglementResource q).pureVector.amp)).submatrix
                (fun x => (x.1.1, x.1.2, x.2))
                (fun x => (x.1.1, x.1.2, x.2)) full full' =
            if m = full.1.1 ∧ m' = full'.1.1 then
              (teleportationEntanglementResource q).pureVector.amp
                  (full.1.2, full.2) *
                star ((teleportationEntanglementResource q).pureVector.amp
                  (full'.1.2, full'.2))
            else 0 := by
        simp [Matrix.kroneckerMap_apply, Matrix.submatrix_apply,
          rankOneMatrix_apply, Matrix.single_apply]
      symm
      calc
        _ = ∑ m : q, ∑ m' : q, rho.matrix (ri, m) (rj, m') *
              (∑ full : Prod (Prod q q) q,
                ∑ full' : Prod (Prod q q) q,
                  (Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
                    (Matrix.single m m' (1 : Complex))
                    (rankOneMatrix
                      (teleportationEntanglementResource q).pureVector.amp)).submatrix
                        (fun x => (x.1.1, x.1.2, x.2))
                        (fun x => (x.1.1, x.1.2, x.2)) full full' *
                    (∑ result : TeleportationOutcome q,
                        MatrixMap.kron
                          (MatrixMap.traceEffectToUnit
                            ((generalizedBellPOVM q).effects result))
                          (teleportationCorrection q result).map)
                      (Matrix.single full full' (1 : Complex))
                        (PUnit.unit, qi) (PUnit.unit, qj)) := by
            apply Finset.sum_congr rfl
            intro m _
            apply Finset.sum_congr rfl
            intro m' _
            apply congrArg
              (fun z : Complex => rho.matrix (ri, m) (rj, m') * z)
            simpa only [LinearMap.sum_apply] using hPhi m m'
        _ = _ := by
          simp_rw [hInput]
          simp only [Finset.mul_sum, mul_ite, ite_mul, mul_zero, zero_mul]
          calc
            _ = ∑ full : Prod (Prod q q) q,
                  ∑ full' : Prod (Prod q q) q,
                    rho.matrix (ri, full.1.1) (rj, full'.1.1) *
                      (((teleportationEntanglementResource q).pureVector.amp
                          (full.1.2, full.2) *
                        star ((teleportationEntanglementResource q).pureVector.amp
                          (full'.1.2, full'.2))) *
                        (∑ c : TeleportationOutcome q,
                            MatrixMap.kron
                              (MatrixMap.traceEffectToUnit
                                ((generalizedBellPOVM q).effects c))
                              (teleportationCorrection q c).map)
                          (Matrix.single full full' (1 : Complex))
                            (PUnit.unit, qi) (PUnit.unit, qj)) :=
                fqswSum_four_pair_single
                  (fun full : Prod (Prod q q) q => full.1.1)
                  (fun full : Prod (Prod q q) q => full.1.1)
                  (fun m m' full full' =>
                    rho.matrix (ri, m) (rj, m') *
                      (((teleportationEntanglementResource q).pureVector.amp
                          (full.1.2, full.2) *
                        star ((teleportationEntanglementResource q).pureVector.amp
                          (full'.1.2, full'.2))) *
                        (∑ c : TeleportationOutcome q,
                            MatrixMap.kron
                              (MatrixMap.traceEffectToUnit
                                ((generalizedBellPOVM q).effects c))
                              (teleportationCorrection q c).map)
                          (Matrix.single full full' (1 : Complex))
                            (PUnit.unit, qi) (PUnit.unit, qj)))
            _ = _ := by
              apply Finset.sum_congr rfl
              intro full _
              apply Finset.sum_congr rfl
              intro full' _
              simp only [teleportationEntanglementResource_state, PureVector.state_matrix,
                rankOneMatrix_apply, LinearMap.sum_apply, mul_assoc]
    _ = rho := htele

private def fqswTeleportationCoreToLiftInputEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    Prod (Prod (Prod (Prod q q) e) (Prod s q)) r ≃
      Prod (Prod (Prod q q) (Prod e (Prod s r))) q where
  toFun t := ((t.1.1.1, (t.1.1.2, (t.1.2.1, t.2))), t.1.2.2)
  invFun t := (((t.1.1, t.1.2.1), (t.1.2.2.1, t.2)), t.1.2.2.2)
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

private def fqswTeleportationLiftToCoreOutputEquiv (q : Type x) (e : Type y) (s : Type v) (r : Type w) :
    Prod (Prod PUnit.{x + 1} (Prod e (Prod s r))) q ≃
      Prod (Prod e (Prod q s)) r where
  toFun t := ((t.1.2.1, (t.2, t.1.2.2.1)), t.1.2.2.2)
  invFun t := ((PUnit.unit, (t.1.1, (t.1.2.2, t.2))), t.1.2.1)
  left_inv := by intro t; cases t.1.1; rfl
  right_inv := by intro t; rfl

set_option maxHeartbeats 800000 in
private theorem fqswTeleportation_coreChannel
    (q : Type x) (e : Type y) (s : Type v) (r : Type w)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    [Fintype s] [DecidableEq s]
    [Fintype r] [DecidableEq r] :
    (fqswStateMergingTeleportationLOCC q e s).toChannel.prod
        (Channel.idChannel r) =
      (Channel.reindex (fqswTeleportationLiftToCoreOutputEquiv q e s r)).comp
        (((teleportationLOCC q).prodIdRight
          (R := Prod e (Prod s r))).toChannel.comp
            (Channel.reindex (fqswTeleportationCoreToLiftInputEquiv q e s r))) := by
  rw [fqswTeleportation_spectators_channel]
  rw [OneWayLOCC.prodIdRight_toChannel,
    OneWayLOCC.prodIdRight_toChannel]
  rw [Channel.mk.injEq]
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
    rw [show Matrix.single i j (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1 j.1 (1 : Complex))
          (Matrix.single i.2 j.2 (1 : Complex)) by
      exact single_prod_eq_kronecker_single _ _ _ _]
  simp only [Channel.prod]
  rw [MatrixMap.kron_apply_kronecker]
  simp only [Channel.idChannel_map_eq_linearMap_id, LinearMap.id_apply]
  simp only [Channel.comp, LinearMap.comp_apply]
  simp only [fqswReindexChannel_map_single]
  have hLhsI :
      (loccReferenceRegroupEquiv (Prod q q) q (Prod e s)).symm
          (fqswTeleportationSpectatorInputEquiv q e s i.1) =
        ((i.1.1.1, i.1.2.2), (i.1.1.2, i.1.2.1)) := rfl
  have hLhsJ :
      (loccReferenceRegroupEquiv (Prod q q) q (Prod e s)).symm
          (fqswTeleportationSpectatorInputEquiv q e s j.1) =
        ((j.1.1.1, j.1.2.2), (j.1.1.2, j.1.2.1)) := rfl
  have hRhsI :
      (loccReferenceRegroupEquiv (Prod q q) q
          (Prod e (Prod s r))).symm
          (fqswTeleportationCoreToLiftInputEquiv q e s r i) =
        ((i.1.1.1, i.1.2.2), (i.1.1.2, (i.1.2.1, i.2))) := rfl
  have hRhsJ :
      (loccReferenceRegroupEquiv (Prod q q) q
          (Prod e (Prod s r))).symm
          (fqswTeleportationCoreToLiftInputEquiv q e s r j) =
        ((j.1.1.1, j.1.2.2), (j.1.1.2, (j.1.2.1, j.2))) := rfl
  rw [hLhsI, hLhsJ, hRhsI, hRhsJ]
  have hLhsInput :
      Matrix.single
          ((i.1.1.1, i.1.2.2), (i.1.1.2, i.1.2.1))
          ((j.1.1.1, j.1.2.2), (j.1.1.2, j.1.2.1))
          (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (i.1.1.1, i.1.2.2)
            (j.1.1.1, j.1.2.2) (1 : Complex))
          (Matrix.single (i.1.1.2, i.1.2.1)
            (j.1.1.2, j.1.2.1) (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  have hRhsInput :
      Matrix.single
          ((i.1.1.1, i.1.2.2), (i.1.1.2, (i.1.2.1, i.2)))
          ((j.1.1.1, j.1.2.2), (j.1.1.2, (j.1.2.1, j.2)))
          (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (i.1.1.1, i.1.2.2)
            (j.1.1.1, j.1.2.2) (1 : Complex))
          (Matrix.single (i.1.1.2, (i.1.2.1, i.2))
            (j.1.1.2, (j.1.2.1, j.2)) (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhsInput, hRhsInput]
  simp_rw [MatrixMap.kron_apply_kronecker]
  simp only [LinearMap.id_apply]
  simp_rw [fqswReindexChannel_map]
  ext k l
  simp [fqswTeleportationSpectatorOutputEquiv,
    fqswTeleportationLiftToCoreOutputEquiv,
    loccReferenceRegroupEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply]
  split_ifs <;> simp_all

set_option maxHeartbeats 800000 in
private theorem fqswTeleportation_core_preserves
    (q : Type x) (e : Type y) (s : Type v) (r : Type w)
    [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype e] [DecidableEq e]
    [Fintype s] [DecidableEq s]
    [Fintype r] [DecidableEq r]
    (rho : State (Prod (Prod q e) (Prod s r))) :
    (((fqswStateMergingTeleportationLOCC q e s).toChannel.prod
          (Channel.idChannel r)).applyState
      ((rho.prod (teleportationEntanglementResource q).state).reindex
        (fqswTeleportationCoreInputEquiv q e s r))) =
      rho.reindex (fqswTeleportationCoreOutputEquiv q e s r) := by
  have hinput :
      (((rho.prod (teleportationEntanglementResource q).state).reindex
          (fqswTeleportationCoreInputEquiv q e s r)).reindex
            (fqswTeleportationCoreToLiftInputEquiv q e s r)) =
        (((rho.reindex (fqswTeleportationToReferenceEquiv q e s r)).prod
            (teleportationEntanglementResource q).state).reindex
              (fqswTeleportationResourceInputEquiv q (Prod e (Prod s r)))) := by
    apply State.ext
    rfl
  have htele := fqswTeleportation_liftedResource_preserves q (Prod e (Prod s r))
    (rho.reindex (fqswTeleportationToReferenceEquiv q e s r))
  rw [fqswTeleportation_coreChannel]
  simp only [Channel.applyState_comp, Channel.reindex_applyState]
  rw [hinput]
  calc
    _ = (((((teleportationLOCC q).prodIdRight
          (R := Prod e (Prod s r))).toChannel.applyState
            (((rho.reindex (fqswTeleportationToReferenceEquiv q e s r)).prod
              (teleportationEntanglementResource q).state).reindex
                (fqswTeleportationResourceInputEquiv q (Prod e (Prod s r))))).reindex
          (fqswTeleportationResourceOutputEquiv q (Prod e (Prod s r)))).reindex
            (fqswTeleportationFromReferenceEquiv q e s r)) := by
        apply State.ext
        rfl
    _ = (rho.reindex (fqswTeleportationToReferenceEquiv q e s r)).reindex
          (fqswTeleportationFromReferenceEquiv q e s r) := by
        simpa only [Channel.reindex_applyState] using congrArg
          (fun tau => tau.reindex (fqswTeleportationFromReferenceEquiv q e s r)) htele
    _ = rho.reindex (fqswTeleportationCoreOutputEquiv q e s r) := by
        apply State.ext
        rfl

private theorem fqswProdCompId
    {alpha : Type u} {beta : Type v} {gamma : Type w} {ref : Type x}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype gamma] [DecidableEq gamma]
    [Fintype ref] [DecidableEq ref]
    (Phi : Channel beta gamma) (Psi : Channel alpha beta) :
    (Phi.comp Psi).prod (Channel.idChannel ref) =
      (Phi.prod (Channel.idChannel ref)).comp
        (Psi.prod (Channel.idChannel ref)) := by
  rw [Channel.prod_comp_prod, Channel.idChannel_comp]

private def fqswStateMergingPreparationInputEquiv
    (a : Type u) (b : Type v) (r : Type w) (q : Type x) :
    Prod (Prod a (Prod b r)) (Prod q q) ≃
      Prod (Prod (Prod a q) (Prod b q)) r where
  toFun t := (((t.1.1, t.2.1), (t.1.2.1, t.2.2)), t.1.2.2)
  invFun t := ((t.1.1.1, (t.1.2.1, t.2)), (t.1.1.2, t.1.2.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

set_option maxHeartbeats 800000 in
private theorem fqswStateMergingPreparationChannel
    {a : Type u} {b : Type v} {r : Type w} {q : Type x} {e : Type y}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r]
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    (Phi : Channel a (Prod q e)) :
    ((((Channel.reindex (fqswStateMergingAliceRegroupEquiv q e)).comp
          (Phi.prod (Channel.idChannel q))).prod
        (Channel.idChannel (Prod b q))).prod (Channel.idChannel r)).comp
          (Channel.reindex (fqswStateMergingPreparationInputEquiv a b r q)) =
      (Channel.reindex (fqswTeleportationCoreInputEquiv q e b r)).comp
        ((Phi.prod (Channel.idChannel (Prod b r))).prod
          (Channel.idChannel (Prod q q))) := by
  rw [Channel.mk.injEq]
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single]
  rw [MatrixMap.map_eq_sum_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [Channel.comp, Channel.prod, LinearMap.comp_apply]
  simp_rw [fqswReindexChannel_map_single]
  simp_rw [fqswReindexChannel_map]
  have hLhs0 :
      Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i)
          (fqswStateMergingPreparationInputEquiv a b r q j) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1
            (fqswStateMergingPreparationInputEquiv a b r q j).1 (1 : Complex))
          (Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).2
            (fqswStateMergingPreparationInputEquiv a b r q j).2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs0, MatrixMap.kron_apply_kronecker]
  have hLhs1 :
      Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1
          (fqswStateMergingPreparationInputEquiv a b r q j).1 (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1.1
            (fqswStateMergingPreparationInputEquiv a b r q j).1.1 (1 : Complex))
          (Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1.2
            (fqswStateMergingPreparationInputEquiv a b r q j).1.2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs1, MatrixMap.kron_apply_kronecker]
  have hLhs2 :
      Matrix.single (fqswStateMergingPreparationInputEquiv a b r q i).1.1
          (fqswStateMergingPreparationInputEquiv a b r q j).1.1 (1 : Complex) =
        Matrix.kronecker
          (Matrix.single i.1.1 j.1.1 (1 : Complex))
          (Matrix.single i.2.1 j.2.1 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs2]
  simp only [LinearMap.comp_apply]
  rw [MatrixMap.kron_apply_kronecker]
  have hRhs0 : Matrix.single i j (1 : Complex) =
      Matrix.kronecker
        (Matrix.single i.1 j.1 (1 : Complex))
        (Matrix.single i.2 j.2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hRhs0]
  rw [MatrixMap.kron_apply_kronecker]
  have hRhs1 : Matrix.single i.1 j.1 (1 : Complex) =
      Matrix.kronecker
        (Matrix.single i.1.1 j.1.1 (1 : Complex))
        (Matrix.single i.1.2 j.1.2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hRhs1]
  rw [MatrixMap.kron_apply_kronecker]
  simp only [Channel.idChannel_map_eq_linearMap_id, LinearMap.id_apply]
  ext k l
  rcases i with ⟨⟨ia, ⟨ib, ir⟩⟩, ⟨iq₁, iq₂⟩⟩
  rcases j with ⟨⟨ja, ⟨jb, jr⟩⟩, ⟨jq₁, jq₂⟩⟩
  rcases k with ⟨⟨⟨⟨kq₁, kq₂⟩, ke⟩, ⟨kb, kq₃⟩⟩, kr⟩
  rcases l with ⟨⟨⟨⟨lq₁, lq₂⟩, le⟩, ⟨lb, lq₃⟩⟩, lr⟩
  rw [fqswReindexChannel_map]
  simp [fqswStateMergingPreparationInputEquiv, fqswTeleportationCoreInputEquiv,
    fqswStateMergingAliceRegroupEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply]
  split_ifs <;> simp_all

private def fqswStateMergingDecoderFinalEquiv (d : Type u) (e : Type y) (r : Type w) :
    Prod d (Prod r e) ≃ Prod (Prod e d) r where
  toFun t := ((t.2.2, t.1), t.2.1)
  invFun t := (t.1.2, (t.2, t.1.1))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

set_option maxHeartbeats 800000 in
private theorem fqswStateMergingDecoderChannel
    {q : Type x} {e : Type y} {s : Type v} {r : Type w} {d : Type u}
    [Fintype q] [DecidableEq q]
    [Fintype e] [DecidableEq e]
    [Fintype s] [DecidableEq s]
    [Fintype r] [DecidableEq r]
    [Fintype d] [DecidableEq d]
    (Phi : Channel (Prod q s) d) :
    ((((Channel.idChannel e).prod Phi).prod (Channel.idChannel r)).comp
          (Channel.reindex (fqswTeleportationCoreOutputEquiv q e s r))) =
      (Channel.reindex (fqswStateMergingDecoderFinalEquiv d e r)).comp
        ((Phi.prod (Channel.idChannel (Prod r e))).comp
          (Channel.reindex (fqswAliceOutputToBobInputEquiv q e s r))) := by
  rw [Channel.mk.injEq]
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single]
  rw [MatrixMap.map_eq_sum_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [Channel.comp, Channel.prod, LinearMap.comp_apply]
  simp_rw [fqswReindexChannel_map_single]
  have hLhs0 :
      Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i)
          (fqswTeleportationCoreOutputEquiv q e s r j) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).1
            (fqswTeleportationCoreOutputEquiv q e s r j).1 (1 : Complex))
          (Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).2
            (fqswTeleportationCoreOutputEquiv q e s r j).2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs0, MatrixMap.kron_apply_kronecker]
  have hLhs1 :
      Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).1
          (fqswTeleportationCoreOutputEquiv q e s r j).1 (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).1.1
            (fqswTeleportationCoreOutputEquiv q e s r j).1.1 (1 : Complex))
          (Matrix.single (fqswTeleportationCoreOutputEquiv q e s r i).1.2
            (fqswTeleportationCoreOutputEquiv q e s r j).1.2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hLhs1, MatrixMap.kron_apply_kronecker]
  have hRhs0 :
      Matrix.single (fqswAliceOutputToBobInputEquiv q e s r i)
          (fqswAliceOutputToBobInputEquiv q e s r j) (1 : Complex) =
        Matrix.kronecker
          (Matrix.single (fqswAliceOutputToBobInputEquiv q e s r i).1
            (fqswAliceOutputToBobInputEquiv q e s r j).1 (1 : Complex))
          (Matrix.single (fqswAliceOutputToBobInputEquiv q e s r i).2
            (fqswAliceOutputToBobInputEquiv q e s r j).2 (1 : Complex)) := by
    exact single_prod_eq_kronecker_single _ _ _ _
  rw [hRhs0, MatrixMap.kron_apply_kronecker]
  simp only [Channel.idChannel_map_eq_linearMap_id, LinearMap.id_apply]
  rw [fqswReindexChannel_map]
  ext k l
  rcases i with ⟨⟨iq, ie⟩, ⟨is, ir⟩⟩
  rcases j with ⟨⟨jq, je⟩, ⟨js, jr⟩⟩
  rcases k with ⟨⟨ke, kd⟩, kr⟩
  rcases l with ⟨⟨le, ld⟩, lr⟩
  simp [fqswTeleportationCoreOutputEquiv, fqswStateMergingDecoderFinalEquiv,
    fqswAliceOutputToBobInputEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply]
  split_ifs <;> simp_all

private theorem fqswStateMergingDecoderFinalReindex
    {a : Type u} {b : Type v} {e : Type y} {r : Type w}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype e] [DecidableEq e]
    [Fintype r] [DecidableEq r]
    (rho : State (Prod (Prod (Prod a b) e) (Prod r e))) :
    rho.reindex (fqswStateMergingDecoderFinalEquiv (Prod (Prod a b) e) e r) =
      (rho.reindex (fqswBobOutputToFinalEquiv a b e r e)).reindex
        (stateMergingTargetEquiv a b r e e) := by
  apply State.ext
  ext i j
  rfl

set_option maxHeartbeats 800000 in
theorem FQSWBlockProtocol.toStateMergingProtocol_outputState_eq_reindex
    {a : Type u} {b : Type v} {r : Type w}
    [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r]
    {psi : PureVector (Prod (Prod a b) r)} {n : Nat}
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
        (Channel.idChannel (TensorPower r n))).applyState
      C.toStateMergingProtocol.initialState = _
  rw [C.stateMergingLOCC_toChannel_eq_encoder_teleportation_decoder]
  rw [fqswProdCompId, fqswProdCompId]
  simp only [Channel.applyState_comp]
  let rhoU : State
      (Prod (Prod q e)
        (Prod (TensorPower b n) (TensorPower r n))) :=
    (C.aliceOperation.prod
      (Channel.idChannel
        (Prod (TensorPower b n) (TensorPower r n)))).applyState
      ((stateMergingBlockSource psi n).state.reindex
        (fqswSourceToAliceInputEquiv
          (TensorPower a n) (TensorPower b n) (TensorPower r n)))
  have hprep :
      (((C.stateMergingAlicePreparation.prod
            (Channel.idChannel (Prod (TensorPower b n) q))).prod
          (Channel.idChannel (TensorPower r n))).applyState
        C.toStateMergingProtocol.initialState) =
        ((rhoU.prod (teleportationEntanglementResource q).state).reindex
          (fqswTeleportationCoreInputEquiv q e (TensorPower b n) (TensorPower r n))) := by
    have hinitial :
        C.toStateMergingProtocol.initialState =
          (((stateMergingBlockSource psi n).state.reindex
              (fqswSourceToAliceInputEquiv
                (TensorPower a n) (TensorPower b n) (TensorPower r n))).prod
            (teleportationEntanglementResource q).state).reindex
              (fqswStateMergingPreparationInputEquiv
                (TensorPower a n) (TensorPower b n) (TensorPower r n) q) := by
      simp [FQSWBlockProtocol.toStateMergingProtocol,
        StateMergingBlockProtocol.initialState,
        fqswStateMergingPreparationInputEquiv, stateMergingInputEquiv,
        fqswSourceToAliceInputEquiv,
        teleportationEntanglementResource_state]
      apply State.ext
      ext i j
      rfl
    rw [hinitial]
    change
      (((((Channel.reindex (fqswStateMergingAliceRegroupEquiv q e)).comp
            (C.aliceOperation.prod (Channel.idChannel q))).prod
          (Channel.idChannel (Prod (TensorPower b n) q))).prod
            (Channel.idChannel (TensorPower r n))).applyState
        _) = _
    rw [← Channel.reindex_applyState]
    rw [← Channel.applyState_comp]
    rw [fqswStateMergingPreparationChannel]
    rw [Channel.applyState_comp, Channel.reindex_applyState,
      Channel.applyState_prod]
    have hresource :
        (Channel.idChannel (Prod q q)).applyState
            (teleportationEntanglementResource q).state =
          (teleportationEntanglementResource q).state := by
      apply State.ext
      change (Channel.idChannel (Prod q q)).map _ = _
      simp [Channel.idChannel, MatrixMap.ofKraus]
    rw [hresource]
  rw [hprep]
  rw [fqswTeleportation_core_preserves]
  unfold FQSWBlockProtocol.outputState FQSWBlockProtocol.outputStateOfState
  unfold FQSWBlockProtocol.outputStateOfBlockState
  dsimp only
  dsimp only [rhoU]
  rw [← Channel.reindex_applyState]
  rw [← Channel.applyState_comp]
  rw [fqswStateMergingDecoderChannel]
  simp only [Channel.applyState_comp, Channel.reindex_applyState]
  rw [fqswStateMergingDecoderFinalReindex]
  have hsource :
      (stateMergingBlockSource psi n).state =
        (psi.state.tensorPower n).reindex
          (fqswTensorPowerTripartiteEquiv a b r n) := by
    rw [stateMergingBlockSource, PureVector.reindex_state,
      PureVector.tensorPower_state]
  rw [hsource]


private theorem squaredFidelity_reindex
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho sigma : State A) (equiv : A ≃ B) :
    (rho.reindex equiv).squaredFidelity (sigma.reindex equiv) =
      rho.squaredFidelity sigma := by
  rw [State.squaredFidelity_eq_fidelity_sq,
    State.squaredFidelity_eq_fidelity_sq,
    SmoothNormalizedExtension.State.fidelity_reindex]

namespace FQSWBlockProtocol

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : PureVector (Prod (Prod a b) r)} {n : Nat}
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
    squaredFidelity_reindex]
  exact State.one_sub_squaredFidelity_le_two_mul_normalizedTraceDistance
    C.outputState C.targetState

end FQSWBlockProtocol

namespace ADHWFQSWIidMixedBlockConstruction

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]
variable {psi : PureVector (Prod (Prod a b) r)} {n : Nat}
variable {deltaTypical deltaRate epsilon : Real}
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
