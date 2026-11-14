/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Symmetry.DeFinetti.Twirling

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
open MeasureTheory

namespace QIT

universe u v w x

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

local instance deFinettiRennerProjectorsCMatrixContinuousENorm
    {α : Type v} [Fintype α] [DecidableEq α] :
    ContinuousENorm (CMatrix α) :=
  SeminormedAddGroup.toContinuousENorm

omit [Fintype a] [DecidableEq a] in
private theorem cMatrix_eq_zero_of_posSemidef_and_neg_posSemidef_general
    {A : CMatrix a} (hA : A.PosSemidef) (hneg : (-A).PosSemidef) :
    A = 0 := by
  have h0A : (0 : CMatrix a) ≤ A := by
    rw [Matrix.le_iff]
    simpa using hA
  have hA0 : A ≤ (0 : CMatrix a) := by
    rw [Matrix.le_iff]
    simpa using hneg
  exact le_antisymm hA0 h0A

private theorem projection_sandwich_fixed_of_le
    (ρ : State a) (P : CMatrix a)
    (hPpos : P.PosSemidef) (hPid : P * P = P)
    (hρP : ρ.matrix ≤ P) :
    P * ρ.matrix * P = ρ.matrix := by
  let Q : CMatrix a := 1 - P
  have hQherm : Q.IsHermitian := by
    dsimp [Q]
    exact Matrix.IsHermitian.sub (by simp [Matrix.IsHermitian]) hPpos.isHermitian
  have hQP : Q * P = 0 := by
    calc
      Q * P = (1 - P) * P := rfl
      _ = P - P * P := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = 0 := by rw [hPid, sub_self]
  have hdiff : (P - ρ.matrix).PosSemidef := by
    rwa [Matrix.le_iff] at hρP
  have hQrhoQ_pos : (Q * ρ.matrix * Q).PosSemidef := by
    have h := ρ.pos.conjTranspose_mul_mul_same Q
    simpa [hQherm.eq] using h
  have hQdiffQ_pos : (Q * (P - ρ.matrix) * Q).PosSemidef := by
    have h := hdiff.conjTranspose_mul_mul_same Q
    simpa [hQherm.eq] using h
  have hQdiffQ_eq_neg :
      Q * (P - ρ.matrix) * Q = -(Q * ρ.matrix * Q) := by
    have hleft : Q * (P - ρ.matrix) = Q * P - Q * ρ.matrix := by
      rw [Matrix.mul_sub]
    calc
      Q * (P - ρ.matrix) * Q =
          (Q * P - Q * ρ.matrix) * Q := by rw [hleft]
      _ = Q * P * Q - Q * ρ.matrix * Q := by rw [Matrix.sub_mul]
      _ = 0 - Q * ρ.matrix * Q := by rw [hQP, Matrix.zero_mul]
      _ = -(Q * ρ.matrix * Q) := by rw [zero_sub]
  have hQrhoQ_zero : Q * ρ.matrix * Q = 0 :=
    cMatrix_eq_zero_of_posSemidef_and_neg_posSemidef_general
      hQrhoQ_pos (by simpa [hQdiffQ_eq_neg] using hQdiffQ_pos)
  let S : CMatrix a := psdSqrt ρ.matrix
  have hSsq : S * S = ρ.matrix := by
    simpa [S] using psdSqrt_mul_self_of_posSemidef ρ.pos
  have hSherm : S.IsHermitian := by
    simpa [S] using psdSqrt_isHermitian ρ.matrix
  have hSQ_conj_self :
      (S * Q).conjTranspose * (S * Q) = 0 := by
    calc
      (S * Q).conjTranspose * (S * Q) =
          Q * S * (S * Q) := by
          rw [Matrix.conjTranspose_mul, hQherm.eq, hSherm.eq]
      _ = Q * ρ.matrix * Q := by
          calc
            Q * S * (S * Q) = (Q * S * S) * Q := by
              rw [← Matrix.mul_assoc]
            _ = Q * (S * S) * Q := by
              rw [Matrix.mul_assoc Q S S]
            _ = Q * ρ.matrix * Q := by rw [hSsq]
      _ = 0 := hQrhoQ_zero
  have hSQ : S * Q = 0 := by
    have htrace : ((S * Q).conjTranspose * (S * Q)).trace = 0 := by
      rw [hSQ_conj_self, Matrix.trace_zero]
    exact (Matrix.trace_conjTranspose_mul_self_eq_zero_iff).mp htrace
  have hρQ : ρ.matrix * Q = 0 := by
    rw [← hSsq, Matrix.mul_assoc, hSQ, Matrix.mul_zero]
  have hQρ : Q * ρ.matrix = 0 := by
    rw [← Matrix.conjTranspose_eq_zero]
    calc
      (Q * ρ.matrix).conjTranspose =
          ρ.matrix.conjTranspose * Q.conjTranspose := by rw [Matrix.conjTranspose_mul]
      _ = ρ.matrix * Q := by rw [ρ.pos.isHermitian.eq, hQherm.eq]
      _ = 0 := hρQ
  have hPρ : P * ρ.matrix = ρ.matrix := by
    calc
      P * ρ.matrix = (1 - Q) * ρ.matrix := by simp [Q, sub_sub_cancel]
      _ = ρ.matrix - Q * ρ.matrix := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = ρ.matrix := by rw [hQρ, sub_zero]
  have hρP : ρ.matrix * P = ρ.matrix := by
    calc
      ρ.matrix * P = ρ.matrix * (1 - Q) := by simp [Q, sub_sub_cancel]
      _ = ρ.matrix - ρ.matrix * Q := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = ρ.matrix := by rw [hρQ, sub_zero]
  calc
    P * ρ.matrix * P = ρ.matrix * P := by rw [hPρ]
    _ = ρ.matrix := hρP

private theorem rankOneMatrix_le_one_of_trace_eq_one (ψ : a → ℂ)
    (hnorm : (rankOneMatrix ψ).trace = 1) :
    rankOneMatrix ψ ≤ (1 : CMatrix a) := by
  rw [Matrix.le_iff]
  have hpos : (rankOneMatrix ψ).PosSemidef := rankOneMatrix_pos ψ
  have hid : rankOneMatrix ψ * rankOneMatrix ψ = rankOneMatrix ψ := by
    let Ψ : PureVector a := ⟨ψ, hnorm⟩
    simpa [Ψ, PureVector.state_matrix] using Ψ.state_matrix_mul_self
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent (rankOneMatrix ψ) hpos hid

omit [DecidableEq a] in
private theorem exists_nonzero_coord_of_rankOne_trace_one (ψ : a → ℂ)
    (hnorm : (rankOneMatrix ψ).trace = 1) :
    ∃ i, ψ i ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : (rankOneMatrix ψ).trace = 0 := by
    rw [rankOneMatrix_trace]
    simp [h]
  rw [hzero] at hnorm
  norm_num at hnorm

omit [DecidableEq a] in
private theorem rankOneMatrix_eq_colinear (ψ φ : a → ℂ)
    (_hψ : (rankOneMatrix ψ).trace = 1)
    (hφ : (rankOneMatrix φ).trace = 1)
    (h : rankOneMatrix ψ = rankOneMatrix φ) :
    ∃ c : ℂ, ψ = c • φ := by
  rcases exists_nonzero_coord_of_rankOne_trace_one φ hφ with ⟨i0, hφ0⟩
  have hψ0 : ψ i0 ≠ 0 := by
    intro hz
    have hii := congrFun (congrFun h i0) i0
    simp [rankOneMatrix_apply, hz, hφ0] at hii
  refine ⟨star (φ i0) / star (ψ i0), ?_⟩
  funext i
  have hii := congrFun (congrFun h i) i0
  simp [rankOneMatrix_apply] at hii
  have hstarψ : star (ψ i0) ≠ 0 := star_ne_zero.mpr hψ0
  have hdiv :
      (ψ i * star (ψ i0)) / star (ψ i0) =
        (φ i * star (φ i0)) / star (ψ i0) :=
    congrArg (fun z => z / star (ψ i0)) hii
  calc
    ψ i = (ψ i * star (ψ i0)) / star (ψ i0) := by field_simp [hstarψ]
    _ = (φ i * star (φ i0)) / star (ψ i0) := hdiv
    _ = (star (φ i0) / star (ψ i0)) * φ i := by ring
    _ = ((star (φ i0) / star (ψ i0)) • φ) i := by rfl

private theorem pureVector_state_eq_colinear (ψ φ : PureVector a)
    (h : ψ.state = φ.state) :
    ∃ c : ℂ, ψ.amp = c • φ.amp :=
  rankOneMatrix_eq_colinear ψ.amp φ.amp ψ.trace_rankOne_eq_one
    φ.trace_rankOne_eq_one (by simpa [PureVector.state] using congrArg State.matrix h)

omit [DecidableEq a] in
private theorem rankOneMatrix_mul_of_mulVec_eq_self
    (P : CMatrix a) (ψ : a → ℂ) (hψ : P.mulVec ψ = ψ) :
    P * rankOneMatrix ψ = rankOneMatrix ψ := by
  ext i j
  rw [Matrix.mul_apply, rankOneMatrix_apply]
  calc
    ∑ k, P i k * (ψ k * star (ψ j))
        = (∑ k, P i k * ψ k) * star (ψ j) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
    _ = ψ i * star (ψ j) := by
            rw [show ∑ k, P i k * ψ k = ψ i by
              simpa [Matrix.mulVec] using congrFun hψ i]

omit [DecidableEq a] in
private theorem rankOneMatrix_mul_right_of_mulVec_eq_self
    (P : CMatrix a) (ψ : a → ℂ) (hPherm : P.IsHermitian)
    (hψ : P.mulVec ψ = ψ) :
    rankOneMatrix ψ * P = rankOneMatrix ψ := by
  have hrow (j : a) : (∑ k, star (ψ k) * P k j) = star (ψ j) := by
    have hconj : (∑ k, P k j * star (ψ k)) = star (ψ j) := by
      have hconj := congrArg star
        (show ∑ k, P j k * ψ k = ψ j by
          simpa [Matrix.mulVec] using congrFun hψ j)
      simpa [map_sum, map_mul, hPherm.apply] using hconj
    calc
      (∑ k, star (ψ k) * P k j) =
          ∑ k, P k j * star (ψ k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
      _ = star (ψ j) := hconj
  ext i j
  calc
    (rankOneMatrix ψ * P) i j
        = ψ i * (∑ k, star (ψ k) * P k j) := by
            simp [Matrix.mul_apply, rankOneMatrix_apply, Finset.mul_sum, mul_assoc]
    _ = ψ i * star (ψ j) := by rw [hrow]
    _ = rankOneMatrix ψ i j := by simp [rankOneMatrix_apply]

private theorem rankOneMatrix_le_projection_of_mulVec_eq_self
    (P : CMatrix a) (ψ : a → ℂ)
    (hPpos : P.PosSemidef) (hPid : P * P = P)
    (hψ : P.mulVec ψ = ψ) (hnorm : (rankOneMatrix ψ).trace = 1) :
    rankOneMatrix ψ ≤ P := by
  rw [Matrix.le_iff]
  let R : CMatrix a := rankOneMatrix ψ
  have hPherm : P.IsHermitian := hPpos.isHermitian
  have hRleone : R ≤ (1 : CMatrix a) := by
    simpa [R] using rankOneMatrix_le_one_of_trace_eq_one ψ hnorm
  have hOneSubR : (1 - R).PosSemidef := by
    simpa [Matrix.le_iff] using hRleone
  have hPR : P * R = R := by
    simpa [R] using rankOneMatrix_mul_of_mulVec_eq_self P ψ hψ
  have hRP : R * P = R := by
    simpa [R] using rankOneMatrix_mul_right_of_mulVec_eq_self P ψ hPherm hψ
  have hconj : (P.conjTranspose * (1 - R) * P).PosSemidef :=
    hOneSubR.conjTranspose_mul_mul_same P
  have hEq : P.conjTranspose * (1 - R) * P = P - R := by
    rw [hPherm.eq]
    calc
      P * (1 - R) * P = (P * 1 - P * R) * P := by rw [Matrix.mul_sub]
      _ = (P - R) * P := by rw [Matrix.mul_one, hPR]
      _ = P * P - R * P := by rw [Matrix.sub_mul]
      _ = P - R := by rw [hPid, hRP]
  simpa [hEq, R] using hconj

theorem rennerMIIDProjectorFor_isHermitian {m r : ℕ} (ν : PureVector a) :
    (rennerMIIDProjectorFor (a := a) m r ν).IsHermitian := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mp
    (by
      simpa [rennerMIIDProjectorFor_toEuclideanLin] using
        (RennerMIIDSubspace a m r ν).starProjection_isSymmetric)

theorem rennerMIIDProjectorFor_idempotent {m r : ℕ} (ν : PureVector a) :
    rennerMIIDProjectorFor (a := a) m r ν *
        rennerMIIDProjectorFor (a := a) m r ν =
      rennerMIIDProjectorFor (a := a) m r ν := by
  apply Matrix.toEuclideanLin.injective
  have hlin := rennerMIIDProjectorFor_toEuclideanLin (a := a) m r ν
  rw [Matrix.toLpLin_mul]
  ext x i
  rw [hlin]
  simp only [LinearMap.comp_apply]
  exact congrArg (fun v : EuclideanSpace ℂ (TensorPower a (m + r)) => v i)
    ((RennerMIIDSubspace a m r ν).starProjection_eq_self_iff.mpr
      ((RennerMIIDSubspace a m r ν).starProjection_apply_mem x))

theorem rennerMIIDProjectorFor_posSemidef {m r : ℕ} (ν : PureVector a) :
    (rennerMIIDProjectorFor (a := a) m r ν).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  rw [rennerMIIDProjectorFor_toEuclideanLin]
  exact (ContinuousLinearMap.isPositive_toLinearMap_iff
    ((RennerMIIDSubspace a m r ν).starProjection)).mpr
      (ContinuousLinearMap.IsPositive.of_isStarProjection
        (isStarProjection_starProjection
          (U := RennerMIIDSubspace a m r ν)))

theorem rennerMIIDProjectorFor_le_one {m r : ℕ} (ν : PureVector a) :
    rennerMIIDProjectorFor (a := a) m r ν ≤
      (1 : CMatrix (TensorPower a (m + r))) := by
  rw [Matrix.le_iff]
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    (rennerMIIDProjectorFor (a := a) m r ν)
    (rennerMIIDProjectorFor_posSemidef (a := a) ν)
    (rennerMIIDProjectorFor_idempotent (a := a) ν)

theorem rennerMIIDProjector_idempotent {m r : ℕ} (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    rennerMIIDProjector (a := a) m r ν U *
        rennerMIIDProjector (a := a) m r ν U =
      rennerMIIDProjector (a := a) m r ν U := by
  let Un : CMatrix (TensorPower a (m + r)) := unitaryTensorPowerMatrix U (m + r)
  let P : CMatrix (TensorPower a (m + r)) := rennerMIIDProjectorId (a := a) m r ν
  have hstar : star Un * Un = 1 := by
    simp [Un]
  have hP : P * P = P := by
    simpa [P, rennerMIIDProjectorId] using
      rennerMIIDProjectorFor_idempotent (a := a) (m := m) (r := r) ν
  dsimp [rennerMIIDProjector]
  change (Un * P * star Un) * (Un * P * star Un) = Un * P * star Un
  calc
    (Un * P * star Un) * (Un * P * star Un) =
        Un * P * (star Un * Un) * P * star Un := by noncomm_ring
    _ = Un * P * 1 * P * star Un := by rw [hstar]
    _ = Un * (P * P) * star Un := by noncomm_ring
    _ = Un * P * star Un := by rw [hP]

theorem rennerMIIDProjector_posSemidef {m r : ℕ} (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    (rennerMIIDProjector (a := a) m r ν U).PosSemidef := by
  dsimp [rennerMIIDProjector, rennerMIIDProjectorId]
  simpa [Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using
    (rennerMIIDProjectorFor_posSemidef (a := a) (m := m) (r := r) ν).mul_mul_conjTranspose_same
      (unitaryTensorPowerMatrix U (m + r) : CMatrix (TensorPower a (m + r)))

theorem rennerMIIDProjector_isHermitian {m r : ℕ} (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    (rennerMIIDProjector (a := a) m r ν U).IsHermitian :=
  (rennerMIIDProjector_posSemidef (a := a) ν U).isHermitian

theorem rennerMIIDProjector_le_one {m r : ℕ} (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    rennerMIIDProjector (a := a) m r ν U ≤
      (1 : CMatrix (TensorPower a (m + r))) := by
  rw [Matrix.le_iff]
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    (rennerMIIDProjector (a := a) m r ν U)
    (rennerMIIDProjector_posSemidef (a := a) ν U)
    (rennerMIIDProjector_idempotent (a := a) ν U)

theorem rennerMIIDProjectorFor_mulVec_eq_self_of_mem {m r : ℕ}
    {ν : PureVector a} {v : TensorPower a (m + r) → ℂ}
    (hv : WithLp.toLp 2 v ∈ RennerMIIDSubspace a m r ν) :
    (rennerMIIDProjectorFor (a := a) m r ν).mulVec v = v := by
  have hproj :
      (RennerMIIDSubspace a m r ν).starProjection (WithLp.toLp 2 v) =
        WithLp.toLp 2 v :=
    (RennerMIIDSubspace a m r ν).starProjection_eq_self_iff.mpr hv
  have hlin :
      (rennerMIIDProjectorFor (a := a) m r ν).toEuclideanLin (WithLp.toLp 2 v) =
        WithLp.toLp 2 v := by
    calc
      (rennerMIIDProjectorFor (a := a) m r ν).toEuclideanLin (WithLp.toLp 2 v) =
          (RennerMIIDSubspace a m r ν).starProjection (WithLp.toLp 2 v) := by
            rw [rennerMIIDProjectorFor_toEuclideanLin]
            rfl
      _ = WithLp.toLp 2 v := hproj
  exact congrArg WithLp.ofLp hlin

theorem rennerMIIDProjectorFor_mulVec_pure_eq_self {m r : ℕ}
    {ν : PureVector a} {ψ : PureVector (TensorPower a (m + r))}
    (hψ : ψ.IsRennerMIIDIn (a := a) (m := m) (r := r) ν) :
    (rennerMIIDProjectorFor (a := a) m r ν).mulVec ψ.amp = ψ.amp :=
  rennerMIIDProjectorFor_mulVec_eq_self_of_mem (a := a)
    (pureVector_mem_RennerMIIDSubspace (a := a) hψ)

theorem State.supportedOnRennerMIIDSubspace_of_rankOne {m r : ℕ}
    {ν : PureVector a} {ψ : PureVector (TensorPower a (m + r))}
    (hψ : ψ.IsRennerMIIDIn (a := a) (m := m) (r := r) ν) :
    ψ.state.SupportedOnRennerMIIDSubspace (a := a) (m := m) (r := r) ν := by
  dsimp [State.SupportedOnRennerMIIDSubspace, PureVector.state]
  apply rankOneMatrix_le_projection_of_mulVec_eq_self
  · exact rennerMIIDProjectorFor_posSemidef (a := a) ν
  · exact rennerMIIDProjectorFor_idempotent (a := a) ν
  · exact rennerMIIDProjectorFor_mulVec_pure_eq_self (a := a) hψ
  · exact ψ.trace_rankOne_eq_one

/-- The rank-one IID tensor power is supported in the zero-residual Renner
m-IID subspace. -/
theorem State.tensorPower_supportedOnRennerMIIDSubspace_zero
    (ν : PureVector a) (m : ℕ) :
    (ν.tensorPower m).state.SupportedOnRennerMIIDSubspace
      (a := a) (m := m) (r := 0) ν :=
  State.supportedOnRennerMIIDSubspace_of_rankOne (a := a)
    (PureVector.tensorPower_isRennerMIIDIn_zero (a := a) ν m)

/-- Canonical reindexing between the repository's `TensorPower a m` and
`TensorPower a (m+0)` conventions.  This keeps Renner's `P_U^{m,0}` projector
usable in formulas written on the literal `m`-fold tensor power. -/
def tensorPowerAddZeroEquiv (a : Type v) [Fintype a] [DecidableEq a] (m : ℕ) :
    TensorPower a m ≃ TensorPower a (m + 0) :=
  Equiv.cast (by simp)

private theorem pure_prod_zero_reindex_state_eq_tensorPower_reindex
    (ν : PureVector a) (m : ℕ) (η : PureVector (TensorPower a 0)) :
    (((ν.tensorPower m).prod η).reindex
          (tensorPowerTakeDropEquiv a m 0).symm).state =
      ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).state := by
  apply State.ext
  ext x y
  simp [PureVector.prod_amp, tensorPowerAddZeroEquiv]
  cases ((tensorPowerTakeDropEquiv a m 0) x).2
  cases ((tensorPowerTakeDropEquiv a m 0) y).2
  have hηtrace := η.trace_rankOne_eq_one
  rw [rankOneMatrix_trace] at hηtrace
  have hη : η.amp PUnit.unit * star (η.amp PUnit.unit) = 1 := by
    change (∑ x : PUnit, η.amp x * star (η.amp x)) = 1 at hηtrace
    simpa using hηtrace
  have hx : ((tensorPowerTakeDropEquiv a m 0) x).1 = x :=
    tensorPowerTakeDropEquiv_zero_fst (a := a) m x
  have hy : ((tensorPowerTakeDropEquiv a m 0) y).1 = y :=
    tensorPowerTakeDropEquiv_zero_fst (a := a) m y
  rw [hx, hy]
  calc
    (ν.tensorPower m).amp x * η.amp PUnit.unit *
        (star ((ν.tensorPower m).amp y) * star (η.amp PUnit.unit)) =
          ((ν.tensorPower m).amp x * star ((ν.tensorPower m).amp y)) *
            (η.amp PUnit.unit * star (η.amp PUnit.unit)) := by
          ring
    _ = (ν.tensorPower m).amp x * star ((ν.tensorPower m).amp y) := by
          rw [hη]
          ring

private theorem tensorPower_reindex_addZero_state_eq_tensorPower_state
    (ν : PureVector a) (m : ℕ) :
    ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).state =
      ν.state.tensorPower (m + 0) := by
  rw [PureVector.reindex_state, PureVector.tensorPower_state]
  apply State.ext
  ext x y
  simp [State.tensorPower_matrix_apply, tensorPowerAddZeroEquiv]

private theorem tensorPower_reindex_addZero_state_reindex_perm_symm_eq
    (ν : PureVector a) (m : ℕ) (σ : Equiv.Perm (Fin (m + 0))) :
    (((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).state.reindex
        (permEquiv (a := a) (m + 0) σ).symm) =
      ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).state := by
  rw [tensorPower_reindex_addZero_state_eq_tensorPower_state]
  apply State.ext
  ext x y
  have h := congrArg State.matrix
    (State.permutationChannel_apply_tensorPower (a := a) ν.state (m + 0) σ)
  change (permutationChannel (a := a) (m + 0) σ).map
      (ν.state.tensorPower (m + 0)).matrix =
    (ν.state.tensorPower (m + 0)).matrix at h
  simpa [State.reindex_matrix, permutationChannel_map_apply] using congrFun (congrFun h x) y

theorem PureVector.isRennerMIIDIn_zero_state_eq_tensorPower_reindex
    {m : ℕ} {ψ : PureVector (TensorPower a (m + 0))} {ν : PureVector a}
    (hψ : ψ.IsRennerMIIDIn (a := a) (m := m) (r := 0) ν) :
    ψ.state = ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).state := by
  rcases hψ with ⟨σ, η, hψ⟩
  rw [hψ]
  rw [pure_prod_zero_reindex_state_eq_tensorPower_reindex]
  exact tensorPower_reindex_addZero_state_reindex_perm_symm_eq (a := a) ν m σ

theorem PureVector.tensorPower_reindex_addZero_isRennerMIIDIn_zero
    (ν : PureVector a) (m : ℕ) :
    ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).IsRennerMIIDIn
      (a := a) (m := m) (r := 0) ν := by
  refine ⟨1, ν.tensorPower 0, ?_⟩
  simpa using (pure_prod_zero_reindex_state_eq_tensorPower_reindex (a := a)
    ν m (ν.tensorPower 0)).symm

private theorem RennerMIIDSubspace_zero_le_tensorPower_span
    (m : ℕ) (ν : PureVector a) :
    RennerMIIDSubspace a m 0 ν ≤
      Submodule.span ℂ
        ({WithLp.toLp 2
            ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).amp} :
          Set (EuclideanSpace ℂ (TensorPower a (m + 0)))) := by
  rw [RennerMIIDSubspace]
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ⟨ψ, hψ, rfl⟩
  have hstate :=
    PureVector.isRennerMIIDIn_zero_state_eq_tensorPower_reindex (a := a) hψ
  rcases pureVector_state_eq_colinear
      (a := TensorPower a (m + 0)) ψ
      ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)) hstate with ⟨c, hc⟩
  have hv :
      WithLp.toLp 2 ψ.amp =
        c • WithLp.toLp 2
          ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).amp := by
    ext x
    exact congrFun hc x
  rw [hv]
  exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))

private theorem tensorPower_span_le_RennerMIIDSubspace_zero
    (m : ℕ) (ν : PureVector a) :
    Submodule.span ℂ
        ({WithLp.toLp 2
            ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).amp} :
          Set (EuclideanSpace ℂ (TensorPower a (m + 0)))) ≤
      RennerMIIDSubspace a m 0 ν := by
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_singleton_iff] at hv
  subst hv
  exact pureVector_mem_RennerMIIDSubspace (a := a)
    (PureVector.tensorPower_reindex_addZero_isRennerMIIDIn_zero (a := a) ν m)

private theorem RennerMIIDSubspace_zero_eq_tensorPower_span
    (m : ℕ) (ν : PureVector a) :
    RennerMIIDSubspace a m 0 ν =
      Submodule.span ℂ
        ({WithLp.toLp 2
            ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).amp} :
          Set (EuclideanSpace ℂ (TensorPower a (m + 0)))) :=
  le_antisymm
    (RennerMIIDSubspace_zero_le_tensorPower_span (a := a) m ν)
    (tensorPower_span_le_RennerMIIDSubspace_zero (a := a) m ν)

set_option synthInstance.maxHeartbeats 80000 in
private theorem starProjection_singleton_apply {ι : Type _} [Fintype ι] [DecidableEq ι]
    (v x : EuclideanSpace ℂ ι) (hv : inner ℂ v v = 1)
    [hK : (Submodule.span ℂ ({v} : Set (EuclideanSpace ℂ ι))).HasOrthogonalProjection] :
    (Submodule.span ℂ ({v} : Set (EuclideanSpace ℂ ι))).starProjection x =
      inner ℂ v x • v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro w hw
    rw [Submodule.mem_span_singleton] at hw
    rcases hw with ⟨c, rfl⟩
    by_cases hc : c = 0
    · simp [hc]
    · simp [inner_sub_left, inner_smul_right, inner_smul_left, hc]
      have hnormsq : ((‖v‖ : ℂ) ^ 2) = 1 := by
        simpa [inner_self_eq_norm_sq_to_K] using hv
      rw [hnormsq]
      ring

set_option synthInstance.maxHeartbeats 80000 in
private theorem starProjection_singleton_matrix_eq_rankOne {ι : Type _}
    [Fintype ι] [DecidableEq ι] (ψ : ι → ℂ)
    (hψ : (rankOneMatrix ψ).trace = 1)
    [hK : (Submodule.span ℂ ({WithLp.toLp 2 ψ} :
      Set (EuclideanSpace ℂ ι))).HasOrthogonalProjection] :
    Matrix.toEuclideanLin.symm
      ((Submodule.span ℂ ({WithLp.toLp 2 ψ} : Set (EuclideanSpace ℂ ι))).starProjection.toLinearMap) =
      rankOneMatrix ψ := by
  apply Matrix.toEuclideanLin.injective
  ext x i
  have hv : inner ℂ (WithLp.toLp 2 ψ) (WithLp.toLp 2 ψ) = 1 := by
    rw [EuclideanSpace.inner_toLp_toLp]
    simpa [rankOneMatrix_trace, dotProduct, mul_comm] using hψ
  have happ := congrFun (congrArg WithLp.ofLp
    (starProjection_singleton_apply (v := WithLp.toLp 2 ψ) (x := x) hv)) i
  simp [Matrix.toEuclideanLin, rankOneMatrix_apply, Matrix.mulVec, dotProduct,
    PiLp.inner_apply, happ, Finset.mul_sum, mul_comm, mul_left_comm]

private theorem RennerMIIDSubspace_zero_starProjection_apply
    (m : ℕ) (ν : PureVector a)
    (x : EuclideanSpace ℂ (TensorPower a (m + 0))) :
    (RennerMIIDSubspace a m 0 ν).starProjection x =
      inner ℂ
        (WithLp.toLp 2
          ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).amp) x •
        WithLp.toLp 2
          ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).amp := by
  let v : EuclideanSpace ℂ (TensorPower a (m + 0)) :=
    WithLp.toLp 2 ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).amp
  have hv : inner ℂ v v = 1 := by
    rw [EuclideanSpace.inner_toLp_toLp]
    simpa [v, rankOneMatrix_trace, dotProduct, mul_comm] using
      ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).trace_rankOne_eq_one
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply tensorPower_span_le_RennerMIIDSubspace_zero (a := a) m ν
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro w hw
    have hwspan := RennerMIIDSubspace_zero_le_tensorPower_span (a := a) m ν hw
    rw [Submodule.mem_span_singleton] at hwspan
    rcases hwspan with ⟨c, rfl⟩
    by_cases hc : c = 0
    · simp [hc]
    · simp [inner_sub_left, inner_smul_right, inner_smul_left, hc]
      have hnormsq : ((‖v‖ : ℂ) ^ 2) = 1 := by
        simpa [inner_self_eq_norm_sq_to_K] using hv
      rw [hnormsq]
      ring

theorem rennerMIIDProjectorId_zero_eq_rankOneTensorPower
    (m : ℕ) (ν : PureVector a) :
    rennerMIIDProjectorId (a := a) m 0 ν =
      rankOneMatrix ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).amp := by
  apply Matrix.toEuclideanLin.injective
  ext x i
  have happ := congrFun (congrArg WithLp.ofLp
    (RennerMIIDSubspace_zero_starProjection_apply (a := a) m ν x)) i
  simp [rennerMIIDProjectorId, rennerMIIDProjectorFor, Matrix.toEuclideanLin,
    rankOneMatrix_apply, Matrix.mulVec, dotProduct, PiLp.inner_apply, happ,
    Finset.mul_sum, mul_comm, mul_left_comm]

/-- A state supported in the Renner m-IID span is fixed by the corresponding
orthogonal-projector sandwich. -/
theorem State.rennerMIIDProjector_sandwich_eq_of_supported {m r : ℕ}
    {ν : PureVector a} {ρ : State (TensorPower a (m + r))}
    (hρ : ρ.SupportedOnRennerMIIDSubspace (a := a) (m := m) (r := r) ν) :
    rennerMIIDProjectorFor (a := a) m r ν * ρ.matrix *
        rennerMIIDProjectorFor (a := a) m r ν = ρ.matrix := by
  exact projection_sandwich_fixed_of_le ρ
    (rennerMIIDProjectorFor (a := a) m r ν)
    (rennerMIIDProjectorFor_posSemidef (a := a) ν)
    (rennerMIIDProjectorFor_idempotent (a := a) ν)
    hρ

namespace State

private theorem matrix_le_one (ρ : State a) :
    ρ.matrix ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := ρ.pos.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : ρ.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using ρ.pos.1.spectral_theorem
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp [U]
  have heig_sum : ∑ i, ρ.pos.1.eigenvalues i = 1 := by
    have hc : (∑ i, ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)) = 1 := by
      exact ρ.pos.1.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
    exact Complex.ofReal_injective (by simpa using hc)
  have heig_le_one : ∀ i, ρ.pos.1.eigenvalues i ≤ 1 := by
    intro i
    have hnonneg (j : a) : 0 ≤ ρ.pos.1.eigenvalues j :=
      ρ.pos.eigenvalues_nonneg j
    calc ρ.pos.1.eigenvalues i
        ≤ ρ.pos.1.eigenvalues i +
            ∑ j ∈ Finset.univ.erase i, ρ.pos.1.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
      _ = ∑ j, ρ.pos.1.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => ρ.pos.1.eigenvalues j) (Finset.mem_univ i)
      _ = 1 := heig_sum
  have hsub :
      1 - ρ.matrix = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
    rw [hdiag]
    have hUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
      simp
    calc
      1 - (U : CMatrix a) * D * star (U : CMatrix a) =
          (U : CMatrix a) * 1 * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
            rw [Matrix.mul_one, hUstar]
      _ = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
            noncomm_ring
  have hdiag_sub :
      (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((1 : ℝ) - ρ.pos.1.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (1 : ℝ) - ρ.pos.1.eigenvalues i := by
    exact sub_nonneg.mpr (heig_le_one i)
  exact_mod_cast hnonneg

end State

/-- Conversely, a state fixed by the Renner m-IID projector sandwich is
supported in the Renner m-IID span. -/
theorem State.supportedOnRennerMIIDSubspace_of_projector_sandwich_eq {m r : ℕ}
    {ν : PureVector a} {ρ : State (TensorPower a (m + r))}
    (hfixed :
      rennerMIIDProjectorFor (a := a) m r ν * ρ.matrix *
          rennerMIIDProjectorFor (a := a) m r ν = ρ.matrix) :
    ρ.SupportedOnRennerMIIDSubspace (a := a) (m := m) (r := r) ν := by
  let P : CMatrix (TensorPower a (m + r)) := rennerMIIDProjectorFor (a := a) m r ν
  have hconj : P.conjTranspose * ρ.matrix * P ≤ P.conjTranspose * 1 * P :=
    star_left_conjugate_le_conjugate (matrix_le_one ρ) P
  simpa [State.SupportedOnRennerMIIDSubspace, P,
    (rennerMIIDProjectorFor_isHermitian (a := a) ν).eq,
    rennerMIIDProjectorFor_idempotent (a := a) ν, Matrix.mul_assoc,
    hfixed] using hconj

/-- Source-facing support equivalence for the Renner m-IID projector. -/
theorem State.supportedOnRennerMIIDSubspace_iff_projector_sandwich_eq {m r : ℕ}
    {ν : PureVector a} {ρ : State (TensorPower a (m + r))} :
    ρ.SupportedOnRennerMIIDSubspace (a := a) (m := m) (r := r) ν ↔
      rennerMIIDProjectorFor (a := a) m r ν * ρ.matrix *
          rennerMIIDProjectorFor (a := a) m r ν = ρ.matrix := by
  constructor
  · exact State.rennerMIIDProjector_sandwich_eq_of_supported (a := a)
  · exact State.supportedOnRennerMIIDSubspace_of_projector_sandwich_eq (a := a)

/-- Renner's rotated `r=0` m-IID projector, reindexed onto `TensorPower a m`.

The generic projector lives on `TensorPower a (m+0)`.  The source
formula for `ρ_U^n` uses `P_U^{k,0}` as an operator on the traced `k` systems,
so this definition removes only that definitional bookkeeping. -/
def rennerMIIDProjectorZero (m : ℕ) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) : CMatrix (TensorPower a m) :=
  (rennerMIIDProjector (a := a) m 0 ν U).submatrix
    (tensorPowerAddZeroEquiv a m) (tensorPowerAddZeroEquiv a m)

/-- The fixed/base `r=0` m-IID projector, reindexed onto `TensorPower a m`. -/
def rennerMIIDProjectorIdZero (m : ℕ) (ν : PureVector a) :
    CMatrix (TensorPower a m) :=
  (rennerMIIDProjectorId (a := a) m 0 ν).submatrix
    (tensorPowerAddZeroEquiv a m) (tensorPowerAddZeroEquiv a m)

theorem rennerMIIDProjectorIdZero_eq_rankOneTensorPower
    (m : ℕ) (ν : PureVector a) :
    rennerMIIDProjectorIdZero (a := a) m ν =
      rankOneMatrix (ν.tensorPower m).amp := by
  rw [rennerMIIDProjectorIdZero, rennerMIIDProjectorId_zero_eq_rankOneTensorPower]
  ext x y
  simp [rankOneMatrix_apply, PureVector.reindex_amp, tensorPowerAddZeroEquiv]

theorem rennerMIIDProjectorIdZero_trace_eq_one
    (m : ℕ) (ν : PureVector a) :
    (rennerMIIDProjectorIdZero (a := a) m ν).trace = 1 := by
  rw [rennerMIIDProjectorIdZero_eq_rankOneTensorPower]
  exact (ν.tensorPower m).trace_rankOne_eq_one

private theorem trace_submatrix_equiv_renner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : CMatrix κ) :
    (M.submatrix e e).trace = M.trace := by
  classical
  unfold Matrix.trace
  exact Fintype.sum_equiv e (fun i => M (e i) (e i)) (fun k => M k k) (by simp)

theorem rennerMIIDProjector_trace_eq_id {m r : ℕ} (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    (rennerMIIDProjector (a := a) m r ν U).trace =
      (rennerMIIDProjectorId (a := a) m r ν).trace := by
  let Un : CMatrix (TensorPower a (m + r)) := unitaryTensorPowerMatrix U (m + r)
  let P : CMatrix (TensorPower a (m + r)) := rennerMIIDProjectorId (a := a) m r ν
  have hstar : star Un * Un = 1 := by
    simp [Un]
  dsimp [rennerMIIDProjector]
  change (Un * P * star Un).trace = P.trace
  calc
    (Un * P * star Un).trace = (star Un * (Un * P)).trace := by
      simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle Un P (star Un)
    _ = ((star Un * Un) * P).trace := by rw [Matrix.mul_assoc]
    _ = (1 * P).trace := by rw [hstar]
    _ = P.trace := by simp

/-- The rotated Renner m-IID projector is exactly the Haar-twirl integrand of
the fixed/base m-IID projector. -/
theorem rennerMIIDProjector_eq_unitaryTwirlIntegrand
    (m r : ℕ) (ν : PureVector a) (U : Matrix.unitaryGroup a ℂ) :
    rennerMIIDProjector (a := a) m r ν U =
      unitaryTwirlIntegrand (a := a) (m + r)
        (rennerMIIDProjectorId (a := a) m r ν) U := rfl

private theorem rennerMIIDProjector_integrable
    [Nonempty a] (m r : ℕ) (ν : PureVector a) :
    Integrable
      (fun U : Matrix.unitaryGroup a ℂ =>
        rennerMIIDProjector (a := a) m r ν U)
      (unitaryHaarMeasure (a := a)) := by
  have h := unitaryTwirl_integrand_integrable (a := a) (m + r)
    (rennerMIIDProjectorId (a := a) m r ν)
  simpa [rennerMIIDProjector_eq_unitaryTwirlIntegrand] using h

private theorem rennerMIIDProjector_continuous
    (m r : ℕ) (ν : PureVector a) :
    Continuous fun U : Matrix.unitaryGroup a ℂ =>
      rennerMIIDProjector (a := a) m r ν U := by
  simpa [rennerMIIDProjector_eq_unitaryTwirlIntegrand] using
    unitaryTwirl_integrand_continuous (a := a) (m + r)
      (rennerMIIDProjectorId (a := a) m r ν)

theorem rennerMIIDProjectorZero_trace_eq_one
    (m : ℕ) (ν : PureVector a) (U : Matrix.unitaryGroup a ℂ) :
    (rennerMIIDProjectorZero (a := a) m ν U).trace = 1 := by
  rw [rennerMIIDProjectorZero, trace_submatrix_equiv_renner,
    rennerMIIDProjector_trace_eq_id, rennerMIIDProjectorId_zero_eq_rankOneTensorPower]
  exact ((ν.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).trace_rankOne_eq_one

private theorem unitaryTensorPowerMatrix_addZero_submatrix
    (m : ℕ) (U : Matrix.unitaryGroup a ℂ) :
    (unitaryTensorPowerMatrix U (m + 0) : CMatrix (TensorPower a (m + 0))).submatrix
        (tensorPowerAddZeroEquiv a m) (tensorPowerAddZeroEquiv a m) =
      (unitaryTensorPowerMatrix U m : CMatrix (TensorPower a m)) := by
  ext x y
  rw [Matrix.submatrix_apply, unitaryTensorPowerMatrix_apply_eq_fin_prod,
    unitaryTensorPowerMatrix_apply_eq_fin_prod]
  simp [tensorPowerAddZeroEquiv]

private theorem rankOneMatrix_reindex_addZero_submatrix
    (m : ℕ) (ψ : PureVector a) :
    (rankOneMatrix ((ψ.tensorPower m).reindex (tensorPowerAddZeroEquiv a m)).amp).submatrix
        (tensorPowerAddZeroEquiv a m) (tensorPowerAddZeroEquiv a m) =
      rankOneMatrix (ψ.tensorPower m).amp := by
  ext x y
  simp [rankOneMatrix_apply, PureVector.reindex_amp, tensorPowerAddZeroEquiv]

private theorem submatrix_equiv_mul_renner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A B : CMatrix κ) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e := by
  classical
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Fintype.sum_equiv e
    (fun x => A (e i) (e x) * B (e x) (e j))
    (fun y => A (e i) y * B y (e j))
    (by simp)).symm

private theorem submatrix_equiv_star_renner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : CMatrix κ) :
    (star A).submatrix e e = star (A.submatrix e e) := by
  ext i j
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private theorem submatrix_equiv_symm_submatrix_equiv_renner {ι κ : Type*}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) (A : CMatrix κ) :
    (A.submatrix e e).submatrix e.symm e.symm = A := by
  ext i j
  simp

private theorem unitaryTwirlIntegrand_takeDrop_submatrix
    (n k : ℕ) (A : CMatrix (Prod (TensorPower a n) (TensorPower a k)))
    (U : Matrix.unitaryGroup a ℂ) :
    (unitaryTwirlIntegrand (a := a) (n + k)
        (A.submatrix (tensorPowerTakeDropEquiv a n k)
          (tensorPowerTakeDropEquiv a n k)) U).submatrix
        (tensorPowerTakeDropEquiv a n k).symm
        (tensorPowerTakeDropEquiv a n k).symm =
      Matrix.kronecker
          (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
          (unitaryTensorPowerMatrix U k : CMatrix (TensorPower a k)) *
        A *
        star (Matrix.kronecker
          (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
          (unitaryTensorPowerMatrix U k : CMatrix (TensorPower a k))) := by
  let e := tensorPowerTakeDropEquiv a n k
  let Un : CMatrix (TensorPower a (n + k)) := unitaryTensorPowerMatrix U (n + k)
  let Us : CMatrix (Prod (TensorPower a n) (TensorPower a k)) :=
    Matrix.kronecker
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
      (unitaryTensorPowerMatrix U k : CMatrix (TensorPower a k))
  have hU : Un.submatrix e.symm e.symm = Us := by
    simpa [Un, Us, e] using
      unitaryTensorPowerMatrix_takeDrop_submatrix (a := a) n k U
  dsimp [unitaryTwirlIntegrand]
  change (Un * A.submatrix e e * star Un).submatrix e.symm e.symm =
    Us * A * star Us
  rw [submatrix_equiv_mul_renner, submatrix_equiv_mul_renner,
    submatrix_equiv_star_renner]
  rw [hU, submatrix_equiv_symm_submatrix_equiv_renner]

theorem rennerMIIDProjectorZero_eq_unitary_rankOneTensorPower
    (m : ℕ) (ν : PureVector a) (U : Matrix.unitaryGroup a ℂ) :
    rennerMIIDProjectorZero (a := a) m ν U =
      (unitaryTensorPowerMatrix U m : CMatrix (TensorPower a m)) *
        rankOneMatrix (ν.tensorPower m).amp *
          star (unitaryTensorPowerMatrix U m : CMatrix (TensorPower a m)) := by
  rw [rennerMIIDProjectorZero, rennerMIIDProjector, rennerMIIDProjectorId_zero_eq_rankOneTensorPower]
  rw [submatrix_equiv_mul_renner, submatrix_equiv_mul_renner,
    unitaryTensorPowerMatrix_addZero_submatrix,
    rankOneMatrix_reindex_addZero_submatrix,
    submatrix_equiv_star_renner, unitaryTensorPowerMatrix_addZero_submatrix]

theorem rennerMIIDProjectorZero_eq_unitaryTwirlIntegrand
    (m : ℕ) (ν : PureVector a) (U : Matrix.unitaryGroup a ℂ) :
    rennerMIIDProjectorZero (a := a) m ν U =
      unitaryTwirlIntegrand (a := a) m (rankOneMatrix (ν.tensorPower m).amp) U := by
  rw [rennerMIIDProjectorZero_eq_unitary_rankOneTensorPower]
  rfl

private theorem rennerGammaIntegrand_takeDrop_submatrix [Nonempty a]
    (ν : PureVector a) (n k r : ℕ) (U : Matrix.unitaryGroup a ℂ) :
    (unitaryTwirlIntegrand (a := a) ((n + r) + k)
        (((Matrix.kronecker
            ((1 : CMatrix (TensorPower a (n + r))) -
              rennerMIIDProjectorId (a := a) n r ν)
            (rennerMIIDProjectorIdZero (a := a) k ν)).submatrix
              (tensorPowerTakeDropEquiv a (n + r) k)
              (tensorPowerTakeDropEquiv a (n + r) k))) U).submatrix
        (tensorPowerTakeDropEquiv a (n + r) k).symm
        (tensorPowerTakeDropEquiv a (n + r) k).symm =
      Matrix.kronecker
        ((1 : CMatrix (TensorPower a (n + r))) -
          rennerMIIDProjector (a := a) n r ν U)
        (rennerMIIDProjectorZero (a := a) k ν U) := by
  let UL : CMatrix (TensorPower a (n + r)) := unitaryTensorPowerMatrix U (n + r)
  let UR : CMatrix (TensorPower a k) := unitaryTensorPowerMatrix U k
  let Pid : CMatrix (TensorPower a (n + r)) := rennerMIIDProjectorId (a := a) n r ν
  let P0id : CMatrix (TensorPower a k) := rennerMIIDProjectorIdZero (a := a) k ν
  have hsplit :=
    unitaryTwirlIntegrand_takeDrop_submatrix (a := a) (n + r) k
      (Matrix.kronecker ((1 : CMatrix (TensorPower a (n + r))) - Pid) P0id) U
  rw [hsplit]
  have hleft :
      UL * ((1 : CMatrix (TensorPower a (n + r))) - Pid) * star UL =
        (1 : CMatrix (TensorPower a (n + r))) -
          rennerMIIDProjector (a := a) n r ν U := by
    have hunit : UL * star UL = 1 := by
      simp [UL]
    dsimp [rennerMIIDProjector, UL, Pid] at hunit ⊢
    calc
      unitaryTensorPowerMatrix U (n + r) *
            (1 - rennerMIIDProjectorId (a := a) n r ν) *
            star (unitaryTensorPowerMatrix U (n + r) : CMatrix (TensorPower a (n + r))) =
          unitaryTensorPowerMatrix U (n + r) * 1 *
              star (unitaryTensorPowerMatrix U (n + r) : CMatrix (TensorPower a (n + r))) -
            unitaryTensorPowerMatrix U (n + r) * rennerMIIDProjectorId (a := a) n r ν *
              star (unitaryTensorPowerMatrix U (n + r) : CMatrix (TensorPower a (n + r))) := by
            noncomm_ring
      _ = 1 -
            unitaryTensorPowerMatrix U (n + r) * rennerMIIDProjectorId (a := a) n r ν *
              star (unitaryTensorPowerMatrix U (n + r) : CMatrix (TensorPower a (n + r))) := by
            rw [Matrix.mul_one, hunit]
  have hright :
      UR * P0id * star UR =
        rennerMIIDProjectorZero (a := a) k ν U := by
    rw [rennerMIIDProjectorZero_eq_unitary_rankOneTensorPower]
    dsimp [UR, P0id]
    rw [rennerMIIDProjectorIdZero_eq_rankOneTensorPower]
  have hstarK :
      star (Matrix.kronecker UL UR) =
        Matrix.kronecker (star UL) (star UR) := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.conjTranspose_kronecker UL UR
  rw [hstarK]
  change
    Matrix.kronecker UL UR * Matrix.kronecker (1 - Pid) P0id *
        Matrix.kronecker (star UL) (star UR) =
      Matrix.kronecker
        ((1 : CMatrix (TensorPower a (n + r))) -
          rennerMIIDProjector (a := a) n r ν U)
        (rennerMIIDProjectorZero (a := a) k ν U)
  have hmul1 :
      Matrix.kronecker UL UR * Matrix.kronecker (1 - Pid) P0id =
        Matrix.kronecker (UL * (1 - Pid)) (UR * P0id) :=
    (Matrix.mul_kronecker_mul UL (1 - Pid) UR P0id).symm
  have hmul2 :
      Matrix.kronecker (UL * (1 - Pid)) (UR * P0id) *
          Matrix.kronecker (star UL) (star UR) =
        Matrix.kronecker ((UL * (1 - Pid)) * star UL)
          ((UR * P0id) * star UR) :=
    (Matrix.mul_kronecker_mul (UL * (1 - Pid)) (star UL)
      (UR * P0id) (star UR)).symm
  calc
    Matrix.kronecker UL UR * Matrix.kronecker (1 - Pid) P0id *
        Matrix.kronecker (star UL) (star UR) =
        Matrix.kronecker (UL * (1 - Pid)) (UR * P0id) *
          Matrix.kronecker (star UL) (star UR) := by
          rw [hmul1]
    _ = Matrix.kronecker ((UL * (1 - Pid)) * star UL)
          ((UR * P0id) * star UR) := by
          rw [hmul2]
    _ = Matrix.kronecker
          ((1 : CMatrix (TensorPower a (n + r))) -
            rennerMIIDProjector (a := a) n r ν U)
          (rennerMIIDProjectorZero (a := a) k ν U) := by
          simp [hleft, hright]

theorem rennerMIIDProjectorIdZero_isHermitian
    (m : ℕ) (ν : PureVector a) :
    (rennerMIIDProjectorIdZero (a := a) m ν).IsHermitian := by
  rw [rennerMIIDProjectorIdZero_eq_rankOneTensorPower]
  exact rankOneMatrix_isHermitian (ν.tensorPower m).amp

theorem rennerMIIDProjectorIdZero_posSemidef
    (m : ℕ) (ν : PureVector a) :
    (rennerMIIDProjectorIdZero (a := a) m ν).PosSemidef := by
  rw [rennerMIIDProjectorIdZero_eq_rankOneTensorPower]
  exact rankOneMatrix_pos (ν.tensorPower m).amp

theorem rennerMIIDProjectorIdZero_idempotent
    (m : ℕ) (ν : PureVector a) :
    rennerMIIDProjectorIdZero (a := a) m ν *
        rennerMIIDProjectorIdZero (a := a) m ν =
      rennerMIIDProjectorIdZero (a := a) m ν := by
  rw [rennerMIIDProjectorIdZero_eq_rankOneTensorPower]
  exact (ν.tensorPower m).state_matrix_mul_self

theorem rennerMIIDProjectorIdZero_le_one
    (m : ℕ) (ν : PureVector a) :
    rennerMIIDProjectorIdZero (a := a) m ν ≤
      (1 : CMatrix (TensorPower a m)) := by
  rw [Matrix.le_iff]
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    (rennerMIIDProjectorIdZero (a := a) m ν)
    (rennerMIIDProjectorIdZero_posSemidef (a := a) m ν)
    (rennerMIIDProjectorIdZero_idempotent (a := a) m ν)

theorem rennerMIIDProjectorZero_posSemidef
    (m : ℕ) (ν : PureVector a) (U : Matrix.unitaryGroup a ℂ) :
    (rennerMIIDProjectorZero (a := a) m ν U).PosSemidef := by
  simpa [rennerMIIDProjectorZero] using
    (rennerMIIDProjector_posSemidef (a := a) (m := m) (r := 0) ν U).submatrix
      (tensorPowerAddZeroEquiv a m)

theorem rennerMIIDProjectorZero_isHermitian
    (m : ℕ) (ν : PureVector a) (U : Matrix.unitaryGroup a ℂ) :
    (rennerMIIDProjectorZero (a := a) m ν U).IsHermitian :=
  (rennerMIIDProjectorZero_posSemidef (a := a) m ν U).isHermitian

theorem rennerMIIDProjectorZero_idempotent
    (m : ℕ) (ν : PureVector a) (U : Matrix.unitaryGroup a ℂ) :
    rennerMIIDProjectorZero (a := a) m ν U *
        rennerMIIDProjectorZero (a := a) m ν U =
      rennerMIIDProjectorZero (a := a) m ν U := by
  rw [rennerMIIDProjectorZero]
  ext x y
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  have hP := congrFun (congrFun
    (rennerMIIDProjector_idempotent (a := a) (m := m) (r := 0) ν U)
      ((tensorPowerAddZeroEquiv a m) x))
      ((tensorPowerAddZeroEquiv a m) y)
  simpa [Matrix.mul_apply] using hP

theorem rennerMIIDProjectorZero_le_one
    (m : ℕ) (ν : PureVector a) (U : Matrix.unitaryGroup a ℂ) :
    rennerMIIDProjectorZero (a := a) m ν U ≤
      (1 : CMatrix (TensorPower a m)) := by
  rw [Matrix.le_iff]
  exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
    (rennerMIIDProjectorZero (a := a) m ν U)
    (rennerMIIDProjectorZero_posSemidef (a := a) m ν U)
    (rennerMIIDProjectorZero_idempotent (a := a) m ν U)

theorem PureVector.tensorPower_amp_eq_fin_prod (ν : PureVector a) :
    ∀ (n : ℕ) (x : TensorPower a n),
      (ν.tensorPower n).amp x = ∏ i : Fin n, ν.amp (tensorPowerEquiv n x i)
  | 0, x => by
      cases x
      simp [PureVector.tensorPower]
  | n + 1, (x0, xs) => by
      change ν.amp x0 * (ν.tensorPower n).amp xs =
        ∏ i : Fin (n + 1), ν.amp (tensorPowerEquiv (n + 1) (x0, xs) i)
      rw [PureVector.tensorPower_amp_eq_fin_prod ν n xs, Fin.prod_univ_succ]
      simp

theorem PureVector.tensorPower_amp_perm (ν : PureVector a) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : TensorPower a n) :
    (ν.tensorPower n).amp ((permEquiv (a := a) n σ) x) =
      (ν.tensorPower n).amp x := by
  rw [PureVector.tensorPower_amp_eq_fin_prod, PureVector.tensorPower_amp_eq_fin_prod]
  rw [tensorPowerEquiv_permEquiv]
  exact Equiv.prod_comp σ.symm (fun i => ν.amp (tensorPowerEquiv n x i))

theorem PureVector.tensorPower_amp_mem_symmetricSubspace
    (ν : PureVector a) (n : ℕ) :
    (ν.tensorPower n).amp ∈ symmetricSubspace (a := a) n := by
  intro σ
  ext x
  exact PureVector.tensorPower_amp_perm (a := a) ν n σ x

theorem State.pureTensorPower_supportedOnSymmetricSubspace
    (ν : PureVector a) (n : ℕ) :
    (ν.tensorPower n).state.SupportedOnSymmetricSubspace (a := a) := by
  dsimp [State.SupportedOnSymmetricSubspace, PureVector.state]
  apply rankOneMatrix_le_projection_of_mulVec_eq_self
  · exact symmetricProjectionMatrix_posSemidef (a := a) n
  · exact symmetricProjectionMatrix_idempotent (a := a) n
  · exact (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self
      (a := a) n (ν.tensorPower n).amp).mp
      (PureVector.tensorPower_amp_mem_symmetricSubspace (a := a) ν n)
  · exact (ν.tensorPower n).trace_rankOne_eq_one

theorem rennerMIIDProjectorIdZero_supportedOnSymmetricSubspace
    (m : ℕ) (ν : PureVector a) :
    (ν.tensorPower m).state.SupportedOnSymmetricSubspace (a := a) :=
  State.pureTensorPower_supportedOnSymmetricSubspace (a := a) ν m

theorem rennerMIIDProjectorZero_average_mul_symmetricProjectionMatrix
    [Nonempty a] (m : ℕ) (ν : PureVector a) :
    (∫ U : Matrix.unitaryGroup a ℂ,
        rennerMIIDProjectorZero (a := a) m ν U
        ∂unitaryHaarMeasure (a := a)) *
        symmetricProjectionMatrix (a := a) m =
      (((Fintype.card (TensorPowerProfile a m) : ℂ)⁻¹) : ℂ) •
        symmetricProjectionMatrix (a := a) m := by
  let A : CMatrix (TensorPower a m) := rankOneMatrix (ν.tensorPower m).amp
  have hAvg :
      (∫ U : Matrix.unitaryGroup a ℂ,
          rennerMIIDProjectorZero (a := a) m ν U
          ∂unitaryHaarMeasure (a := a)) =
        unitaryTwirl m A := by
    rw [unitaryTwirl]
    congr 1
    funext U
    simpa [A] using
      rennerMIIDProjectorZero_eq_unitaryTwirlIntegrand (a := a) m ν U
  have htracePA :
      (symmetricProjectionMatrix (a := a) m * A).trace = 1 := by
    have hmulVec :
        (symmetricProjectionMatrix (a := a) m).mulVec (ν.tensorPower m).amp =
          (ν.tensorPower m).amp :=
      (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self
        (a := a) m (ν.tensorPower m).amp).mp
        (PureVector.tensorPower_amp_mem_symmetricSubspace (a := a) ν m)
    have hmul :
        symmetricProjectionMatrix (a := a) m * A = A := by
      simpa [A] using
        rankOneMatrix_mul_of_mulVec_eq_self
          (symmetricProjectionMatrix (a := a) m) (ν.tensorPower m).amp hmulVec
    rw [hmul]
    exact (ν.tensorPower m).trace_rankOne_eq_one
  rw [hAvg, unitaryTwirl_mul_symmetricProjectionMatrix_eq_trace_smul]
  rw [htracePA, symmetricProjectionMatrix_trace_eq_profile_card]
  simp

private theorem rennerMIIDProjectorZero_integrable
    [Nonempty a] (m : ℕ) (ν : PureVector a) :
    Integrable
      (fun U : Matrix.unitaryGroup a ℂ =>
        rennerMIIDProjectorZero (a := a) m ν U)
      (unitaryHaarMeasure (a := a)) := by
  have h := unitaryTwirl_integrand_integrable (a := a) m
    (rankOneMatrix (ν.tensorPower m).amp)
  convert h using 1
  ext U x y
  rw [rennerMIIDProjectorZero_eq_unitaryTwirlIntegrand]

private theorem rennerMIIDProjectorZero_continuous
    (m : ℕ) (ν : PureVector a) :
    Continuous fun U : Matrix.unitaryGroup a ℂ =>
      rennerMIIDProjectorZero (a := a) m ν U := by
  have h := unitaryTwirl_integrand_continuous (a := a) m
    (rankOneMatrix (ν.tensorPower m).amp)
  convert h using 1
  ext U x y
  rw [rennerMIIDProjectorZero_eq_unitaryTwirlIntegrand]

namespace State

/-- If a state on `n+k` tensor factors is supported on the global symmetric
subspace, then after the source `n|k` split it is fixed by projecting the
right `k` block onto its symmetric subspace. -/
theorem splitRightSymmetricProjection_mul_of_supported {n k : ℕ}
    {ρ : State (TensorPower a (n + k))}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    Matrix.kronecker (1 : CMatrix (TensorPower a n))
        (symmetricProjectionMatrix (a := a) k) *
      (ρ.reindex (tensorPowerTakeDropEquiv a n k)).matrix =
      (ρ.reindex (tensorPowerTakeDropEquiv a n k)).matrix := by
  let e := tensorPowerTakeDropEquiv a n k
  let Pfull : CMatrix (TensorPower a (n + k)) :=
    symmetricProjectionMatrix (a := a) (n + k)
  let Psplit : CMatrix (Prod (TensorPower a n) (TensorPower a k)) :=
    Pfull.submatrix e.symm e.symm
  let Q : CMatrix (Prod (TensorPower a n) (TensorPower a k)) :=
    Matrix.kronecker (1 : CMatrix (TensorPower a n))
      (symmetricProjectionMatrix (a := a) k)
  let ρsplit : CMatrix (Prod (TensorPower a n) (TensorPower a k)) :=
    (ρ.reindex e).matrix
  have hfull_fixed : Pfull * ρ.matrix * Pfull = ρ.matrix := by
    exact projection_sandwich_fixed_of_le ρ Pfull
      (by simpa [Pfull] using symmetricProjectionMatrix_posSemidef (a := a) (n + k))
      (by simpa [Pfull] using symmetricProjectionMatrix_idempotent (a := a) (n + k))
      (by simpa [State.SupportedOnSymmetricSubspace, Pfull] using hρ)
  have hsplit_fixed : Psplit * ρsplit * Psplit = ρsplit := by
    have h := congrArg (fun M : CMatrix (TensorPower a (n + k)) =>
      M.submatrix e.symm e.symm) hfull_fixed
    change (Pfull * ρ.matrix * Pfull).submatrix e.symm e.symm =
      ρ.matrix.submatrix e.symm e.symm at h
    rw [submatrix_equiv_mul_renner, submatrix_equiv_mul_renner] at h
    simpa [Psplit, ρsplit, Pfull, e, State.reindex_matrix, Matrix.mul_assoc] using h
  have hQPs : Q * Psplit = Psplit := by
    simpa [Q, Psplit, Pfull, e] using
      kronecker_one_symmetricProjection_mul_reindexed_symmetricProjection
        (a := a) n k
  calc
    Q * ρsplit = Q * (Psplit * ρsplit * Psplit) := by rw [hsplit_fixed]
    _ = (Q * Psplit) * ρsplit * Psplit := by noncomm_ring
    _ = Psplit * ρsplit * Psplit := by rw [hQPs]
    _ = ρsplit := hsplit_fixed

end State

private noncomputable def deFinettiCMatrixEntryCLM {ι : Type v}
    [Fintype ι] [DecidableEq ι] (i j : ι) : CMatrix ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A i j
       map_add' := by
        intro A B
        rfl
       map_smul' := by
        intro c A
        simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℝ] ℂ)

private theorem integral_cMatrix_apply_apply {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) (i j : ι) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  simpa [deFinettiCMatrixEntryCLM] using
    ((deFinettiCMatrixEntryCLM (ι := ι) i j).integral_comp_comm hf).symm

private theorem integrable_cMatrix_apply_apply {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) (i j : ι) :
    Integrable (fun x => f x i j) μ :=
  (deFinettiCMatrixEntryCLM (ι := ι) i j).integrable_comp hf

private noncomputable def partialTraceBCLM {ι κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] :
    CMatrix (Prod ι κ) →L[ℝ] CMatrix ι :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun X => partialTraceB (a := ι) (b := κ) X
       map_add' := by
        intro X Y
        exact partialTraceB_add (a := ι) (b := κ) X Y
       map_smul' := by
        intro c X
        exact partialTraceB_smul (a := ι) (b := κ) c X } :
      CMatrix (Prod ι κ) →ₗ[ℝ] CMatrix ι)

private theorem partialTraceB_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι κ : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {f : α → CMatrix (Prod ι κ)} (hf : Integrable f μ) :
    partialTraceB (a := ι) (b := κ) (∫ x, f x ∂μ) =
      ∫ x, partialTraceB (a := ι) (b := κ) (f x) ∂μ := by
  simpa [partialTraceBCLM] using
    ((partialTraceBCLM (ι := ι) (κ := κ)).integral_comp_comm hf).symm

private theorem partialTraceB_kronecker_one_left_mul {ι κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (L : CMatrix ι) (X : CMatrix (Prod ι κ)) :
    partialTraceB (a := ι) (b := κ)
      (Matrix.kronecker L (1 : CMatrix κ) * X) =
      L * partialTraceB (a := ι) (b := κ) X := by
  ext i i'
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]

private noncomputable def kroneckerOneMulConstCLM {ι κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : CMatrix (Prod ι κ)) : CMatrix κ →L[ℝ] CMatrix (Prod ι κ) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun P => Matrix.kronecker (1 : CMatrix ι) P * X
       map_add' := by
        intro P Q
        ext i j
        simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring
       map_smul' := by
        intro c P
        ext i j
        simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.smul_apply, RingHom.id_apply]
        change ∑ x, (1 : CMatrix ι) i.1 x.1 * ((c : ℂ) * P i.2 x.2) *
            X x j =
          (c : ℂ) * ∑ x, (1 : CMatrix ι) i.1 x.1 * P i.2 x.2 * X x j
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring } :
      CMatrix κ →ₗ[ℝ] CMatrix (Prod ι κ))

private theorem integral_kronecker_one_mul_const {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι κ : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {f : α → CMatrix κ} (hf : Integrable f μ) (X : CMatrix (Prod ι κ)) :
    (∫ x, Matrix.kronecker (1 : CMatrix ι) (f x) * X ∂μ) =
      Matrix.kronecker (1 : CMatrix ι) (∫ x, f x ∂μ) * X := by
  simpa [kroneckerOneMulConstCLM] using
    (kroneckerOneMulConstCLM (ι := ι) (κ := κ) X).integral_comp_comm hf

private noncomputable def submatrixEquivSymmMulConstCLM {ι κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (X : CMatrix ι) : CMatrix κ →L[ℝ] CMatrix ι :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => M.submatrix e.symm e.symm * X
       map_add' := by
        intro M N
        ext i j
        simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring
       map_smul' := by
        intro c M
        ext i j
        simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.smul_apply,
          RingHom.id_apply]
        change ∑ x, ((c : ℂ) * M (e.symm i) (e.symm x)) * X x j =
          (c : ℂ) * ∑ x, M (e.symm i) (e.symm x) * X x j
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring } :
      CMatrix κ →ₗ[ℝ] CMatrix ι)

private theorem integral_submatrix_equiv_symm_mul_const {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {ι κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {f : α → CMatrix κ} (hf : Integrable f μ) (e : κ ≃ ι) (X : CMatrix ι) :
    (∫ x, (f x).submatrix e.symm e.symm * X ∂μ) =
      (∫ x, f x ∂μ).submatrix e.symm e.symm * X := by
  simpa [submatrixEquivSymmMulConstCLM] using
    (submatrixEquivSymmMulConstCLM e X).integral_comp_comm hf

private noncomputable def definettiCMatrixEntryCLM {ι : Type v}
    [Fintype ι] [DecidableEq ι] (i j : ι) : CMatrix ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => M i j
       map_add' := by intro M N; simp
       map_smul' := by intro c M; simp } : CMatrix ι →ₗ[ℝ] ℂ)

private noncomputable def definettiCMatrixTraceCLM {ι : Type v}
    [Fintype ι] [DecidableEq ι] : CMatrix ι →L[ℝ] ℂ :=
  ∑ i, definettiCMatrixEntryCLM (ι := ι) i i

private theorem integral_trace {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).trace = ∫ x, (f x).trace ∂μ := by
  rw [Matrix.trace]
  change ∑ i, (∫ x, f x ∂μ) i i = ∫ x, ∑ i, f x i i ∂μ
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro i _
    simpa [definettiCMatrixEntryCLM] using
      ((definettiCMatrixEntryCLM (ι := ι) i i).integral_comp_comm hf).symm
  · intro i _
    exact (definettiCMatrixEntryCLM (ι := ι) i i).integrable_comp hf

private noncomputable def definettiCMatrixEntryCLMComplex {ι : Type v}
    [Fintype ι] [DecidableEq ι] (i j : ι) : CMatrix ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => M i j
       map_add' := by intro M N; simp
       map_smul' := by intro c M; simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℂ] ℂ)

private noncomputable def definettiCMatrixConjTransposeCLM {ι : Type v}
    [Fintype ι] [DecidableEq ι] : CMatrix ι →L[ℝ] CMatrix ι :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun M => Matrix.conjTranspose M
       map_add' := by intro M N; simp
       map_smul' := by intro c M; ext i j; simp } : CMatrix ι →ₗ[ℝ] CMatrix ι)

private theorem integral_matrix_conjTranspose {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) :
    Matrix.conjTranspose (∫ x, f x ∂μ) =
      ∫ x, Matrix.conjTranspose (f x) ∂μ := by
  simpa [definettiCMatrixConjTransposeCLM] using
    ((definettiCMatrixConjTransposeCLM (ι := ι)).integral_comp_comm hf).symm

private noncomputable def definettiCMatrixQuadraticCLM {ι : Type v}
    [Fintype ι] [DecidableEq ι] (x : ι → ℂ) : CMatrix ι →L[ℂ] ℂ :=
  ∑ i, ∑ j, (star (x i) * x j) •
    definettiCMatrixEntryCLMComplex (ι := ι) i j

private theorem definettiCMatrixQuadraticCLM_apply {ι : Type v}
    [Fintype ι] [DecidableEq ι] (x : ι → ℂ) (A : CMatrix ι) :
    definettiCMatrixQuadraticCLM x A = dotProduct (star x) (Matrix.mulVec A x) := by
  simp [definettiCMatrixQuadraticCLM, definettiCMatrixEntryCLMComplex,
    Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

private theorem integral_dotProduct_mulVec {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) (x : ι → ℂ) :
    dotProduct (star x) (Matrix.mulVec (∫ t, f t ∂μ) x) =
      ∫ t, dotProduct (star x) (Matrix.mulVec (f t) x) ∂μ := by
  simp_rw [← definettiCMatrixQuadraticCLM_apply x]
  exact
    ((definettiCMatrixQuadraticCLM x).integral_comp_comm hf).symm

private theorem integral_posSemidef_of_forall {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type v} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ)
    (hpos : ∀ t, (f t).PosSemidef) :
    (∫ t, f t ∂μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, integral_matrix_conjTranspose (hf := hf)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => (hpos t).isHermitian.eq
  · intro x
    rw [integral_dotProduct_mulVec (hf := hf) x]
    exact integral_nonneg fun t => (hpos t).dotProduct_mulVec_nonneg x

private theorem trace_re_le_traceNorm {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) :
    A.trace.re ≤ traceNorm A := by
  have hunit := traceNorm_variational_unitary_abs_trace_le A
    (1 : Matrix.unitaryGroup ι ℂ)
  have hre : A.trace.re ≤ Complex.abs A.trace := by
    simpa [Complex.abs] using Complex.re_le_norm A.trace
  have habs : Complex.abs A.trace ≤ traceNorm A := by
    simpa using hunit
  exact le_trans hre habs

private theorem one_sub_projection_posSemidef {ι : Type v}
    [Fintype ι] [DecidableEq ι] {P : CMatrix ι}
    (hPpos : P.PosSemidef) (hPid : P * P = P) :
    (1 - P).PosSemidef :=
  MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent P hPpos hPid

private theorem one_sub_projection_idempotent {ι : Type v}
    [Fintype ι] [DecidableEq ι] {P : CMatrix ι}
    (hPid : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  calc
    (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P := by rw [hPid]; noncomm_ring

private theorem rennerGentle_integral_traceNorm_bound {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (A P : α → CMatrix ι)
    (hDInt : Integrable (fun t => (1 - P t) * A t) μ)
    (hRInt : Integrable (fun t => A t * (1 - P t)) μ)
    (hEInt : Integrable (fun t => (1 - P t) * A t * (1 - P t)) μ)
    (hApos : ∀ t, (A t).PosSemidef)
    (hPpos : ∀ t, (P t).PosSemidef)
    (hPid : ∀ t, P t * P t = P t) :
    traceNorm (∫ t, A t - P t * A t * P t ∂μ) ≤
      3 * traceNorm (∫ t, (1 - P t) * A t ∂μ) := by
  let D : CMatrix ι := ∫ t, (1 - P t) * A t ∂μ
  let R : CMatrix ι := ∫ t, A t * (1 - P t) ∂μ
  let E : CMatrix ι := ∫ t, (1 - P t) * A t * (1 - P t) ∂μ
  have hQpos : ∀ t, (1 - P t).PosSemidef := fun t =>
    one_sub_projection_posSemidef (P := P t) (hPpos t) (hPid t)
  have hQherm : ∀ t, (1 - P t).IsHermitian := fun t => (hQpos t).isHermitian
  have hEpos_point : ∀ t, ((1 - P t) * A t * (1 - P t)).PosSemidef := by
    intro t
    have h := (hApos t).conjTranspose_mul_mul_same (1 - P t)
    rw [(hQherm t).eq] at h
    simpa [Matrix.mul_assoc] using h
  have hEpos : E.PosSemidef := by
    exact integral_posSemidef_of_forall (hf := hEInt) hEpos_point
  have hR_eq_starD : R = Matrix.conjTranspose D := by
    calc
      R = ∫ t, A t * (1 - P t) ∂μ := rfl
      _ = ∫ t, Matrix.conjTranspose ((1 - P t) * A t) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by
          change A t * (1 - P t) = Matrix.conjTranspose ((1 - P t) * A t)
          rw [Matrix.conjTranspose_mul, (hApos t).isHermitian.eq, (hQherm t).eq]
      _ = Matrix.conjTranspose D := by
        dsimp [D]
        rw [← integral_matrix_conjTranspose (hf := hDInt)]
  have hEtrace_eq_Dtrace : E.trace = D.trace := by
    dsimp [E, D]
    rw [integral_trace (hf := hEInt), integral_trace (hf := hDInt)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      have hQid : (1 - P t) * (1 - P t) = 1 - P t :=
        one_sub_projection_idempotent (P := P t) (hPid t)
      calc
        (((1 - P t) * A t * (1 - P t)).trace) =
            ((((1 - P t) * (1 - P t)) * A t).trace) := by
              exact Matrix.trace_mul_cycle (1 - P t) (A t) (1 - P t)
        _ = (((1 - P t) * A t).trace) := by
              rw [hQid]
  have hEnorm_le_Dnorm : traceNorm E ≤ traceNorm D := by
    calc
      traceNorm E = E.trace.re := traceNorm_posSemidef_eq_trace_re E hEpos
      _ = D.trace.re := by rw [hEtrace_eq_Dtrace]
      _ ≤ traceNorm D := trace_re_le_traceNorm D
  have hRnorm : traceNorm R = traceNorm D := by
    rw [hR_eq_starD, traceNorm_conjTranspose]
  have hdecomp :
      (∫ t, A t - P t * A t * P t ∂μ) = D + R - E := by
    dsimp [D, R, E]
    have hpoint :
        (fun t => A t - P t * A t * P t) =
          fun t => (1 - P t) * A t + A t * (1 - P t) -
            (1 - P t) * A t * (1 - P t) := by
      funext t
      have hrhs :
          (1 - P t) * A t + A t * (1 - P t) -
              (1 - P t) * A t * (1 - P t) =
            A t - P t * A t * P t := by
        rw [show (1 - P t) * A t * (1 - P t) =
            A t - P t * A t - A t * P t + P t * A t * P t by
              noncomm_ring]
        noncomm_ring
      exact hrhs.symm
    calc
      (∫ t, A t - P t * A t * P t ∂μ)
          = ∫ t, ((1 - P t) * A t + A t * (1 - P t) -
              (1 - P t) * A t * (1 - P t)) ∂μ := by
            rw [hpoint]
      _ = ∫ t, ((1 - P t) * A t + A t * (1 - P t)) ∂μ -
            ∫ t, (1 - P t) * A t * (1 - P t) ∂μ := by
            simpa [Pi.add_apply, Pi.sub_apply] using
              (integral_sub (hDInt.add hRInt) hEInt)
      _ = ∫ t, (1 - P t) * A t ∂μ + ∫ t, A t * (1 - P t) ∂μ -
            ∫ t, (1 - P t) * A t * (1 - P t) ∂μ := by
            simpa [Pi.add_apply] using congrArg
              (fun X => X - ∫ t, (1 - P t) * A t * (1 - P t) ∂μ)
              (integral_add hDInt hRInt)
  calc
    traceNorm (∫ t, A t - P t * A t * P t ∂μ) =
        traceNorm (D + R - E) := by rw [hdecomp]
    _ = traceNorm (D + R + (-E)) := by rw [sub_eq_add_neg]
    _ ≤ traceNorm (D + R) + traceNorm (-E) := traceNorm_add_le _ _
    _ = traceNorm (D + R) + traceNorm E := by rw [traceNorm_neg]
    _ ≤ (traceNorm D + traceNorm R) + traceNorm E := by
          nlinarith [traceNorm_add_le D R]
    _ ≤ (traceNorm D + traceNorm D) + traceNorm D := by
          rw [hRnorm]
          nlinarith [hEnorm_le_Dnorm]
    _ = 3 * traceNorm D := by ring
    _ = 3 * traceNorm (∫ t, (1 - P t) * A t ∂μ) := rfl

private theorem matrix_mul_rankOneMatrix_mul_conjTranspose
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix κ ι ℂ) (ψ : ι → ℂ) :
    M * rankOneMatrix ψ * Matrix.conjTranspose M = rankOneMatrix (M.mulVec ψ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, rankOneMatrix_apply, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  ring

private noncomputable def contractedAmp {α β : Type*} [Fintype β]
    (η : β → ℂ) (ψ : Prod α β → ℂ) : α → ℂ :=
  fun x => ∑ y, star (η y) * ψ (x, y)

private theorem partialTraceB_kronecker_rankOne_left_mul_rankOne
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (η : β → ℂ) (ψ : Prod α β → ℂ) :
    partialTraceB (a := α) (b := β)
      (Matrix.kronecker (1 : CMatrix α) (rankOneMatrix η) * rankOneMatrix ψ) =
      rankOneMatrix (contractedAmp η ψ) := by
  ext x x'
  simp only [partialTraceB, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.kronecker,
    rankOneMatrix_apply, contractedAmp, Matrix.one_apply]
  calc
    (∑ x_1 : β, ∑ x_2 : α × β,
      (if x = x_2.1 then (1 : ℂ) else 0) * (η x_1 * star (η x_2.2)) *
        (ψ x_2 * star (ψ (x', x_1)))) =
        ∑ x_1 : β, ∑ y : β,
          η x_1 * star (η y) * (ψ (x, y) * star (ψ (x', x_1))) := by
          apply Finset.sum_congr rfl
          intro x1 _hx1
          rw [Fintype.sum_prod_type]
          simp
    _ = (∑ y, star (η y) * ψ (x, y)) *
        star (∑ y, star (η y) * ψ (x', y)) := by
          simp [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x1 _hx1
          apply Finset.sum_congr rfl
          intro x2 _hx2
          ring

/-- Renner's `Γ^{n+k}` operator, in the finite-dimensional matrix form used by
the later exponential-bound assembly.  It is the Haar twirl of
`(I-P_id^{n,r}) ⊗ P_id^{k,0}` after the `n|k` tensor split. -/
def rennerGammaMatrix [Nonempty a] (ν : PureVector a) (n k r : ℕ) :
    CMatrix (TensorPower a ((n + r) + k)) :=
  unitaryTwirl ((n + r) + k)
    (((Matrix.kronecker
        ((1 : CMatrix (TensorPower a (n + r))) -
          rennerMIIDProjectorId (a := a) n r ν)
        (rennerMIIDProjectorIdZero (a := a) k ν)).submatrix
          (tensorPowerTakeDropEquiv a (n + r) k)
          (tensorPowerTakeDropEquiv a (n + r) k)))

namespace State

/-- Renner's source operator
`ρ_U^n = dim(Sym^k H) · tr_k((I^n ⊗ P_U^{k,0}) ρ^{n+k})`.

This is intentionally a matrix, not a normalized state: the source scaling by
the symmetric dimension is not pointwise trace-normalized. -/
def rennerRhoUMatrix [Nonempty a] {n k : ℕ}
    (ρ : State (TensorPower a (n + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) : CMatrix (TensorPower a n) :=
  ((Fintype.card (TensorPowerProfile a k) : ℝ) : ℂ) •
    partialTraceB (a := TensorPower a n) (b := TensorPower a k)
      ((Matrix.kronecker (1 : CMatrix (TensorPower a n))
          (rennerMIIDProjectorZero (a := a) k ν U)) *
        (ρ.reindex (tensorPowerTakeDropEquiv a n k)).matrix)

theorem rennerRhoUMatrix_trace [Nonempty a] {n k : ℕ}
    (ρ : State (TensorPower a (n + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    (ρ.rennerRhoUMatrix (a := a) (n := n) (k := k) ν U).trace =
      ((Fintype.card (TensorPowerProfile a k) : ℝ) : ℂ) *
        (((Matrix.kronecker (1 : CMatrix (TensorPower a n))
            (rennerMIIDProjectorZero (a := a) k ν U)) *
          (ρ.reindex (tensorPowerTakeDropEquiv a n k)).matrix).trace) := by
  rw [rennerRhoUMatrix, Matrix.trace_smul, partialTraceB_trace]
  rfl

theorem rennerRhoUMatrix_posSemidef_of_pure [Nonempty a] {n k : ℕ}
    (ψ : PureVector (TensorPower a (n + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    (ψ.state.rennerRhoUMatrix (a := a) (n := n) (k := k) ν U).PosSemidef := by
  let e := tensorPowerTakeDropEquiv a n k
  let η : TensorPower a k → ℂ :=
    (unitaryTensorPowerMatrix U k : CMatrix (TensorPower a k)).mulVec
      (ν.tensorPower k).amp
  have hP :
      rennerMIIDProjectorZero (a := a) k ν U = rankOneMatrix η := by
    rw [rennerMIIDProjectorZero_eq_unitary_rankOneTensorPower]
    exact matrix_mul_rankOneMatrix_mul_conjTranspose
      (unitaryTensorPowerMatrix U k : CMatrix (TensorPower a k))
      (ν.tensorPower k).amp
  have hpt :
      partialTraceB (a := TensorPower a n) (b := TensorPower a k)
        (Matrix.kronecker (1 : CMatrix (TensorPower a n))
            (rennerMIIDProjectorZero (a := a) k ν U) *
          (ψ.state.reindex e).matrix) =
        rankOneMatrix
          (contractedAmp (α := TensorPower a n) (β := TensorPower a k) η
          ((ψ.reindex e).amp)) := by
    rw [hP, ← PureVector.reindex_state, PureVector.state_matrix]
    exact partialTraceB_kronecker_rankOne_left_mul_rankOne η (ψ.reindex e).amp
  rw [rennerRhoUMatrix, hpt]
  change (((Fintype.card (TensorPowerProfile a k) : ℝ) •
    rankOneMatrix
      (contractedAmp (α := TensorPower a n) (β := TensorPower a k) η
        ((ψ.reindex e).amp))).PosSemidef)
  exact (rankOneMatrix_pos
    (contractedAmp (α := TensorPower a n) (β := TensorPower a k) η
      ((ψ.reindex e).amp))).smul (by positivity : 0 ≤ (Fintype.card (TensorPowerProfile a k) : ℝ))

private theorem rennerRhoUMatrix_continuous [Nonempty a] {n k : ℕ}
    (ρ : State (TensorPower a (n + k))) (ν : PureVector a) :
    Continuous fun U : Matrix.unitaryGroup a ℂ =>
      ρ.rennerRhoUMatrix (a := a) (n := n) (k := k) ν U := by
  let X : CMatrix (Prod (TensorPower a n) (TensorPower a k)) :=
    (ρ.reindex (tensorPowerTakeDropEquiv a n k)).matrix
  have hP := rennerMIIDProjectorZero_continuous (a := a) k ν
  have hK :
      Continuous fun U : Matrix.unitaryGroup a ℂ =>
        Matrix.kronecker (1 : CMatrix (TensorPower a n))
            (rennerMIIDProjectorZero (a := a) k ν U) * X :=
    (kroneckerOneMulConstCLM (ι := TensorPower a n) (κ := TensorPower a k) X).continuous.comp hP
  have hPT :
      Continuous fun U : Matrix.unitaryGroup a ℂ =>
        partialTraceB (a := TensorPower a n) (b := TensorPower a k)
          (Matrix.kronecker (1 : CMatrix (TensorPower a n))
              (rennerMIIDProjectorZero (a := a) k ν U) * X) :=
    (partialTraceBCLM (ι := TensorPower a n) (κ := TensorPower a k)).continuous.comp hK
  simpa [rennerRhoUMatrix, X] using
    hPT.const_smul (((Fintype.card (TensorPowerProfile a k) : ℝ) : ℂ))

private theorem rennerRhoUMatrix_integrable [Nonempty a] {n k : ℕ}
    (ρ : State (TensorPower a (n + k))) (ν : PureVector a) :
    Integrable
      (fun U : Matrix.unitaryGroup a ℂ =>
        ρ.rennerRhoUMatrix (a := a) (n := n) (k := k) ν U)
      (unitaryHaarMeasure (a := a)) :=
  (rennerRhoUMatrix_continuous (a := a) (n := n) (k := k) ρ ν).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Renner's projected family
`barρ_U = P_U^{m,r} ρ_U P_U^{m,r}` on the retained `m+r`
systems.  Renner's source notation often writes the total retained length as
`n`; here we keep the already-used Lean convention where the `m`-IID projector
has parameters `(m,r)` and acts on `m+r` tensor factors. -/
def rennerProjectedRhoUMatrix [Nonempty a] {m k r : ℕ}
    (ρ : State (TensorPower a ((m + r) + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) : CMatrix (TensorPower a (m + r)) :=
  rennerMIIDProjector (a := a) m r ν U *
    (ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U) *
      rennerMIIDProjector (a := a) m r ν U

/-- Haar average of Renner's unprojected operator family. -/
def rennerRhoUAverageMatrix [Nonempty a] {n k : ℕ}
    (ρ : State (TensorPower a (n + k))) (ν : PureVector a) :
    CMatrix (TensorPower a n) :=
  ∫ U : Matrix.unitaryGroup a ℂ,
    ρ.rennerRhoUMatrix (a := a) (n := n) (k := k) ν U
    ∂unitaryHaarMeasure (a := a)

/-- Haar average of Renner's projected operator family. -/
def rennerProjectedRhoUAverageMatrix [Nonempty a] {m k r : ℕ}
    (ρ : State (TensorPower a ((m + r) + k))) (ν : PureVector a) :
    CMatrix (TensorPower a (m + r)) :=
  ∫ U : Matrix.unitaryGroup a ℂ,
    ρ.rennerProjectedRhoUMatrix (a := a) (m := m) (k := k) (r := r) ν U
    ∂unitaryHaarMeasure (a := a)

/-- The projected Renner family is fixed by the corresponding m-IID
orthogonal-projector sandwich.  This is the matrix form of support in the
projected m-IID span. -/
theorem rennerProjectedRhoUMatrix_projector_sandwich [Nonempty a] {m k r : ℕ}
    (ρ : State (TensorPower a ((m + r) + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    rennerMIIDProjector (a := a) m r ν U *
        ρ.rennerProjectedRhoUMatrix (a := a) (m := m) (k := k) (r := r) ν U *
        rennerMIIDProjector (a := a) m r ν U =
      ρ.rennerProjectedRhoUMatrix (a := a) (m := m) (k := k) (r := r) ν U := by
  let P : CMatrix (TensorPower a (m + r)) := rennerMIIDProjector (a := a) m r ν U
  let A : CMatrix (TensorPower a (m + r)) :=
    ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U
  have hP : P * P = P := rennerMIIDProjector_idempotent (a := a) ν U
  dsimp [rennerProjectedRhoUMatrix]
  change P * (P * A * P) * P = P * A * P
  calc
    P * (P * A * P) * P = (P * P) * A * (P * P) := by noncomm_ring
    _ = P * A * P := by rw [hP]

theorem rennerProjectedRhoUMatrix_trace [Nonempty a] {m k r : ℕ}
    (ρ : State (TensorPower a ((m + r) + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    (ρ.rennerProjectedRhoUMatrix (a := a) (m := m) (k := k) (r := r) ν U).trace =
      (rennerMIIDProjector (a := a) m r ν U *
        ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U).trace := by
  let P : CMatrix (TensorPower a (m + r)) := rennerMIIDProjector (a := a) m r ν U
  let A : CMatrix (TensorPower a (m + r)) :=
    ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U
  have hP : P * P = P := rennerMIIDProjector_idempotent (a := a) ν U
  dsimp [rennerProjectedRhoUMatrix]
  change (P * A * P).trace = (P * A).trace
  calc
    (P * A * P).trace = (P * (P * A)).trace := by
      simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle P A P
    _ = ((P * P) * A).trace := by rw [Matrix.mul_assoc]
    _ = (P * A).trace := by rw [hP]

theorem rennerProjectedRhoUMatrix_posSemidef_of_rennerRhoUMatrix_posSemidef
    [Nonempty a] {m k r : ℕ}
    (ρ : State (TensorPower a ((m + r) + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ)
    (hρU : (ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U).PosSemidef) :
    (ρ.rennerProjectedRhoUMatrix (a := a) (m := m) (k := k) (r := r) ν U).PosSemidef := by
  let P : CMatrix (TensorPower a (m + r)) := rennerMIIDProjector (a := a) m r ν U
  let A : CMatrix (TensorPower a (m + r)) :=
    ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U
  have hPherm : P.IsHermitian := rennerMIIDProjector_isHermitian (a := a) ν U
  dsimp [rennerProjectedRhoUMatrix]
  change (P * A * P).PosSemidef
  simpa [hPherm.eq, Matrix.mul_assoc] using hρU.conjTranspose_mul_mul_same P

theorem rennerProjectedRhoUMatrix_posSemidef_of_pure
    [Nonempty a] {m k r : ℕ}
    (ψ : PureVector (TensorPower a ((m + r) + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    (ψ.state.rennerProjectedRhoUMatrix (a := a) (m := m) (k := k) (r := r) ν U).PosSemidef := by
  exact rennerProjectedRhoUMatrix_posSemidef_of_rennerRhoUMatrix_posSemidef
    (a := a) (m := m) (k := k) (r := r) ψ.state ν U
    (rennerRhoUMatrix_posSemidef_of_pure (a := a) (n := m + r) (k := k) ψ ν U)

theorem rennerProjectedRhoUMatrix_isHermitian_of_rennerRhoUMatrix_isHermitian
    [Nonempty a] {m k r : ℕ}
    (ρ : State (TensorPower a ((m + r) + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ)
    (hρU : (ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U).IsHermitian) :
    (ρ.rennerProjectedRhoUMatrix (a := a) (m := m) (k := k) (r := r) ν U).IsHermitian := by
  let P : CMatrix (TensorPower a (m + r)) := rennerMIIDProjector (a := a) m r ν U
  let A : CMatrix (TensorPower a (m + r)) :=
    ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U
  have hPherm : P.IsHermitian := rennerMIIDProjector_isHermitian (a := a) ν U
  have hAherm : A.IsHermitian := by
    simpa [A] using hρU
  dsimp [rennerProjectedRhoUMatrix]
  change (P * A * P).IsHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hPherm.eq, hAherm.eq]
  rw [Matrix.mul_assoc]

/-- Pointwise `Γ`-integrand rewrite for Renner's defect family:
`(I-P_U^{m,r})ρ_U` is the partial trace of
`((I-P_U^{m,r}) ⊗ P_U^{k,0})ρ^{m+r+k}`, with Renner's symmetric-dimension
scaling. -/
theorem rennerDefectRhoUMatrix_eq_gammaIntegrand_partialTrace
    [Nonempty a] {m k r : ℕ}
    (ρ : State (TensorPower a ((m + r) + k))) (ν : PureVector a)
    (U : Matrix.unitaryGroup a ℂ) :
    ((1 : CMatrix (TensorPower a (m + r))) -
        rennerMIIDProjector (a := a) m r ν U) *
        ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U =
      ((Fintype.card (TensorPowerProfile a k) : ℝ) : ℂ) •
        partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          ((unitaryTwirlIntegrand (a := a) ((m + r) + k)
              (((Matrix.kronecker
                  ((1 : CMatrix (TensorPower a (m + r))) -
                    rennerMIIDProjectorId (a := a) m r ν)
                  (rennerMIIDProjectorIdZero (a := a) k ν)).submatrix
                    (tensorPowerTakeDropEquiv a (m + r) k)
                    (tensorPowerTakeDropEquiv a (m + r) k))) U).submatrix
                (tensorPowerTakeDropEquiv a (m + r) k).symm
                (tensorPowerTakeDropEquiv a (m + r) k).symm *
              (ρ.reindex (tensorPowerTakeDropEquiv a (m + r) k)).matrix) := by
  let L : CMatrix (TensorPower a (m + r)) :=
    (1 : CMatrix (TensorPower a (m + r))) -
      rennerMIIDProjector (a := a) m r ν U
  let R : CMatrix (TensorPower a k) := rennerMIIDProjectorZero (a := a) k ν U
  let X : CMatrix (Prod (TensorPower a (m + r)) (TensorPower a k)) :=
    (ρ.reindex (tensorPowerTakeDropEquiv a (m + r) k)).matrix
  let c : ℂ := ((Fintype.card (TensorPowerProfile a k) : ℝ) : ℂ)
  have hsplit :
      (unitaryTwirlIntegrand (a := a) ((m + r) + k)
          (((Matrix.kronecker
              ((1 : CMatrix (TensorPower a (m + r))) -
                rennerMIIDProjectorId (a := a) m r ν)
              (rennerMIIDProjectorIdZero (a := a) k ν)).submatrix
                (tensorPowerTakeDropEquiv a (m + r) k)
                (tensorPowerTakeDropEquiv a (m + r) k))) U).submatrix
            (tensorPowerTakeDropEquiv a (m + r) k).symm
            (tensorPowerTakeDropEquiv a (m + r) k).symm =
        Matrix.kronecker L R := by
    simpa [L, R] using
      rennerGammaIntegrand_takeDrop_submatrix (a := a) ν m k r U
  have hkr :
      Matrix.kronecker L R * X =
        Matrix.kronecker L (1 : CMatrix (TensorPower a k)) *
          (Matrix.kronecker (1 : CMatrix (TensorPower a (m + r))) R * X) := by
    have hmul :
        Matrix.kronecker L (1 : CMatrix (TensorPower a k)) *
            Matrix.kronecker (1 : CMatrix (TensorPower a (m + r))) R =
          Matrix.kronecker L R := by
      simpa using
        (Matrix.mul_kronecker_mul L (1 : CMatrix (TensorPower a (m + r)))
          (1 : CMatrix (TensorPower a k)) R).symm
    calc
      Matrix.kronecker L R * X =
          (Matrix.kronecker L (1 : CMatrix (TensorPower a k)) *
              Matrix.kronecker (1 : CMatrix (TensorPower a (m + r))) R) * X := by
            rw [hmul]
      _ = Matrix.kronecker L (1 : CMatrix (TensorPower a k)) *
            (Matrix.kronecker (1 : CMatrix (TensorPower a (m + r))) R * X) := by
            rw [Matrix.mul_assoc]
  calc
    L * ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U =
        L * (c • partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          (Matrix.kronecker (1 : CMatrix (TensorPower a (m + r))) R * X)) := by
          rfl
    _ = c • (L * partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          (Matrix.kronecker (1 : CMatrix (TensorPower a (m + r))) R * X)) := by
          ext i j
          simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = c • partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          (Matrix.kronecker L (1 : CMatrix (TensorPower a k)) *
            (Matrix.kronecker (1 : CMatrix (TensorPower a (m + r))) R * X)) := by
          rw [partialTraceB_kronecker_one_left_mul]
    _ = c • partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          (Matrix.kronecker L R * X) := by
          rw [hkr]
    _ = c • partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          ((unitaryTwirlIntegrand (a := a) ((m + r) + k)
              (((Matrix.kronecker
                  ((1 : CMatrix (TensorPower a (m + r))) -
                    rennerMIIDProjectorId (a := a) m r ν)
                  (rennerMIIDProjectorIdZero (a := a) k ν)).submatrix
                    (tensorPowerTakeDropEquiv a (m + r) k)
                    (tensorPowerTakeDropEquiv a (m + r) k))) U).submatrix
                (tensorPowerTakeDropEquiv a (m + r) k).symm
                (tensorPowerTakeDropEquiv a (m + r) k).symm * X) := by
          rw [hsplit]

/-- Renner's `Γ^{n+k}` rewrite for the Haar-averaged defect operator. -/
theorem rennerProjectedFamily_gamma_rewrite
    [Nonempty a] {m k r : ℕ}
    (ρ : State (TensorPower a ((m + r) + k))) (ν : PureVector a) :
    (∫ U : Matrix.unitaryGroup a ℂ,
        ((1 : CMatrix (TensorPower a (m + r))) -
          rennerMIIDProjector (a := a) m r ν U) *
          ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U
        ∂unitaryHaarMeasure (a := a)) =
      ((Fintype.card (TensorPowerProfile a k) : ℝ) : ℂ) •
        partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          ((QIT.rennerGammaMatrix (a := a) ν m k r).submatrix
              (tensorPowerTakeDropEquiv a (m + r) k).symm
              (tensorPowerTakeDropEquiv a (m + r) k).symm *
            (ρ.reindex (tensorPowerTakeDropEquiv a (m + r) k)).matrix) := by
  let e := tensorPowerTakeDropEquiv a (m + r) k
  let X : CMatrix (Prod (TensorPower a (m + r)) (TensorPower a k)) :=
    (ρ.reindex e).matrix
  let A : CMatrix (TensorPower a ((m + r) + k)) :=
    ((Matrix.kronecker
      ((1 : CMatrix (TensorPower a (m + r))) -
        rennerMIIDProjectorId (a := a) m r ν)
      (rennerMIIDProjectorIdZero (a := a) k ν)).submatrix e e)
  let c : ℂ := ((Fintype.card (TensorPowerProfile a k) : ℝ) : ℂ)
  have hAint :
      Integrable
        (fun U : Matrix.unitaryGroup a ℂ =>
          unitaryTwirlIntegrand (a := a) ((m + r) + k) A U)
        (unitaryHaarMeasure (a := a)) :=
    unitaryTwirl_integrand_integrable (a := a) ((m + r) + k) A
  have hsplitInt :
      Integrable
        (fun U : Matrix.unitaryGroup a ℂ =>
          (unitaryTwirlIntegrand (a := a) ((m + r) + k) A U).submatrix
            e.symm e.symm * X)
        (unitaryHaarMeasure (a := a)) :=
    (submatrixEquivSymmMulConstCLM e X).integrable_comp hAint
  calc
    (∫ U : Matrix.unitaryGroup a ℂ,
        ((1 : CMatrix (TensorPower a (m + r))) -
          rennerMIIDProjector (a := a) m r ν U) *
          ρ.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U
        ∂unitaryHaarMeasure (a := a)) =
        ∫ U : Matrix.unitaryGroup a ℂ,
          c • partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
            ((unitaryTwirlIntegrand (a := a) ((m + r) + k) A U).submatrix
              e.symm e.symm * X)
          ∂unitaryHaarMeasure (a := a) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun U => by
            simpa [A, X, c, e] using
              rennerDefectRhoUMatrix_eq_gammaIntegrand_partialTrace
                (a := a) (m := m) (k := k) (r := r) ρ ν U)
    _ = c • ∫ U : Matrix.unitaryGroup a ℂ,
          partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
            ((unitaryTwirlIntegrand (a := a) ((m + r) + k) A U).submatrix
              e.symm e.symm * X)
          ∂unitaryHaarMeasure (a := a) := by
          rw [integral_smul]
    _ = c • partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          (∫ U : Matrix.unitaryGroup a ℂ,
            (unitaryTwirlIntegrand (a := a) ((m + r) + k) A U).submatrix
              e.symm e.symm * X
            ∂unitaryHaarMeasure (a := a)) := by
          rw [partialTraceB_integral (hf := hsplitInt)]
    _ = c • partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          ((∫ U : Matrix.unitaryGroup a ℂ,
              unitaryTwirlIntegrand (a := a) ((m + r) + k) A U
              ∂unitaryHaarMeasure (a := a)).submatrix e.symm e.symm * X) := by
          rw [integral_submatrix_equiv_symm_mul_const (hf := hAint)]
    _ = c • partialTraceB (a := TensorPower a (m + r)) (b := TensorPower a k)
          ((QIT.rennerGammaMatrix (a := a) ν m k r).submatrix e.symm e.symm * X) := by
          rfl

/-- Renner's Haar-averaged source family recovers the ordinary partial trace
over the last `k` systems, under the global symmetric-support hypothesis. -/
theorem rennerTraceOutLastK_eq_haarAverage_rhoU [Nonempty a] {n k : ℕ}
    (ρ : State (TensorPower a (n + k))) (ν : PureVector a)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    (ρ.traceOutLastK (a := a) (n := n) (k := k)).matrix =
      ρ.rennerRhoUAverageMatrix (a := a) (n := n) (k := k) ν := by
  let X : CMatrix (Prod (TensorPower a n) (TensorPower a k)) :=
    (ρ.reindex (tensorPowerTakeDropEquiv a n k)).matrix
  let Pavg : CMatrix (TensorPower a k) :=
    ∫ U : Matrix.unitaryGroup a ℂ,
      rennerMIIDProjectorZero (a := a) k ν U
      ∂unitaryHaarMeasure (a := a)
  let P : CMatrix (TensorPower a k) := symmetricProjectionMatrix (a := a) k
  let Q : CMatrix (Prod (TensorPower a n) (TensorPower a k)) :=
    Matrix.kronecker (1 : CMatrix (TensorPower a n)) P
  let c : ℂ := ((Fintype.card (TensorPowerProfile a k) : ℝ) : ℂ)
  have hPint := rennerMIIDProjectorZero_integrable (a := a) k ν
  have hKint :
      Integrable
        (fun U : Matrix.unitaryGroup a ℂ =>
          Matrix.kronecker (1 : CMatrix (TensorPower a n))
              (rennerMIIDProjectorZero (a := a) k ν U) * X)
        (unitaryHaarMeasure (a := a)) :=
    (kroneckerOneMulConstCLM (ι := TensorPower a n) (κ := TensorPower a k) X).integrable_comp hPint
  have hPTint :
      Integrable
        (fun U : Matrix.unitaryGroup a ℂ =>
          partialTraceB (a := TensorPower a n) (b := TensorPower a k)
            (Matrix.kronecker (1 : CMatrix (TensorPower a n))
              (rennerMIIDProjectorZero (a := a) k ν U) * X))
        (unitaryHaarMeasure (a := a)) :=
    (partialTraceBCLM (ι := TensorPower a n) (κ := TensorPower a k)).integrable_comp hKint
  have hQX : Q * X = X := by
    simpa [Q, P, X] using
      State.splitRightSymmetricProjection_mul_of_supported (a := a) (n := n) (k := k)
        (ρ := ρ) hρ
  have hPavgP : Pavg * P = (c⁻¹) • P := by
    simpa [Pavg, P, c] using
      rennerMIIDProjectorZero_average_mul_symmetricProjectionMatrix (a := a) k ν
  have hKavgX :
      Matrix.kronecker (1 : CMatrix (TensorPower a n)) Pavg * X = c⁻¹ • X := by
    calc
      Matrix.kronecker (1 : CMatrix (TensorPower a n)) Pavg * X =
          Matrix.kronecker (1 : CMatrix (TensorPower a n)) Pavg * (Q * X) := by
            rw [hQX]
      _ = (Matrix.kronecker (1 : CMatrix (TensorPower a n)) Pavg * Q) * X := by
            rw [Matrix.mul_assoc]
      _ = Matrix.kronecker (1 : CMatrix (TensorPower a n)) (Pavg * P) * X := by
            dsimp [Q, P]
            rw [← Matrix.mul_kronecker_mul]
            simp
      _ = Matrix.kronecker (1 : CMatrix (TensorPower a n)) (c⁻¹ • P) * X := by
            rw [hPavgP]
      _ = c⁻¹ • (Q * X) := by
            simp [Q, P, Matrix.kronecker_smul]
      _ = c⁻¹ • X := by rw [hQX]
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast TensorPowerProfile.card_ne_zero (a := a) k
  have haverage :
      ρ.rennerRhoUAverageMatrix (a := a) (n := n) (k := k) ν =
        c • partialTraceB (a := TensorPower a n) (b := TensorPower a k)
          (Matrix.kronecker (1 : CMatrix (TensorPower a n)) Pavg * X) := by
    rw [rennerRhoUAverageMatrix]
    change (∫ U : Matrix.unitaryGroup a ℂ,
        c • partialTraceB (a := TensorPower a n) (b := TensorPower a k)
          (Matrix.kronecker (1 : CMatrix (TensorPower a n))
            (rennerMIIDProjectorZero (a := a) k ν U) * X)
        ∂unitaryHaarMeasure (a := a)) =
      c • partialTraceB (a := TensorPower a n) (b := TensorPower a k)
        (Matrix.kronecker (1 : CMatrix (TensorPower a n)) Pavg * X)
    rw [integral_smul]
    rw [← partialTraceB_integral (hf := hKint)]
    rw [integral_kronecker_one_mul_const (hf := hPint)]
  rw [haverage, hKavgX]
  rw [traceOutLastK_matrix]
  change partialTraceB (a := TensorPower a n) (b := TensorPower a k) X =
    c • partialTraceB (a := TensorPower a n) (b := TensorPower a k) (c⁻¹ • X)
  rw [partialTraceB_smul]
  ext i j
  simp [hc_ne]

/-- Renner's gentle-measurement bridge for the projected Haar family, in the
rank-one source form used in the proof of the de Finetti theorem.  The
pointwise positivity of `ρ_U` is obtained from the rank-one input
`ψ.state`, matching Renner `sub.tex:858-860`. -/
theorem rennerProjectedFamily_gentle_traceNorm_bound [Nonempty a] {m k r : ℕ}
    (ψ : PureVector (TensorPower a ((m + r) + k))) (ν : PureVector a)
    (hψsym : ψ.state.SupportedOnSymmetricSubspace (a := a)) :
    traceNorm
        ((ψ.state.traceOutLastK (a := a) (n := m + r) (k := k)).matrix -
          ψ.state.rennerProjectedRhoUAverageMatrix (a := a) (m := m) (k := k) (r := r) ν)
      ≤
        3 * traceNorm
          (∫ U : Matrix.unitaryGroup a ℂ,
            ((1 : CMatrix (TensorPower a (m + r))) -
              rennerMIIDProjector (a := a) m r ν U) *
              ψ.state.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U
            ∂unitaryHaarMeasure (a := a)) := by
  let A : Matrix.unitaryGroup a ℂ → CMatrix (TensorPower a (m + r)) :=
    fun U => ψ.state.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U
  let P : Matrix.unitaryGroup a ℂ → CMatrix (TensorPower a (m + r)) :=
    fun U => rennerMIIDProjector (a := a) m r ν U
  have hAcont : Continuous A := by
    simpa [A] using
      rennerRhoUMatrix_continuous (a := a) (n := m + r) (k := k) ψ.state ν
  have hPcont : Continuous P := by
    simpa [P] using rennerMIIDProjector_continuous (a := a) m r ν
  have hQcont : Continuous fun U : Matrix.unitaryGroup a ℂ =>
      (1 : CMatrix (TensorPower a (m + r))) - P U :=
    continuous_const.sub hPcont
  have hAInt : Integrable A (unitaryHaarMeasure (a := a)) :=
    hAcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPAPInt :
      Integrable (fun U : Matrix.unitaryGroup a ℂ => P U * A U * P U)
        (unitaryHaarMeasure (a := a)) :=
    ((hPcont.matrix_mul hAcont).matrix_mul hPcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDInt :
      Integrable (fun U : Matrix.unitaryGroup a ℂ => (1 - P U) * A U)
        (unitaryHaarMeasure (a := a)) :=
    (hQcont.matrix_mul hAcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRInt :
      Integrable (fun U : Matrix.unitaryGroup a ℂ => A U * (1 - P U))
        (unitaryHaarMeasure (a := a)) :=
    (hAcont.matrix_mul hQcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hEInt :
      Integrable (fun U : Matrix.unitaryGroup a ℂ => (1 - P U) * A U * (1 - P U))
        (unitaryHaarMeasure (a := a)) :=
    ((hQcont.matrix_mul hAcont).matrix_mul hQcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hApos : ∀ U, (A U).PosSemidef := by
    intro U
    simpa [A] using
      rennerRhoUMatrix_posSemidef_of_pure (a := a) (n := m + r) (k := k) ψ ν U
  have hPpos : ∀ U, (P U).PosSemidef := by
    intro U
    simpa [P] using rennerMIIDProjector_posSemidef (a := a) (m := m) (r := r) ν U
  have hPid : ∀ U, P U * P U = P U := by
    intro U
    simpa [P] using rennerMIIDProjector_idempotent (a := a) (m := m) (r := r) ν U
  have hleft :
      (ψ.state.traceOutLastK (a := a) (n := m + r) (k := k)).matrix -
          ψ.state.rennerProjectedRhoUAverageMatrix (a := a) (m := m) (k := k) (r := r) ν =
        ∫ U : Matrix.unitaryGroup a ℂ, A U - P U * A U * P U
          ∂unitaryHaarMeasure (a := a) := by
    have havg :=
      rennerTraceOutLastK_eq_haarAverage_rhoU
        (a := a) (n := m + r) (k := k) ψ.state ν hψsym
    calc
      (ψ.state.traceOutLastK (a := a) (n := m + r) (k := k)).matrix -
          ψ.state.rennerProjectedRhoUAverageMatrix (a := a) (m := m) (k := k) (r := r) ν =
          (∫ U : Matrix.unitaryGroup a ℂ, A U ∂unitaryHaarMeasure (a := a)) -
            (∫ U : Matrix.unitaryGroup a ℂ, P U * A U * P U
              ∂unitaryHaarMeasure (a := a)) := by
            rw [havg]
            rfl
      _ = ∫ U : Matrix.unitaryGroup a ℂ, A U - P U * A U * P U
            ∂unitaryHaarMeasure (a := a) := by
            rw [integral_sub hAInt hPAPInt]
  calc
    traceNorm
        ((ψ.state.traceOutLastK (a := a) (n := m + r) (k := k)).matrix -
          ψ.state.rennerProjectedRhoUAverageMatrix (a := a) (m := m) (k := k) (r := r) ν)
        =
        traceNorm
          (∫ U : Matrix.unitaryGroup a ℂ, A U - P U * A U * P U
            ∂unitaryHaarMeasure (a := a)) := by
          rw [hleft]
    _ ≤ 3 * traceNorm
          (∫ U : Matrix.unitaryGroup a ℂ, (1 - P U) * A U
            ∂unitaryHaarMeasure (a := a)) :=
        rennerGentle_integral_traceNorm_bound
          (A := A) (P := P)
          (μ := unitaryHaarMeasure (a := a))
          hDInt hRInt hEInt hApos hPpos hPid
    _ = 3 * traceNorm
          (∫ U : Matrix.unitaryGroup a ℂ,
            ((1 : CMatrix (TensorPower a (m + r))) -
              rennerMIIDProjector (a := a) m r ν U) *
              ψ.state.rennerRhoUMatrix (a := a) (n := m + r) (k := k) ν U
            ∂unitaryHaarMeasure (a := a)) := by
          rfl

end State

private theorem psdSqrt_permutationChannel_map {n : ℕ}
    (M : CMatrix (TensorPower a n)) (hM : M.PosSemidef)
    (σ : Equiv.Perm (Fin n)) :
    psdSqrt ((permutationChannel (a := a) n σ).map M) =
      (permutationChannel (a := a) n σ).map (psdSqrt M) := by
  let U : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    ⟨permutationMatrix (a := a) n σ⁻¹, by
      rw [Matrix.mem_unitaryGroup_iff]
      simpa [Matrix.star_eq_conjTranspose] using
        permutationMatrix_mul_conjTranspose_self (a := a) n σ⁻¹⟩
  have hpow := cMatrix_rpow_unitary_conj (a := TensorPower a n) hM U
    (s := (1/2 : ℝ)) (by norm_num)
  rw [permutationChannel_map, permutationChannel_map]
  simpa [psdSqrt, CFC.sqrt_eq_rpow, U, Matrix.star_eq_conjTranspose,
    permutationMatrix_conjTranspose, Equiv.Perm.inv_def, Matrix.mul_assoc] using hpow

namespace State

/-- The positive square root of a permutation-invariant tensor-power state is
fixed by the same permutation channel. -/
theorem sqrtMatrix_permutationChannel_map_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a))
    (σ : Equiv.Perm (Fin n)) :
    (permutationChannel (a := a) n σ).map ρ.sqrtMatrix = ρ.sqrtMatrix := by
  have hmap : (permutationChannel (a := a) n σ).map ρ.matrix = ρ.matrix := by
    simpa [Channel.applyState] using congrArg State.matrix (hρ σ)
  have hsqrt := psdSqrt_permutationChannel_map (a := a) ρ.matrix ρ.pos σ
  rw [hmap] at hsqrt
  simpa [State.sqrtMatrix] using hsqrt.symm

theorem sqrtMatrix_apply_permEquiv_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a))
    (σ : Equiv.Perm (Fin n)) (x y : TensorPower a n) :
    ρ.sqrtMatrix (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y) =
      ρ.sqrtMatrix x y := by
  have h := congrFun
    (congrFun (sqrtMatrix_permutationChannel_map_of_invariant (a := a) hρ σ) x) y
  simpa [permutationChannel_map_apply] using h

end State

omit [Fintype a] [DecidableEq a] in
private theorem tensorPowerProdEquiv_fst_apply {b : Type w}
    [Fintype b] [DecidableEq b]
    (n : ℕ) (z : TensorPower (Prod a b) n) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerProdEquiv a b n z).1) i =
      (tensorPowerEquiv n z i).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
            simp [tensorPowerProdEquiv, tensorPowerEquiv]
            exact ih tail i

omit [Fintype a] [DecidableEq a] in
private theorem tensorPowerProdEquiv_snd_apply {b : Type w}
    [Fintype b] [DecidableEq b]
    (n : ℕ) (z : TensorPower (Prod a b) n) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerProdEquiv a b n z).2) i =
      (tensorPowerEquiv n z i).2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
            simp [tensorPowerProdEquiv, tensorPowerEquiv]
            exact ih tail i

omit [Fintype a] [DecidableEq a] in
private theorem tensorPowerProdEquiv_permEquiv_fst {b : Type w}
    [Fintype b] [DecidableEq b]
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : TensorPower (Prod a b) n) :
    (tensorPowerProdEquiv a b n (permEquiv (a := Prod a b) n σ z)).1 =
      permEquiv (a := a) n σ ((tensorPowerProdEquiv a b n z).1) := by
  apply (tensorPowerEquiv n).injective
  ext i
  rw [tensorPowerProdEquiv_fst_apply]
  rw [tensorPowerEquiv_permEquiv]
  rw [tensorPowerEquiv_permEquiv]
  change ((tensorPowerEquiv n) z (σ⁻¹ i)).1 =
    (tensorPowerEquiv n ((tensorPowerProdEquiv a b n z).1) (σ⁻¹ i))
  rw [tensorPowerProdEquiv_fst_apply]

omit [Fintype a] [DecidableEq a] in
private theorem tensorPowerProdEquiv_permEquiv_snd {b : Type w}
    [Fintype b] [DecidableEq b]
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : TensorPower (Prod a b) n) :
    (tensorPowerProdEquiv a b n (permEquiv (a := Prod a b) n σ z)).2 =
      permEquiv (a := b) n σ ((tensorPowerProdEquiv a b n z).2) := by
  apply (tensorPowerEquiv n).injective
  ext i
  rw [tensorPowerProdEquiv_snd_apply]
  rw [tensorPowerEquiv_permEquiv]
  rw [tensorPowerEquiv_permEquiv]
  change ((tensorPowerEquiv n) z (σ⁻¹ i)).2 =
    (tensorPowerEquiv n ((tensorPowerProdEquiv a b n z).2) (σ⁻¹ i))
  rw [tensorPowerProdEquiv_snd_apply]

namespace State

theorem canonicalTensorPowerPurificationAmp_permEquiv_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a))
    (σ : Equiv.Perm (Fin n)) (x : TensorPower (Prod a a) n) :
    ρ.canonicalTensorPowerPurificationAmp (permEquiv (a := Prod a a) n σ x) =
      ρ.canonicalTensorPowerPurificationAmp x := by
  simp [canonicalTensorPowerPurificationAmp, State.canonicalPurification,
    State.canonicalPurificationAmp, tensorPowerProdEquiv_permEquiv_fst,
    tensorPowerProdEquiv_permEquiv_snd,
    sqrtMatrix_apply_permEquiv_of_invariant (a := a) hρ σ]

theorem inputCanonicalTensorPowerPurificationAmp_permEquiv_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a))
    (σ : Equiv.Perm (Fin n)) (x : TensorPower (Prod a a) n) :
    ρ.inputCanonicalTensorPowerPurificationAmp (permEquiv (a := Prod a a) n σ x) =
      ρ.inputCanonicalTensorPowerPurificationAmp x := by
  simp [inputCanonicalTensorPowerPurificationAmp, tensorPowerProdEquiv_permEquiv_fst,
    tensorPowerProdEquiv_permEquiv_snd,
    sqrtMatrix_apply_permEquiv_of_invariant (a := a) hρ σ]

theorem canonicalTensorPowerPurificationAmp_mem_symmetric_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.canonicalTensorPowerPurificationAmp ∈ symmetricSubspace (a := Prod a a) n := by
  intro σ
  ext x
  exact canonicalTensorPowerPurificationAmp_permEquiv_of_invariant (a := a) hρ σ x

theorem inputCanonicalTensorPowerPurificationAmp_mem_symmetric_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.inputCanonicalTensorPowerPurificationAmp ∈ symmetricSubspace (a := Prod a a) n := by
  intro σ
  ext x
  exact inputCanonicalTensorPowerPurificationAmp_permEquiv_of_invariant
    (a := a) hρ σ x

/-- The canonical purification of a permutation-invariant tensor-power state,
viewed on `(H × H)^n`, is supported on the symmetric subspace. -/
theorem canonicalTensorPowerPurification_supported_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.canonicalTensorPowerPurificationState.SupportedOnSymmetricSubspace
      (a := Prod a a) := by
  dsimp [SupportedOnSymmetricSubspace]
  rw [canonicalTensorPowerPurificationState_matrix]
  apply rankOneMatrix_le_projection_of_mulVec_eq_self
  · exact symmetricProjectionMatrix_posSemidef (a := Prod a a) n
  · exact symmetricProjectionMatrix_idempotent (a := Prod a a) n
  · exact (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self
      (a := Prod a a) n ρ.canonicalTensorPowerPurificationAmp).mp
      (canonicalTensorPowerPurificationAmp_mem_symmetric_of_invariant (a := a) hρ)
  · rw [← canonicalTensorPowerPurificationState_matrix]
    exact ρ.canonicalTensorPowerPurificationState.trace_eq_one

/-- The input-first canonical purification of a permutation-invariant
tensor-power state, viewed on `(H × H)^n`, is supported on the symmetric
subspace. -/
theorem inputCanonicalTensorPowerPurification_supported_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.inputCanonicalTensorPowerPurificationState.SupportedOnSymmetricSubspace
      (a := Prod a a) := by
  dsimp [SupportedOnSymmetricSubspace]
  rw [inputCanonicalTensorPowerPurificationState_matrix]
  apply rankOneMatrix_le_projection_of_mulVec_eq_self
  · exact symmetricProjectionMatrix_posSemidef (a := Prod a a) n
  · exact symmetricProjectionMatrix_idempotent (a := Prod a a) n
  · exact (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self
      (a := Prod a a) n ρ.inputCanonicalTensorPowerPurificationAmp).mp
      (inputCanonicalTensorPowerPurificationAmp_mem_symmetric_of_invariant (a := a) hρ)
  · rw [← inputCanonicalTensorPowerPurificationState_matrix]
    exact ρ.inputCanonicalTensorPowerPurificationState.trace_eq_one

/-- The canonical purification of the input marginal of a twirled
input-reference state is supported on the joint symmetric subspace. -/
theorem inputPermutationTwirling_canonicalPurification_supported
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    @State.SupportedOnSymmetricSubspace (Prod a a) _ _ n
      (@State.canonicalTensorPowerPurificationState a _ _ n
        ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)) := by
  exact @canonicalTensorPowerPurification_supported_of_invariant a _ _ n
    ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)
    (inputPermutationTwirling_marginalA_isPermutationInvariant (a := a) (r := r) ω)

/-- Input-first version of the symmetric canonical lift for the twirled input
marginal.  This orientation matches the channel-input-first convention of
`diamondTraceDistance`. -/
theorem inputPermutationTwirling_inputCanonicalPurification_supported
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    @State.SupportedOnSymmetricSubspace (Prod a a) _ _ n
      (@State.inputCanonicalTensorPowerPurificationState a _ _ n
        ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)) := by
  exact @inputCanonicalTensorPowerPurification_supported_of_invariant a _ _ n
    ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)
    (inputPermutationTwirling_marginalA_isPermutationInvariant (a := a) (r := r) ω)

/-- The symmetric canonical lift of the twirled input marginal reduces back to
that twirled input marginal after reindexing as `H^n × H^n` and tracing out the
left reference register. -/
theorem inputPermutationTwirling_canonicalPurification_reindex_marginalB
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    ((State.canonicalTensorPowerPurificationState
          ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)).reindex
        (tensorPowerProdEquiv a a n)).marginalB =
      (ω.inputPermutationTwirling (a := a) (r := r)).marginalA :=
  canonicalTensorPowerPurificationState_reindex_marginalB
    ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)

/-- The input-first symmetric canonical lift of the twirled input marginal
reduces back to that twirled input marginal after reindexing as `H^n × H^n`
and tracing out the right reference register. -/
theorem inputPermutationTwirling_inputCanonicalPurification_reindex_marginalA
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    ((State.inputCanonicalTensorPowerPurificationState
          ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)).reindex
        (tensorPowerProdEquiv a a n)).marginalA =
      (ω.inputPermutationTwirling (a := a) (r := r)).marginalA :=
  inputCanonicalTensorPowerPurificationState_reindex_marginalA
    ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)

/-- The `i`th eigenvector of a finite state, packaged as a normalized pure
state. -/
def spectralPureVector (ρ : State a) (i : a) : PureVector a where
  amp := fun x => (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a) x i
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace, dotProduct]
    apply Complex.ext
    · have h := unitary_col_normSq_sum ρ.pos.isHermitian.eigenvectorUnitary i
      simpa [Complex.normSq] using h
    · simp [mul_comm]

/-- Spectral decomposition of a finite state as a convex combination of pure
eigenvector states. -/
theorem matrix_eq_sum_spectralPureVector (ρ : State a) :
    ρ.matrix = ∑ i : a,
      ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
        (ρ.spectralPureVector i).state.matrix := by
  let U : Matrix.unitaryGroup a ℂ := ρ.pos.isHermitian.eigenvectorUnitary
  let D : CMatrix a :=
    Matrix.diagonal (fun i => ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ))
  have hspec : ρ.matrix = (U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using ρ.pos.isHermitian.spectral_theorem
  calc
    ρ.matrix = (U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ) := hspec
    _ = ∑ i : a,
      ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
        (ρ.spectralPureVector i).state.matrix := by
        ext x y
        simp [U, D, spectralPureVector, PureVector.state_matrix, rankOneMatrix,
          Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
          Matrix.diagonal, mul_assoc, mul_comm]

/-- The eigenvalue weights in the spectral pure-state decomposition sum to
one. -/
theorem sum_eigenvalues_eq_one (ρ : State a) :
    ∑ i : a, ρ.pos.isHermitian.eigenvalues i = 1 := by
  have h := congrArg Complex.re ρ.pos.isHermitian.trace_eq_sum_eigenvalues
  rw [ρ.trace_eq_one] at h
  norm_num at h
  exact h.symm

end State

namespace PureVector

/-- A pure input-reference state is obtained from the canonical purification of
its input marginal by a reference-side isometry, after swapping to the local
purification convention.  This is the pure-state CKR lift adapter used before
the symmetric post-selection reduction. -/
theorem exists_referenceIsometry_reindex_prodComm_eq_applyCanonicalOfMarginalA
    {n : ℕ} (Ψ : PureVector (Prod (TensorPower a n) (TensorPower a n))) :
    ∃ V : ReferenceIsometry (TensorPower a n) (TensorPower a n),
      Ψ.reindex (Equiv.prodComm (TensorPower a n) (TensorPower a n)) =
        V.applyPureVector Ψ.state.marginalA.canonicalPurification := by
  exact exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
    Ψ.state.marginalA.canonicalPurification_purifies
    Ψ.reindex_prodComm_purifies_marginalA
    le_rfl

/-- Input-first version of the reference-isometry purification adapter: a pure
input-reference state is obtained from the canonical purification of its input
marginal by an isometry on the right/reference factor. -/
theorem exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA
    {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ : PureVector (Prod a a)) :
    ∃ V : ReferenceIsometry a a,
      Ψ = V.applyPureVectorRight
        (Ψ.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)) := by
  rcases exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      Ψ.state.marginalA.canonicalPurification_purifies
      Ψ.reindex_prodComm_purifies_marginalA le_rfl with ⟨V, hV⟩
  refine ⟨V, ?_⟩
  apply PureVector.ext_amp
  funext x
  have hx := congrArg (fun Φ : PureVector (Prod a a) => Φ.amp (x.2, x.1)) hV
  simpa [ReferenceIsometry.applyPureVectorRight_amp, ReferenceIsometry.applyAmpRight,
    PureVector.reindex_amp, ReferenceIsometry.applyPureVector_amp,
    ReferenceIsometry.applyAmp, Matrix.mulVec, dotProduct] using hx

/-- Pure-state action version of the input-first reference-isometry adapter.
For every pure input-reference state, the channel-difference action is obtained
from the canonical purification of its input marginal, followed by a
right-reference isometry. -/
theorem exists_referenceIsometryRight_channelDifference_action_eq
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Φ Ψc : Channel a b) (Ω : PureVector (Prod a a)) :
    ∃ V : ReferenceIsometry a a,
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
          Ω.state.matrix =
        V.applyMatrixRight
          (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
            (Ω.state.marginalA.canonicalPurification.reindex
              (Equiv.prodComm a a)).state.matrix) := by
  rcases Ω.exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA with ⟨V, hV⟩
  refine ⟨V, ?_⟩
  have hAction := MatrixMap.channelDifference_kron_id_apply_applyPureVectorRight
    (a := a) (b := b) (r₁ := a) (r₂ := a) Φ Ψc V
    (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a))
  simpa [← hV] using hAction

/-- Pure-state CKR reduction step: the channel-difference action on an
arbitrary pure input-reference state is no larger than the action on the
canonical purification of its input marginal.  The proof uses only the
right-reference isometry adapter and trace-norm invariance under square
reference isometries. -/
theorem channelDifference_action_traceNorm_le_canonicalOfMarginalA
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Φ Ψc : Channel a b) (Ω : PureVector (Prod a a)) :
    traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
          Ω.state.matrix) ≤
      traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
          (Ω.state.marginalA.canonicalPurification.reindex
            (Equiv.prodComm a a)).state.matrix) := by
  rcases Ω.exists_referenceIsometryRight_channelDifference_action_eq Φ Ψc with ⟨V, hV⟩
  rw [hV]
  exact traceNorm_applyMatrixRight_le V
    (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
      (Ω.state.marginalA.canonicalPurification.reindex
        (Equiv.prodComm a a)).state.matrix)

/-- Normalized-action form of
`channelDifference_action_traceNorm_le_canonicalOfMarginalA`. -/
theorem channelDifference_normalizedAction_le_canonicalOfMarginalA
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Φ Ψc : Channel a b) (Ω : PureVector (Prod a a)) :
    MatrixMap.ancillaNormalizedTraceAction
        (MatrixMap.channelDifference Φ Ψc) Ω.state ≤
      MatrixMap.ancillaNormalizedTraceAction
        (MatrixMap.channelDifference Φ Ψc)
        (Ω.state.marginalA.canonicalPurification.reindex
          (Equiv.prodComm a a)).state := by
  unfold MatrixMap.ancillaNormalizedTraceAction MatrixMap.normalizedTraceAction
  exact mul_le_mul_of_nonneg_left
    (Ω.channelDifference_action_traceNorm_le_canonicalOfMarginalA Φ Ψc) (by norm_num)

/-- Arbitrary-reference version of
`exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA`: if the reference
system is large enough, a pure input-reference state is obtained from the
canonical purification of its input marginal by a right-reference isometry. -/
theorem exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA_of_card_le
    {a : Type u} {r : Type w} [Fintype a] [DecidableEq a] [Fintype r] [DecidableEq r]
    (Ω : PureVector (Prod a r)) (hcard : Fintype.card a ≤ Fintype.card r) :
    ∃ V : ReferenceIsometry a r,
      Ω = V.applyPureVectorRight
        (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)) := by
  rcases exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      Ω.state.marginalA.canonicalPurification_purifies
      Ω.reindex_prodComm_purifies_marginalA hcard with ⟨V, hV⟩
  refine ⟨V, ?_⟩
  apply PureVector.ext_amp
  funext x
  have hx := congrArg (fun Φ : PureVector (Prod r a) => Φ.amp (x.2, x.1)) hV
  simpa [ReferenceIsometry.applyPureVectorRight_amp, ReferenceIsometry.applyAmpRight,
    PureVector.reindex_amp, ReferenceIsometry.applyPureVector_amp,
    ReferenceIsometry.applyAmp, Matrix.mulVec, dotProduct] using hx

/-- Arbitrary-reference pure-state CKR reduction step.  The channel-difference
action on a pure extension is no larger than the action on the canonical
purification of its input marginal, provided the reference is large enough to
contain the canonical reference. -/
theorem channelDifference_normalizedAction_le_canonicalOfMarginalA_of_card_le
    {a : Type u} {b : Type v} {r : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r]
    (Φ Ψc : Channel a b) (Ω : PureVector (Prod a r))
    (hcard : Fintype.card a ≤ Fintype.card r) :
    MatrixMap.ancillaNormalizedTraceAction
        (MatrixMap.channelDifference Φ Ψc) Ω.state ≤
      MatrixMap.ancillaNormalizedTraceAction
        (MatrixMap.channelDifference Φ Ψc)
        (Ω.state.marginalA.canonicalPurification.reindex
          (Equiv.prodComm a a)).state := by
  classical
  rcases Ω.exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA_of_card_le hcard
    with ⟨V, hV⟩
  let X : CMatrix (Prod b a) :=
    MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
      (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)).state.matrix
  have hAction :
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel r).map
          Ω.state.matrix =
        V.applyMatrixRight X := by
    have h := MatrixMap.channelDifference_kron_id_apply_applyPureVectorRight
      (a := a) (b := b) (r₁ := a) (r₂ := r) Φ Ψc V
      (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a))
    simpa [X, ← hV] using h
  have hXHerm : X.IsHermitian := by
    simpa [X] using MatrixMap.channelDifference_kron_id_apply_isHermitian
      (a := a) (b := b) (r := a) Φ Ψc
      (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)).state
  have hXtr : X.trace = 0 := by
    simpa [X] using MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
      (a := a) (b := b) (r := a) Φ Ψc
      (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)).state
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) *
      traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel r).map
          Ω.state.matrix) ≤
    (1 / 2 : ℝ) *
      traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
          (Ω.state.marginalA.canonicalPurification.reindex
            (Equiv.prodComm a a)).state.matrix)
  rw [hAction]
  change (1 / 2 : ℝ) * traceNorm (V.applyMatrixRight X) ≤
    (1 / 2 : ℝ) * traceNorm X
  exact mul_le_mul_of_nonneg_left
    (MatrixMap.traceNorm_applyMatrixRight_le_of_isHermitian_trace_zero V hXHerm hXtr)
    (by norm_num)

end PureVector

/-- CKR purifying register for the purified de-Finetti reference state.

We use the finite profile basis as the purification label set. -/
abbrev ckrPurifyingRegister (a : Type v) [Fintype a] [DecidableEq a] (n : ℕ) :=
  TensorPowerProfile (Prod a a) n

instance ckrPurifyingRegisterDecidableEq
    (a : Type v) [Fintype a] [DecidableEq a] (n : ℕ) :
    DecidableEq (ckrPurifyingRegister a n) :=
  Classical.decEq _

private theorem inv_sqrt_profile_count_mul_inv_sqrt_profile_count
    [Nonempty a] (n : ℕ) :
    ((Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹) *
        ((Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹) =
      ((Fintype.card (ckrPurifyingRegister a n) : ℂ)⁻¹) := by
  have hpos : 0 < (Fintype.card (ckrPurifyingRegister a n) : ℝ) := by
    exact_mod_cast TensorPowerProfile.card_pos (a := Prod a a) n
  have hsqrt_sq :
      (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ) *
          (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ) =
        (Fintype.card (ckrPurifyingRegister a n) : ℂ) := by
    norm_cast
    simp
  rw [← mul_inv_rev, hsqrt_sq]

/-- CKR purified reference vector for `τ_{H^n K^n N}`.

The vector is the normalized coherent superposition of the normalized profile
vectors, with the profile itself used as the purifying register. -/
def ckrPurifiedReferenceVector [Nonempty a] (n : ℕ) :
    PureVector (Prod (TensorPower (Prod a a) n) (ckrPurifyingRegister a n)) where
  amp xp :=
    ((Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹) *
      tensorPowerProfileUnitVector (a := Prod a a) xp.2 xp.1
  trace_rankOne_eq_one := by
    classical
    let g : ℂ := (Fintype.card (ckrPurifyingRegister a n) : ℂ)
    let c : ℂ := (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹
    have hcstar : star c = c := by
      simp [c]
    have hc2 : c * c = g⁻¹ := by
      simpa [c, g] using inv_sqrt_profile_count_mul_inv_sqrt_profile_count (a := a) n
    have hg_ne : g ≠ 0 := by
      dsimp [g]
      exact_mod_cast TensorPowerProfile.card_ne_zero (a := Prod a a) n
    have hunit :
        ∀ p : ckrPurifyingRegister a n,
          ∑ x : TensorPower (Prod a a) n,
            tensorPowerProfileUnitVector (a := Prod a a) p x *
              star (tensorPowerProfileUnitVector (a := Prod a a) p x) = 1 := by
      intro p
      simpa [Matrix.trace, rankOneMatrix_apply] using
        tensorPowerProfileUnitVector_trace_rankOne_eq_one (a := Prod a a) p
    calc
      (rankOneMatrix
          (fun xp : Prod (TensorPower (Prod a a) n) (ckrPurifyingRegister a n) =>
            c * tensorPowerProfileUnitVector (a := Prod a a) xp.2 xp.1)).trace =
          ∑ xp : Prod (TensorPower (Prod a a) n) (ckrPurifyingRegister a n),
            (c * tensorPowerProfileUnitVector (a := Prod a a) xp.2 xp.1) *
              star (c * tensorPowerProfileUnitVector (a := Prod a a) xp.2 xp.1) := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = ∑ p : ckrPurifyingRegister a n,
            ∑ x : TensorPower (Prod a a) n,
              (c * c) *
                (tensorPowerProfileUnitVector (a := Prod a a) p x *
                  star (tensorPowerProfileUnitVector (a := Prod a a) p x)) := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun x _ => ?_
            calc
              c * tensorPowerProfileUnitVector (a := Prod a a) (x, p).2 (x, p).1 *
                  star (c * tensorPowerProfileUnitVector (a := Prod a a) (x, p).2 (x, p).1) =
                c * tensorPowerProfileUnitVector (a := Prod a a) p x *
                  (star (tensorPowerProfileUnitVector (a := Prod a a) p x) * star c) := by
                  rw [star_mul]
              _ = (c * c) *
                    (tensorPowerProfileUnitVector (a := Prod a a) p x *
                      star (tensorPowerProfileUnitVector (a := Prod a a) p x)) := by
                  rw [hcstar]
                  ring
      _ = ∑ p : ckrPurifyingRegister a n, g⁻¹ := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hc2, ← Finset.mul_sum, hunit p, mul_one]
      _ = 1 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simpa [g] using mul_inv_cancel₀ hg_ne

/-- Purified CKR post-selection reference state before the `H^n × H^n`
reindexing. -/
def ckrPurifiedReferenceState [Nonempty a] (n : ℕ) :
    State (Prod (TensorPower (Prod a a) n) (ckrPurifyingRegister a n)) :=
  (ckrPurifiedReferenceVector (a := a) n).state

@[simp]
theorem ckrPurifiedReferenceState_matrix [Nonempty a] (n : ℕ) :
    (ckrPurifiedReferenceState (a := a) n).matrix =
      rankOneMatrix (ckrPurifiedReferenceVector (a := a) n).amp :=
  rfl

/-- The profile isometry whose columns are the normalized profile vectors. -/
def ckrProfileIsometryMatrix (a : Type v) [Fintype a] [DecidableEq a] (n : ℕ) :
    Matrix (TensorPower (Prod a a) n) (ckrPurifyingRegister a n) ℂ :=
  fun x p => tensorPowerProfileUnitVector (a := Prod a a) p x

theorem ckrProfileIsometryMatrix_mul_conjTranspose [Nonempty a] (n : ℕ) :
    ckrProfileIsometryMatrix a n *
        (ckrProfileIsometryMatrix a n).conjTranspose =
      symmetricProjectionMatrix (a := Prod a a) n := by
  classical
  ext x y
  calc
    (ckrProfileIsometryMatrix a n *
        (ckrProfileIsometryMatrix a n).conjTranspose) x y =
        ∑ p : ckrPurifyingRegister a n,
          tensorPowerProfileUnitVector (a := Prod a a) p x *
            star (tensorPowerProfileUnitVector (a := Prod a a) p y) := by
          simp [ckrProfileIsometryMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
    _ = (∑ p : ckrPurifyingRegister a n,
          rankOneMatrix (tensorPowerProfileUnitVector (a := Prod a a) p)) x y := by
          rw [Matrix.sum_apply]
          rfl
    _ = symmetricProjectionMatrix (a := Prod a a) n x y := by
          rw [symmetricProjectionMatrix_eq_sum_rankOne_profileUnitVector]

theorem ckrProfileIsometryMatrix_conjTranspose_mul [Nonempty a] (n : ℕ) :
    (ckrProfileIsometryMatrix a n).conjTranspose *
        ckrProfileIsometryMatrix a n =
      1 := by
  classical
  ext p q
  calc
    ((ckrProfileIsometryMatrix a n).conjTranspose *
        ckrProfileIsometryMatrix a n) p q =
        ∑ x : TensorPower (Prod a a) n,
          star (tensorPowerProfileUnitVector (a := Prod a a) p x) *
            tensorPowerProfileUnitVector (a := Prod a a) q x := by
          simp [ckrProfileIsometryMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
    _ = (1 : CMatrix (ckrPurifyingRegister a n)) p q := by
          rw [tensorPowerProfileUnitVector_inner]
          by_cases hpq : p = q
          · subst q
            simp
          · simp [hpq]

theorem ckrPurifiedReference_marginal_eq_symmetricProjectionReferenceState
    [Nonempty a] (n : ℕ) :
    (ckrPurifiedReferenceState (a := a) n).marginalA =
      State.symmetricProjectionReferenceState (a := Prod a a) n := by
  classical
  ext x y
  let g : ℂ := (Fintype.card (ckrPurifyingRegister a n) : ℂ)
  let c : ℂ := (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹
  have hcstar : star c = c := by
    simp [c]
  have hc2 : c * c = g⁻¹ := by
    simpa [c, g] using inv_sqrt_profile_count_mul_inv_sqrt_profile_count (a := a) n
  calc
    (ckrPurifiedReferenceState (a := a) n).marginalA.matrix x y =
        ∑ p : ckrPurifyingRegister a n,
          (c * tensorPowerProfileUnitVector (a := Prod a a) p x) *
            star (c * tensorPowerProfileUnitVector (a := Prod a a) p y) := by
          simp [State.marginalA, partialTraceB, ckrPurifiedReferenceState,
            PureVector.state, ckrPurifiedReferenceVector, c]
    _ = g⁻¹ *
        (∑ p : ckrPurifyingRegister a n,
          rankOneMatrix (tensorPowerProfileUnitVector (a := Prod a a) p) x y) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [rankOneMatrix_apply]
          calc
            c * tensorPowerProfileUnitVector (a := Prod a a) p x *
                star (c * tensorPowerProfileUnitVector (a := Prod a a) p y) =
              c * tensorPowerProfileUnitVector (a := Prod a a) p x *
                (star (tensorPowerProfileUnitVector (a := Prod a a) p y) * star c) := by
                rw [star_mul]
            _ = (c * c) *
                (tensorPowerProfileUnitVector (a := Prod a a) p x *
                  star (tensorPowerProfileUnitVector (a := Prod a a) p y)) := by
                rw [hcstar]
                ring
            _ = g⁻¹ *
                (tensorPowerProfileUnitVector (a := Prod a a) p x *
                  star (tensorPowerProfileUnitVector (a := Prod a a) p y)) := by
                rw [hc2]
    _ = ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ)⁻¹ : ℂ) *
        symmetricProjectionMatrix (a := Prod a a) n x y := by
          rw [← Matrix.sum_apply,
            ← symmetricProjectionMatrix_eq_sum_rankOne_profileUnitVector (a := Prod a a)]
          rfl
    _ = (State.symmetricProjectionReferenceState (a := Prod a a) n).matrix x y := by
          simp [Matrix.smul_apply]

/-- CKR purified post-selection reference state, reindexed as
`(H^n × H^n) × N`.  Its first marginal is the source-shaped
`ckrPostSelectionReferenceState`. -/
def ckrPostSelectionPurifiedReferenceStatePair [Nonempty a] (n : ℕ) :
    State (Prod (Prod (TensorPower a n) (TensorPower a n))
      (ckrPurifyingRegister a n)) :=
  (ckrPurifiedReferenceState (a := a) n).reindex
    (Equiv.prodCongr (tensorPowerProdEquiv a a n)
      (Equiv.refl (ckrPurifyingRegister a n)))

theorem ckrPostSelectionPurifiedReferenceStatePair_marginalA [Nonempty a] (n : ℕ) :
    (ckrPostSelectionPurifiedReferenceStatePair (a := a) n).marginalA =
      ckrPostSelectionReferenceState (a := a) n := by
  rw [ckrPostSelectionPurifiedReferenceStatePair]
  rw [State.marginalA_reindex_prodCongr]
  rw [ckrPurifiedReference_marginal_eq_symmetricProjectionReferenceState]

/-- CKR purified post-selection reference state, reindexed as
`H^n × (H^n × N)`, so a channel can act on the first/input factor while the
ordinary reference and the profile purifying register are kept as one joint
ancilla. -/
def ckrPostSelectionPurifiedReferenceState [Nonempty a] (n : ℕ) :
    State (Prod (TensorPower a n)
      (Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))) :=
  (ckrPostSelectionPurifiedReferenceStatePair (a := a) n).reindex
    (Equiv.prodAssoc (TensorPower a n) (TensorPower a n) (ckrPurifyingRegister a n))

/-- Compatibility bridge for the older pair-shaped purified reference name.
Source-facing statements should prefer `ckrPostSelectionPurifiedReferenceStatePair`. -/
abbrev postSelectionPurifiedReferenceStatePair [Nonempty a] (n : ℕ) :
    State (Prod (Prod (TensorPower a n) (TensorPower a n))
      (ckrPurifyingRegister a n)) :=
  ckrPostSelectionPurifiedReferenceStatePair (a := a) n

theorem postSelectionPurifiedReferenceStatePair_marginalA [Nonempty a] (n : ℕ) :
    (postSelectionPurifiedReferenceStatePair (a := a) n).marginalA =
      postSelectionReferenceState (a := a) n := by
  simpa [postSelectionPurifiedReferenceStatePair, postSelectionReferenceState] using
    ckrPostSelectionPurifiedReferenceStatePair_marginalA (a := a) n

/-- Compatibility bridge for the older channel-input-shaped purified reference
name. Source-facing statements should prefer `ckrPostSelectionPurifiedReferenceState`. -/
abbrev postSelectionPurifiedReferenceState [Nonempty a] (n : ℕ) :
    State (Prod (TensorPower a n)
      (Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))) :=
  ckrPostSelectionPurifiedReferenceState (a := a) n

end

end QIT
