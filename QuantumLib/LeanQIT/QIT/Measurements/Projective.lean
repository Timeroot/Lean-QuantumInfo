/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Measurements.Map
public import QIT.States.Schatten
public import QIT.States.TraceNorm.Distance

/-!
# Finite projective measurements

A finite projective measurement is a finite family of mutually orthogonal
Hermitian idempotent effects summing to the identity.  This is the local PVM
surface needed for the POVM-to-projective realization route, following the
projective-measurement/Naimark reduction recorded in
[ColadangeloGohScarani2016SelfTesting, all_pure_v2.tex:124-128] and
[MayersYao2003SelfTesting, mayers-yao-2003-self-testing.tex:307-325].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

variable {y : Type u} {a : Type v}
variable [Fintype y] [Fintype a] [DecidableEq a]

/--
A finite projective measurement (PVM) with outcomes indexed by `y`.

The fields keep projectivity explicit: each effect is Hermitian and
idempotent, distinct effects are orthogonal, and all effects sum to identity.
-/
structure ProjectiveMeasurement (y : Type u) (a : Type v)
    [Fintype y] [Fintype a] [DecidableEq a] where
  /-- The projection associated with an outcome. -/
  effects : y → CMatrix a
  /-- Each effect is Hermitian. -/
  isHermitian : ∀ outcome, (effects outcome).IsHermitian
  /-- Each effect is idempotent. -/
  idempotent : ∀ outcome, effects outcome * effects outcome = effects outcome
  /-- Distinct effects are mutually orthogonal. -/
  orthogonal : ∀ i j, i ≠ j → effects i * effects j = 0
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ outcome, effects outcome = 1

namespace ProjectiveMeasurement

variable (P : ProjectiveMeasurement y a)

/-- A projective measurement's effects sum to the identity matrix. -/
@[simp]
theorem sum_effects : ∑ outcome, P.effects outcome = 1 :=
  P.sum_eq_one

/-- Each projective effect is positive semidefinite. -/
theorem effect_posSemidef (outcome : y) :
    (P.effects outcome).PosSemidef := by
  have hpsd :
      (Matrix.conjTranspose (P.effects outcome) * P.effects outcome).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self (P.effects outcome)
  rw [P.isHermitian outcome, P.idempotent outcome] at hpsd
  exact hpsd

/-- The square of a projective effect is positive semidefinite. -/
theorem effect_mul_self_posSemidef (outcome : y) :
    (P.effects outcome * P.effects outcome).PosSemidef := by
  rw [P.idempotent outcome]
  exact P.effect_posSemidef outcome

/-- A finite projective measurement is a finite POVM. -/
def toPOVM : POVM y a where
  effects := P.effects
  pos := P.effect_posSemidef
  sum_eq_one := P.sum_eq_one

/-- The POVM associated to a projective measurement has the same effects. -/
@[simp]
theorem toPOVM_effects (outcome : y) :
    P.toPOVM.effects outcome = P.effects outcome :=
  rfl

/-- The POVM associated to a projective measurement has the same completeness law. -/
@[simp]
theorem toPOVM_sum_effects :
    ∑ outcome, P.toPOVM.effects outcome = 1 := by
  simp [toPOVM]

/-- For trace-one projective effects, the associated measurement channel sends
the identity to the identity. This is the rank-one/projective case from
Tomamichel's measurement-map source route. -/
theorem toPOVM_measureMap_one_eq_one_of_traceOne
    [DecidableEq y]
    (htrace : ∀ outcome, (P.effects outcome).trace = 1) :
    (Channel.measure P.toPOVM).map (1 : CMatrix a) = (1 : CMatrix y) := by
  rw [Channel.measure_map]
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single i]
    · simp [htrace i]
    · intro outcome _ houtcome
      simp [houtcome]
    · intro hi
      simp at hi
  · rw [Matrix.one_apply, if_neg hij]
    refine Finset.sum_eq_zero fun outcome _ => ?_
    rw [Matrix.smul_apply, Matrix.single_apply]
    have hnot : ¬ (outcome = i ∧ outcome = j) := by
      intro h
      exact hij (h.1.symm.trans h.2)
    simp [hnot]

/-- Trace-one projective measurements satisfy the local unit-effect condition
required by the source-facing measurement monotonicity statement. -/
theorem toPOVM_measurementMapDoesNotEnlargeUnit_of_traceOne
    [DecidableEq y]
    (htrace : ∀ outcome, (P.effects outcome).trace = 1) :
    measurementMapDoesNotEnlargeUnit P.toPOVM := by
  rw [measurementMapDoesNotEnlargeUnit]
  rw [P.toPOVM_measureMap_one_eq_one_of_traceOne htrace]

/-- The pinching map associated with a projective measurement.

It is represented in Kraus form by the projective effects themselves:
`X ↦ ∑ᵢ Pᵢ X Pᵢ`. -/
def pinchingMap : MatrixMap a a :=
  MatrixMap.ofKraus P.effects

/-- The pinching map unfolds to the usual `∑ᵢ Pᵢ X Pᵢ` expression. -/
@[simp]
theorem pinchingMap_apply (X : CMatrix a) :
    P.pinchingMap X = ∑ outcome, P.effects outcome * X * P.effects outcome := by
  change
    ∑ outcome, P.effects outcome * X * Matrix.conjTranspose (P.effects outcome) =
      ∑ outcome, P.effects outcome * X * P.effects outcome
  refine Finset.sum_congr rfl fun outcome _ => ?_
  have hHerm : Matrix.conjTranspose (P.effects outcome) = P.effects outcome := by
    simpa [Matrix.IsHermitian] using P.isHermitian outcome
  rw [hHerm]

/-- Projective pinching is completely positive. -/
theorem pinchingMap_isCompletelyPositive :
    MatrixMap.IsCompletelyPositive P.pinchingMap :=
  MatrixMap.ofKraus_completelyPositive P.effects

/-- Projective pinching is trace preserving. -/
theorem pinchingMap_isTracePreserving :
    MatrixMap.IsTracePreserving P.pinchingMap := by
  intro X
  calc
    (P.pinchingMap X).trace =
        (∑ outcome, P.effects outcome * X * P.effects outcome).trace := by
          rw [pinchingMap_apply]
    _ = ∑ outcome, (P.effects outcome * X * P.effects outcome).trace := by
          rw [Matrix.trace_sum]
    _ = ∑ outcome, (X * P.effects outcome).trace := by
          refine Finset.sum_congr rfl fun outcome _ => ?_
          calc
            (P.effects outcome * X * P.effects outcome).trace =
                ((P.effects outcome * X) * P.effects outcome).trace := by
                  rw [Matrix.mul_assoc]
            _ = (P.effects outcome * (P.effects outcome * X)).trace := by
                  rw [Matrix.trace_mul_comm]
            _ = ((P.effects outcome * P.effects outcome) * X).trace := by
                  rw [Matrix.mul_assoc]
            _ = (P.effects outcome * X).trace := by
                  rw [P.idempotent outcome]
            _ = (X * P.effects outcome).trace := by
                  rw [Matrix.trace_mul_comm]
    _ = (∑ outcome, X * P.effects outcome).trace := by
          rw [Matrix.trace_sum]
    _ = (X * ∑ outcome, P.effects outcome).trace := by
          congr 1
          exact (Matrix.mul_sum Finset.univ P.effects X).symm
    _ = (X * 1).trace := by rw [P.sum_eq_one]
    _ = X.trace := by simp

/-- Projective pinching preserves positive semidefinite matrices. -/
theorem pinchingMap_mapsPositive :
    ∀ X : CMatrix a, X.PosSemidef → (P.pinchingMap X).PosSemidef :=
  MatrixMap.ofKraus_mapsPositive P.effects

/-- The CPTP channel induced by projective pinching. -/
def pinchingChannel : Channel a a where
  map := P.pinchingMap
  completelyPositive := P.pinchingMap_isCompletelyPositive
  tracePreserving := P.pinchingMap_isTracePreserving
  mapsPositive := P.pinchingMap_mapsPositive

/-- The pinching channel acts by pinching with the projective effects. -/
@[simp]
theorem pinchingChannel_map (X : CMatrix a) :
    P.pinchingChannel.map X = ∑ outcome, P.effects outcome * X * P.effects outcome :=
  P.pinchingMap_apply X

/-- The state obtained by applying the pinching channel has the expected
pinched matrix. -/
@[simp]
theorem pinchingChannel_applyState_matrix (ρ : State a) :
    (P.pinchingChannel.applyState ρ).matrix =
      ∑ outcome, P.effects outcome * ρ.matrix * P.effects outcome :=
  P.pinchingChannel_map ρ.matrix

/-- Projective pinching is idempotent as a matrix map. -/
theorem pinchingMap_idempotent (X : CMatrix a) :
    P.pinchingMap (P.pinchingMap X) = P.pinchingMap X := by
  classical
  rw [pinchingMap_apply, pinchingMap_apply]
  calc
    ∑ outcome, P.effects outcome *
        (∑ outcome, P.effects outcome * X * P.effects outcome) *
        P.effects outcome =
      ∑ i, ∑ j,
        P.effects i * (P.effects j * X * P.effects j) * P.effects i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Matrix.mul_sum, Finset.sum_mul]
    _ = ∑ i, P.effects i * X * P.effects i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · calc
            P.effects i * (P.effects i * X * P.effects i) * P.effects i =
                (P.effects i * P.effects i) * X * (P.effects i * P.effects i) := by
                  noncomm_ring
            _ = P.effects i * X * P.effects i := by
                  rw [P.idempotent i]
        · intro j _ hji
          have hij : i ≠ j := by
            intro hij
            exact hji hij.symm
          calc
            P.effects i * (P.effects j * X * P.effects j) * P.effects i =
                (P.effects i * P.effects j) * X * P.effects j * P.effects i := by
                  noncomm_ring
            _ = 0 := by
                  rw [P.orthogonal i j hij]
                  simp
        · intro hi
          simp at hi

/-- Pinching fixes matrices that commute with every projective effect. -/
theorem pinchingMap_eq_self_of_commute (X : CMatrix a)
    (hcomm : ∀ outcome, P.effects outcome * X = X * P.effects outcome) :
    P.pinchingMap X = X := by
  rw [pinchingMap_apply]
  calc
    ∑ outcome, P.effects outcome * X * P.effects outcome =
        ∑ outcome, X * P.effects outcome := by
          refine Finset.sum_congr rfl fun outcome _ => ?_
          calc
            P.effects outcome * X * P.effects outcome =
                (X * P.effects outcome) * P.effects outcome := by
                  rw [hcomm outcome]
            _ = X * (P.effects outcome * P.effects outcome) := by
                  rw [Matrix.mul_assoc]
            _ = X * P.effects outcome := by
                  rw [P.idempotent outcome]
    _ = X * ∑ outcome, P.effects outcome := by
          exact (Matrix.mul_sum Finset.univ P.effects X).symm
    _ = X * 1 := by rw [P.sum_eq_one]
    _ = X := by simp

/-- Applying the pinching channel twice to a state is the same as applying it
once. -/
theorem pinchingChannel_applyState_idempotent (ρ : State a) :
    P.pinchingChannel.applyState (P.pinchingChannel.applyState ρ) =
      P.pinchingChannel.applyState ρ := by
  apply State.ext
  exact P.pinchingMap_idempotent ρ.matrix

/-- Pinching by the coordinate rank-one diagonal projectors keeps exactly the
diagonal part of a matrix. -/
private theorem diagonalRankOnePinching_sum (X : CMatrix a) :
    (∑ outcome : a,
        Matrix.diagonal (fun i => if i = outcome then (1 : ℂ) else 0) * X *
          Matrix.diagonal (fun i => if i = outcome then (1 : ℂ) else 0)) =
      Matrix.diagonal (fun i => X i i) := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    · intro outcome _ hout
      have hiout : i ≠ outcome := fun h => hout h.symm
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hiout]
    · intro hi
      simp at hi
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact Finset.sum_eq_zero fun outcome _ => by
      by_cases hi : i = outcome
      · by_cases hj : j = outcome
        · exact False.elim (hij (hi.trans hj.symm))
        · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj]
      · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hi]

/-- The spectral projective measurement associated with a Hermitian matrix. -/
def ofHermitianEigenbasis (M : CMatrix a) (hM : M.IsHermitian) :
    ProjectiveMeasurement a a where
  effects := fun outcome =>
    (hM.eigenvectorUnitary : CMatrix a) *
      Matrix.diagonal (fun i => if i = outcome then (1 : ℂ) else 0) *
      star (hM.eigenvectorUnitary : CMatrix a)
  isHermitian := by
    intro outcome
    let U : CMatrix a := hM.eigenvectorUnitary
    let D : CMatrix a := Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0
    have hD : Matrix.conjTranspose D = D := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D]
      · have hji : j ≠ i := fun hji => hij hji.symm
        simp [D, Matrix.diagonal, hij, hji]
    change Matrix.conjTranspose (U * D * star U) = U * D * star U
    have hstar : Matrix.conjTranspose (star U) = U := by
      rw [← Matrix.star_eq_conjTranspose, star_star]
    have hUct : Matrix.conjTranspose U = star U := by
      rw [← Matrix.star_eq_conjTranspose]
    calc
      Matrix.conjTranspose (U * D * star U) =
          Matrix.conjTranspose (star U) * Matrix.conjTranspose D *
            Matrix.conjTranspose U := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = U * D * star U := by
            rw [hstar, hD, hUct]
  idempotent := by
    intro outcome
    let U : CMatrix a := hM.eigenvectorUnitary
    let D : CMatrix a := Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0
    have hU : star U * U = 1 := by
      simp [U, Unitary.coe_star_mul_self hM.eigenvectorUnitary]
    have hDD : D * D = D := by
      change (Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0) *
          (Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0) =
        Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : i = outcome <;> simp [hi]
      · simp [Matrix.diagonal, hij]
    change (U * D * star U) * (U * D * star U) = U * D * star U
    calc
      (U * D * star U) * (U * D * star U) =
          U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * D * 1 * D * star U := by rw [hU]
      _ = U * (D * D) * star U := by noncomm_ring
      _ = U * D * star U := by rw [hDD]
  orthogonal := by
    intro i j hij
    let U : CMatrix a := hM.eigenvectorUnitary
    let Di : CMatrix a := Matrix.diagonal fun k => if k = i then (1 : ℂ) else 0
    let Dj : CMatrix a := Matrix.diagonal fun k => if k = j then (1 : ℂ) else 0
    have hU : star U * U = 1 := by
      simp [U, Unitary.coe_star_mul_self hM.eigenvectorUnitary]
    have hDD : Di * Dj = 0 := by
      change (Matrix.diagonal fun k => if k = i then (1 : ℂ) else 0) *
          (Matrix.diagonal fun k => if k = j then (1 : ℂ) else 0) =
        0
      rw [Matrix.diagonal_mul_diagonal]
      ext r c
      by_cases hrc : r = c
      · subst c
        by_cases hri : r = i
        · subst i
          have hrj : r ≠ j := hij
          simp [hrj]
        · simp [hri]
      · simp [Matrix.diagonal, hrc]
    change (U * Di * star U) * (U * Dj * star U) = 0
    calc
      (U * Di * star U) * (U * Dj * star U) =
          U * Di * (star U * U) * Dj * star U := by noncomm_ring
      _ = U * Di * 1 * Dj * star U := by rw [hU]
      _ = U * (Di * Dj) * star U := by noncomm_ring
      _ = 0 := by rw [hDD]; simp
  sum_eq_one := by
    let U : CMatrix a := hM.eigenvectorUnitary
    let D : a → CMatrix a := fun outcome =>
      Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0
    have hsumD : ∑ outcome, D outcome = (1 : CMatrix a) := by
      ext i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.sum_apply]
        simp only [D, Matrix.diagonal_apply, Matrix.one_apply, if_true]
        change (∑ outcome, if i = outcome then (1 : ℂ) else 0) = 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro outcome _ hne
          have hne' : i ≠ outcome := fun h => hne h.symm
          simp [hne']
        · intro hi
          simp at hi
      · rw [Matrix.sum_apply]
        rw [show (1 : CMatrix a) i j = 0 by simp [hij]]
        exact Finset.sum_eq_zero fun outcome _ => by
          simpa [D] using
            (Matrix.diagonal_apply_ne (fun k => if k = outcome then (1 : ℂ) else 0) hij)
    change ∑ outcome, U * D outcome * star U = 1
    calc
      ∑ outcome, U * D outcome * star U =
          (∑ outcome, U * D outcome) * star U := by
            rw [Finset.sum_mul]
      _ = (U * ∑ outcome, D outcome) * star U := by
            rw [Matrix.mul_sum]
      _ = (U * 1) * star U := by rw [hsumD]
      _ = U * star U := by simp
      _ = 1 := by
            simp [U]

@[simp]
theorem ofHermitianEigenbasis_effects (M : CMatrix a) (hM : M.IsHermitian)
    (outcome : a) :
    (ofHermitianEigenbasis M hM).effects outcome =
      (hM.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => if i = outcome then (1 : ℂ) else 0) *
        star (hM.eigenvectorUnitary : CMatrix a) :=
  rfl

/-- A spectral projective effect is a right eigen-effect of the matrix whose
eigenbasis defines it. -/
theorem ofHermitianEigenbasis_mul_effect (M : CMatrix a) (hM : M.IsHermitian)
    (outcome : a) :
    M * (ofHermitianEigenbasis M hM).effects outcome =
      (hM.eigenvalues outcome : ℂ) • (ofHermitianEigenbasis M hM).effects outcome := by
  classical
  let U : CMatrix a := hM.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0
  let Λ : CMatrix a := Matrix.diagonal fun i => (hM.eigenvalues i : ℂ)
  let lam : ℂ := hM.eigenvalues outcome
  have hspec : M = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hM.spectral_theorem
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hM.eigenvectorUnitary]
  have hΛD : Λ * D = lam • D := by
    change (Matrix.diagonal fun i => (hM.eigenvalues i : ℂ)) *
        (Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0) =
      lam • (Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0)
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = outcome
      · subst outcome
        simp [lam]
      · simp [lam, hi, Matrix.smul_apply]
    · simp [Matrix.diagonal, Matrix.smul_apply, hij]
  change M * (U * D * star U) = lam • (U * D * star U)
  calc
    M * (U * D * star U) =
        (U * Λ * star U) * (U * D * star U) := by rw [hspec]
    _ = U * Λ * (star U * U) * D * star U := by noncomm_ring
    _ = U * Λ * 1 * D * star U := by rw [hU]
    _ = U * (Λ * D) * star U := by noncomm_ring
    _ = U * (lam • D) * star U := by rw [hΛD]
    _ = lam • (U * D * star U) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]

/-- A spectral projective effect is a left eigen-effect of the matrix whose
eigenbasis defines it. -/
theorem ofHermitianEigenbasis_effect_mul (M : CMatrix a) (hM : M.IsHermitian)
    (outcome : a) :
    (ofHermitianEigenbasis M hM).effects outcome * M =
      (hM.eigenvalues outcome : ℂ) • (ofHermitianEigenbasis M hM).effects outcome := by
  classical
  let U : CMatrix a := hM.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0
  let Λ : CMatrix a := Matrix.diagonal fun i => (hM.eigenvalues i : ℂ)
  let lam : ℂ := hM.eigenvalues outcome
  have hspec : M = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hM.spectral_theorem
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hM.eigenvectorUnitary]
  have hDΛ : D * Λ = lam • D := by
    change (Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0) *
        (Matrix.diagonal fun i => (hM.eigenvalues i : ℂ)) =
      lam • (Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0)
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = outcome
      · subst outcome
        simp [lam]
      · simp [lam, hi, Matrix.smul_apply]
    · simp [Matrix.diagonal, Matrix.smul_apply, hij]
  change (U * D * star U) * M = lam • (U * D * star U)
  calc
    (U * D * star U) * M =
        (U * D * star U) * (U * Λ * star U) := by rw [hspec]
    _ = U * D * (star U * U) * Λ * star U := by noncomm_ring
    _ = U * D * 1 * Λ * star U := by rw [hU]
    _ = U * (D * Λ) * star U := by noncomm_ring
    _ = U * (lam • D) * star U := by rw [hDΛ]
    _ = lam • (U * D * star U) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Each spectral projective effect commutes with the Hermitian matrix whose
eigenbasis defines it. -/
theorem ofHermitianEigenbasis_effect_commute (M : CMatrix a) (hM : M.IsHermitian)
    (outcome : a) :
    (ofHermitianEigenbasis M hM).effects outcome * M =
      M * (ofHermitianEigenbasis M hM).effects outcome := by
  classical
  let U : CMatrix a := hM.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0
  let Λ : CMatrix a := Matrix.diagonal fun i => (hM.eigenvalues i : ℂ)
  have hspec : M = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hM.spectral_theorem
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hM.eigenvectorUnitary]
  have hDΛ : D * Λ = Λ * D := by
    change (Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0) *
        (Matrix.diagonal fun i => (hM.eigenvalues i : ℂ)) =
      (Matrix.diagonal fun i => (hM.eigenvalues i : ℂ)) *
        (Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0)
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, hij]
  change (U * D * star U) * M = M * (U * D * star U)
  calc
    (U * D * star U) * M =
        (U * D * star U) * (U * Λ * star U) := by rw [hspec]
    _ = U * D * (star U * U) * Λ * star U := by noncomm_ring
    _ = U * D * 1 * Λ * star U := by rw [hU]
    _ = U * (D * Λ) * star U := by noncomm_ring
    _ = U * (Λ * D) * star U := by rw [hDΛ]
    _ = U * Λ * 1 * D * star U := by noncomm_ring
    _ = U * Λ * (star U * U) * D * star U := by rw [hU]
    _ = (U * Λ * star U) * (U * D * star U) := by noncomm_ring
    _ = M * (U * D * star U) := by rw [hspec]

/-- In the eigenbasis of the reference Hermitian matrix, spectral pinching is
exactly the operation that discards off-diagonal entries. -/
theorem ofHermitianEigenbasis_pinchingMap_eigenbasis (M : CMatrix a)
    (hM : M.IsHermitian) (X : CMatrix a) :
    star (hM.eigenvectorUnitary : CMatrix a) *
        (ofHermitianEigenbasis M hM).pinchingMap X *
        (hM.eigenvectorUnitary : CMatrix a) =
      Matrix.diagonal
        (fun i =>
          (star (hM.eigenvectorUnitary : CMatrix a) * X *
            (hM.eigenvectorUnitary : CMatrix a)) i i) := by
  classical
  let U : CMatrix a := hM.eigenvectorUnitary
  let P : ProjectiveMeasurement a a := ofHermitianEigenbasis M hM
  let D : a → CMatrix a := fun outcome =>
    Matrix.diagonal fun i => if i = outcome then (1 : ℂ) else 0
  let Y : CMatrix a := star U * X * U
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hM.eigenvectorUnitary]
  rw [P.pinchingMap_apply]
  calc
    star U * (∑ outcome, P.effects outcome * X * P.effects outcome) * U =
        ∑ outcome, star U * (P.effects outcome * X * P.effects outcome) * U := by
          rw [Matrix.mul_sum, Finset.sum_mul]
    _ = ∑ outcome, D outcome * Y * D outcome := by
          refine Finset.sum_congr rfl fun outcome _ => ?_
          calc
            star U * (P.effects outcome * X * P.effects outcome) * U =
                star U * ((U * D outcome * star U) * X *
                  (U * D outcome * star U)) * U := by
                  rfl
            _ = (star U * U) * D outcome * star U * X * U *
                  D outcome * (star U * U) := by
                  noncomm_ring
            _ = 1 * D outcome * star U * X * U * D outcome * 1 := by
                  rw [hU]
            _ = D outcome * Y * D outcome := by
                  simp [Y, Matrix.mul_assoc]
    _ = Matrix.diagonal (fun i => Y i i) := by
          exact diagonalRankOnePinching_sum Y
    _ = Matrix.diagonal
        (fun i =>
          (star (hM.eigenvectorUnitary : CMatrix a) * X *
            (hM.eigenvectorUnitary : CMatrix a)) i i) := by
          rfl

/-- Spectral rank-one pinching contracts PSD power traces in the convex range
`q ≥ 1`.

This is the trace-power form of the pinching inequality used by the
sandwiched-Renyi DPI proof route. -/
theorem ofHermitianEigenbasis_pinchingMap_psdTracePower_le
    (M : CMatrix a) (hM : M.IsHermitian) {X : CMatrix a} (hX : X.PosSemidef)
    {q : ℝ} (hq : 1 ≤ q) :
    psdTracePower ((ofHermitianEigenbasis M hM).pinchingMap X)
        ((ofHermitianEigenbasis M hM).pinchingMap_mapsPositive X hX) q ≤
      psdTracePower X hX q := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.eigenvectorUnitary
  let P : ProjectiveMeasurement a a := ofHermitianEigenbasis M hM
  let Xp : CMatrix a := P.pinchingMap X
  let X' : CMatrix a := star (U : CMatrix a) * X * (U : CMatrix a)
  have hq_nonneg : 0 ≤ q := le_trans zero_le_one hq
  have hXp : Xp.PosSemidef := by
    simpa [Xp, P] using P.pinchingMap_mapsPositive X hX
  have hX' : X'.PosSemidef := by
    simpa [X', U] using posSemidef_unitary_conj hX U
  have hpinch_conj :
      star (U : CMatrix a) * Xp * (U : CMatrix a) =
        Matrix.diagonal (fun i => X' i i) := by
    simpa [U, P, Xp, X'] using ofHermitianEigenbasis_pinchingMap_eigenbasis M hM X
  have hreal_fun : (fun i => (((X' i i).re : ℝ) : ℂ)) = fun i => X' i i := by
    simpa [Matrix.diag] using hX'.isHermitian.coe_re_diag
  have hpinch_conj_real :
      star (U : CMatrix a) * Xp * (U : CMatrix a) =
        Matrix.diagonal (fun i => (((X' i i).re : ℝ) : ℂ)) := by
    rw [hpinch_conj, hreal_fun]
  have hdiag_nonneg : ∀ i, 0 ≤ (X' i i).re :=
    posSemidef_diagonal_re_nonneg hX'
  have hleft_diag :
      psdTracePower (star (U : CMatrix a) * Xp * (U : CMatrix a))
          (posSemidef_unitary_conj hXp U) q =
        ∑ i, (X' i i).re ^ q := by
    simpa [hpinch_conj_real] using
      psdTracePower_diagonal_ofReal (a := a) (fun i => (X' i i).re)
        hdiag_nonneg q
  calc
    psdTracePower ((ofHermitianEigenbasis M hM).pinchingMap X)
        ((ofHermitianEigenbasis M hM).pinchingMap_mapsPositive X hX) q =
        psdTracePower Xp hXp q := by
          simp [P, Xp]
    _ = psdTracePower (star (U : CMatrix a) * Xp * (U : CMatrix a))
          (posSemidef_unitary_conj hXp U) q := by
          rw [psdTracePower_unitary_conj U hXp (p := q) hq_nonneg]
    _ = ∑ i, (X' i i).re ^ q := hleft_diag
    _ ≤ psdTracePower X' hX' q :=
          posSemidef_sum_diagonal_re_rpow_le_psdTracePower hX' hq
    _ = psdTracePower X hX q := by
          rw [psdTracePower_unitary_conj U hX (p := q) hq_nonneg]

/-- Spectral rank-one pinching expands PSD power traces in the concave range
`0 ≤ p ≤ 1`.

This is the lower-parameter counterpart of
`ofHermitianEigenbasis_pinchingMap_psdTracePower_le`, and supplies the
trace-power direction needed when the Renyi logarithmic prefactor is negative. -/
theorem ofHermitianEigenbasis_pinchingMap_psdTracePower_ge
    (M : CMatrix a) (hM : M.IsHermitian) {X : CMatrix a} (hX : X.PosSemidef)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    psdTracePower X hX p ≤
      psdTracePower ((ofHermitianEigenbasis M hM).pinchingMap X)
        ((ofHermitianEigenbasis M hM).pinchingMap_mapsPositive X hX) p := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hM.eigenvectorUnitary
  let P : ProjectiveMeasurement a a := ofHermitianEigenbasis M hM
  let Xp : CMatrix a := P.pinchingMap X
  let X' : CMatrix a := star (U : CMatrix a) * X * (U : CMatrix a)
  have hXp : Xp.PosSemidef := by
    simpa [Xp, P] using P.pinchingMap_mapsPositive X hX
  have hX' : X'.PosSemidef := by
    simpa [X', U] using posSemidef_unitary_conj hX U
  have hpinch_conj :
      star (U : CMatrix a) * Xp * (U : CMatrix a) =
        Matrix.diagonal (fun i => X' i i) := by
    simpa [U, P, Xp, X'] using ofHermitianEigenbasis_pinchingMap_eigenbasis M hM X
  have hreal_fun : (fun i => (((X' i i).re : ℝ) : ℂ)) = fun i => X' i i := by
    simpa [Matrix.diag] using hX'.isHermitian.coe_re_diag
  have hpinch_conj_real :
      star (U : CMatrix a) * Xp * (U : CMatrix a) =
        Matrix.diagonal (fun i => (((X' i i).re : ℝ) : ℂ)) := by
    rw [hpinch_conj, hreal_fun]
  have hdiag_nonneg : ∀ i, 0 ≤ (X' i i).re :=
    posSemidef_diagonal_re_nonneg hX'
  have hright_diag :
      psdTracePower (star (U : CMatrix a) * Xp * (U : CMatrix a))
          (posSemidef_unitary_conj hXp U) p =
        ∑ i, (X' i i).re ^ p := by
    simpa [hpinch_conj_real] using
      psdTracePower_diagonal_ofReal (a := a) (fun i => (X' i i).re)
        hdiag_nonneg p
  calc
    psdTracePower X hX p =
        psdTracePower X' hX' p := by
          rw [psdTracePower_unitary_conj U hX (p := p) hp0]
    _ ≤ ∑ i, (X' i i).re ^ p :=
          psdTracePower_le_posSemidef_sum_diagonal_re_rpow hX' hp0 hp1
    _ = psdTracePower (star (U : CMatrix a) * Xp * (U : CMatrix a))
          (posSemidef_unitary_conj hXp U) p := hright_diag.symm
    _ = psdTracePower Xp hXp p := by
          rw [psdTracePower_unitary_conj U hXp (p := p) hp0]
    _ = psdTracePower ((ofHermitianEigenbasis M hM).pinchingMap X)
        ((ofHermitianEigenbasis M hM).pinchingMap_mapsPositive X hX) p := by
          simp [P, Xp]

/-- Spectral rank-one pinching contracts the PSD Schatten `p`-norm expression
for `p ≥ 1`.

This is the PSD downstream specialization of Tomamichel's pinching norm
inequality `metric.tex`, Eq. `eq:pinch-norm`.  The proof packages the existing
trace-power contraction for spectral pinching with the monotonicity of the
positive real `1 / p` power in the local PSD Schatten expression. -/
theorem ofHermitianEigenbasis_pinchingMap_psdSchattenPNorm_le
    (M : CMatrix a) (hM : M.IsHermitian) {X : CMatrix a} (hX : X.PosSemidef)
    {p : ℝ} (hp : 1 ≤ p) :
    psdSchattenPNorm ((ofHermitianEigenbasis M hM).pinchingMap X)
        ((ofHermitianEigenbasis M hM).pinchingMap_mapsPositive X hX)
        ⟨p, lt_of_lt_of_le zero_lt_one hp⟩ ≤
      psdSchattenPNorm X hX ⟨p, lt_of_lt_of_le zero_lt_one hp⟩ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  exact psdSchattenPNorm_le_of_psdTracePower_le
    ((ofHermitianEigenbasis M hM).pinchingMap_mapsPositive X hX) hX hp_pos
    (ofHermitianEigenbasis_pinchingMap_psdTracePower_le M hM hX hp)

/-- Projective pinching preserves the trace norm of positive semidefinite
inputs.

For positive inputs the trace norm is the trace, and projective pinching is
trace-preserving.  This is the trace-norm support bridge needed by downstream
finite-resource pinching arguments. -/
theorem pinchingMap_traceNorm_eq_of_posSemidef
    (X : CMatrix a) (hX : X.PosSemidef) :
    traceNorm (P.pinchingMap X) = traceNorm X := by
  rw [traceNorm_posSemidef_eq_trace_re (P.pinchingMap X)
      (P.pinchingMap_mapsPositive X hX),
    traceNorm_posSemidef_eq_trace_re X hX]
  exact congrArg Complex.re (P.pinchingMap_isTracePreserving X)

/-- Projective pinching contracts the trace norm on positive semidefinite
inputs. -/
theorem pinchingMap_traceNorm_le_of_posSemidef
    (X : CMatrix a) (hX : X.PosSemidef) :
    traceNorm (P.pinchingMap X) ≤ traceNorm X :=
  le_of_eq (P.pinchingMap_traceNorm_eq_of_posSemidef X hX)

/-- Spectral pinching contracts the trace norm on positive semidefinite inputs.

This is the trace-norm specialization of Tomamichel's pinching norm inequality
`metric.tex`, Eq. `eq:pinch-norm`, in the finite-dimensional PSD form used by
the local one-shot/Renyi infrastructure. -/
theorem ofHermitianEigenbasis_pinchingMap_traceNorm_le_of_posSemidef
    (M : CMatrix a) (hM : M.IsHermitian) {X : CMatrix a} (hX : X.PosSemidef) :
    traceNorm ((ofHermitianEigenbasis M hM).pinchingMap X) ≤ traceNorm X :=
  (ofHermitianEigenbasis M hM).pinchingMap_traceNorm_le_of_posSemidef X hX

/-- Pinching in the spectral projective measurement of a Hermitian matrix
fixes that matrix. -/
theorem ofHermitianEigenbasis_pinchingMap_self (M : CMatrix a) (hM : M.IsHermitian) :
    (ofHermitianEigenbasis M hM).pinchingMap M = M :=
  (ofHermitianEigenbasis M hM).pinchingMap_eq_self_of_commute M
    (ofHermitianEigenbasis_effect_commute M hM)

/-- Spectral pinching of any matrix commutes with the Hermitian matrix whose
eigenbasis defines the pinching. -/
theorem ofHermitianEigenbasis_pinchingMap_commute (M : CMatrix a) (hM : M.IsHermitian)
    (X : CMatrix a) :
    (ofHermitianEigenbasis M hM).pinchingMap X * M =
      M * (ofHermitianEigenbasis M hM).pinchingMap X := by
  classical
  let P : ProjectiveMeasurement a a := ofHermitianEigenbasis M hM
  rw [P.pinchingMap_apply]
  calc
    (∑ outcome, P.effects outcome * X * P.effects outcome) * M =
        ∑ outcome, (P.effects outcome * X * P.effects outcome) * M := by
          rw [Finset.sum_mul]
    _ = ∑ outcome, M * (P.effects outcome * X * P.effects outcome) := by
          refine Finset.sum_congr rfl fun outcome _ => ?_
          let E : CMatrix a := P.effects outcome
          let lam : ℂ := hM.eigenvalues outcome
          have hEM : E * M = lam • E := by
            simpa [P, E, lam] using ofHermitianEigenbasis_effect_mul M hM outcome
          have hME : M * E = lam • E := by
            simpa [P, E, lam] using ofHermitianEigenbasis_mul_effect M hM outcome
          have hright : (E * X * E) * M = lam • (E * X * E) := by
            calc
              (E * X * E) * M = E * X * (E * M) := by noncomm_ring
              _ = E * X * (lam • E) := by rw [hEM]
              _ = lam • (E * X * E) := by
                    rw [Matrix.mul_smul]
          have hleft : M * (E * X * E) = lam • (E * X * E) := by
            calc
              M * (E * X * E) = (M * E) * X * E := by noncomm_ring
              _ = (lam • E) * X * E := by rw [hME]
              _ = lam • (E * X * E) := by
                    rw [Matrix.smul_mul, Matrix.smul_mul]
          change (E * X * E) * M = M * (E * X * E)
          rw [hright, hleft]
    _ = M * ∑ outcome, P.effects outcome * X * P.effects outcome := by
          exact (Matrix.mul_sum Finset.univ
            (fun outcome => P.effects outcome * X * P.effects outcome) M).symm

/-- Spectral pinching of a state in its own eigenbasis fixes the state. -/
theorem ofHermitianEigenbasis_pinchingChannel_applyState_self (ρ : State a) :
    (ofHermitianEigenbasis ρ.matrix ρ.pos.isHermitian).pinchingChannel.applyState ρ = ρ := by
  apply State.ext
  exact ofHermitianEigenbasis_pinchingMap_self ρ.matrix ρ.pos.isHermitian

/-- State-level form of spectral pinching diagonalization: in the eigenbasis of
the reference state, applying the reference spectral pinching channel keeps
only diagonal entries of the input state. -/
theorem ofHermitianEigenbasis_pinchingChannel_applyState_eigenbasis
    (ρ σ : State a) :
    star (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
        ((ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel.applyState ρ).matrix *
        (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a) =
      Matrix.diagonal
        (fun i =>
          (star (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a) * ρ.matrix *
            (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a)) i i) := by
  simpa using
    ofHermitianEigenbasis_pinchingMap_eigenbasis σ.matrix σ.pos.isHermitian ρ.matrix

/-- The diagonal distribution of a state in a reference state's eigenbasis. -/
def eigenbasisDiagonalProb (ρ σ : State a) : a → ℝ≥0 :=
  fun i =>
    ⟨((star (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a) * ρ.matrix *
        (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a)) i i).re,
      by
        let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
        have hstar : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
          rw [← Matrix.star_eq_conjTranspose, star_star]
        have hpsd :
            (star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)).PosSemidef := by
          simpa [hstar] using ρ.pos.mul_mul_conjTranspose_same (star (U : CMatrix a))
        exact posSemidef_diagonal_re_nonneg hpsd i⟩

/-- The eigenbasis diagonal distribution of a state sums to one. -/
theorem eigenbasisDiagonalProb_sum (ρ σ : State a) :
    ∑ i, eigenbasisDiagonalProb ρ σ i = 1 := by
  classical
  let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
  let Y : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  have hUU : (U : CMatrix a) * star (U : CMatrix a) = 1 :=
    Unitary.coe_mul_star_self U
  have htrace : Y.trace = 1 := by
    calc
      Y.trace = ((star (U : CMatrix a) * ρ.matrix) * (U : CMatrix a)).trace := by
        rfl
      _ = ((U : CMatrix a) * (star (U : CMatrix a) * ρ.matrix)).trace := by
        rw [Matrix.trace_mul_comm]
      _ = (((U : CMatrix a) * star (U : CMatrix a)) * ρ.matrix).trace := by
        rw [Matrix.mul_assoc]
      _ = (1 * ρ.matrix).trace := by
        rw [hUU]
      _ = 1 := by
        simpa using ρ.trace_eq_one
  apply NNReal.coe_injective
  calc
    ((∑ i, eigenbasisDiagonalProb ρ σ i : ℝ≥0) : ℝ) =
        ∑ i, ((eigenbasisDiagonalProb ρ σ i : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_sum]
    _ = ∑ i, (Y i i).re := by
          refine Finset.sum_congr rfl fun i _ => ?_
          change ((star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)) i i).re =
            (Y i i).re
          rfl
    _ = Y.trace.re := by
          simp [Matrix.trace]
    _ = 1 := by
          rw [htrace]
          norm_num

/-- The eigenvalue distribution of a density state. -/
def stateEigenvalueProb (σ : State a) : a → ℝ≥0 :=
  fun i => ⟨σ.pos.isHermitian.eigenvalues i, σ.pos.eigenvalues_nonneg i⟩

/-- A density state's eigenvalue distribution sums to one. -/
theorem stateEigenvalueProb_sum (σ : State a) :
    ∑ i, stateEigenvalueProb σ i = 1 := by
  have hcomplex : (∑ i, ((σ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 :=
    σ.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans σ.trace_eq_one
  have hreal := congrArg Complex.re hcomplex
  apply NNReal.coe_injective
  calc
    ((∑ i, stateEigenvalueProb σ i : ℝ≥0) : ℝ) =
        ∑ i, ((stateEigenvalueProb σ i : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_sum]
    _ = ∑ i, σ.pos.isHermitian.eigenvalues i := by
          rfl
    _ = 1 := by
          simpa using hreal

/-- Full-rank density states have strictly positive eigenvalue distribution. -/
theorem stateEigenvalueProb_pos_of_posDef (σ : State a) (hσ : σ.matrix.PosDef) :
    ∀ i, 0 < (stateEigenvalueProb σ i : ℝ) := by
  intro i
  exact hσ.eigenvalues_pos i

/-- A density matrix reconstructed from its eigenvalue distribution. -/
theorem state_matrix_eq_unitary_diagonalEigenvalueProb (σ : State a) :
    σ.matrix =
      (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => ((stateEigenvalueProb σ i : ℝ≥0) : ℂ)) *
        star (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a) := by
  let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
  have hdiag :
      Matrix.diagonal (fun i => ((σ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) =
        Matrix.diagonal (fun i => ((stateEigenvalueProb σ i : ℝ≥0) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
  calc
    σ.matrix =
        (U : CMatrix a) *
          Matrix.diagonal (fun i => ((σ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
          simpa [U, Function.comp_def, Unitary.conjStarAlgAut_apply]
            using σ.pos.isHermitian.spectral_theorem
    _ = (U : CMatrix a) *
        Matrix.diagonal (fun i => ((stateEigenvalueProb σ i : ℝ≥0) : ℂ)) *
        star (U : CMatrix a) := by
          rw [hdiag]

/-- The reference spectral pinching of a state is exactly the unitary
reconstruction of its eigenbasis diagonal probability distribution. -/
theorem ofHermitianEigenbasis_pinchingChannel_applyState_matrix_eq_unitary_diagonalProb
    (ρ σ : State a) :
    ((ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel.applyState ρ).matrix =
      (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => ((eigenbasisDiagonalProb ρ σ i : ℝ≥0) : ℂ)) *
        star (σ.pos.isHermitian.eigenvectorUnitary : CMatrix a) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := σ.pos.isHermitian.eigenvectorUnitary
  let Xp : CMatrix a :=
    ((ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel.applyState ρ).matrix
  let Y : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
  let D : CMatrix a := Matrix.diagonal (fun i => ((eigenbasisDiagonalProb ρ σ i : ℝ≥0) : ℂ))
  have hUU : (U : CMatrix a) * star (U : CMatrix a) = 1 :=
    Unitary.coe_mul_star_self U
  have hstar : Matrix.conjTranspose (star (U : CMatrix a)) = (U : CMatrix a) := by
    rw [← Matrix.star_eq_conjTranspose, star_star]
  have hYpsd : Y.PosSemidef := by
    simpa [Y, hstar] using ρ.pos.mul_mul_conjTranspose_same (star (U : CMatrix a))
  have hYdiag :
      Matrix.diagonal (fun i => Y i i) = D := by
    have hreal_fun : (fun i => (((Y i i).re : ℝ) : ℂ)) = fun i => Y i i := by
      simpa [Matrix.diag] using hYpsd.isHermitian.coe_re_diag
    ext i j
    simp only [D]
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      have hreal_i : (((Y i i).re : ℝ) : ℂ) = Y i i :=
        congrFun hreal_fun i
      rw [← hreal_i]
      change (((eigenbasisDiagonalProb ρ σ i : ℝ≥0) : ℝ) : ℂ) = (((Y i i).re : ℝ) : ℂ)
      congr 1
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
  have hdiag :
      star (U : CMatrix a) * Xp * (U : CMatrix a) = D := by
    calc
      star (U : CMatrix a) * Xp * (U : CMatrix a) =
          Matrix.diagonal (fun i => Y i i) := by
            simpa [Xp, Y, U] using
              ofHermitianEigenbasis_pinchingChannel_applyState_eigenbasis ρ σ
      _ = D := hYdiag
  calc
    Xp = ((U : CMatrix a) * star (U : CMatrix a)) * Xp *
          ((U : CMatrix a) * star (U : CMatrix a)) := by
          rw [hUU]
          simp
    _ = (U : CMatrix a) * (star (U : CMatrix a) * Xp * (U : CMatrix a)) *
          star (U : CMatrix a) := by
          noncomm_ring
    _ = (U : CMatrix a) * D * star (U : CMatrix a) := by
          rw [hdiag]

/-- Pinching a state in the spectral projective measurement of a reference
state produces a state commuting with that reference. -/
theorem ofHermitianEigenbasis_pinchingChannel_applyState_commute
    (ρ σ : State a) :
    ((ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel.applyState ρ).matrix *
        σ.matrix =
      σ.matrix *
        ((ofHermitianEigenbasis σ.matrix σ.pos.isHermitian).pinchingChannel.applyState ρ).matrix := by
  simpa using
    ofHermitianEigenbasis_pinchingMap_commute σ.matrix σ.pos.isHermitian ρ.matrix

end ProjectiveMeasurement

end

end QIT
