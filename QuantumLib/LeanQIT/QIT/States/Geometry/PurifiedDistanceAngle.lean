/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Geometry.PurifiedDistance
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Angular geometry of purified distance

This module formalizes the angular-distance route used for the tight triangle
inequality in Tomamichel, `metric.tex:537-573`.
-/

@[expose] public section

namespace QIT

universe u

noncomputable section

namespace PurifiedDistanceAngle

/-- A unit-modulus phase that rotates `z` onto the nonnegative real axis. -/
private def unitPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

private theorem unitPhase_normSq (z : ℂ) : Complex.normSq (unitPhase z) = 1 := by
  by_cases hz : z = 0
  · simp [unitPhase, hz]
  · rw [unitPhase, if_neg hz, Complex.normSq_div,
      Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    field_simp [hn]

private theorem star_unitPhase_mul_self (z : ℂ) :
    star (unitPhase z) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [unitPhase, hz]
  · rw [unitPhase, if_neg hz, star_div₀]
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    field_simp [hn]
    change (starRingEnd ℂ) z * z =
      (starRingEnd ℂ) (‖z‖ : ℂ) * (‖z‖ : ℂ)
    rw [← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.conj_ofReal]
    exact_mod_cast (Complex.norm_mul_self_eq_normSq z).symm

end PurifiedDistanceAngle

namespace PureVector

/-- Multiply a pure vector by a global unit phase. -/
private def phase {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ : PureVector a) (c : ℂ) (hc : Complex.normSq c = 1) : PureVector a where
  amp i := c * Ψ.amp i
  trace_rankOne_eq_one := by
    have hmatrix : rankOneMatrix (fun i => c * Ψ.amp i) =
        (c * star c : ℂ) • rankOneMatrix Ψ.amp := by
      ext i j
      simp [rankOneMatrix_apply, mul_assoc, mul_left_comm]
    rw [hmatrix, Matrix.trace_smul, Ψ.trace_rankOne_eq_one]
    have hunit : c * star c = 1 := by
      have hcC : (Complex.normSq c : ℂ) = 1 := by exact_mod_cast hc
      simpa [Complex.normSq_eq_conj_mul_self, mul_comm] using hcC
    change (c * star c) * 1 = 1
    rw [hunit, one_mul]

@[simp]
private theorem phase_amp {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ : PureVector a) (c : ℂ) (hc : Complex.normSq c = 1) (i : a) :
    (phase Ψ c hc).amp i = c * Ψ.amp i :=
  rfl

private theorem phase_state {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ : PureVector a) (c : ℂ) (hc : Complex.normSq c = 1) :
    (phase Ψ c hc).state = Ψ.state := by
  apply State.ext
  ext i j
  have hunit : c * star c = 1 := by
    have hcC : (Complex.normSq c : ℂ) = 1 := by exact_mod_cast hc
    rw [Complex.normSq_eq_conj_mul_self] at hcC
    simpa [mul_comm] using hcC
  change c * Ψ.amp i * star (c * Ψ.amp j) = Ψ.amp i * star (Ψ.amp j)
  rw [star_mul]
  calc
    c * Ψ.amp i * (star (Ψ.amp j) * star c) =
        (c * star c) * (Ψ.amp i * star (Ψ.amp j)) := by ring
    _ = Ψ.amp i * star (Ψ.amp j) := by rw [hunit, one_mul]

private theorem phase_purifies {r a : Type u}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
    {Ψ : PureVector (Prod r a)} {ρ : State a}
    (hΨ : Ψ.Purifies ρ) (c : ℂ) (hc : Complex.normSq c = 1) :
    (phase Ψ c hc).Purifies ρ := by
  rw [PureVector.purifies_iff, phase_state]
  exact hΨ

private theorem overlap_phase_left {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) (c : ℂ) (hc : Complex.normSq c = 1) :
    (phase Ψ c hc).overlap Φ = star c * Ψ.overlap Φ := by
  simp [PureVector.overlap, phase_amp, Finset.mul_sum, mul_assoc]

private theorem overlap_phase_right {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) (c : ℂ) (hc : Complex.normSq c = 1) :
    Ψ.overlap (phase Φ c hc) = c * Ψ.overlap Φ := by
  simp [PureVector.overlap, phase_amp, Finset.mul_sum, mul_left_comm]

/-- The projective angle between two pure vectors. -/
noncomputable def projectiveAngle {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) : ℝ :=
  Real.arccos ‖Ψ.overlap Φ‖

private def ampVector {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ : PureVector a) : EuclideanSpace ℂ a :=
  WithLp.toLp 2 Ψ.amp

private theorem inner_ampVector {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) :
    inner ℂ (ampVector Ψ) (ampVector Φ) = Ψ.overlap Φ := by
  rw [ampVector, ampVector, EuclideanSpace.inner_toLp_toLp]
  simp [PureVector.overlap, dotProduct, mul_comm]

private theorem norm_ampVector {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ : PureVector a) : ‖ampVector Ψ‖ = 1 := by
  have hinner : inner ℂ (ampVector Ψ) (ampVector Ψ) = 1 := by
    rw [inner_ampVector]
    simpa [PureVector.overlap, rankOneMatrix_trace, dotProduct, mul_comm] using
      Ψ.trace_rankOne_eq_one
  have hsqC : ((‖ampVector Ψ‖ : ℂ) ^ 2) = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ampVector Ψ)
    rw [hinner] at h
    exact h.symm
  have hsq : ‖ampVector Ψ‖ ^ 2 = (1 : ℝ) := by exact_mod_cast hsqC
  nlinarith [norm_nonneg (ampVector Ψ)]

private theorem overlap_norm_le_one {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) : ‖Ψ.overlap Φ‖ ≤ 1 := by
  have hsq : Ψ.overlapSq Φ ≤ 1 :=
    (PureVector.overlapSq_le_state_squaredFidelity Ψ Φ).trans
      (State.squaredFidelity_le_one_of_uhlmann Ψ.state Φ.state)
  rw [PureVector.overlapSq_eq_normSq, Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (Ψ.overlap Φ)]

theorem sin_projectiveAngle {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) :
    Real.sin (projectiveAngle Ψ Φ) = Real.sqrt (1 - Ψ.overlapSq Φ) := by
  rw [projectiveAngle, Real.sin_arccos]
  rw [PureVector.overlapSq_eq_normSq, Complex.normSq_eq_norm_sq]

theorem projectiveAngle_nonneg {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) : 0 ≤ projectiveAngle Ψ Φ :=
  Real.arccos_nonneg _

theorem projectiveAngle_le_pi_div_two {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) : projectiveAngle Ψ Φ ≤ Real.pi / 2 := by
  rw [projectiveAngle, Real.arccos_le_pi_div_two]
  exact norm_nonneg _

/-- Projective angle satisfies the triangle inequality.  The proof phase-aligns
the two adjacent overlaps and then applies the real inner-product angle
triangle inequality. -/
theorem projectiveAngle_triangle {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ Ω : PureVector a) :
    projectiveAngle Ψ Ω ≤ projectiveAngle Ψ Φ + projectiveAngle Φ Ω := by
  by_cases hΨΦ : Ψ.overlap Φ = 0
  · have hright : projectiveAngle Ψ Φ = Real.pi / 2 := by
      simp [projectiveAngle, hΨΦ, Real.arccos_zero]
    rw [hright]
    exact (projectiveAngle_le_pi_div_two Ψ Ω).trans
      (le_add_of_nonneg_right (projectiveAngle_nonneg Φ Ω))
  by_cases hΦΩ : Φ.overlap Ω = 0
  · have hright : projectiveAngle Φ Ω = Real.pi / 2 := by
      simp [projectiveAngle, hΦΩ, Real.arccos_zero]
    rw [hright]
    exact (projectiveAngle_le_pi_div_two Ψ Ω).trans
      (le_add_of_nonneg_left (projectiveAngle_nonneg Ψ Φ))
  let c : ℂ := PurifiedDistanceAngle.unitPhase (Ψ.overlap Φ)
  let d : ℂ := star (PurifiedDistanceAngle.unitPhase (Φ.overlap Ω))
  have hc : Complex.normSq c = 1 :=
    PurifiedDistanceAngle.unitPhase_normSq _
  have hd : Complex.normSq d = 1 := by
    dsimp [d]
    let q := PurifiedDistanceAngle.unitPhase (Φ.overlap Ω)
    change Complex.normSq (star q) = 1
    rw [Complex.normSq_apply]
    change q.re * q.re + (-q.im) * (-q.im) = 1
    have hq := PurifiedDistanceAngle.unitPhase_normSq (Φ.overlap Ω)
    change Complex.normSq q = 1 at hq
    rw [Complex.normSq_apply] at hq
    nlinarith
  let Ψ' : PureVector a := phase Ψ c hc
  let Ω' : PureVector a := phase Ω d hd
  let x : EuclideanSpace ℂ a := ampVector Ψ'
  let y : EuclideanSpace ℂ a := ampVector Φ
  let z : EuclideanSpace ℂ a := ampVector Ω'
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ a) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ a)
  have hx : ‖x‖ = 1 := norm_ampVector Ψ'
  have hy : ‖y‖ = 1 := norm_ampVector Φ
  have hz : ‖z‖ = 1 := norm_ampVector Ω'
  have hxy_inner : inner ℝ x y = ‖Ψ.overlap Φ‖ := by
    change (inner ℂ x y).re = _
    rw [inner_ampVector]
    rw [show Ψ'.overlap Φ = star c * Ψ.overlap Φ by
      exact overlap_phase_left Ψ Φ c hc]
    dsimp [c]
    have hphase :=
      PurifiedDistanceAngle.star_unitPhase_mul_self (Ψ.overlap Φ)
    exact congrArg Complex.re hphase
  have hyz_inner : inner ℝ y z = ‖Φ.overlap Ω‖ := by
    change (inner ℂ y z).re = _
    rw [inner_ampVector]
    rw [show Φ.overlap Ω' = d * Φ.overlap Ω by
      exact overlap_phase_right Φ Ω d hd]
    dsimp [d]
    have hphase :=
      PurifiedDistanceAngle.star_unitPhase_mul_self (Φ.overlap Ω)
    exact congrArg Complex.re hphase
  have hxz_inner : inner ℝ x z ≤ ‖Ψ.overlap Ω‖ := by
    change (inner ℂ x z).re ≤ _
    rw [inner_ampVector]
    calc
      (Ψ'.overlap Ω').re ≤ ‖Ψ'.overlap Ω'‖ := Complex.re_le_norm _
      _ = ‖Ψ.overlap Ω‖ := by
        rw [show Ψ'.overlap Ω' = d * (star c * Ψ.overlap Ω) by
          rw [overlap_phase_right, overlap_phase_left]]
        rw [norm_mul, norm_mul]
        have hcnorm : ‖c‖ = 1 := by
          have hsq : ‖c‖ ^ 2 = (1 : ℝ) := by
            rw [← Complex.normSq_eq_norm_sq, hc]
          nlinarith [norm_nonneg c]
        have hdnorm : ‖d‖ = 1 := by
          have hsq : ‖d‖ ^ 2 = (1 : ℝ) := by
            rw [← Complex.normSq_eq_norm_sq, hd]
          nlinarith [norm_nonneg d]
        simp [hcnorm, hdnorm]
  have hangle_xz :
      projectiveAngle Ψ Ω ≤ InnerProductGeometry.angle x z := by
    rw [projectiveAngle, InnerProductGeometry.angle, hx, hz, mul_one, div_one]
    exact Real.arccos_le_arccos hxz_inner
  have hangle_xy :
      InnerProductGeometry.angle x y = projectiveAngle Ψ Φ := by
    rw [InnerProductGeometry.angle, hx, hy, mul_one, div_one, hxy_inner,
      projectiveAngle]
  have hangle_yz :
      InnerProductGeometry.angle y z = projectiveAngle Φ Ω := by
    rw [InnerProductGeometry.angle, hy, hz, mul_one, div_one, hyz_inner,
      projectiveAngle]
  calc
    projectiveAngle Ψ Ω ≤ InnerProductGeometry.angle x z := hangle_xz
    _ ≤ InnerProductGeometry.angle x y + InnerProductGeometry.angle y z :=
      InnerProductGeometry.angle_le_angle_add_angle x y z
    _ = projectiveAngle Ψ Φ + projectiveAngle Φ Ω := by
      rw [hangle_xy, hangle_yz]

end PureVector

namespace State

/-- Two purified-distance bounds expressed as angles compose by addition.
This is Eq. `pd-triangle-eps` in Tomamichel, `metric.tex:567-573`. -/
theorem purifiedDistance_le_sin_add {a : Type u} [Fintype a] [DecidableEq a]
    (ρ σ τ : State a) {φ θ : ℝ}
    (hφ : 0 ≤ φ) (hθ : 0 ≤ θ) (hsum : φ + θ < Real.pi / 2)
    (hρσ : ρ.purifiedDistance σ ≤ Real.sin φ)
    (hστ : σ.purifiedDistance τ ≤ Real.sin θ) :
    ρ.purifiedDistance τ ≤ Real.sin (φ + θ) := by
  let Ψ : PureVector (Prod a a) := ρ.canonicalPurification
  have hΨ : Ψ.Purifies ρ := by
    simpa [Ψ] using ρ.canonicalPurification_purifies
  obtain ⟨Φ, hΦ, hρσeq⟩ :=
    State.exists_purification_purifiedDistance_eq_sqrt_one_sub_overlapSq
      (ρ := ρ) (σ := σ) hΨ (le_refl (Fintype.card a))
  obtain ⟨Ω, hΩ, hστeq⟩ :=
    State.exists_purification_purifiedDistance_eq_sqrt_one_sub_overlapSq
      (ρ := σ) (σ := τ) hΦ (le_refl (Fintype.card a))
  have hφ_lt : φ < Real.pi / 2 := by linarith
  have hθ_lt : θ < Real.pi / 2 := by linarith
  have hangle_ΨΦ : PureVector.projectiveAngle Ψ Φ ≤ φ := by
    have hsin : Real.sin (PureVector.projectiveAngle Ψ Φ) ≤ Real.sin φ := by
      rw [PureVector.sin_projectiveAngle, ← hρσeq]
      exact hρσ
    exact (Real.strictMonoOn_sin.le_iff_le
      ⟨by linarith [PureVector.projectiveAngle_nonneg Ψ Φ],
        PureVector.projectiveAngle_le_pi_div_two Ψ Φ⟩
      ⟨by linarith, hφ_lt.le⟩).mp hsin
  have hangle_ΦΩ : PureVector.projectiveAngle Φ Ω ≤ θ := by
    have hsin : Real.sin (PureVector.projectiveAngle Φ Ω) ≤ Real.sin θ := by
      rw [PureVector.sin_projectiveAngle, ← hστeq]
      exact hστ
    exact (Real.strictMonoOn_sin.le_iff_le
      ⟨by linarith [PureVector.projectiveAngle_nonneg Φ Ω],
        PureVector.projectiveAngle_le_pi_div_two Φ Ω⟩
      ⟨by linarith, hθ_lt.le⟩).mp hsin
  have hangle : PureVector.projectiveAngle Ψ Ω ≤ φ + θ :=
    (PureVector.projectiveAngle_triangle Ψ Φ Ω).trans
      (add_le_add hangle_ΨΦ hangle_ΦΩ)
  have hsin_angle :
      Real.sin (PureVector.projectiveAngle Ψ Ω) ≤ Real.sin (φ + θ) :=
    (Real.strictMonoOn_sin.le_iff_le
      ⟨by linarith [PureVector.projectiveAngle_nonneg Ψ Ω],
        PureVector.projectiveAngle_le_pi_div_two Ψ Ω⟩
      ⟨by linarith, hsum.le⟩).mpr hangle
  calc
    ρ.purifiedDistance τ ≤ Real.sqrt (1 - Ψ.overlapSq Ω) :=
      State.purifiedDistance_le_sqrt_one_sub_overlapSq_of_purifies hΨ hΩ
    _ = Real.sin (PureVector.projectiveAngle Ψ Ω) :=
      (PureVector.sin_projectiveAngle Ψ Ω).symm
    _ ≤ Real.sin (φ + θ) := hsin_angle

end State

namespace SubnormalizedState

/-- Subnormalized version of `State.purifiedDistance_le_sin_add`, obtained
through normalized hat extensions. -/
theorem purifiedDistance_le_sin_add {a : Type u} [Fintype a] [DecidableEq a]
    (ρ σ τ : SubnormalizedState a) {φ θ : ℝ}
    (hφ : 0 ≤ φ) (hθ : 0 ≤ θ) (hsum : φ + θ < Real.pi / 2)
    (hρσ : ρ.purifiedDistance σ ≤ Real.sin φ)
    (hστ : σ.purifiedDistance τ ≤ Real.sin θ) :
    ρ.purifiedDistance τ ≤ Real.sin (φ + θ) := by
  let ρhat : State (Sum PUnit.{u + 1} a) := ρ.hatExtension
  let σhat : State (Sum PUnit.{u + 1} a) := σ.hatExtension
  let τhat : State (Sum PUnit.{u + 1} a) := τ.hatExtension
  have hρσhat : ρhat.purifiedDistance σhat ≤ Real.sin φ := by
    have heq : ρ.purifiedDistance σ = ρhat.purifiedDistance σhat := by
      simpa [ρhat, σhat] using
        (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension ρ σ)
    rw [← heq]
    exact hρσ
  have hστhat : σhat.purifiedDistance τhat ≤ Real.sin θ := by
    have heq : σ.purifiedDistance τ = σhat.purifiedDistance τhat := by
      simpa [σhat, τhat] using
        (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension σ τ)
    rw [← heq]
    exact hστ
  have h := State.purifiedDistance_le_sin_add
    ρhat σhat τhat hφ hθ hsum hρσhat hστhat
  have heq : ρ.purifiedDistance τ = ρhat.purifiedDistance τhat := by
    simpa [ρhat, τhat] using
      (SubnormalizedState.purifiedDistance_eq_purifiedDistance_hatExtension ρ τ)
  rw [heq]
  exact h

end SubnormalizedState

end

end QIT
