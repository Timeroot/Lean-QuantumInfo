/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.SDP.HermitianPSDTraceDuality
public import QIT.Information.Renyi.Renyi
public import QIT.Information.Renyi.ConditionalRenyi
public import QIT.Information.Renyi.RenyiDPIStatement
public import QIT.Measurements.Map
public import QIT.Measurements.Projective
public import QIT.States.Purification.Uhlmann
public import QIT.States.Schatten
public import QIT.States.MaximallyMixed
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Sandwiched Renyi DPI domain support

Finite/PSD domain APIs, interpolation kernels, MatrixMap support, classical
finite-channel power inequalities, and dual-parameter algebra.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

section ComplexInterpolation

/-- Unit-bound form of the Hadamard three-lines theorem.

This is the scalar analytic kernel needed by the sandwiched Renyi interpolation
route: once a trace-pairing family is built on the strip and bounded by `1` on
both boundary lines, its interior value is bounded by `1`. -/
theorem complex_three_lines_unit_bound
    {f : ℂ → ℂ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f z‖ ≤ 1)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖f z‖ ≤ 1) :
    ‖f (θ : ℂ)‖ ≤ 1 := by
  have hz : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, hθ0, hθ1]
  have h :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := f) (z := (θ : ℂ)) (a := (1 : ℝ)) (b := (1 : ℝ))
      (l := (0 : ℝ)) (u := (1 : ℝ))
      (by norm_num) hz hd hB hleft hright
  simpa using h

/-- Constant-bound form of the Hadamard three-lines theorem.

This is the version used after normalizing a trace-pairing analytic family by
the candidate Schatten bound. The constant is assumed positive; zero-norm test
operators are handled separately by the surrounding Schatten variational
interface. -/
theorem complex_three_lines_const_bound
    {f : ℂ → ℂ} {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hC : 0 < C)
    (hd : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f z‖ ≤ C)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖f z‖ ≤ C) :
    ‖f (θ : ℂ)‖ ≤ C := by
  have hz : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, hθ0, hθ1]
  have h :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := f) (z := (θ : ℂ)) (a := C) (b := C)
      (l := (0 : ℝ)) (u := (1 : ℝ))
      (by norm_num) hz hd hB hleft hright
  have hmain : ‖f (θ : ℂ)‖ ≤ C ^ (1 - θ) * C ^ θ := by
    simpa using h
  have hrhs : C ^ (1 - θ) * C ^ θ = C := by
    calc
      C ^ (1 - θ) * C ^ θ = C ^ ((1 - θ) + θ) := by
        rw [← Real.rpow_add hC]
      _ = C ^ (1 : ℝ) := by ring_nf
      _ = C := by rw [Real.rpow_one]
  exact hmain.trans_eq hrhs

/-- Unit-bound three-lines theorem for the local Beigi strip convention.

The current rotated Kraus family is written as `L_z = τ^z K σ^{-z}`.  Its
`p = 1` boundary is `Re z = 0`, while its `p = ∞` boundary is
`Re z = -1/2`.  This lemma transfers the standard `0 ≤ Re w ≤ 1` strip by
`z = -w/2`, so the interpolation point is `z = -θ/2`. -/
theorem complex_three_lines_unit_bound_neg_half_strip
    {f : ℂ → ℂ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd : DiffContOnCl ℂ (fun w : ℂ => f (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ (fun w : ℂ => f (-(w / 2)))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f z‖ ≤ 1)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ), ‖f z‖ ≤ 1) :
    ‖f (-((θ : ℂ) / 2))‖ ≤ 1 := by
  have hleft' : ∀ w ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f (-(w / 2))‖ ≤ 1 := by
    intro w hw
    apply hleft
    simpa [Complex.div_re, hw]
  have hright' : ∀ w ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖f (-(w / 2))‖ ≤ 1 := by
    intro w hw
    apply hright
    simp at hw
    norm_num [Complex.div_re, hw]
  have h := complex_three_lines_unit_bound (f := fun w : ℂ => f (-(w / 2)))
    hθ0 hθ1 hd hB hleft' hright'
  simpa using h

/-- Constant-bound three-lines theorem for the local Beigi strip convention.

This is the non-normalized companion to
`complex_three_lines_unit_bound_neg_half_strip`, used after scaling the scalar
trace-pairing family by its candidate Schatten bound. -/
theorem complex_three_lines_const_bound_neg_half_strip
    {f : ℂ → ℂ} {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hC : 0 < C)
    (hd : DiffContOnCl ℂ (fun w : ℂ => f (-(w / 2)))
      (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ (fun w : ℂ => f (-(w / 2)))) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f z‖ ≤ C)
    (hright : ∀ z ∈ Complex.re ⁻¹' ({-(1 / 2 : ℝ)} : Set ℝ), ‖f z‖ ≤ C) :
    ‖f (-((θ : ℂ) / 2))‖ ≤ C := by
  have hleft' : ∀ w ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖f (-(w / 2))‖ ≤ C := by
    intro w hw
    apply hleft
    simpa [Complex.div_re, hw]
  have hright' : ∀ w ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖f (-(w / 2))‖ ≤ C := by
    intro w hw
    apply hright
    simp at hw
    norm_num [Complex.div_re, hw]
  have h := complex_three_lines_const_bound (f := fun w : ℂ => f (-(w / 2)))
    hθ0 hθ1 hC hd hB hleft' hright'
  simpa using h

/-- For Holder-conjugate exponents, the interpolation parameter `θ = 1 / q`
lies in the unit interval. -/
theorem holderConjugate_inv_right_mem_unit_interval
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    0 ≤ 1 / q ∧ 1 / q ≤ 1 := by
  constructor
  · exact one_div_nonneg.mpr (le_of_lt hpq.symm.pos)
  · rw [one_div]
    exact inv_le_one_of_one_le₀ (le_of_lt hpq.symm.lt)

end ComplexInterpolation

/-- Dual Renyi parameter for the low-`α` purification/conditional-duality route.

For `1 / 2 < α < 1`, this parameter satisfies `1 < β` and
`1 / α + 1 / β = 2`, so it is the algebraic bridge from the subunit
sandwiched-Renyi range to the already-proved `β > 1` endpoint. -/
def renyiDualParameter (α : ℝ) : ℝ :=
  α / (2 * α - 1)

/-- The denominator in the dual Renyi parameter is positive for
`1 / 2 < α`. -/
theorem renyiDualParameter_den_pos {α : ℝ} (hα_half : 1 / 2 < α) :
    0 < 2 * α - 1 := by
  linarith

/-- The low-`α` dual parameter is positive. -/
theorem renyiDualParameter_pos {α : ℝ} (hα_half : 1 / 2 < α) :
    0 < renyiDualParameter α := by
  have hα_pos : 0 < α := by linarith
  have hden : 0 < 2 * α - 1 := renyiDualParameter_den_pos hα_half
  exact div_pos hα_pos hden

/-- The low-`α` dual parameter is nonzero. -/
theorem renyiDualParameter_ne_zero {α : ℝ} (hα_half : 1 / 2 < α) :
    renyiDualParameter α ≠ 0 :=
  ne_of_gt (renyiDualParameter_pos hα_half)

/-- The low-`α` dual parameter lies in the already-proved `> 1` range. -/
theorem renyiDualParameter_gt_one {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    1 < renyiDualParameter α := by
  have hden : 0 < 2 * α - 1 := renyiDualParameter_den_pos hα_half
  rw [renyiDualParameter]
  rw [lt_div_iff₀ hden]
  linarith

/-- The low-`α` dual parameter is in the conditional-Renyi admissible range. -/
theorem renyiDualParameter_half_le {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    1 / 2 ≤ renyiDualParameter α := by
  linarith [renyiDualParameter_gt_one hα_half hα_lt_one]

/-- The low-`α` dual parameter is not the singular value `1`. -/
theorem renyiDualParameter_ne_one {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    renyiDualParameter α ≠ 1 :=
  ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)

/-- The source duality relation `1 / α + 1 / β = 2` for
`β = α / (2α - 1)`. -/
theorem renyiDualParameter_inv_add_inv_eq_two {α : ℝ}
    (hα_ne_zero : α ≠ 0) :
    1 / α + 1 / renyiDualParameter α = 2 := by
  unfold renyiDualParameter
  field_simp [hα_ne_zero]
  ring

/-- The source duality relation specialized to `1 / 2 < α < 1`. -/
theorem renyiDualParameter_inv_add_inv_eq_two_of_half_lt {α : ℝ}
    (hα_half : 1 / 2 < α) (_hα_lt_one : α < 1) :
    1 / α + 1 / renyiDualParameter α = 2 := by
  have hα_pos : 0 < α := by linarith
  exact renyiDualParameter_inv_add_inv_eq_two (ne_of_gt hα_pos)

/-- Above `1`, the same algebraic dual parameter lies back in the subunit
range. This is the reverse direction needed when symmetry of the conditional
Renyi duality statement swaps the two exponents. -/
theorem renyiDualParameter_half_lt_of_one_lt {β : ℝ} (hβ_gt_one : 1 < β) :
    1 / 2 < renyiDualParameter β := by
  have hden : 0 < 2 * β - 1 := by linarith
  rw [renyiDualParameter]
  rw [lt_div_iff₀ hden]
  linarith

/-- Above `1`, the same algebraic dual parameter is strictly below `1`. -/
theorem renyiDualParameter_lt_one_of_one_lt {β : ℝ} (hβ_gt_one : 1 < β) :
    renyiDualParameter β < 1 := by
  have hden : 0 < 2 * β - 1 := by linarith
  rw [renyiDualParameter]
  rw [div_lt_one hden]
  linarith

/-- The denominator of the dual parameter after one dualization is the inverse
of the original denominator. -/
theorem renyiDualParameter_den_eq_inv_den {α : ℝ}
    (hden : 2 * α - 1 ≠ 0) :
    2 * renyiDualParameter α - 1 = 1 / (2 * α - 1) := by
  unfold renyiDualParameter
  field_simp [hden]
  ring

/-- The Renyi dual-parameter map is an involution away from its singular
denominator. -/
theorem renyiDualParameter_involutive {α : ℝ}
    (_hα_ne_zero : α ≠ 0) (hden : 2 * α - 1 ≠ 0) :
    renyiDualParameter (renyiDualParameter α) = α := by
  unfold renyiDualParameter
  have hden' : 2 * (α / (2 * α - 1)) - 1 = 1 / (2 * α - 1) := by
    field_simp [hden]
    ring_nf
  rw [hden']
  rw [div_eq_mul_inv]
  rw [one_div, inv_inv]
  rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hden, mul_one]

/-- The involution law specialized to the low-`α` source range. -/
theorem renyiDualParameter_involutive_of_half_lt_lt_one {α : ℝ}
    (hα_half : 1 / 2 < α) (_hα_lt_one : α < 1) :
    renyiDualParameter (renyiDualParameter α) = α := by
  have hα_pos : 0 < α := by linarith
  have hden_pos : 0 < 2 * α - 1 := renyiDualParameter_den_pos hα_half
  exact renyiDualParameter_involutive (ne_of_gt hα_pos) (ne_of_gt hden_pos)

/-- The involution law specialized to the `> 1` endpoint range. -/
theorem renyiDualParameter_involutive_of_one_lt {β : ℝ}
    (hβ_gt_one : 1 < β) :
    renyiDualParameter (renyiDualParameter β) = β := by
  have hβ_pos : 0 < β := lt_trans zero_lt_one hβ_gt_one
  have hden_pos : 0 < 2 * β - 1 := by linarith
  exact renyiDualParameter_involutive (ne_of_gt hβ_pos) (ne_of_gt hden_pos)

/-- Packaged admissibility facts for the dual parameter of a strict subunit
Renyi exponent. -/
theorem renyiDualParameter_low_admissible {α : ℝ}
    (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    1 / 2 ≤ renyiDualParameter α ∧
      renyiDualParameter α ≠ 1 ∧
        1 < renyiDualParameter α ∧
          1 / α + 1 / renyiDualParameter α = 2 := by
  exact ⟨renyiDualParameter_half_le hα_half hα_lt_one,
    renyiDualParameter_ne_one hα_half hα_lt_one,
    renyiDualParameter_gt_one hα_half hα_lt_one,
    renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one⟩

/-- Packaged admissibility facts when starting from the already-proved
`β > 1` endpoint range and dualizing back to a subunit exponent. -/
theorem renyiDualParameter_high_admissible {β : ℝ}
    (hβ_gt_one : 1 < β) :
    1 / 2 < renyiDualParameter β ∧
      renyiDualParameter β < 1 ∧
        1 / β + 1 / renyiDualParameter β = 2 := by
  have hβ_pos : 0 < β := lt_trans zero_lt_one hβ_gt_one
  exact ⟨renyiDualParameter_half_lt_of_one_lt hβ_gt_one,
    renyiDualParameter_lt_one_of_one_lt hβ_gt_one,
    renyiDualParameter_inv_add_inv_eq_two (ne_of_gt hβ_pos)⟩

namespace MatrixMap

section L2OperatorEndpoint

open scoped Matrix.Norms.L2Operator

local instance cMatrixNonUnitalCStarAlgebraForEndpoint (n : Type*) [Fintype n]
    [DecidableEq n] : NonUnitalCStarAlgebra (Matrix n n ℂ) := ⟨⟩

local instance cMatrixCStarAlgebraForEndpoint (n : Type*) [Fintype n]
    [DecidableEq n] : CStarAlgebra (Matrix n n ℂ) := ⟨⟩

/-- The L2-operator norm of the finite matrix identity is at most one.

The nonempty case has equality, but the inequality is the endpoint fact that is
valid without adding a `Nonempty` assumption on the finite index type. -/
theorem cMatrix_l2OperatorNorm_one_le :
    ‖(1 : CMatrix a)‖ ≤ (1 : ℝ) := by
  rw [Matrix.cstar_norm_def]
  simpa using
    (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := EuclideanSpace ℂ a))

/-- Matrix unit-ball criterion for the L2 operator norm.

This is the finite-dimensional C⋆-algebra step behind the `p = ∞` endpoint:
`Xᴴ X ≤ I` implies `‖X‖∞ ≤ 1`. -/
theorem cMatrix_l2OperatorNorm_le_one_of_conjTranspose_mul_self_le_one
    (X : CMatrix a) (hX : Matrix.conjTranspose X * X ≤ 1) :
    ‖X‖ ≤ (1 : ℝ) := by
  have hpos : 0 ≤ Matrix.conjTranspose X * X := by
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self X)
  have hnorm_sq_le_norm_one :
      ‖Matrix.conjTranspose X * X‖ ≤ ‖(1 : CMatrix a)‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos hX
  have hnorm_one_le : ‖(1 : CMatrix a)‖ ≤ (1 : ℝ) :=
    cMatrix_l2OperatorNorm_one_le
  have hnorm_sq_le_one : ‖Matrix.conjTranspose X * X‖ ≤ (1 : ℝ) :=
    hnorm_sq_le_norm_one.trans hnorm_one_le
  have hnorm_eq :
      ‖Matrix.conjTranspose X * X‖ = ‖X‖ * ‖X‖ := by
    simpa [Matrix.star_eq_conjTranspose] using
      (CStarRing.norm_star_mul_self (x := X))
  have hmul : ‖X‖ * ‖X‖ ≤ (1 : ℝ) := by
    rwa [hnorm_eq] at hnorm_sq_le_one
  have hsq : ‖X‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    simpa [pow_two] using hmul
  exact (sq_le_sq₀ (norm_nonneg X) zero_le_one).1 hsq

/-- Converse unit-ball criterion for the finite-dimensional L2 operator norm:
`‖X‖∞ ≤ 1` implies `Xᴴ X ≤ I`.

This lets Beigi endpoint contractions proved as operator-norm estimates feed
the trace-norm variational API, which represents test contractions by the
matrix-order condition `XᴴX ≤ I`. -/
theorem cMatrix_conjTranspose_mul_self_le_one_of_l2OperatorNorm_le_one
    (X : CMatrix a) (hX : ‖X‖ ≤ (1 : ℝ)) :
    Matrix.conjTranspose X * X ≤ 1 := by
  have hpos : 0 ≤ Matrix.conjTranspose X * X := by
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self X)
  have hnorm_eq :
      ‖Matrix.conjTranspose X * X‖ = ‖X‖ * ‖X‖ := by
    simpa [Matrix.star_eq_conjTranspose] using
      (CStarRing.norm_star_mul_self (x := X))
  have hnorm_le : ‖Matrix.conjTranspose X * X‖ ≤ (1 : ℝ) := by
    rw [hnorm_eq]
    have hmul : ‖X‖ * ‖X‖ ≤ (1 : ℝ) * (1 : ℝ) :=
      mul_le_mul hX hX (norm_nonneg X) zero_le_one
    simpa using hmul
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg
    (Matrix.conjTranspose X * X) hpos).mp hnorm_le

/-- Turning a Schrödinger-picture Kraus family into a Heisenberg adjoint of the
conjugate-transpose family recovers the original Kraus map. -/
theorem krausAdjoint_conjTranspose_family_eq_ofKraus
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) (X : CMatrix a) :
    MatrixMap.krausAdjoint (fun k => Matrix.conjTranspose (K k)) X =
      MatrixMap.ofKraus K X := by
  unfold MatrixMap.krausAdjoint MatrixMap.ofKraus
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.conjTranspose_conjTranspose]

/-- Kadison-Schwarz inequality for a unital Kraus map in Schrödinger picture.

It is obtained by applying the existing Heisenberg-adjoint Kadison-Schwarz
lemma to the conjugate-transpose Kraus family. -/
theorem ofKraus_conjTranspose_mul_self_le_of_unital
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hUnital : MatrixMap.ofKraus K (1 : CMatrix a) = (1 : CMatrix b))
    (X : CMatrix a) :
    Matrix.conjTranspose (MatrixMap.ofKraus K X) * MatrixMap.ofKraus K X ≤
      MatrixMap.ofKraus K (Matrix.conjTranspose X * X) := by
  let L : κ → Matrix a b ℂ := fun k => Matrix.conjTranspose (K k)
  have hLone : MatrixMap.krausAdjoint L (1 : CMatrix a) = (1 : CMatrix b) := by
    simpa [L, krausAdjoint_conjTranspose_family_eq_ofKraus] using hUnital
  have hKS :=
    MatrixMap.krausAdjoint_conjTranspose_mul_self_le_of_krausAdjoint_one
      L hLone X
  simpa [L, krausAdjoint_conjTranspose_family_eq_ofKraus] using hKS

/-- Unit-ball operator-norm contraction for unital finite Kraus maps.

This is the source-specific `p = ∞` endpoint needed by the Beigi interpolation
route: a unital CP Kraus map sends contractions to contractions. -/
theorem opNorm_contract_ofKraus_of_unital_on_unitBall
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hUnital : MatrixMap.ofKraus K (1 : CMatrix a) = (1 : CMatrix b))
    {X : CMatrix a} (hX : Matrix.conjTranspose X * X ≤ 1) :
    ‖MatrixMap.ofKraus K X‖ ≤ (1 : ℝ) := by
  have hKS := ofKraus_conjTranspose_mul_self_le_of_unital K hUnital X
  have hsub_pos : (1 - Matrix.conjTranspose X * X).PosSemidef := by
    simpa [Matrix.le_iff] using hX
  have hmap_sub_pos :
      (MatrixMap.ofKraus K (1 - Matrix.conjTranspose X * X)).PosSemidef :=
    MatrixMap.ofKraus_mapsPositive K (1 - Matrix.conjTranspose X * X) hsub_pos
  have hmap_le_one :
      MatrixMap.ofKraus K (Matrix.conjTranspose X * X) ≤ (1 : CMatrix b) := by
    rw [Matrix.le_iff]
    simpa [map_sub, hUnital] using hmap_sub_pos
  have hY_le_one :
      Matrix.conjTranspose (MatrixMap.ofKraus K X) * MatrixMap.ofKraus K X ≤
        (1 : CMatrix b) :=
    hKS.trans hmap_le_one
  exact cMatrix_l2OperatorNorm_le_one_of_conjTranspose_mul_self_le_one
    (MatrixMap.ofKraus K X) hY_le_one

/-- Squared operator-norm bound from a matrix order bound.

This is the rescaling step that turns a contraction-on-the-unit-ball statement
into an ordinary operator-norm contraction. -/
theorem cMatrix_l2OperatorNorm_sq_le_of_conjTranspose_mul_self_le_smul_one
    (Y : CMatrix b) {r : ℝ} (hr : 0 ≤ r)
    (hY : Matrix.conjTranspose Y * Y ≤ ((r : ℂ) • (1 : CMatrix b))) :
    ‖Y‖ ^ 2 ≤ r := by
  have hpos : 0 ≤ Matrix.conjTranspose Y * Y := by
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self Y)
  have hnorm_le :
      ‖Matrix.conjTranspose Y * Y‖ ≤ ‖((r : ℂ) • (1 : CMatrix b))‖ :=
    CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos hY
  have hone : ‖(1 : CMatrix b)‖ ≤ (1 : ℝ) :=
    cMatrix_l2OperatorNorm_one_le
  have hnorm_rhs : ‖((r : ℂ) • (1 : CMatrix b))‖ ≤ r := by
    calc
      ‖((r : ℂ) • (1 : CMatrix b))‖ =
          ‖(r : ℂ)‖ * ‖(1 : CMatrix b)‖ := by
            rw [norm_smul]
      _ = r * ‖(1 : CMatrix b)‖ := by
            rw [Complex.norm_real, Real.norm_of_nonneg hr]
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hone hr
      _ = r := by ring
  have hnorm_star :
      ‖Matrix.conjTranspose Y * Y‖ = ‖Y‖ * ‖Y‖ := by
    simpa [Matrix.star_eq_conjTranspose] using
      (CStarRing.norm_star_mul_self (x := Y))
  calc
    ‖Y‖ ^ 2 = ‖Matrix.conjTranspose Y * Y‖ := by
        rw [hnorm_star, pow_two]
    _ ≤ ‖((r : ℂ) • (1 : CMatrix b))‖ := hnorm_le
    _ ≤ r := hnorm_rhs

/-- Operator-norm contraction for unital finite Kraus maps.

This is the ordinary `p = ∞` endpoint needed by the Beigi interpolation route;
it upgrades the unit-ball version by applying Kadison-Schwarz to
`XᴴX ≤ ‖X‖² I`. -/
theorem opNorm_contract_ofKraus_of_unital
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hUnital : MatrixMap.ofKraus K (1 : CMatrix a) = (1 : CMatrix b))
    (X : CMatrix a) :
    ‖MatrixMap.ofKraus K X‖ ≤ ‖X‖ := by
  have hKS := ofKraus_conjTranspose_mul_self_le_of_unital K hUnital X
  have hXbound :
      Matrix.conjTranspose X * X ≤ (((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix a)) := by
    have hXboundReal :
        Matrix.conjTranspose X * X ≤ ((‖X‖ ^ 2 : ℝ) • (1 : CMatrix a)) := by
      simpa [Matrix.star_eq_conjTranspose, Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := X))
    have hsmul :
        ((‖X‖ ^ 2 : ℝ) • (1 : CMatrix a)) =
          (((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix a)) := by
      ext i j
      simp [Matrix.smul_apply]
    simpa [hsmul] using hXboundReal
  have hdiff_pos :
      ((((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix a)) -
        Matrix.conjTranspose X * X).PosSemidef := by
    simpa [Matrix.le_iff] using hXbound
  have hmap_diff_pos :
      (MatrixMap.ofKraus K
        ((((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix a)) -
          Matrix.conjTranspose X * X)).PosSemidef :=
    MatrixMap.ofKraus_mapsPositive K _ hdiff_pos
  have hmap_bound :
      MatrixMap.ofKraus K (Matrix.conjTranspose X * X) ≤
        (((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix b)) := by
    rw [Matrix.le_iff]
    simpa [map_sub, map_smul, hUnital] using hmap_diff_pos
  have hY_bound :
      Matrix.conjTranspose (MatrixMap.ofKraus K X) * MatrixMap.ofKraus K X ≤
        (((‖X‖ ^ 2 : ℝ) : ℂ) • (1 : CMatrix b)) :=
    hKS.trans hmap_bound
  have hsq :
      ‖MatrixMap.ofKraus K X‖ ^ 2 ≤ ‖X‖ ^ 2 :=
    cMatrix_l2OperatorNorm_sq_le_of_conjTranspose_mul_self_le_smul_one
      (MatrixMap.ofKraus K X) (sq_nonneg ‖X‖) hY_bound
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

end L2OperatorEndpoint

/-- Right multiplication by a finite-dimensional contraction does not increase
the trace norm.

This is a local helper for the Beigi endpoint estimates: the boundary complex
powers are used only through the contraction condition `KᴴK ≤ I`. -/
theorem traceNorm_mul_contraction_le
    (M K : CMatrix a) (hK : Matrix.conjTranspose K * K ≤ 1) :
    traceNorm (M * K) ≤ traceNorm M := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (M * K)
  rw [← hU]
  let KU : CMatrix a := K * (U : CMatrix a)
  have hKU : Matrix.conjTranspose KU * KU ≤ 1 := by
    have hdiff : (1 - Matrix.conjTranspose K * K).PosSemidef := by
      simpa [Matrix.le_iff] using hK
    have hconj :
        (star (U : CMatrix a) * (1 - Matrix.conjTranspose K * K) *
          (U : CMatrix a)).PosSemidef := by
      exact hdiff.conjTranspose_mul_mul_same (U : CMatrix a)
    have hUstarU :
        Matrix.conjTranspose (U : CMatrix a) * (U : CMatrix a) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Unitary.coe_star_mul_self U : star (U : CMatrix a) * (U : CMatrix a) = 1)
    have heq :
        1 - Matrix.conjTranspose KU * KU =
          star (U : CMatrix a) * (1 - Matrix.conjTranspose K * K) *
            (U : CMatrix a) := by
      calc
        1 - Matrix.conjTranspose KU * KU =
            Matrix.conjTranspose (U : CMatrix a) * (U : CMatrix a) -
              Matrix.conjTranspose KU * KU := by rw [hUstarU]
        _ = star (U : CMatrix a) * (1 - Matrix.conjTranspose K * K) *
            (U : CMatrix a) := by
              simp [KU, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
              noncomm_ring
    rw [Matrix.le_iff]
    rwa [heq]
  have htrace : ((M * K) * (U : CMatrix a)).trace = (M * KU).trace := by
    simp [KU, Matrix.mul_assoc]
  rw [htrace]
  exact traceNorm_variational_contraction_abs_trace_le M KU hKU

/-- Left multiplication by a square isometry does not increase the trace norm.

This companion to `traceNorm_mul_contraction_le` is the exact form needed for
the Beigi boundary reference factors. -/
theorem traceNorm_isometry_mul_le
    (K M : CMatrix a) (hK : Matrix.conjTranspose K * K = 1) :
    traceNorm (K * M) ≤ traceNorm M := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (K * M)
  rw [← hU]
  let UK : CMatrix a := (U : CMatrix a) * K
  have hUK : Matrix.conjTranspose UK * UK ≤ 1 := by
    have hUstarU :
        Matrix.conjTranspose (U : CMatrix a) * (U : CMatrix a) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Unitary.coe_star_mul_self U : star (U : CMatrix a) * (U : CMatrix a) = 1)
    have hUKeq : Matrix.conjTranspose UK * UK = 1 := by
      calc
        Matrix.conjTranspose UK * UK =
            Matrix.conjTranspose K *
              (Matrix.conjTranspose (U : CMatrix a) * (U : CMatrix a)) * K := by
              simp [UK, Matrix.mul_assoc]
        _ = Matrix.conjTranspose K * K := by rw [hUstarU]; simp
        _ = 1 := hK
    rw [hUKeq]
  have htrace : ((K * M) * (U : CMatrix a)).trace = (M * UK).trace := by
    calc
      ((K * M) * (U : CMatrix a)).trace =
          ((U : CMatrix a) * (K * M)).trace := by rw [Matrix.trace_mul_comm]
      _ = (((U : CMatrix a) * K) * M).trace := by simp [Matrix.mul_assoc]
      _ = (M * UK).trace := by
            rw [Matrix.trace_mul_comm]
  rw [htrace]
  exact traceNorm_variational_contraction_abs_trace_le M UK hUK

/-- The product of two finite-dimensional contractions is a contraction. -/
theorem cMatrix_contraction_mul
    (A B : CMatrix a)
    (hA : Matrix.conjTranspose A * A ≤ 1)
    (hB : Matrix.conjTranspose B * B ≤ 1) :
    Matrix.conjTranspose (A * B) * (A * B) ≤ 1 := by
  have hdiffA : (1 - Matrix.conjTranspose A * A).PosSemidef := by
    simpa [Matrix.le_iff] using hA
  have hconj :
      (Matrix.conjTranspose B * (1 - Matrix.conjTranspose A * A) * B).PosSemidef := by
    simpa [Matrix.star_eq_conjTranspose] using
      hdiffA.conjTranspose_mul_mul_same B
  have hle : Matrix.conjTranspose (A * B) * (A * B) ≤
      Matrix.conjTranspose B * B := by
    rw [Matrix.le_iff]
    convert hconj using 1
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    noncomm_ring
  exact hle.trans hB

/-- Two-sided multiplication by left isometry and right contraction does not
increase the trace norm. -/
theorem traceNorm_isometry_mul_contraction_mul_le
    (L M R : CMatrix a)
    (hL : Matrix.conjTranspose L * L = 1)
    (hR : Matrix.conjTranspose R * R ≤ 1) :
    traceNorm (L * M * R) ≤ traceNorm M := by
  exact (traceNorm_mul_contraction_le (L * M) R hR).trans
    (traceNorm_isometry_mul_le L M hL)

/-- Complex scalar multiplication is bounded by the scalar norm in trace norm. -/
theorem traceNorm_complex_smul_le (c : ℂ) (M : CMatrix a) :
    traceNorm (c • M) ≤ ‖c‖ * traceNorm M := by
  classical
  obtain ⟨U, hU⟩ := traceNorm_variational_exists_unitary_abs_trace (c • M)
  rw [← hU]
  have htrace :
      (((c • M) * (U : CMatrix a)).trace) =
        c * ((M * (U : CMatrix a)).trace) := by
    simp [Matrix.trace_smul]
  have habs :
      Complex.abs (c * ((M * (U : CMatrix a)).trace)) =
        ‖c‖ * Complex.abs ((M * (U : CMatrix a)).trace) := by
    simp [Complex.abs]
  calc
    Complex.abs (((c • M) * (U : CMatrix a)).trace) =
        ‖c‖ * Complex.abs ((M * (U : CMatrix a)).trace) := by
          rw [htrace, habs]
    _ ≤ ‖c‖ * traceNorm M :=
        mul_le_mul_of_nonneg_left
          (traceNorm_variational_unitary_abs_trace_le M U) (norm_nonneg c)

/-- Trace pairing with a contraction is bounded by the trace norm of the other
factor. -/
theorem abs_trace_mul_le_of_traceNorm_le_of_contraction
    (Y W : CMatrix a) {C : ℝ}
    (hY : traceNorm Y ≤ C)
    (hW : Matrix.conjTranspose W * W ≤ 1) :
    Complex.abs ((W * Y).trace) ≤ C := by
  have hcycle : (W * Y).trace = (Y * W).trace := by
    rw [Matrix.trace_mul_comm]
  calc
    Complex.abs ((W * Y).trace) = Complex.abs ((Y * W).trace) := by rw [hcycle]
    _ ≤ traceNorm Y := traceNorm_variational_contraction_abs_trace_le Y W hW
    _ ≤ C := hY

/-- If `W / C` is a contraction and `Y` is in the trace-norm unit ball, then
the trace pairing of `W` with `Y` is bounded by `C`. -/
theorem abs_trace_mul_le_of_traceNorm_le_one_of_scaled_contraction
    (Y W : CMatrix a) {C : ℝ} (hCpos : 0 < C)
    (hY : traceNorm Y ≤ 1)
    (hW : Matrix.conjTranspose (((C : ℂ)⁻¹) • W) *
        (((C : ℂ)⁻¹) • W) ≤ 1) :
    Complex.abs ((W * Y).trace) ≤ C := by
  let W' : CMatrix a := ((C : ℂ)⁻¹) • W
  have hW_eq : W = (C : ℂ) • W' := by
    ext i j
    have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hCpos
    simp [W', Matrix.smul_apply, hCne]
  have hpair : Complex.abs ((W' * Y).trace) ≤ 1 :=
    abs_trace_mul_le_of_traceNorm_le_of_contraction Y W' hY (by simpa [W'] using hW)
  have htrace : (W * Y).trace = (C : ℂ) * (W' * Y).trace := by
    rw [hW_eq]
    simp [Matrix.trace_smul]
  have hnormC : ‖(C : ℂ)‖ = C := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hCpos)]
  calc
    Complex.abs ((W * Y).trace) =
        ‖(C : ℂ) * (W' * Y).trace‖ := by rw [htrace]
    _ = C * Complex.abs ((W' * Y).trace) := by
          rw [norm_mul, hnormC]
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpair (le_of_lt hCpos)
    _ = C := by ring

/-- The trace norm of a positive real power is its PSD trace power. -/
theorem traceNorm_rpow_eq_psdTracePower
    {A : CMatrix a} (hA : A.PosSemidef) (p : ℝ) :
    traceNorm (CFC.rpow A p) = psdTracePower A hA p := by
  have hp : (CFC.rpow A p).PosSemidef :=
    cMatrix_rpow_posSemidef (A := A) (s := p) hA
  simpa [psdTracePower] using QIT.traceNorm_posSemidef_eq_trace_re _ hp

/-- The trace norm of a positive-definite complex power depends only on the
real part of the exponent. -/
theorem traceNorm_cMatrixPosDefComplexPower_eq_psdTracePower_re
    {A : CMatrix a} (hA : A.PosDef) (z : ℂ) :
    traceNorm (cMatrixPosDefComplexPower A hA z) =
      psdTracePower A hA.posSemidef z.re := by
  have hsqrt :
      psdSqrt (CFC.rpow A (2 * z.re)) = CFC.rpow A z.re := by
    have hsq :
        CFC.rpow A z.re * CFC.rpow A z.re = CFC.rpow A (2 * z.re) := by
      calc
        CFC.rpow A z.re * CFC.rpow A z.re =
            CFC.rpow A (z.re + z.re) := by
              exact (CFC.rpow_add (a := A) (x := z.re) (y := z.re) hA.isUnit).symm
        _ = CFC.rpow A (2 * z.re) := by ring_nf
    have hpos : (CFC.rpow A z.re).PosSemidef :=
      cMatrix_rpow_posSemidef (A := A) (s := z.re) hA.posSemidef
    simpa [psdSqrt] using
      (CFC.sqrt_unique (a := CFC.rpow A (2 * z.re))
        (b := CFC.rpow A z.re) hsq hpos.nonneg)
  have hgram :
      Matrix.conjTranspose (cMatrixPosDefComplexPower A hA z) *
          cMatrixPosDefComplexPower A hA z =
        CFC.rpow A (2 * z.re) := by
    simpa [Matrix.star_eq_conjTranspose] using
      cMatrixPosDefComplexPower_star_mul_self hA z
  rw [traceNorm, hgram, hsqrt]
  rfl

/-- Trace-norm contraction for trace-preserving Kraus maps.

This is the finite-dimensional `p = 1` endpoint used in Beigi's weighted
Schatten interpolation route. The proof is by trace-norm variational duality:
an output unitary witness is pulled back through the Heisenberg adjoint, and
Kadison-Schwarz for unital Kraus adjoints makes the pulled-back witness a
contraction. -/
theorem traceNorm_contract_ofKraus_of_tracePreserving
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    (X : CMatrix a) :
    traceNorm ((MatrixMap.ofKraus K) X) ≤ traceNorm X := by
  classical
  obtain ⟨U, hU⟩ :=
    traceNorm_variational_exists_unitary_abs_trace ((MatrixMap.ofKraus K) X)
  rw [← hU]
  have hdual := MatrixMap.ofKraus_trace_duality K X (U : CMatrix b)
  rw [hdual]
  refine traceNorm_variational_contraction_abs_trace_le X
    (MatrixMap.krausAdjoint K (U : CMatrix b)) ?_
  have hUstarU :
      Matrix.conjTranspose (U : CMatrix b) * (U : CMatrix b) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self U : star (U : CMatrix b) * (U : CMatrix b) = 1)
  have hKS :=
    MatrixMap.krausAdjoint_conjTranspose_mul_self_le_of_tracePreserving
      K hTP (U : CMatrix b)
  have hone : MatrixMap.krausAdjoint K (1 : CMatrix b) = (1 : CMatrix a) :=
    MatrixMap.krausAdjoint_one_of_tracePreserving K hTP
  simpa [hUstarU, hone] using hKS

end MatrixMap

section ClassicalPower

variable {ι : Type*} [Fintype ι]

/-- Scalar Jensen inequality for nonnegative weighted averages, in the form
used by the classical endpoint of Renyi DPI. -/
theorem real_rpow_weighted_sum_le_sum_weighted_rpow
    {weight value : ι → ℝ} {α : ℝ} (hα : 1 ≤ α)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : ∑ i, weight i = 1)
    (hvalue_nonneg : ∀ i, 0 ≤ value i) :
    (∑ i, weight i * value i) ^ α ≤ ∑ i, weight i * value i ^ α := by
  classical
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), value i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    exact hvalue_nonneg i
  have hjensen :=
    (convexOn_rpow hα).map_sum_le
      (t := (Finset.univ : Finset ι)) (w := weight) (p := value)
      (by intro i _; exact hweight_nonneg i)
      (by simpa using hweight_sum)
      hmem
  simpa [smul_eq_mul] using hjensen

/-- Concave Jensen inequality for nonnegative weighted averages, used for the
`0 ≤ α ≤ 1` classical Renyi DPI endpoint. -/
theorem real_sum_weighted_rpow_le_rpow_weighted_sum
    {weight value : ι → ℝ} {α : ℝ} (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : ∑ i, weight i = 1)
    (hvalue_nonneg : ∀ i, 0 ≤ value i) :
    (∑ i, weight i * value i ^ α) ≤ (∑ i, weight i * value i) ^ α := by
  classical
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), value i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    exact hvalue_nonneg i
  have hjensen :=
    (Real.concaveOn_rpow hα_nonneg hα_le_one).le_map_sum
      (t := (Finset.univ : Finset ι)) (w := weight) (p := value)
      (by intro i _; exact hweight_nonneg i)
      (by simpa using hweight_sum)
      hmem
  simpa [smul_eq_mul] using hjensen

/-- Pointwise scalar log-sum inequality behind the `α ≥ 1` classical Renyi DPI.

For one output letter of a classical stochastic map, `t i` is the transition
weight from input `i`, and the inequality controls the output power term by the
corresponding weighted input power terms. -/
theorem real_classical_renyi_weighted_power_term_le
    {p q t : ι → ℝ} {α : ℝ} (hα : 1 ≤ α)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_pos : ∀ i, 0 < q i)
    (ht_nonneg : ∀ i, 0 ≤ t i)
    (hQ_pos : 0 < ∑ i, q i * t i) :
    (∑ i, p i * t i) ^ α * (∑ i, q i * t i) ^ (1 - α) ≤
      ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
  classical
  let P : ℝ := ∑ i, p i * t i
  let Q : ℝ := ∑ i, q i * t i
  let weight : ι → ℝ := fun i => q i * t i / Q
  let value : ι → ℝ := fun i => p i / q i
  have hQ_ne : Q ≠ 0 := ne_of_gt (by simpa [Q] using hQ_pos)
  have hQ_nonneg : 0 ≤ Q := le_of_lt (by simpa [Q] using hQ_pos)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp_nonneg i) (ht_nonneg i)
  have hweight_nonneg : ∀ i, 0 ≤ weight i := by
    intro i
    exact div_nonneg (mul_nonneg (le_of_lt (hq_pos i)) (ht_nonneg i)) hQ_nonneg
  have hweight_sum : ∑ i, weight i = 1 := by
    calc
      ∑ i, weight i = (∑ i, q i * t i) / Q := by
          simp [weight, Finset.sum_div]
      _ = Q / Q := by rfl
      _ = 1 := div_self hQ_ne
  have hvalue_nonneg : ∀ i, 0 ≤ value i := by
    intro i
    exact div_nonneg (hp_nonneg i) (le_of_lt (hq_pos i))
  have hweighted_eq : ∑ i, weight i * value i = P / Q := by
    calc
      ∑ i, weight i * value i =
          ∑ i, (p i * t i) / Q := by
            apply Finset.sum_congr rfl
            intro i _
            have hqi_ne : q i ≠ 0 := ne_of_gt (hq_pos i)
            dsimp [weight, value]
            field_simp [hqi_ne, hQ_ne]
      _ = (∑ i, p i * t i) / Q := by
            rw [Finset.sum_div]
      _ = P / Q := by rfl
  have hjensen :
      (P / Q) ^ α ≤ ∑ i, weight i * value i ^ α := by
    rw [← hweighted_eq]
    exact real_rpow_weighted_sum_le_sum_weighted_rpow hα hweight_nonneg
      hweight_sum hvalue_nonneg
  have hright_eq :
      Q * (∑ i, weight i * value i ^ α) =
        ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
    calc
      Q * (∑ i, weight i * value i ^ α) =
          ∑ i, Q * (weight i * value i ^ α) := by
            rw [Finset.mul_sum]
      _ = ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
            apply Finset.sum_congr rfl
            intro i _
            have hqi : 0 < q i := hq_pos i
            have hqi_ne : q i ≠ 0 := ne_of_gt hqi
            have hp_i_nonneg : 0 ≤ p i := hp_nonneg i
            have hq_i_nonneg : 0 ≤ q i := le_of_lt hqi
            calc
              Q * (weight i * value i ^ α) =
                  q i * t i * (p i / q i) ^ α := by
                    dsimp [weight, value]
                    field_simp [hQ_ne]
              _ = q i * t i * (p i ^ α / q i ^ α) := by
                    rw [Real.div_rpow hp_i_nonneg hq_i_nonneg]
              _ = t i * p i ^ α * (q i ^ (1 : ℝ) / q i ^ α) := by
                    rw [Real.rpow_one]
                    ring
              _ = t i * p i ^ α * q i ^ (1 - α) := by
                    rw [← Real.rpow_sub hqi 1 α]
  have hleft_eq :
      P ^ α * Q ^ (1 - α) = Q * (P / Q) ^ α := by
    have hP_div_nonneg : 0 ≤ P / Q := div_nonneg hP_nonneg hQ_nonneg
    calc
      P ^ α * Q ^ (1 - α) =
          (Q * (P / Q)) ^ α * Q ^ (1 - α) := by
            rw [mul_div_cancel₀ P hQ_ne]
      _ = (Q ^ α * (P / Q) ^ α) * Q ^ (1 - α) := by
            rw [Real.mul_rpow hQ_nonneg hP_div_nonneg]
      _ = (P / Q) ^ α * (Q ^ α * Q ^ (1 - α)) := by
            ring
      _ = (P / Q) ^ α * Q ^ (α + (1 - α)) := by
            rw [Real.rpow_add (by simpa [Q] using hQ_pos) α (1 - α)]
      _ = (P / Q) ^ α * Q := by
            have hexp : α + (1 - α) = 1 := by ring
            rw [hexp, Real.rpow_one]
      _ = Q * (P / Q) ^ α := by
            ring
  calc
    (∑ i, p i * t i) ^ α * (∑ i, q i * t i) ^ (1 - α) =
        P ^ α * Q ^ (1 - α) := by rfl
    _ = Q * (P / Q) ^ α := hleft_eq
    _ ≤ Q * (∑ i, weight i * value i ^ α) :=
        mul_le_mul_of_nonneg_left hjensen hQ_nonneg
    _ = ∑ i, t i * p i ^ α * q i ^ (1 - α) := hright_eq

/-- Pointwise scalar log-sum inequality in the reverse direction for
`0 ≤ α ≤ 1`, the classical Renyi DPI range with negative logarithmic
prefactor. -/
theorem real_classical_renyi_weighted_power_term_ge
    {p q t : ι → ℝ} {α : ℝ} (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_pos : ∀ i, 0 < q i)
    (ht_nonneg : ∀ i, 0 ≤ t i)
    (hQ_pos : 0 < ∑ i, q i * t i) :
    ∑ i, t i * p i ^ α * q i ^ (1 - α) ≤
      (∑ i, p i * t i) ^ α * (∑ i, q i * t i) ^ (1 - α) := by
  classical
  let P : ℝ := ∑ i, p i * t i
  let Q : ℝ := ∑ i, q i * t i
  let weight : ι → ℝ := fun i => q i * t i / Q
  let value : ι → ℝ := fun i => p i / q i
  have hQ_ne : Q ≠ 0 := ne_of_gt (by simpa [Q] using hQ_pos)
  have hQ_nonneg : 0 ≤ Q := le_of_lt (by simpa [Q] using hQ_pos)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp_nonneg i) (ht_nonneg i)
  have hweight_nonneg : ∀ i, 0 ≤ weight i := by
    intro i
    exact div_nonneg (mul_nonneg (le_of_lt (hq_pos i)) (ht_nonneg i)) hQ_nonneg
  have hweight_sum : ∑ i, weight i = 1 := by
    calc
      ∑ i, weight i = (∑ i, q i * t i) / Q := by
          simp [weight, Finset.sum_div]
      _ = Q / Q := by rfl
      _ = 1 := div_self hQ_ne
  have hvalue_nonneg : ∀ i, 0 ≤ value i := by
    intro i
    exact div_nonneg (hp_nonneg i) (le_of_lt (hq_pos i))
  have hweighted_eq : ∑ i, weight i * value i = P / Q := by
    calc
      ∑ i, weight i * value i =
          ∑ i, (p i * t i) / Q := by
            apply Finset.sum_congr rfl
            intro i _
            have hqi_ne : q i ≠ 0 := ne_of_gt (hq_pos i)
            dsimp [weight, value]
            field_simp [hqi_ne, hQ_ne]
      _ = (∑ i, p i * t i) / Q := by
            rw [Finset.sum_div]
      _ = P / Q := by rfl
  have hjensen :
      ∑ i, weight i * value i ^ α ≤ (P / Q) ^ α := by
    rw [← hweighted_eq]
    exact real_sum_weighted_rpow_le_rpow_weighted_sum hα_nonneg hα_le_one
      hweight_nonneg hweight_sum hvalue_nonneg
  have hright_eq :
      Q * (∑ i, weight i * value i ^ α) =
        ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
    calc
      Q * (∑ i, weight i * value i ^ α) =
          ∑ i, Q * (weight i * value i ^ α) := by
            rw [Finset.mul_sum]
      _ = ∑ i, t i * p i ^ α * q i ^ (1 - α) := by
            apply Finset.sum_congr rfl
            intro i _
            have hqi : 0 < q i := hq_pos i
            have hqi_ne : q i ≠ 0 := ne_of_gt hqi
            have hp_i_nonneg : 0 ≤ p i := hp_nonneg i
            have hq_i_nonneg : 0 ≤ q i := le_of_lt hqi
            calc
              Q * (weight i * value i ^ α) =
                  q i * t i * (p i / q i) ^ α := by
                    dsimp [weight, value]
                    field_simp [hQ_ne]
              _ = q i * t i * (p i ^ α / q i ^ α) := by
                    rw [Real.div_rpow hp_i_nonneg hq_i_nonneg]
              _ = t i * p i ^ α * (q i ^ (1 : ℝ) / q i ^ α) := by
                    rw [Real.rpow_one]
                    ring
              _ = t i * p i ^ α * q i ^ (1 - α) := by
                    rw [← Real.rpow_sub hqi 1 α]
  have hleft_eq :
      P ^ α * Q ^ (1 - α) = Q * (P / Q) ^ α := by
    have hP_div_nonneg : 0 ≤ P / Q := div_nonneg hP_nonneg hQ_nonneg
    calc
      P ^ α * Q ^ (1 - α) =
          (Q * (P / Q)) ^ α * Q ^ (1 - α) := by
            rw [mul_div_cancel₀ P hQ_ne]
      _ = (Q ^ α * (P / Q) ^ α) * Q ^ (1 - α) := by
            rw [Real.mul_rpow hQ_nonneg hP_div_nonneg]
      _ = (P / Q) ^ α * (Q ^ α * Q ^ (1 - α)) := by
            ring
      _ = (P / Q) ^ α * Q ^ (α + (1 - α)) := by
            rw [Real.rpow_add (by simpa [Q] using hQ_pos) α (1 - α)]
      _ = (P / Q) ^ α * Q := by
            have hexp : α + (1 - α) = 1 := by ring
            rw [hexp, Real.rpow_one]
      _ = Q * (P / Q) ^ α := by
            ring
  calc
    ∑ i, t i * p i ^ α * q i ^ (1 - α) =
        Q * (∑ i, weight i * value i ^ α) := hright_eq.symm
    _ ≤ Q * (P / Q) ^ α :=
        mul_le_mul_of_nonneg_left hjensen hQ_nonneg
    _ = P ^ α * Q ^ (1 - α) := hleft_eq.symm
    _ = (∑ i, p i * t i) ^ α * (∑ i, q i * t i) ^ (1 - α) := by rfl

/-- Finite classical stochastic-map Renyi power-sum contraction for `α ≥ 1`.

This is the classical/commuting endpoint needed by the pinching route.  The
transition kernel is represented by nonnegative real weights `T i y` whose rows
sum to one. -/
theorem real_classical_renyi_stochastic_power_sum_le
    {ο : Type*} [Fintype ο]
    {p q : ι → ℝ} {T : ι → ο → ℝ} {α : ℝ}
    (hα : 1 ≤ α)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_pos : ∀ i, 0 < q i)
    (hT_nonneg : ∀ i y, 0 ≤ T i y)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hQout_pos : ∀ y, 0 < ∑ i, q i * T i y) :
    (∑ y, (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α)) ≤
      ∑ i, p i ^ α * q i ^ (1 - α) := by
  classical
  have hpoint :
      ∀ y,
        (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α) ≤
          ∑ i, T i y * p i ^ α * q i ^ (1 - α) := by
    intro y
    exact real_classical_renyi_weighted_power_term_le
      (ι := ι) (p := p) (q := q) (t := fun i => T i y) hα
      hp_nonneg hq_pos (fun i => hT_nonneg i y) (hQout_pos y)
  calc
    (∑ y, (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α))
        ≤ ∑ y, ∑ i, T i y * p i ^ α * q i ^ (1 - α) :=
          Finset.sum_le_sum fun y _ => hpoint y
    _ = ∑ i, ∑ y, T i y * p i ^ α * q i ^ (1 - α) := by
          rw [Finset.sum_comm]
    _ = ∑ i, (∑ y, T i y) * p i ^ α * q i ^ (1 - α) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Finset.sum_mul, mul_assoc]
    _ = ∑ i, p i ^ α * q i ^ (1 - α) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hT_sum i]
          ring

/-- Finite classical stochastic-map Renyi power-sum expansion for
`0 ≤ α ≤ 1`. This is the classical endpoint for the lower-α DPI range, where
the logarithmic prefactor is nonpositive. -/
theorem real_classical_renyi_stochastic_power_sum_ge
    {ο : Type*} [Fintype ο]
    {p q : ι → ℝ} {T : ι → ο → ℝ} {α : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_pos : ∀ i, 0 < q i)
    (hT_nonneg : ∀ i y, 0 ≤ T i y)
    (hT_sum : ∀ i, ∑ y, T i y = 1)
    (hQout_pos : ∀ y, 0 < ∑ i, q i * T i y) :
    (∑ i, p i ^ α * q i ^ (1 - α)) ≤
      ∑ y, (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α) := by
  classical
  have hpoint :
      ∀ y,
        ∑ i, T i y * p i ^ α * q i ^ (1 - α) ≤
          (∑ i, p i * T i y) ^ α * (∑ i, q i * T i y) ^ (1 - α) := by
    intro y
    exact real_classical_renyi_weighted_power_term_ge
      (ι := ι) (p := p) (q := q) (t := fun i => T i y)
      hα_nonneg hα_le_one hp_nonneg hq_pos
      (fun i => hT_nonneg i y) (hQout_pos y)
  calc
    (∑ i, p i ^ α * q i ^ (1 - α)) =
        ∑ i, (∑ y, T i y) * p i ^ α * q i ^ (1 - α) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hT_sum i]
          ring
    _ = ∑ i, ∑ y, T i y * p i ^ α * q i ^ (1 - α) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Finset.sum_mul, mul_assoc]
    _ = ∑ y, ∑ i, T i y * p i ^ α * q i ^ (1 - α) := by
          rw [Finset.sum_comm]
    _ ≤ ∑ y, (∑ i, p i * T i y) ^ α *
          (∑ i, q i * T i y) ^ (1 - α) :=
          Finset.sum_le_sum fun y _ => hpoint y

/-- The finite classical Renyi power sum is strictly positive for full-support
probability vectors. -/
theorem nnreal_classical_renyi_power_sum_pos
    (p q : ι → ℝ≥0) (hp_sum : ∑ i, p i = 1)
    (hp_pos : ∀ i, 0 < (p i : ℝ)) (hq_pos : ∀ i, 0 < (q i : ℝ))
    (α : ℝ) :
    0 < ∑ i, ((p i : ℝ) ^ α) * ((q i : ℝ) ^ (1 - α)) := by
  classical
  have hnonempty : Nonempty ι := by
    by_contra h
    haveI : IsEmpty ι := not_nonempty_iff.mp h
    have hzero : (∑ i, p i) = 0 := by simp
    rw [hzero] at hp_sum
    exact zero_ne_one hp_sum
  exact Finset.sum_pos' (fun i _ =>
      le_of_lt <| mul_pos (Real.rpow_pos_of_pos (hp_pos i) α)
        (Real.rpow_pos_of_pos (hq_pos i) (1 - α)))
    ⟨Classical.choice hnonempty, Finset.mem_univ _,
      mul_pos
        (Real.rpow_pos_of_pos (hp_pos (Classical.choice hnonempty)) α)
        (Real.rpow_pos_of_pos (hq_pos (Classical.choice hnonempty)) (1 - α))⟩

end ClassicalPower

namespace Classical

/-- Push-forward of a finite classical distribution through a row-stochastic
kernel. -/
def stochasticOutput (p : a → ℝ≥0) (T : a → b → ℝ≥0) : b → ℝ≥0 :=
  fun y => ∑ i, p i * T i y

omit [DecidableEq a] [DecidableEq b] in
/-- The push-forward through a row-stochastic kernel is normalized. -/
theorem stochasticOutput_sum
    (p : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hT_sum : ∀ i, ∑ y, T i y = 1) :
    ∑ y, stochasticOutput p T y = 1 := by
  classical
  calc
    ∑ y, stochasticOutput p T y = ∑ y, ∑ i, p i * T i y := by rfl
    _ = ∑ i, ∑ y, p i * T i y := by rw [Finset.sum_comm]
    _ = ∑ i, p i * ∑ y, T i y := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ i, p i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hT_sum i, mul_one]
    _ = 1 := hp_sum

/-- A row-stochastic classical kernel as a CPTP channel between diagonal
classical registers. -/
def stochasticChannel (T : a → b → ℝ≥0) (hT_sum : ∀ i, ∑ y, T i y = 1) :
    Channel a b :=
  Channel.prepare fun i => diagonalState (T i) (hT_sum i)

/-- The stochastic channel sends a diagonal state to the diagonal push-forward
distribution. -/
theorem stochasticChannel_applyState_diagonalState
    (p : a → ℝ≥0) (T : a → b → ℝ≥0)
    (hp_sum : ∑ i, p i = 1) (hT_sum : ∀ i, ∑ y, T i y = 1) :
    (stochasticChannel T hT_sum).applyState (diagonalState p hp_sum) =
      diagonalState (stochasticOutput p T) (stochasticOutput_sum p T hp_sum hT_sum) := by
  classical
  apply State.ext
  ext y y'
  by_cases hyy : y = y'
  · subst y'
    simp only [stochasticChannel, Channel.applyState, Channel.prepare, Channel.prepareMap,
      LinearMap.coe_mk, AddHom.coe_mk, diagonalState_matrix, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.diagonal_apply_eq, stochasticOutput]
    change (∑ x, ((p x : ℂ) * (T x y : ℂ))) =
      (((∑ x, p x * T x y) : ℝ≥0) : ℂ)
    simp
  · simp [stochasticChannel, Channel.applyState, Channel.prepare, Channel.prepareMap,
      diagonalState_matrix, Matrix.sum_apply, Matrix.diagonal, hyy]

end Classical

namespace State

omit [Fintype a] in
theorem cMatrix_real_smul_one_posDef_local {r : ℝ} (hr : 0 < r) :
    (r • (1 : CMatrix a)).PosDef := by
  rw [show r • (1 : CMatrix a) = Matrix.diagonal (fun _ : a => (r : ℂ)) by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]]
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact_mod_cast hr

omit [Fintype a] in
theorem cMatrix_le_add_pos_smul_one {A : CMatrix a}
    {ε : ℝ} (hε : 0 < ε) :
    A ≤ A + ε • (1 : CMatrix a) := by
  rw [Matrix.le_iff]
  have hpos : (ε • (1 : CMatrix a)).PosSemidef :=
    (cMatrix_real_smul_one_posDef_local (a := a) hε).posSemidef
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpos

omit [Fintype a] in
theorem cMatrix_posSemidef_add_pos_smul_one_posDef {A : CMatrix a}
    (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (A + ε • (1 : CMatrix a)).PosDef :=
  Matrix.PosDef.posSemidef_add hA
    (cMatrix_real_smul_one_posDef_local (a := a) hε)

/-- The sandwiched inner operator of a state with itself is the reference
power `σ^(1/α)` in the full-rank domain.

This algebraic identity is one endpoint needed for the α > 1 interpolation
route. -/
theorem sandwichedRenyiInner_self_eq_rpow
    (σ : State a) (hσ : σ.matrix.PosDef) (α : ℝ) (hα_ne_zero : α ≠ 0) :
    sandwichedRenyiInner σ σ α = CFC.rpow σ.matrix (1 / α) := by
  let s : ℝ := (1 - α) / (2 * α)
  have hnonneg : 0 ≤ σ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hpow_one : CFC.rpow σ.matrix (1 : ℝ) = σ.matrix :=
    CFC.rpow_one σ.matrix (ha := hnonneg)
  have hs_left :
      CFC.rpow σ.matrix s * σ.matrix = CFC.rpow σ.matrix (s + 1) := by
    calc
      CFC.rpow σ.matrix s * σ.matrix =
          CFC.rpow σ.matrix s * CFC.rpow σ.matrix (1 : ℝ) := by
            rw [hpow_one]
      _ = CFC.rpow σ.matrix (s + 1) := by
            exact (CFC.rpow_add (a := σ.matrix) (x := s) (y := 1) hσ.isUnit).symm
  have hs_total :
      CFC.rpow σ.matrix (s + 1) * CFC.rpow σ.matrix s =
        CFC.rpow σ.matrix ((s + 1) + s) := by
    exact (CFC.rpow_add (a := σ.matrix) (x := s + 1) (y := s) hσ.isUnit).symm
  have hexp : (s + 1) + s = 1 / α := by
    dsimp [s]
    field_simp [hα_ne_zero]
    ring
  unfold sandwichedRenyiInner
  change CFC.rpow σ.matrix s * σ.matrix * CFC.rpow σ.matrix s =
    CFC.rpow σ.matrix (1 / α)
  calc
    CFC.rpow σ.matrix s * σ.matrix * CFC.rpow σ.matrix s =
        (CFC.rpow σ.matrix s * σ.matrix) * CFC.rpow σ.matrix s := by
          rw [Matrix.mul_assoc]
    _ = CFC.rpow σ.matrix (s + 1) * CFC.rpow σ.matrix s := by
          rw [hs_left]
    _ = CFC.rpow σ.matrix ((s + 1) + s) := hs_total
    _ = CFC.rpow σ.matrix (1 / α) := by rw [hexp]

/-- The interpolation reference endpoint `σ^(1/α)` has normalized
`α`-power trace. -/
theorem state_rpow_one_div_psdTracePower_eq_one
    (σ : State a) (hσ : σ.matrix.PosDef) (α : ℝ) (hα_pos : 0 < α) :
    psdTracePower (CFC.rpow σ.matrix (1 / α))
        (σ.rpowMatrix_posSemidef (1 / α)) α = 1 := by
  have hσ_nonneg : 0 ≤ σ.matrix :=
    Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hone_div_nonneg : 0 ≤ 1 / α := by positivity
  have hα_ne_zero : α ≠ 0 := ne_of_gt hα_pos
  have hpow :
      CFC.rpow (CFC.rpow σ.matrix (1 / α)) α =
        CFC.rpow σ.matrix (1 : ℝ) := by
    calc
      CFC.rpow (CFC.rpow σ.matrix (1 / α)) α =
          CFC.rpow σ.matrix ((1 / α) * α) := by
            exact CFC.rpow_rpow_of_exponent_nonneg σ.matrix
              (1 / α) α hone_div_nonneg hα_nonneg hσ_nonneg
      _ = CFC.rpow σ.matrix (1 : ℝ) := by
            congr 1
            field_simp [hα_ne_zero]
  have hone : CFC.rpow σ.matrix (1 : ℝ) = σ.matrix :=
    CFC.rpow_one σ.matrix (ha := hσ_nonneg)
  rw [psdTracePower, hpow, hone, σ.trace_eq_one]
  norm_num

/-- The full-rank sandwiched Renyi divergence of a state from itself is zero.

This is the normalization endpoint needed for turning the already-proved
`β > 1` DPI into ordinary nonnegativity once a discard/terminal channel is
available. -/
theorem sandwichedRenyi_self_eq_zero
    (σ : State a) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    sandwichedRenyi σ σ hσ hσ α hα_pos hα_ne_one = 0 := by
  have hinner :
      sandwichedRenyiInner σ σ α = CFC.rpow σ.matrix (1 / α) :=
    sandwichedRenyiInner_self_eq_rpow σ hσ α (ne_of_gt hα_pos)
  have htrace :
      psdTracePower (sandwichedRenyiInner σ σ α)
          (sandwichedRenyiInner_posSemidef σ σ α) α = 1 := by
    simpa [hinner] using state_rpow_one_div_psdTracePower_eq_one σ hσ α hα_pos
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner, htrace]
  simp [log2]

/-- The PSD-friendly low-`α` `Q` functional is normalized on equal states.

This is the `Q_α(ω,ω)=1` factor needed when local-unitary twirling produces a
common maximally mixed tensor factor. -/
theorem sandwichedRenyiQ_state_self
    (σ : State a) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) :
    sandwichedRenyiQ σ.matrix σ.matrix σ.pos σ.pos α = 1 := by
  rw [sandwichedRenyiQ_eq_psdTracePower_inner]
  simpa [sandwichedRenyiInner_self_eq_rpow σ hσ α (ne_of_gt hα_pos), psdTracePower]
    using state_rpow_one_div_psdTracePower_eq_one σ hσ α hα_pos

/-- The maximally mixed tensor factor contributes unit `Q` mass. -/
theorem sandwichedRenyiQ_maximallyMixed_self [Nonempty a]
    (α : ℝ) (hα_pos : 0 < α) :
    sandwichedRenyiQ
      (maximallyMixed a).matrix (maximallyMixed a).matrix
      (maximallyMixed a).pos (maximallyMixed a).pos α = 1 :=
  sandwichedRenyiQ_state_self (maximallyMixed a)
    (maximallyMixed_posDef (a := a)) α hα_pos

/-- Tensoring both arguments with the same maximally mixed state leaves the
low-`α` `Q` functional unchanged.

This is the normalization side of the local-unitary twirling route for partial
trace monotonicity. -/
theorem sandwichedRenyiQ_kronecker_maximallyMixed_right [Nonempty b]
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1) :
    sandwichedRenyiQ
        (Matrix.kronecker ρ (maximallyMixed b).matrix)
        (Matrix.kronecker σ (maximallyMixed b).matrix)
        (hρ.kronecker (maximallyMixed b).pos)
        (hσ.kronecker (maximallyMixed b).pos) α =
      sandwichedRenyiQ ρ σ hρ hσ α := by
  have hα_pos : 0 < α := by linarith
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hs_nonneg : 0 ≤ (1 - α) / (2 * α) := by
    have hnum : 0 ≤ 1 - α := le_of_lt (sub_pos.mpr hα_lt_one)
    have hden : 0 ≤ 2 * α := by positivity
    exact div_nonneg hnum hden
  rw [sandwichedRenyiQ_kronecker hρ hσ (maximallyMixed b).pos
    (maximallyMixed b).pos α hs_nonneg hα_nonneg]
  rw [sandwichedRenyiQ_maximallyMixed_self (a := b) α hα_pos]
  ring

/-- The unitary acting as identity on the left tensor factor and as `U` on the
right tensor factor. -/
def localRightUnitary (U : Matrix.unitaryGroup b ℂ) :
    Matrix.unitaryGroup (Prod a b) ℂ :=
  ⟨Matrix.kronecker (1 : CMatrix a) (U : CMatrix b), by
    let I : Matrix.unitaryGroup a ℂ := ⟨1, by simp⟩
    simpa using Matrix.kronecker_mem_unitary I.2 U.2⟩

@[simp] theorem localRightUnitary_coe (U : Matrix.unitaryGroup b ℂ) :
    (localRightUnitary (a := a) U : CMatrix (Prod a b)) =
      Matrix.kronecker (1 : CMatrix a) (U : CMatrix b) := rfl

/-- The low-`α` `Q` functional is invariant under unitary conjugation on the
right tensor factor. -/
theorem sandwichedRenyiQ_localRightUnitary_conj
    {ρ σ : CMatrix (Prod a b)}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (U : Matrix.unitaryGroup b ℂ) (α : ℝ)
    (hs_nonneg : 0 ≤ (1 - α) / (2 * α)) (hα_nonneg : 0 ≤ α) :
    sandwichedRenyiQ
        ((localRightUnitary (a := a) U : CMatrix (Prod a b)) * ρ *
          star (localRightUnitary (a := a) U : CMatrix (Prod a b)))
        ((localRightUnitary (a := a) U : CMatrix (Prod a b)) * σ *
          star (localRightUnitary (a := a) U : CMatrix (Prod a b)))
        (by
          simpa using
            posSemidef_unitary_conj hρ (localRightUnitary (a := a) U)⁻¹)
        (by
          simpa using
            posSemidef_unitary_conj hσ (localRightUnitary (a := a) U)⁻¹)
        α =
      sandwichedRenyiQ ρ σ hρ hσ α :=
  sandwichedRenyiQ_unitary_conj hρ hσ (localRightUnitary (a := a) U)
    α hs_nonneg hα_nonneg

end State

end

end QIT
