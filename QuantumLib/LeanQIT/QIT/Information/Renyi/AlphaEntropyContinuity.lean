/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalPetzRenyi
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.Information.Entropy.RelativeEntropyDPI
public import QIT.States.Schatten
public import QIT.Util.BlockMatrix
public import QIT.Util.Matrix
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Alpha-to-von-Neumann continuity interface

This module records the fixed-reference endpoint and convergence parameter used
in Tomamichel--Colbeck--Renner 2008, Lemma `alpha-bound`
(`tomamichel-colbeck-renner-2008-fqaep.tex`, lines 699--706).

The hard analytic estimate is downstream: it requires the purification
trace-bracket representation, the scalar remainder bound for `t^β`, the
`s_β`/cosh comparison, and Jensen's inequality for the functional calculus of
`sqrt X + X^{-1/2} + I`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Matrix Polynomial

namespace QIT

universe u v w

noncomputable section

noncomputable local instance cMatrixCStarAlgebraForAlphaEntropyContinuity
    (n : Type*) [Fintype n] [DecidableEq n] : CStarAlgebra (CMatrix n) := {}

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

private theorem roots_X_pow_map_re_xlog2_sum_zero (n : ℕ) :
    ((Polynomial.X ^ n : ℂ[X]).roots.map (fun z : ℂ => xlog2 z.re)).sum = 0 := by
  rw [Polynomial.roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton]
  simp [xlog2]

private theorem roots_re_xlog2_sum_eq_of_X_pow_mul_eq
    {P Q : ℂ[X]} {m n : ℕ}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : Polynomial.X ^ m * P = Polynomial.X ^ n * Q) :
    (P.roots.map (fun z : ℂ => xlog2 z.re)).sum =
      (Q.roots.map (fun z : ℂ => xlog2 z.re)).sum := by
  have hXm : (Polynomial.X ^ m : ℂ[X]) ≠ 0 := by simp
  have hXn : (Polynomial.X ^ n : ℂ[X]) ≠ 0 := by simp
  have hleft_ne : (Polynomial.X ^ m : ℂ[X]) * P ≠ 0 := mul_ne_zero hXm hP
  have hright_ne : (Polynomial.X ^ n : ℂ[X]) * Q ≠ 0 := mul_ne_zero hXn hQ
  have hroots := congrArg Polynomial.roots h
  rw [Polynomial.roots_mul hleft_ne, Polynomial.roots_mul hright_ne] at hroots
  have hsum :=
    congrArg (fun s : Multiset ℂ => (s.map (fun z : ℂ => xlog2 z.re)).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add] at hsum
  rw [roots_X_pow_map_re_xlog2_sum_zero m,
    roots_X_pow_map_re_xlog2_sum_zero n] at hsum
  simpa using hsum

/-- Von Neumann entropy is invariant under rectangular isometry embedding.

For an isometry `V : a → r`, the embedded state `V ρ Vᴴ` has the same
nonzero eigenvalues as `ρ`, with only extra zero eigenvalues. The entropy
convention `xlog2 0 = 0` removes those extra roots. -/
theorem vonNeumann_eq_of_matrix_eq_isometry_conj
    (ρ : State a) (σ : State b) (V : Matrix b a ℂ)
    (hV : Matrix.conjTranspose V * V = (1 : CMatrix a))
    (hσ : σ.matrix = V * ρ.matrix * Matrix.conjTranspose V) :
    σ.vonNeumann = ρ.vonNeumann := by
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset,
    vonNeumann_eq_neg_sum_eigenvalueMultiset]
  congr 1
  have hpoly := Matrix.charpoly_isometry_conj (V := V) (A := ρ.matrix) hV
  have hpolyσ :
      Polynomial.X ^ Fintype.card a * σ.matrix.charpoly =
        Polynomial.X ^ Fintype.card b * ρ.matrix.charpoly := by
    simpa [hσ] using hpoly
  have hP : σ.matrix.charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hQ : ρ.matrix.charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hroot :=
    roots_re_xlog2_sum_eq_of_X_pow_mul_eq
      (P := σ.matrix.charpoly) (Q := ρ.matrix.charpoly) hP hQ hpolyσ
  have hrootsσ := σ.pos.isHermitian.roots_charpoly_eq_eigenvalues
  have hrootsρ := ρ.pos.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hrootsσ, hrootsρ] at hroot
  simpa [eigenvalueMultiset, Multiset.map_map, Function.comp_def] using hroot

private theorem kronecker_one_isometry
    {bPlus : Type w} [Fintype bPlus] [DecidableEq bPlus]
    (V : ReferenceIsometry b bPlus) :
    Matrix.conjTranspose (Matrix.kronecker (1 : CMatrix a) V.matrix) *
        Matrix.kronecker (1 : CMatrix a) V.matrix =
      (1 : CMatrix (Prod a b)) := by
  ext x y
  rcases x with ⟨xA, xB⟩
  rcases y with ⟨yA, yB⟩
  have hV := congrFun (congrFun V.isometry xB) yB
  by_cases hxy : xA = yA
  · subst yA
    simpa [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Finset.sum_ite_eq', apply_ite] using hV
  · simp [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      apply_ite, hxy, eq_comm]

/-- Conditional entropy is invariant under an isometry on the conditioning
register. -/
theorem conditionalEntropy_conditioningIsometryApply
    {bPlus : Type w} [Fintype bPlus] [DecidableEq bPlus]
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalEntropy = ρ.conditionalEntropy := by
  rw [conditionalEntropy_eq, conditionalEntropy_eq]
  have hjoint :
      (ρ.conditioningIsometryApply V).vonNeumann = ρ.vonNeumann :=
    vonNeumann_eq_of_matrix_eq_isometry_conj
      (ρ := ρ) (σ := ρ.conditioningIsometryApply V)
      (V := Matrix.kronecker (1 : CMatrix a) V.matrix)
      (kronecker_one_isometry (a := a) V)
      (ρ.conditioningIsometryApply_matrix_eq_kronecker_conj V)
  have hmarg :
      (ρ.conditioningIsometryApply V).marginalB.vonNeumann =
        ρ.marginalB.vonNeumann :=
    vonNeumann_eq_of_matrix_eq_isometry_conj
      (ρ := ρ.marginalB) (σ := (ρ.conditioningIsometryApply V).marginalB)
      (V := V.matrix) V.isometry
      (ρ.conditioningIsometryApply_marginalB_matrix V)
  rw [hjoint, hmarg]

/-- Compressing the conditioning register to the support of the marginal and
then comparing ordinary conditional von Neumann entropy loses no entropy. -/
theorem conditionalEntropy_conditioningSupportCompressedState
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.conditionalEntropy = ρ.conditionalEntropy := by
  let V : ReferenceIsometry
      (psdSupportIndex ρ.marginalB.matrix ρ.marginalB.pos) b :=
    psdSupportReferenceIsometry ρ.marginalB.matrix ρ.marginalB.pos
  have h :=
    conditionalEntropy_conditioningIsometryApply
      (ρ := ρ.conditioningSupportCompressedState) V
  rw [ρ.conditioningSupportCompressedState_conditioningIsometryApply] at h
  exact h.symm

/-- Scalar remainder in the source proof of TCR Lemma `alpha-bound`:
`r_β(t) = t^β - β log t - 1`. -/
def alphaRemainder (β t : ℝ) : ℝ :=
  t ^ β - β * Real.log t - 1

/-- Cosh majorant used in the source proof of TCR Lemma `alpha-bound`:
`s_β(t) = 2 (cosh(β log t) - 1)`. -/
def alphaCoshMajorant (β t : ℝ) : ℝ :=
  2 * (Real.cosh (β * Real.log t) - 1)

/-- Source-line scalar estimate `r_β(t) ≤ s_β(t)` for positive `t`.

This is the elementary comparison from
`tomamichel-colbeck-renner-2008-fqaep.tex`, lines 730--733. -/
theorem alphaRemainder_le_alphaCoshMajorant
    {β t : ℝ} (ht : 0 < t) :
    alphaRemainder β t ≤ alphaCoshMajorant β t := by
  let x : ℝ := β * Real.log t
  have hpow : t ^ β = Real.exp x := by
    rw [Real.rpow_def_of_pos ht β]
    simp [x, mul_comm]
  have hmajor :
      alphaCoshMajorant β t = Real.exp x + Real.exp (-x) - 2 := by
    simp [alphaCoshMajorant, Real.cosh_eq, x, two_mul, sub_eq_add_neg, add_comm,
      add_left_comm]
    ring
  have hrem : alphaRemainder β t = Real.exp x - x - 1 := by
    simp [alphaRemainder, hpow, x, sub_eq_add_neg]
  rw [hrem, hmajor]
  have hbase : -x + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  linarith

/-- The source majorant `s_β(t)` is invariant under `t ↦ t⁻¹`. -/
theorem alphaCoshMajorant_inv
    {β t : ℝ} (ht : 0 < t) :
    alphaCoshMajorant β t⁻¹ = alphaCoshMajorant β t := by
  have _ : t ≠ 0 := ne_of_gt ht
  rw [alphaCoshMajorant, alphaCoshMajorant, Real.log_inv]
  rw [show β * -Real.log t = -(β * Real.log t) by ring_nf]
  rw [Real.cosh_neg]

/-- Square identity for the source majorant: `s_β(t^2) = s_{2β}(t)`. -/
theorem alphaCoshMajorant_sq
    {β t : ℝ} (ht : 0 < t) :
    alphaCoshMajorant β (t ^ 2) = alphaCoshMajorant (2 * β) t := by
  have _ : t ≠ 0 := ne_of_gt ht
  rw [alphaCoshMajorant, alphaCoshMajorant, Real.log_pow]
  congr 2
  ring_nf

/-- Positive-input rpow form of the source majorant:
`s_γ(x) = x^γ + x^{-γ} - 2`. -/
theorem alphaCoshMajorant_eq_rpow_add_rpow_neg_sub_two
    {γ x : ℝ} (hx : 0 < x) :
    alphaCoshMajorant γ x = x ^ γ + x ^ (-γ) - 2 := by
  rw [alphaCoshMajorant, Real.cosh_eq]
  rw [Real.rpow_def_of_pos hx γ, Real.rpow_def_of_pos hx (-γ)]
  ring_nf

private theorem alphaCoshMajorant_rpowModel_concaveOn_Ici_three_of_shape
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (hshape : γ + 1 ≤ (1 - γ) * (3 : ℝ) ^ (2 * γ)) :
    ConcaveOn ℝ (Set.Ici (3 : ℝ))
      (fun x : ℝ => x ^ γ + x ^ (-γ) - 2) := by
  let D : Set ℝ := Set.Ici (3 : ℝ)
  let f : ℝ → ℝ := fun x => x ^ γ + x ^ (-γ) - 2
  let f' : ℝ → ℝ := fun x => γ * x ^ (γ - 1) + (-γ) * x ^ (-γ - 1)
  let f'' : ℝ → ℝ := fun x =>
    γ * ((γ - 1) * x ^ (γ - 2)) + (-γ) * ((-γ - 1) * x ^ (-γ - 2))
  have hcont : ContinuousOn f D := by
    intro x hx
    have hxpos : 0 < x := by
      have : (3 : ℝ) ≤ x := hx
      linarith
    exact
      (((continuousAt_id.rpow_const (Or.inl hxpos.ne')).add
        (continuousAt_id.rpow_const (Or.inl hxpos.ne'))).sub
          continuousAt_const).continuousWithinAt
  have hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x := by
    intro x hx
    have hxmem : x ∈ Set.Ioi (3 : ℝ) := by simpa [D, interior_Ici] using hx
    have hxne : x ≠ 0 := by
      have hxgt : (3 : ℝ) < x := by simpa using hxmem
      have : 0 < x := by linarith
      exact ne_of_gt this
    have hder : HasDerivAt f (f' x) x := by
      simpa [f, f'] using
        ((Real.hasDerivAt_rpow_const (x := x) (p := γ) (Or.inl hxne)).add
          (Real.hasDerivAt_rpow_const (x := x) (p := -γ) (Or.inl hxne))).sub_const 2
    exact hder.hasDerivWithinAt
  have hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x := by
    intro x hx
    have hxmem : x ∈ Set.Ioi (3 : ℝ) := by simpa [D, interior_Ici] using hx
    have hxne : x ≠ 0 := by
      have hxgt : (3 : ℝ) < x := by simpa using hxmem
      have : 0 < x := by linarith
      exact ne_of_gt this
    have hder : HasDerivAt f' (f'' x) x := by
      convert
        ((Real.hasDerivAt_rpow_const (x := x) (p := γ - 1) (Or.inl hxne)).const_mul γ).add
          ((Real.hasDerivAt_rpow_const (x := x) (p := -γ - 1) (Or.inl hxne)).const_mul (-γ))
        using 1
      simp [f'']
      ring_nf
    exact hder.hasDerivWithinAt
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici (3 : ℝ)) hcont hf' hf'' ?_
  intro x hx
  have hxmem : x ∈ Set.Ioi (3 : ℝ) := by simpa [D, interior_Ici] using hx
  have hxgt : (3 : ℝ) < x := by simpa using hxmem
  dsimp [f'']
  convert
    (show γ * ((γ - 1) * x ^ (γ - 2) + (γ + 1) * x ^ (-γ - 2)) ≤ 0 from
      (by
        have hxpos : 0 < x := by linarith
        have hx3le : (3 : ℝ) ≤ x := hxgt.le
        have hγle1 : γ ≤ 1 := by linarith
        have hnonneg1 : 0 ≤ 1 - γ := sub_nonneg.mpr hγle1
        have hpowmono : (3 : ℝ) ^ (2 * γ) ≤ x ^ (2 * γ) := by
          exact Real.rpow_le_rpow (by norm_num) hx3le (by nlinarith)
        have hshape_x : γ + 1 ≤ (1 - γ) * x ^ (2 * γ) := by
          exact hshape.trans (mul_le_mul_of_nonneg_left hpowmono hnonneg1)
        have hmul :=
          mul_le_mul_of_nonneg_right hshape_x (Real.rpow_nonneg hxpos.le (-γ - 2))
        have hpow :
            x ^ (2 * γ) * x ^ (-γ - 2) = x ^ (γ - 2) := by
          rw [← Real.rpow_add hxpos]
          congr 1
          ring
        have hcmp :
            (γ + 1) * x ^ (-γ - 2) ≤ (1 - γ) * x ^ (γ - 2) := by
          calc
            (γ + 1) * x ^ (-γ - 2) ≤
                ((1 - γ) * x ^ (2 * γ)) * x ^ (-γ - 2) := hmul
            _ = (1 - γ) * x ^ (γ - 2) := by rw [mul_assoc, hpow]
        have hbr :
            (γ - 1) * x ^ (γ - 2) + (γ + 1) * x ^ (-γ - 2) ≤ 0 := by
          nlinarith [hcmp]
        exact mul_nonpos_of_nonneg_of_nonpos hγ0 hbr)) using 1
  ring

/-- Concavity of the source majorant on `[3, ∞)` from the exact scalar
shape inequality needed by the second-derivative sign.  For the TCR parameter
range it remains to discharge `γ + 1 ≤ (1 - γ) * 3^(2γ)` from `0 ≤ γ ≤ 1/2`. -/
theorem alphaCoshMajorant_concaveOn_Ici_three_of_shape
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (hshape : γ + 1 ≤ (1 - γ) * (3 : ℝ) ^ (2 * γ)) :
    ConcaveOn ℝ (Set.Ici (3 : ℝ)) (fun x : ℝ => alphaCoshMajorant γ x) := by
  exact
    (alphaCoshMajorant_rpowModel_concaveOn_Ici_three_of_shape hγ0 hγ hshape).congr
      (fun x hx =>
        (alphaCoshMajorant_eq_rpow_add_rpow_neg_sub_two (by
          have hx3 : (3 : ℝ) ≤ x := hx
          linarith)).symm)

private theorem logRatio_convexOn_Icc_zero_one :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun x : ℝ => Real.log ((2 + x) / (2 - x))) := by
  let D : Set ℝ := Set.Icc (0 : ℝ) 1
  let f : ℝ → ℝ := fun x => Real.log ((2 + x) / (2 - x))
  let f' : ℝ → ℝ := fun x => 1 / (2 + x) + 1 / (2 - x)
  let f'' : ℝ → ℝ := fun x => -1 / (2 + x) ^ 2 + 1 / (2 - x) ^ 2
  have hf'At : ∀ x ∈ D, HasDerivAt f (f' x) x := by
    intro x hx
    have hnum : 2 + x ≠ 0 := by nlinarith [hx.1]
    have hden : 2 - x ≠ 0 := by nlinarith [hx.2]
    have hdiv : (2 + x) / (2 - x) ≠ 0 := div_ne_zero hnum hden
    have hraw := ((((hasDerivAt_id x).const_add 2).div
      (((hasDerivAt_const x 2).sub (hasDerivAt_id x))) hden).log hdiv)
    convert hraw using 1
    dsimp [f']
    field_simp [hnum, hden]
    ring_nf
  have hcont : ContinuousOn f D := by
    intro x hx
    exact ((hf'At x hx).continuousAt).continuousWithinAt
  have hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x := by
    intro x hx
    exact (hf'At x (interior_subset hx)).hasDerivWithinAt
  have hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x := by
    intro x hx
    have hxI : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [D, interior_Icc] using hx
    have hnum : 2 + x ≠ 0 := by nlinarith [hxI.1]
    have hden : 2 - x ≠ 0 := by nlinarith [hxI.2]
    have hraw := (((hasDerivAt_id x).const_add 2).inv hnum).add
      ((((hasDerivAt_const x 2).sub (hasDerivAt_id x)).inv hden))
    have hraw' : HasDerivAt f'
        (-1 / (2 + x) ^ 2 + 1 / (2 - x) ^ 2) x := by
      convert hraw using 1
      · funext y
        simp [f', one_div]
      · field_simp [hnum, hden]
        simp only [id_eq, Pi.sub_apply]
        ring_nf
    exact hraw'.hasDerivWithinAt
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1) hcont hf' hf'' ?_
  intro x hx
  have hxI : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [D, interior_Icc] using hx
  have hleft : 0 < 2 + x := by nlinarith [hxI.1]
  have hright : 0 < 2 - x := by nlinarith [hxI.2]
  dsimp [f'']
  have habs : |2 - x| ≤ |2 + x| := by
    rw [abs_of_pos hright, abs_of_pos hleft]
    nlinarith [hxI.1]
  have hsq : (2 - x) ^ 2 ≤ (2 + x) ^ 2 := sq_le_sq.mpr habs
  have hle : 1 / (2 + x) ^ 2 ≤ 1 / (2 - x) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hright) hsq
  have hnonneg : 0 ≤ 1 / (2 - x) ^ 2 - 1 / (2 + x) ^ 2 := sub_nonneg.mpr hle
  convert hnonneg using 1
  ring

private theorem logRatio_le_chord
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.log ((2 + θ) / (2 - θ)) ≤ θ * Real.log 3 := by
  have hconv := logRatio_convexOn_Icc_zero_one
  have h :
      Real.log ((2 + ((1 - θ) * 0 + θ * 1)) / (2 - ((1 - θ) * 0 + θ * 1))) ≤
        (1 - θ) * Real.log ((2 + (0 : ℝ)) / (2 - (0 : ℝ))) +
          θ * Real.log ((2 + (1 : ℝ)) / (2 - (1 : ℝ))) := by
    exact hconv.2
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
      (sub_nonneg.mpr hθ1) hθ0 (by ring)
  norm_num at h ⊢
  simpa using h

/-- Endpoint-sharp scalar shape inequality behind concavity of `s_γ` on
`[3, ∞)` for the TCR parameter range `0 ≤ γ ≤ 1/2`. -/
theorem alphaCoshMajorant_shape_of_Icc_zero_half
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγhalf : γ ≤ 1 / 2) :
    γ + 1 ≤ (1 - γ) * (3 : ℝ) ^ (2 * γ) := by
  have hθ0 : 0 ≤ 2 * γ := mul_nonneg zero_le_two hγ0
  have hθ1 : 2 * γ ≤ 1 := by nlinarith
  have hlog := logRatio_le_chord hθ0 hθ1
  have hdenpos : 0 < 1 - γ := by nlinarith
  have hnumpos : 0 < γ + 1 := by nlinarith
  have hratioeq : (2 + 2 * γ) / (2 - 2 * γ) = (γ + 1) / (1 - γ) := by
    field_simp [hdenpos.ne']
    ring
  have hapos : 0 < (γ + 1) / (1 - γ) := div_pos hnumpos hdenpos
  have hpowpos : 0 < (3 : ℝ) ^ (2 * γ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlogpow : Real.log ((3 : ℝ) ^ (2 * γ)) = (2 * γ) * Real.log 3 := by
    rw [Real.log_rpow (by norm_num)]
  have hle_div : (γ + 1) / (1 - γ) ≤ (3 : ℝ) ^ (2 * γ) := by
    rw [← Real.log_le_log_iff hapos hpowpos]
    calc
      Real.log ((γ + 1) / (1 - γ)) =
          Real.log ((2 + 2 * γ) / (2 - 2 * γ)) := by rw [hratioeq]
      _ ≤ (2 * γ) * Real.log 3 := hlog
      _ = Real.log ((3 : ℝ) ^ (2 * γ)) := hlogpow.symm
  nlinarith [(div_le_iff₀ hdenpos).mp hle_div]

/-- Concavity of the source majorant on `[3, ∞)` throughout
`0 ≤ γ ≤ 1/2`. -/
theorem alphaCoshMajorant_concaveOn_Ici_three
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγhalf : γ ≤ 1 / 2) :
    ConcaveOn ℝ (Set.Ici (3 : ℝ)) (fun x : ℝ => alphaCoshMajorant γ x) :=
  alphaCoshMajorant_concaveOn_Ici_three_of_shape hγ0 hγhalf
    (alphaCoshMajorant_shape_of_Icc_zero_half hγ0 hγhalf)

/-- Monotonicity of `s_β` on `[1, ∞)` for nonnegative `β`. -/
theorem alphaCoshMajorant_mono_on_one_le
    {β x y : ℝ} (hβ : 0 ≤ β) (hx : 1 ≤ x) (hxy : x ≤ y) :
    alphaCoshMajorant β x ≤ alphaCoshMajorant β y := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  have hxlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hylog_nonneg : 0 ≤ Real.log y :=
    Real.log_nonneg (hx.trans hxy)
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
  have hxarg_nonneg : 0 ≤ β * Real.log x := mul_nonneg hβ hxlog_nonneg
  have hyarg_nonneg : 0 ≤ β * Real.log y := mul_nonneg hβ hylog_nonneg
  have harg_le : β * Real.log x ≤ β * Real.log y :=
    mul_le_mul_of_nonneg_left hlog_le hβ
  have hcosh :
      Real.cosh (β * Real.log x) ≤ Real.cosh (β * Real.log y) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg hxarg_nonneg, abs_of_nonneg hyarg_nonneg]
    exact harg_le
  rw [alphaCoshMajorant, alphaCoshMajorant]
  nlinarith

/-- Source-line scalar comparison after the square/inverse trick in TCR lines 736--739. -/
theorem alphaRemainder_le_alphaCoshMajorant_sqrt_add_inv_add_one
    {β t : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) :
    alphaRemainder β t ≤
      alphaCoshMajorant (2 * β) (Real.sqrt t + (Real.sqrt t)⁻¹ + 1) := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_nonneg : 0 ≤ Real.sqrt t := hsqrt_pos.le
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_inv_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hsqrt_pos
  have hsum_pos : 0 < Real.sqrt t + (Real.sqrt t)⁻¹ + 1 := by positivity
  have hsqrt_sq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hsq :
      alphaCoshMajorant β t =
        alphaCoshMajorant (2 * β) (Real.sqrt t) := by
    calc
      alphaCoshMajorant β t =
          alphaCoshMajorant β (Real.sqrt t ^ 2) := by rw [hsqrt_sq]
      _ = alphaCoshMajorant (2 * β) (Real.sqrt t) :=
          alphaCoshMajorant_sq hsqrt_pos
  have hrem : alphaRemainder β t ≤ alphaCoshMajorant β t :=
    alphaRemainder_le_alphaCoshMajorant ht
  have hβ2 : 0 ≤ 2 * β := by nlinarith
  have hsum_ge_sqrt : Real.sqrt t ≤ Real.sqrt t + (Real.sqrt t)⁻¹ + 1 := by
    nlinarith [hsqrt_inv_pos.le]
  have hsum_ge_inv : (Real.sqrt t)⁻¹ ≤ Real.sqrt t + (Real.sqrt t)⁻¹ + 1 := by
    nlinarith [hsqrt_nonneg]
  have hmajor :
      alphaCoshMajorant (2 * β) (Real.sqrt t) ≤
        alphaCoshMajorant (2 * β) (Real.sqrt t + (Real.sqrt t)⁻¹ + 1) := by
    by_cases hle : 1 ≤ Real.sqrt t
    · exact alphaCoshMajorant_mono_on_one_le hβ2 hle hsum_ge_sqrt
    · have hlt : Real.sqrt t < 1 := lt_of_not_ge hle
      have hinv_one : 1 ≤ (Real.sqrt t)⁻¹ := by
        rw [le_inv_comm₀ zero_lt_one hsqrt_pos]
        simpa using hlt.le
      have hmajor_inv :
          alphaCoshMajorant (2 * β) (Real.sqrt t)⁻¹ ≤
            alphaCoshMajorant (2 * β) (Real.sqrt t + (Real.sqrt t)⁻¹ + 1) :=
        alphaCoshMajorant_mono_on_one_le hβ2 hinv_one hsum_ge_inv
      rwa [alphaCoshMajorant_inv hsqrt_pos] at hmajor_inv
  exact hrem.trans (by simpa [hsq] using hmajor)

/-- The scalar Jensen input in the TCR proof lies in `[3, ∞)`. -/
theorem three_le_sqrt_add_inv_add_one {t : ℝ} (ht : 0 < t) :
    3 ≤ Real.sqrt t + (Real.sqrt t)⁻¹ + 1 := by
  let x : ℝ := Real.sqrt t
  have hx : 0 < x := Real.sqrt_pos.mpr ht
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hsq : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
  have hquad : 2 * x ≤ x ^ 2 + 1 := by nlinarith
  have htwo : 2 ≤ x + x⁻¹ := by
    calc
      2 = (2 * x) / x := by
        field_simp [hx_ne]
      _ ≤ (x ^ 2 + 1) / x :=
        div_le_div_of_nonneg_right hquad hx.le
      _ = x + x⁻¹ := by
        field_simp [hx_ne]
  change 3 ≤ x + x⁻¹ + 1
  linarith

private theorem exp_sub_one_le_div_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.exp x - 1 ≤ x / (1 - x) := by
  have hden_pos : 0 < 1 - x := sub_pos.mpr hx1
  calc
    Real.exp x - 1 ≤ 1 / (1 - x) - 1 := by
      exact sub_le_sub_right (Real.exp_bound_div_one_sub_of_interval hx0 hx1) 1
    _ = x / (1 - x) := by
      field_simp [ne_of_gt hden_pos]
      ring

/-- A reusable Taylor/cosh scalar estimate for small `γ log η`. -/
theorem alphaCoshMajorant_le_quadratic_of_small
    {γ η : ℝ} (hη : 1 < η)
    (hsmall : ((γ * Real.log η) ^ 2) / 2 ≤ 1 - Real.log 2) :
    alphaCoshMajorant γ η ≤ (γ * Real.log η) ^ 2 / Real.log 2 := by
  have _ : 0 < η := lt_trans zero_lt_one hη
  let x : ℝ := γ * Real.log η
  let y : ℝ := x ^ 2 / 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hy_nonneg : 0 ≤ y := by positivity
  have hy_lt_one : y < 1 := by
    change (γ * Real.log η) ^ 2 / 2 < 1
    nlinarith [hsmall, hlog2_pos]
  have hcosh : Real.cosh x - 1 ≤ Real.exp y - 1 := by
    exact sub_le_sub_right (Real.cosh_le_exp_half_sq x) 1
  have hexp : Real.exp y - 1 ≤ y / (1 - y) :=
    exp_sub_one_le_div_one_sub hy_nonneg hy_lt_one
  have hy_denom : Real.log 2 ≤ 1 - y := by
    change Real.log 2 ≤ 1 - x ^ 2 / 2
    nlinarith [hsmall]
  have hfrac : y / (1 - y) ≤ y / Real.log 2 := by
    exact div_le_div_of_nonneg_left hy_nonneg hlog2_pos hy_denom
  calc
    alphaCoshMajorant γ η =
        2 * (Real.cosh x - 1) := by
      simp [alphaCoshMajorant, x]
    _ ≤ 2 * (Real.exp y - 1) := by
      nlinarith
    _ ≤ 2 * (y / (1 - y)) := by
      nlinarith
    _ ≤ 2 * (y / Real.log 2) := by
      nlinarith
    _ = (γ * Real.log η) ^ 2 / Real.log 2 := by
      simp [y, x]
      ring

/-- Final scalar Taylor estimate in the form needed after the TCR Jensen step. -/
theorem alphaCoshMajorant_two_mul_taylor_bound
    {β η : ℝ} (hβ : 0 < β) (hη : 1 < η)
    (hsmall : ((2 * β * Real.log η) ^ 2) / 2 ≤ 1 - Real.log 2) :
    (1 / (β * Real.log 2)) * alphaCoshMajorant (2 * β) η ≤
      4 * β * (log2 η) ^ 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hscale_nonneg : 0 ≤ 1 / (β * Real.log 2) := by positivity
  have hquad :
      alphaCoshMajorant (2 * β) η ≤
        ((2 * β) * Real.log η) ^ 2 / Real.log 2 :=
    alphaCoshMajorant_le_quadratic_of_small hη (by
      simpa [mul_assoc] using hsmall)
  calc
    (1 / (β * Real.log 2)) * alphaCoshMajorant (2 * β) η ≤
        (1 / (β * Real.log 2)) *
          (((2 * β) * Real.log η) ^ 2 / Real.log 2) :=
      mul_le_mul_of_nonneg_left hquad hscale_nonneg
    _ = 4 * β * (log2 η) ^ 2 := by
      rw [log2]
      field_simp [ne_of_gt hβ, ne_of_gt hlog2_pos]
      ring

private theorem cfc_conjStarAlgAut_posDef
    {n : Type u} [Fintype n] [DecidableEq n]
    (u : Matrix.unitaryGroup n ℂ) {A : CMatrix n} (hA : A.PosDef)
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    cfc f (Unitary.conjStarAlgAut ℂ _ u A) =
      Unitary.conjStarAlgAut ℂ _ u (cfc f A) := by
  simpa using
    (StarAlgHomClass.map_cfc
      (Unitary.conjStarAlgAut ℂ (CMatrix n) u) f A
      (hf := hf)
      (hφ := by
        change Continuous fun A : CMatrix n => (u : CMatrix n) * A * star (u : CMatrix n)
        fun_prop)).symm

omit [DecidableEq b] in
private theorem kronecker_one_mul_mul
    (A B C : CMatrix b) :
    Matrix.kronecker (1 : CMatrix a) (A * (B * C)) =
      Matrix.kronecker (1 : CMatrix a) A *
        (Matrix.kronecker (1 : CMatrix a) B *
          Matrix.kronecker (1 : CMatrix a) C) := by
  have hBC :
      Matrix.kronecker (1 : CMatrix a) B * Matrix.kronecker (1 : CMatrix a) C =
        Matrix.kronecker (1 : CMatrix a) (B * C) := by
    simpa using
      (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a) B C).symm
  rw [hBC]
  rw [show Matrix.kronecker (1 : CMatrix a) A *
      Matrix.kronecker (1 : CMatrix a) (B * C) =
        Matrix.kronecker ((1 : CMatrix a) * 1) (A * (B * C)) by
    simpa using
      (Matrix.mul_kronecker_mul (1 : CMatrix a) (1 : CMatrix a) A (B * C)).symm]
  simp

omit [DecidableEq b] in
private theorem kronecker_one_mul_mul_assoc
    (A B C : CMatrix b) :
    Matrix.kronecker (1 : CMatrix a) ((A * B) * C) =
      Matrix.kronecker (1 : CMatrix a) A *
        Matrix.kronecker (1 : CMatrix a) B *
          Matrix.kronecker (1 : CMatrix a) C := by
  rw [show (A * B) * C = A * (B * C) by rw [Matrix.mul_assoc]]
  rw [kronecker_one_mul_mul]
  rw [Matrix.mul_assoc]

/-- Matrix logarithm of the side-reference `I_A ⊗ σ_B`.

For full-rank `σ_B`, the CFC logarithm of the reference matrix used by the
fixed-side conditional Petz entropy is exactly `I_A ⊗ log σ_B`. -/
theorem psdLog_identityTensorStateMatrix
    (σ : State b) (hσ : σ.matrix.PosDef) :
    psdLog (identityTensorStateMatrix (a := a) σ)
        (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ) =
      Matrix.kronecker (1 : CMatrix a) (psdLog σ.matrix hσ) := by
  classical
  let Uσ : Matrix.unitaryGroup b ℂ := hσ.1.eigenvectorUnitary
  let UI : Matrix.unitaryGroup a ℂ := ⟨1, by simp⟩
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (1 : CMatrix a) (Uσ : CMatrix b),
      Matrix.kronecker_mem_unitary UI.2 Uσ.2⟩
  let d : b → ℝ := hσ.1.eigenvalues
  let dside : Prod a b → ℝ := fun i => d i.2
  have hd_pos : ∀ i, 0 < d i := by
    intro i
    exact hσ.eigenvalues_pos i
  have hD_pos : (Matrix.diagonal (fun i => (d i : ℂ)) : CMatrix b).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    exact_mod_cast hd_pos i
  have hDside_pos :
      (Matrix.diagonal (fun i => (dside i : ℂ)) : CMatrix (Prod a b)).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    exact_mod_cast hd_pos i.2
  have hσ_spec :
      σ.matrix =
        Unitary.conjStarAlgAut ℂ _ Uσ (Matrix.diagonal (fun i => (d i : ℂ))) := by
    simpa [Uσ, d, Function.comp_def] using hσ.1.spectral_theorem
  have hside_spec :
      identityTensorStateMatrix (a := a) σ =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => (dside i : ℂ))) := by
    have hDside_kr :
        (Matrix.diagonal (fun i => (dside i : ℂ)) : CMatrix (Prod a b)) =
          Matrix.kronecker (1 : CMatrix a)
            (Matrix.diagonal (fun i => (d i : ℂ)) : CMatrix b) := by
      ext x y
      by_cases h₁ : x.1 = y.1
      · by_cases h₂ : x.2 = y.2
        · simp [dside, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
            Matrix.diagonal, Prod.ext_iff, h₁, h₂]
        · simp [dside, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
            Matrix.diagonal, Prod.ext_iff, h₁, h₂]
      · simp [dside, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.diagonal, Prod.ext_iff, h₁]
    rw [identityTensorStateMatrix, hσ_spec]
    rw [hDside_kr]
    simpa [U, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Matrix.mul_assoc] using
      (kronecker_one_mul_mul_assoc (a := a)
        ((Uσ : CMatrix b))
        (Matrix.diagonal (fun i => (d i : ℂ)) : CMatrix b)
        ((Uσ : CMatrix b)ᴴ))
  have hlogσ :
      psdLog σ.matrix hσ =
        Unitary.conjStarAlgAut ℂ _ Uσ
          (Matrix.diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ))) := by
    rw [psdLog, hσ_spec]
    rw [cfc_conjStarAlgAut_posDef Uσ hD_pos Real.log]
    · rw [cfc_diagonal_ofReal d Real.log]
    · intro x hx
      exact (Real.continuousAt_log
        (ne_of_gt ((Matrix.PosDef.isStrictlyPositive hD_pos).spectrum_pos hx))).continuousWithinAt
  have hlogside :
      psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ) =
        Unitary.conjStarAlgAut ℂ _ U
          (Matrix.diagonal (fun i => ((Real.log (dside i) : ℝ) : ℂ))) := by
    rw [psdLog, hside_spec]
    rw [cfc_conjStarAlgAut_posDef U hDside_pos Real.log]
    · rw [cfc_diagonal_ofReal dside Real.log]
    · intro x hx
      exact (Real.continuousAt_log
        (ne_of_gt ((Matrix.PosDef.isStrictlyPositive hDside_pos).spectrum_pos hx))).continuousWithinAt
  rw [hlogside, hlogσ]
  have hDside_kr :
      (Matrix.diagonal (fun i => ((Real.log (dside i) : ℝ) : ℂ)) : CMatrix (Prod a b)) =
        Matrix.kronecker (1 : CMatrix a)
          (Matrix.diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ)) : CMatrix b) := by
    ext x y
    by_cases h₁ : x.1 = y.1
    · by_cases h₂ : x.2 = y.2
      · simp [dside, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
          Matrix.diagonal, Prod.ext_iff, h₁, h₂]
      · simp [dside, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
          Matrix.diagonal, Prod.ext_iff, h₁, h₂]
    · simp [dside, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.diagonal, Prod.ext_iff, h₁]
  rw [hDside_kr]
  simpa [U, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.mul_assoc] using
    (kronecker_one_mul_mul_assoc (a := a)
      ((Uσ : CMatrix b))
      (Matrix.diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ)) : CMatrix b)
      ((Uσ : CMatrix b)ᴴ)).symm

private theorem posSemidef_eigenvalue_mul_sum_eq_support_sum
    {n : Type u} [Fintype n] [DecidableEq n]
    {M : CMatrix n} (hM : M.PosSemidef) (f : n → ℝ) :
    ∑ i, hM.isHermitian.eigenvalues i * f i =
      ∑ i : psdSupportIndex M hM,
        hM.isHermitian.eigenvalues i.1 * f i.1 := by
  classical
  let d : n → ℝ := hM.isHermitian.eigenvalues
  let g : n → ℝ := fun i => d i * f i
  have hsub :
      (∑ i : psdSupportIndex M hM, d i.1 * f i.1) =
        ∑ i ∈ (Finset.univ : Finset n) with 0 < d i, g i := by
    simpa [d, g] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset n))
        (p := fun i => 0 < d i)
        (f := g))
  have hfilter :
      (∑ i ∈ (Finset.univ : Finset n) with 0 < d i, g i) =
        ∑ i, g i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpos : 0 < d i
    · simp [hpos]
    · have hzero : d i = 0 :=
        le_antisymm (not_lt.mp hpos) (by simpa [d] using hM.eigenvalues_nonneg i)
      simp [hzero, g]
  rw [hsub, hfilter]

/-- Support-restricted `Tr ρ log ρ` term for an arbitrary finite state.

Only positive eigenvalues of `ρ` are indexed, matching the source convention
that zero spectral weights do not contribute (`0 log 0 = 0`) without requiring
a global `psdLog ρ`. -/
def supportEntropyTraceTerm (ρ : State a) : ℝ :=
  ∑ i : psdSupportIndex ρ.matrix ρ.pos,
    ρ.pos.isHermitian.eigenvalues i.1 *
      Real.log (ρ.pos.isHermitian.eigenvalues i.1)

/-- On positive-definite states, the support-restricted entropy trace is the
old matrix-log trace term. -/
theorem supportEntropyTraceTerm_eq_psdLog_trace_of_posDef
    (ρ : State a) (hρ : ρ.matrix.PosDef) :
    ρ.supportEntropyTraceTerm =
      ((ρ.matrix * psdLog ρ.matrix hρ).trace).re := by
  classical
  have htrace := trace_mul_psdLog_eq_sum_eigenvalues_mul_log ρ hρ
  have hHerm : hρ.1 = ρ.pos.isHermitian := Subsingleton.elim _ _
  rw [htrace]
  unfold supportEntropyTraceTerm
  rw [hHerm]
  exact (posSemidef_eigenvalue_mul_sum_eq_support_sum
    (M := ρ.matrix) ρ.pos
    (fun i => Real.log (ρ.pos.isHermitian.eigenvalues i))).symm

/-- The support-restricted entropy trace is the spectral-sum von Neumann
entropy numerator for arbitrary finite states. -/
theorem supportEntropyTraceTerm_eq_neg_vonNeumann_mul_log_two
    (ρ : State a) :
    ρ.supportEntropyTraceTerm = -ρ.vonNeumann * Real.log 2 := by
  classical
  have hsum :
      ρ.supportEntropyTraceTerm =
        ∑ i, ρ.pos.isHermitian.eigenvalues i *
          Real.log (ρ.pos.isHermitian.eigenvalues i) := by
    unfold supportEntropyTraceTerm
    exact (posSemidef_eigenvalue_mul_sum_eq_support_sum
      (M := ρ.matrix) ρ.pos
      (fun i => Real.log (ρ.pos.isHermitian.eigenvalues i))).symm
  have hxlog (i : a) :
      xlog2 (ρ.pos.isHermitian.eigenvalues i) * Real.log 2 =
        ρ.pos.isHermitian.eigenvalues i *
          Real.log (ρ.pos.isHermitian.eigenvalues i) := by
    have hnonneg : 0 ≤ ρ.pos.isHermitian.eigenvalues i :=
      ρ.pos.eigenvalues_nonneg i
    unfold xlog2 log2
    by_cases hzero : ρ.pos.isHermitian.eigenvalues i = 0
    · simp [hzero, Real.log_zero]
    · have hpos : 0 < ρ.pos.isHermitian.eigenvalues i :=
        lt_of_le_of_ne hnonneg (Ne.symm hzero)
      simp [hzero]
      field_simp [(Real.log_pos one_lt_two).ne']
  rw [hsum, State.vonNeumann]
  simp_rw [← hxlog]
  rw [← Finset.sum_mul]
  ring

/-- Fixed-reference conditional von Neumann entropy.

This is the positive-definite matrix-log endpoint
`H(A|B)_{ρ|σ} = -D(ρ_AB ‖ I_A ⊗ σ_B)`, with logarithms in bits.  The second
argument is intentionally the unnormalized reference matrix `I_A ⊗ σ_B`,
matching the fixed-side Petz candidate in `conditionalPetzRenyiEntropyCandidate`.
-/
def conditionalEntropyRelative
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) : ℝ :=
  -(((ρ.matrix * psdLog ρ.matrix hρ).trace.re -
      (ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace.re) /
    Real.log 2)

/-- Support-aware fixed-reference conditional entropy for arbitrary left state
and full-rank reference.

The left `ρ log ρ` term is the support-restricted spectral sum, while the
reference log remains an ordinary matrix logarithm because `σ_B` is full-rank. -/
def conditionalEntropyRelativeFullReference
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) : ℝ :=
  -((ρ.supportEntropyTraceTerm -
      (ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace.re) /
    Real.log 2)

@[simp]
theorem conditionalEntropyRelative_eq
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ρ.conditionalEntropyRelative hρ σ hσ =
      -(((ρ.matrix * psdLog ρ.matrix hρ).trace.re -
          (ρ.matrix *
            psdLog (identityTensorStateMatrix (a := a) σ)
              (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace.re) /
        Real.log 2) :=
  rfl

/-- TCR ordering route, trace-log residual step.

If a normalized conditional-min witness certifies exponent `lam`, then the
remaining ingredient in Tomamichel--Colbeck--Renner's proof is the nonnegativity
of the scaled trace-log residual
`Tr ρ (log(2^{-lam} I_A ⊗ σ_B) - log ρ)`.  After expanding the scalar
`log(2^{-lam})`, this residual has the algebraic form below and implies the
fixed-reference comparison `lam ≤ H(A|B)_{ρ|σ}`.

The later source step is to obtain `htrace` from the feasible operator
inequality by operator monotonicity of the logarithm. -/
theorem conditionalMinEntropyFeasible_le_conditionalEntropyRelative_of_traceLog_nonneg
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) {lam : ℝ}
    (_hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam)
    (htrace :
      0 ≤
        (((ρ.matrix *
            psdLog (identityTensorStateMatrix (a := a) σ)
              (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re -
          ((ρ.matrix * psdLog ρ.matrix hρ).trace).re) - lam * Real.log 2) :
    lam ≤ ρ.conditionalEntropyRelative hρ σ hσ := by
  let A : ℝ := ((ρ.matrix * psdLog ρ.matrix hρ).trace).re
  let B : ℝ :=
    ((ρ.matrix *
      psdLog (identityTensorStateMatrix (a := a) σ)
        (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmul : lam * Real.log 2 ≤ B - A := by
    change 0 ≤ (B - A) - lam * Real.log 2 at htrace
    linarith
  have hmain : lam ≤ (B - A) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    simpa [mul_comm] using hmul
  have hrel : ρ.conditionalEntropyRelative hρ σ hσ = (B - A) / Real.log 2 := by
    rw [conditionalEntropyRelative_eq]
    change -((A - B) / Real.log 2) = (B - A) / Real.log 2
    ring
  rwa [hrel]

/-- TCR ordering route, operator-log residual step.

The conditional-min feasibility inequality
`ρ_AB ≤ 2^{-lam} • (I_A ⊗ σ_B)` implies the nonnegativity of the trace-log
residual used in
`conditionalMinEntropyFeasible_le_conditionalEntropyRelative_of_traceLog_nonneg`,
by operator monotonicity of the CFC logarithm. -/
theorem conditionalMinEntropyFeasible_traceLog_residual_nonneg
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    0 ≤
      (((ρ.matrix *
          psdLog (identityTensorStateMatrix (a := a) σ)
            (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re -
        ((ρ.matrix * psdLog ρ.matrix hρ).trace).re) - lam * Real.log 2 := by
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let c : ℝ := Real.rpow 2 (-lam)
  have hc : 0 < c := by
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lam)
  have hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  have hle : ρ.matrix ≤ (c : ℝ) • τ := by
    simpa [ConditionalMinEntropyFeasible, τ, c] using hfeas
  have hlog_le : CFC.log ρ.matrix ≤ CFC.log ((c : ℝ) • τ) := by
    exact CFC.log_le_log hle (ha := Matrix.PosDef.isStrictlyPositive hρ)
  have hlog_smul :
      CFC.log ((c : ℝ) • τ) =
        algebraMap ℝ (CMatrix (Prod a b)) (Real.log c) + CFC.log τ := by
    exact CFC.log_smul' τ hc (ha := Matrix.PosDef.isStrictlyPositive hτpos)
  have hdiff_pos : (CFC.log ((c : ℝ) • τ) - CFC.log ρ.matrix).PosSemidef := by
    simpa [Matrix.le_iff] using hlog_le
  have htrace_nonneg :
      0 ≤ ((ρ.matrix *
        (CFC.log ((c : ℝ) • τ) - CFC.log ρ.matrix)).trace).re :=
    trace_mul_posSemidef_re_nonneg hρ.posSemidef hdiff_pos
  have htrace_expand :
      ((ρ.matrix * (CFC.log ((c : ℝ) • τ) - CFC.log ρ.matrix)).trace).re =
        ((ρ.matrix * CFC.log τ).trace).re -
          ((ρ.matrix * CFC.log ρ.matrix).trace).re + Real.log c := by
    rw [hlog_smul]
    simp [Matrix.mul_add, Matrix.trace_add, Algebra.algebraMap_eq_smul_one,
      Matrix.trace_smul, ρ.trace_eq_one, add_comm, add_left_comm, sub_eq_add_neg]
  have hlogc : Real.log c = -lam * Real.log 2 := by
    simp [c, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have hmain :
      0 ≤
        ((ρ.matrix * CFC.log τ).trace).re -
          ((ρ.matrix * CFC.log ρ.matrix).trace).re - lam * Real.log 2 := by
    rw [htrace_expand] at htrace_nonneg
    rw [hlogc] at htrace_nonneg
    linarith
  simpa [τ, psdLog, CFC.log, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain

/-- TCR ordering route, fixed-reference entropy comparison.

For positive-definite `ρ_AB` and full-rank side reference `σ_B`, every
normalized conditional-min feasible exponent is bounded above by the
fixed-reference conditional von Neumann entropy. -/
theorem conditionalMinEntropyFeasible_le_conditionalEntropyRelative
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ ρ.conditionalEntropyRelative hρ σ hσ :=
  conditionalMinEntropyFeasible_le_conditionalEntropyRelative_of_traceLog_nonneg
    ρ hρ σ hσ hfeas
    (conditionalMinEntropyFeasible_traceLog_residual_nonneg
      ρ hρ σ hσ hfeas)

/-- Support-aware TCR ordering route, trace-log residual step.

This is the arbitrary-left analogue of
`conditionalMinEntropyFeasible_le_conditionalEntropyRelative_of_traceLog_nonneg`:
the `Tr ρ log ρ` term is replaced by the support-restricted spectral trace. -/
theorem conditionalMinEntropyFeasible_le_conditionalEntropyRelativeFullReference_of_supportTraceLog_nonneg
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) {lam : ℝ}
    (_hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam)
    (htrace :
      0 ≤
        (((ρ.matrix *
            psdLog (identityTensorStateMatrix (a := a) σ)
              (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re -
          ρ.supportEntropyTraceTerm) - lam * Real.log 2) :
    lam ≤ ρ.conditionalEntropyRelativeFullReference σ hσ := by
  let A : ℝ := ρ.supportEntropyTraceTerm
  let B : ℝ :=
    ((ρ.matrix *
      psdLog (identityTensorStateMatrix (a := a) σ)
        (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmul : lam * Real.log 2 ≤ B - A := by
    change 0 ≤ (B - A) - lam * Real.log 2 at htrace
    linarith
  have hmain : lam ≤ (B - A) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    simpa [mul_comm] using hmul
  have hrel : ρ.conditionalEntropyRelativeFullReference σ hσ = (B - A) / Real.log 2 := by
    rw [conditionalEntropyRelativeFullReference]
    change -((A - B) / Real.log 2) = (B - A) / Real.log 2
    ring
  rwa [hrel]

theorem conditionalEntropyRelativeFullReference_eq_conditionalEntropyRelative_of_posDef
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ρ.conditionalEntropyRelativeFullReference σ hσ =
      ρ.conditionalEntropyRelative hρ σ hσ := by
  rw [conditionalEntropyRelativeFullReference, conditionalEntropyRelative_eq,
    supportEntropyTraceTerm_eq_psdLog_trace_of_posDef (ρ := ρ) hρ]

/-- The fixed-reference matrix-log conditional entropy agrees with ordinary
conditional von Neumann entropy once the side-reference trace term has been
identified with the marginal entropy trace term.

For the canonical reference this isolates the remaining tensor-log bridge:
`Tr ρ_AB log(I_A ⊗ ρ_B) = Tr ρ_B log ρ_B`. -/
theorem conditionalEntropyRelative_to_conditionalEntropy_of_reference_trace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef)
    (href :
      ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) ρ.marginalB)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) ρ.marginalB hρB)).trace).re =
        ((ρ.marginalB.matrix * psdLog ρ.marginalB.matrix hρB).trace).re) :
    ρ.conditionalEntropyRelative hρ ρ.marginalB hρB = ρ.conditionalEntropy := by
  rw [conditionalEntropyRelative_eq, conditionalEntropy_eq,
    State.vonNeumann_eq_neg_trace_mul_psdLog_div_log_two ρ hρ,
    State.vonNeumann_eq_neg_trace_mul_psdLog_div_log_two ρ.marginalB hρB,
    href]
  ring

/-- The canonical fixed-reference matrix-log conditional entropy is the usual
conditional von Neumann entropy in the positive-definite case. -/
theorem conditionalEntropyRelative_to_conditionalEntropy
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) :
    ρ.conditionalEntropyRelative hρ ρ.marginalB hρB = ρ.conditionalEntropy := by
  refine
    conditionalEntropyRelative_to_conditionalEntropy_of_reference_trace
      (ρ := ρ) hρ hρB ?_
  rw [psdLog_identityTensorStateMatrix (a := a) ρ.marginalB hρB]
  calc
    ((ρ.matrix *
      Matrix.kronecker (1 : CMatrix a) (psdLog ρ.marginalB.matrix hρB)).trace).re =
        ((Matrix.kronecker (1 : CMatrix a) (psdLog ρ.marginalB.matrix hρB) *
          ρ.matrix).trace).re := by
      rw [Matrix.trace_mul_comm]
    _ = ((psdLog ρ.marginalB.matrix hρB *
          partialTraceA (a := a) (b := b) ρ.matrix).trace).re := by
      rw [trace_kronecker_one_mul_eq_trace_mul_partialTraceA]
    _ = ((psdLog ρ.marginalB.matrix hρB * ρ.marginalB.matrix).trace).re := by
      simp [State.marginalB_matrix]
    _ = ((ρ.marginalB.matrix * psdLog ρ.marginalB.matrix hρB).trace).re := by
      rw [Matrix.trace_mul_comm]

theorem marginalB_posDef_of_posDef
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef) :
    ρ.marginalB.matrix.PosDef := by
  letI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  simpa [State.marginalB_matrix] using
    (partialTraceA_posDef_of_posDef (a := a) (b := b) (M := ρ.matrix) hρ)

/-- Positive-definite quantum relative entropy is nonnegative. -/
theorem relativeEntropy_nonneg_of_posDef
    (ρ σ : State a) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) :
    0 ≤ ρ.relativeEntropyPosDefFinite σ hρ hσ := by
  have hlim :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_posDef_traceLog
      (rho := ρ) (sigma := σ.matrix) hσ
  have hlimRel :
      Filter.Tendsto
        (fun alpha : {alpha : Real // 1 < alpha} =>
          ρ.sandwichedRenyiPSDReferenceHighAlphaFinite σ.matrix hσ.posSemidef alpha.1)
        relativeEntropyHighAlphaRightToOne
        (nhds (ρ.relativeEntropyPosDefFinite σ hρ hσ)) := by
    convert hlim using 1
    rw [relativeEntropyPosDefFinite, vonNeumann_eq_neg_trace_mul_psdLog_div_log_two ρ hρ]
    ring_nf
  haveI : Filter.NeBot relativeEntropyHighAlphaRightToOne :=
    relativeEntropyHighAlphaRightToOne_neBot
  exact ge_of_tendsto hlimRel (Filter.Eventually.of_forall fun alpha => by
    have hnonneg :=
      sandwichedRenyi_nonneg_of_one_lt ρ σ hρ hσ alpha.1 alpha.2
    simpa [sandwichedRenyiPSDReferenceHighAlphaFinite,
      sandwichedRenyi_eq_log2_psdTracePower_inner] using hnonneg)

/-- Fixed-reference conditional entropy is bounded above by the canonical
conditional von Neumann entropy.

Equivalently,
`H(A|B)_{ρ|σ} = H(A|B)_ρ - D(ρ_B ‖ σ)`, and the side relative entropy is
nonnegative for full-rank references. -/
theorem conditionalEntropyRelative_le_conditionalEntropy
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ρ.conditionalEntropyRelative hρ σ hσ ≤ ρ.conditionalEntropy := by
  let hρB : ρ.marginalB.matrix.PosDef := marginalB_posDef_of_posDef ρ hρ
  have hrefσ :
      ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re =
        ((ρ.marginalB.matrix * psdLog σ.matrix hσ).trace).re := by
    rw [psdLog_identityTensorStateMatrix (a := a) σ hσ]
    calc
      ((ρ.matrix * Matrix.kronecker (1 : CMatrix a) (psdLog σ.matrix hσ)).trace).re =
          ((Matrix.kronecker (1 : CMatrix a) (psdLog σ.matrix hσ) *
            ρ.matrix).trace).re := by
        rw [Matrix.trace_mul_comm]
      _ = ((psdLog σ.matrix hσ *
            partialTraceA (a := a) (b := b) ρ.matrix).trace).re := by
        rw [trace_kronecker_one_mul_eq_trace_mul_partialTraceA]
      _ = ((psdLog σ.matrix hσ * ρ.marginalB.matrix).trace).re := by
        simp [State.marginalB_matrix]
      _ = ((ρ.marginalB.matrix * psdLog σ.matrix hσ).trace).re := by
        rw [Matrix.trace_mul_comm]
  have hrel :
      ρ.conditionalEntropyRelative hρ σ hσ =
        ρ.conditionalEntropy - ρ.marginalB.relativeEntropyPosDefFinite σ hρB hσ := by
    rw [conditionalEntropyRelative_eq, conditionalEntropy_eq, relativeEntropyPosDefFinite,
      vonNeumann_eq_neg_trace_mul_psdLog_div_log_two ρ hρ,
      vonNeumann_eq_neg_trace_mul_psdLog_div_log_two ρ.marginalB hρB,
      hrefσ]
    ring
  have hD : 0 ≤ ρ.marginalB.relativeEntropyPosDefFinite σ hρB hσ :=
    relativeEntropy_nonneg_of_posDef ρ.marginalB σ hρB hσ
  rw [hrel]
  linarith

/-- Support-aware fixed-reference conditional entropy is bounded above by the
canonical conditional von Neumann entropy.

This is the arbitrary-left analogue of
`conditionalEntropyRelative_le_conditionalEntropy`: the relative-entropy term
on the side system is nonnegative by the source-limit PSD-reference DPI
endpoint, so replacing the side reference by an arbitrary full-rank `σ_B` can
only decrease `H(A|B)`. -/
theorem conditionalEntropyRelativeFullReference_le_conditionalEntropy
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) :
    ρ.conditionalEntropyRelativeFullReference σ hσ ≤ ρ.conditionalEntropy := by
  have hrefσ :
      ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re =
        ((ρ.marginalB.matrix * psdLog σ.matrix hσ).trace).re := by
    rw [psdLog_identityTensorStateMatrix (a := a) σ hσ]
    calc
      ((ρ.matrix * Matrix.kronecker (1 : CMatrix a) (psdLog σ.matrix hσ)).trace).re =
          ((Matrix.kronecker (1 : CMatrix a) (psdLog σ.matrix hσ) *
            ρ.matrix).trace).re := by
        rw [Matrix.trace_mul_comm]
      _ = ((psdLog σ.matrix hσ *
            partialTraceA (a := a) (b := b) ρ.matrix).trace).re := by
        rw [trace_kronecker_one_mul_eq_trace_mul_partialTraceA]
      _ = ((psdLog σ.matrix hσ * ρ.marginalB.matrix).trace).re := by
        simp [State.marginalB_matrix]
      _ = ((ρ.marginalB.matrix * psdLog σ.matrix hσ).trace).re := by
        rw [Matrix.trace_mul_comm]
  have hsupport :
      ρ.supportEntropyTraceTerm = -ρ.vonNeumann * Real.log 2 :=
    ρ.supportEntropyTraceTerm_eq_neg_vonNeumann_mul_log_two
  have hD := relativeEntropy_posDefReferenceTraceLog_nonneg ρ.marginalB σ hσ
  rw [conditionalEntropyRelativeFullReference, conditionalEntropy_eq, hrefσ, hsupport]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog] at hD ⊢
  linarith

theorem conditionalMinEntropyFeasible_le_conditionalEntropy_of_supportTraceLog_nonneg
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam)
    (htrace :
      0 ≤
        (((ρ.matrix *
            psdLog (identityTensorStateMatrix (a := a) σ)
              (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re -
          ρ.supportEntropyTraceTerm) - lam * Real.log 2) :
    lam ≤ ρ.conditionalEntropy := by
  exact
    (conditionalMinEntropyFeasible_le_conditionalEntropyRelativeFullReference_of_supportTraceLog_nonneg
      ρ σ hσ hfeas htrace).trans
      (conditionalEntropyRelativeFullReference_le_conditionalEntropy ρ σ hσ)

/-- Canonical-reference ordering used by the source upper half.

For a positive-definite bipartite state whose side marginal is full rank, every
conditional-min exponent feasible with the canonical reference `ρ_B` is bounded
above by the ordinary conditional von Neumann entropy.  This is the
source-aligned fixed-reference form of `H_min(A|B)_ρ ≤ H(A|B)_ρ`; passing from
the optimized supremum over all side references to this canonical witness is a
separate endpoint/attainment step. -/
theorem conditionalMinEntropyFeasible_canonical_le_conditionalEntropy
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ ρ.marginalB lam) :
    lam ≤ ρ.conditionalEntropy := by
  exact
    (conditionalMinEntropyFeasible_le_conditionalEntropyRelative
      ρ hρ ρ.marginalB hρB hfeas).trans_eq
      (conditionalEntropyRelative_to_conditionalEntropy ρ hρ hρB)

/-- The support-aware canonical fixed-reference entropy is the ordinary
conditional von Neumann entropy.  Only the side marginal is required to be
full rank. -/
theorem conditionalEntropyRelativeFullReference_to_conditionalEntropy
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef) :
    ρ.conditionalEntropyRelativeFullReference ρ.marginalB hρB =
      ρ.conditionalEntropy := by
  have href :
      ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) ρ.marginalB)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) ρ.marginalB hρB)).trace).re =
        ((ρ.marginalB.matrix * psdLog ρ.marginalB.matrix hρB).trace).re := by
    rw [psdLog_identityTensorStateMatrix (a := a) ρ.marginalB hρB]
    calc
      ((ρ.matrix *
        Matrix.kronecker (1 : CMatrix a) (psdLog ρ.marginalB.matrix hρB)).trace).re =
          ((Matrix.kronecker (1 : CMatrix a) (psdLog ρ.marginalB.matrix hρB) *
            ρ.matrix).trace).re := by
        rw [Matrix.trace_mul_comm]
      _ = ((psdLog ρ.marginalB.matrix hρB *
            partialTraceA (a := a) (b := b) ρ.matrix).trace).re := by
        rw [trace_kronecker_one_mul_eq_trace_mul_partialTraceA]
      _ = ((psdLog ρ.marginalB.matrix hρB * ρ.marginalB.matrix).trace).re := by
        simp [State.marginalB_matrix]
      _ = ((ρ.marginalB.matrix * psdLog ρ.marginalB.matrix hρB).trace).re := by
        rw [Matrix.trace_mul_comm]
  have hsupport :
      ρ.supportEntropyTraceTerm = -ρ.vonNeumann * Real.log 2 :=
    ρ.supportEntropyTraceTerm_eq_neg_vonNeumann_mul_log_two
  have hmarg :
      ρ.marginalB.vonNeumann =
        -((ρ.marginalB.matrix * psdLog ρ.marginalB.matrix hρB).trace.re) /
          Real.log 2 :=
    State.vonNeumann_eq_neg_trace_mul_psdLog_div_log_two ρ.marginalB hρB
  have href_vn :
      ((ρ.marginalB.matrix * psdLog ρ.marginalB.matrix hρB).trace.re) =
        -ρ.marginalB.vonNeumann * Real.log 2 := by
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    rw [hmarg]
    field_simp [hlog]
  rw [conditionalEntropyRelativeFullReference, conditionalEntropy_eq, href,
    hsupport, href_vn]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog]
  ring

/-- Canonical fixed-reference conditional entropy is additive on grouped
IID tensor powers, with no full-rank assumption on the joint state. -/
theorem tensorPowerBipartite_conditionalEntropyRelativeFullReference_canonical
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef) (n : ℕ)
    (hρnB : (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef) :
    (ρ.tensorPowerBipartite n).conditionalEntropyRelativeFullReference
        (ρ.tensorPowerBipartite n).marginalB hρnB =
      (n : ℝ) *
        ρ.conditionalEntropyRelativeFullReference ρ.marginalB hρB := by
  rw [
    conditionalEntropyRelativeFullReference_to_conditionalEntropy
      (ρ := ρ.tensorPowerBipartite n) hρnB,
    conditionalEntropyRelativeFullReference_to_conditionalEntropy
      (ρ := ρ) hρB]
  have hAB :
      State.vonNeumann (ρ.tensorPowerBipartite n) =
        State.vonNeumann (ρ.tensorPower n) := by
    change State.vonNeumann
        ((ρ.tensorPower n).reindex (tensorPowerProdEquiv a b n)) =
      State.vonNeumann (ρ.tensorPower n)
    rw [State.vonNeumann_reindex]
  rw [conditionalEntropy_eq, conditionalEntropy_eq, hAB]
  rw [State.tensorPowerBipartite_marginalB]
  rw [State.vonNeumann_tensorPower, State.vonNeumann_tensorPower]
  ring

/-- Fixed-reference Petz trace at `α = 1 + β`, expanded in the eigenbasis of
the side reference `τ = I_A ⊗ σ_B`.

This is the first matrix-route bridge for TCR Lemma `alpha-bound`: the
noncommutative trace term is reduced to diagonal weights against the spectral
values of the fixed reference. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_reference_eigenbasis_sum
    (ρ : State (Prod a b)) (σ : State b) (β : ℝ) :
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτ : τ.PosSemidef := identityTensorStateMatrix_posSemidef_of_state (a := a) σ
    let U : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      ∑ i,
        ((star (U : CMatrix (Prod a b)) *
          CFC.rpow ρ.matrix (1 + β) * (U : CMatrix (Prod a b))) i i).re *
          hτ.isHermitian.eigenvalues i ^ (-β) := by
  classical
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτ : τ.PosSemidef := identityTensorStateMatrix_posSemidef_of_state (a := a) σ
  have h :=
    trace_mul_cMatrix_rpow_eq_conjugate_diag_sum
      (M := CFC.rpow ρ.matrix (1 + β)) (N := τ) hτ (-β)
  simpa [conditionalPetzRenyiTraceTerm, τ, hτ, sub_eq_add_neg] using h

/-- Matrix-log endpoint against the side reference `τ = I_A ⊗ σ_B`, expanded
in the same reference eigenbasis as
`conditionalPetzRenyiTraceTerm_one_add_eq_reference_eigenbasis_sum`. -/
theorem trace_mul_psdLog_identityTensorStateMatrix_eq_reference_eigenbasis_sum
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) :
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let U : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    ((ρ.matrix *
      psdLog (identityTensorStateMatrix (a := a) σ)
        (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re =
      ∑ i,
        ((star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))) i i).re *
          Real.log (hτ.isHermitian.eigenvalues i) := by
  classical
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let U : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let D : CMatrix (Prod a b) :=
    Matrix.diagonal fun i => ((Real.log (hτ.isHermitian.eigenvalues i) : ℝ) : ℂ)
  have hlog :
      psdLog τ hτpos = (U : CMatrix (Prod a b)) * D * star (U : CMatrix (Prod a b)) := by
    rw [psdLog, hτpos.1.cfc_eq]
    simp [U, D, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def]
  have htrace :
      (ρ.matrix * psdLog τ hτpos).trace =
        ((star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))) *
          D).trace := by
    rw [hlog]
    calc
      (ρ.matrix * ((U : CMatrix (Prod a b)) * D * star (U : CMatrix (Prod a b)))).trace
          = (((ρ.matrix * (U : CMatrix (Prod a b))) * D) *
              star (U : CMatrix (Prod a b))).trace := by
            noncomm_ring
      _ = (star (U : CMatrix (Prod a b)) *
            ((ρ.matrix * (U : CMatrix (Prod a b))) * D)).trace := by
            exact Matrix.trace_mul_comm
              (((ρ.matrix * (U : CMatrix (Prod a b))) * D))
              (star (U : CMatrix (Prod a b)))
      _ = ((star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))) *
            D).trace := by
            noncomm_ring
  have hdiag :
      (((star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))) *
        D).trace).re =
        ∑ i,
          ((star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))) i i).re *
            Real.log (hτ.isHermitian.eigenvalues i) := by
    simp [D, Matrix.trace, Matrix.diagonal, Matrix.mul_apply, Complex.mul_re]
  change ((ρ.matrix * psdLog τ hτpos).trace).re =
    ∑ i,
      ((star (U : CMatrix (Prod a b)) * ρ.matrix * (U : CMatrix (Prod a b))) i i).re *
        Real.log (hτ.isHermitian.eigenvalues i)
  rw [htrace]
  exact hdiag

private theorem unitary_conj_rpow_diagonal_re_eq_eigenvalue_sum
    {n : Type u} [Fintype n] [DecidableEq n]
    {M : CMatrix n} (hM : M.PosSemidef)
    (U : Matrix.unitaryGroup n ℂ) (s : ℝ) (i : n) :
    ((star (U : CMatrix n) * CFC.rpow M s * (U : CMatrix n)) i i).re =
      ∑ j, hM.isHermitian.eigenvalues j ^ s *
        Complex.normSq ((star (hM.isHermitian.eigenvectorUnitary : CMatrix n) *
          (U : CMatrix n)) j i) := by
  classical
  let V : Matrix.unitaryGroup n ℂ := hM.isHermitian.eigenvectorUnitary
  let D : CMatrix n := Matrix.diagonal
    (fun j => ((hM.isHermitian.eigenvalues j ^ s : ℝ) : ℂ))
  let W : CMatrix n := star (V : CMatrix n) * (U : CMatrix n)
  have diagonal_star_mul_diagonal_mul_re
      (W : CMatrix n) (d : n → ℝ) (i : n) :
      ((star W * Matrix.diagonal (fun j => ((d j : ℝ) : ℂ)) * W) i i).re =
        ∑ j, d j * Complex.normSq (W j i) := by
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.star_apply, Complex.normSq_apply,
      mul_comm]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpow : CFC.rpow M s = (V : CMatrix n) * D * star (V : CMatrix n) := by
    simpa [V, D] using cMatrix_rpow_eq_eigenbasis_diagonal hM s
  have hconj :
      star (U : CMatrix n) * ((V : CMatrix n) * D * star (V : CMatrix n)) *
          (U : CMatrix n) =
        star W * D * W := by
    simp [W, Matrix.mul_assoc]
  rw [hpow]
  rw [hconj]
  simpa [D, W] using
    diagonal_star_mul_diagonal_mul_re W
      (fun j => hM.isHermitian.eigenvalues j ^ s) i

/-- Fixed-reference Petz trace at `α = 1 + β`, expanded in the eigenbases of
both the arbitrary state `ρ` and the full-rank side reference `τ = I_A ⊗ σ_B`.

This is the PSD-left version of
`conditionalPetzRenyiTraceTerm_one_add_eq_double_eigenbasis_sum`; it does not
ask for a positive-definite witness for `ρ`. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_double_eigenbasis_sum_psdLeft
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      ∑ i,
        (∑ j,
          hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
          hτ.isHermitian.eigenvalues i ^ (-β) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have htrace :
      ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
        ∑ i,
          ((star (Uτ : CMatrix (Prod a b)) *
            CFC.rpow ρ.matrix (1 + β) *
              (Uτ : CMatrix (Prod a b))) i i).re *
            hτ.isHermitian.eigenvalues i ^ (-β) := by
    have h :=
      trace_mul_cMatrix_rpow_eq_conjugate_diag_sum
        (M := CFC.rpow ρ.matrix (1 + β)) (N := τ) hτ (-β)
    simpa [conditionalPetzRenyiTraceTerm, τ, hτ, Uτ, sub_eq_add_neg] using h
  have hdiag (i : Prod a b) :
      ((star (Uτ : CMatrix (Prod a b)) *
        CFC.rpow ρ.matrix (1 + β) *
          (Uτ : CMatrix (Prod a b))) i i).re =
        ∑ j,
          hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i) := by
    simpa [hρpsd, Uρ] using
      unitary_conj_rpow_diagonal_re_eq_eigenvalue_sum
        (M := ρ.matrix) hρpsd Uτ (1 + β) i
  rw [htrace]
  simp_rw [hdiag]
  rfl

private theorem rpow_one_add_mul_rpow_neg_eq_mul_div_rpow_of_nonneg_left
    {x y β : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hβ : 0 < β) :
    x ^ (1 + β) * y ^ (-β) = x * (x / y) ^ β := by
  by_cases hxzero : x = 0
  · subst x
    have hβ_ne : (1 + β : ℝ) ≠ 0 := by positivity
    simp [Real.zero_rpow hβ_ne]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    have hxy : 0 < x / y := div_pos hxpos hy
    calc
      x ^ (1 + β) * y ^ (-β)
          = Real.exp ((1 + β) * Real.log x) *
              Real.exp ((-β) * Real.log y) := by
            rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hy]
            ring_nf
      _ = Real.exp (Real.log x + β * (Real.log x - Real.log y)) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ = x * Real.exp (β * Real.log (x / y)) := by
            rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hy), Real.exp_add,
              Real.exp_log hxpos]
      _ = x * (x / y) ^ β := by
            rw [Real.rpow_def_of_pos hxy]
            ring_nf

/-- Ratio form of the PSD-left double-eigenbasis expansion for positive
`β`. Zero eigenvalues of `ρ` contribute zero weight. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_eigenvalue_ratio_sum_psdLeft
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) (hβ : 0 < β) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      ∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hdouble :=
    conditionalPetzRenyiTraceTerm_one_add_eq_double_eigenbasis_sum_psdLeft
      (ρ := ρ) (σ := σ) hσ β
  change
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      ∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β
  rw [hdouble]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hρeig_nonneg : 0 ≤ hρpsd.isHermitian.eigenvalues j :=
    hρpsd.eigenvalues_nonneg j
  have hτeig_pos : 0 < hτ.isHermitian.eigenvalues i := by
    simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos i
  have hratio :=
    rpow_one_add_mul_rpow_neg_eq_mul_div_rpow_of_nonneg_left
      (x := hρpsd.isHermitian.eigenvalues j)
      (y := hτ.isHermitian.eigenvalues i)
      (β := β) hρeig_nonneg hτeig_pos hβ
  calc
    (hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
      Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
        (Uτ : CMatrix (Prod a b))) j i)) *
        hτ.isHermitian.eigenvalues i ^ (-β)
        =
      (hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
        hτ.isHermitian.eigenvalues i ^ (-β)) *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i) := by
          ring
    _ =
      (hρpsd.isHermitian.eigenvalues j *
        (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β) *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i) := by
          rw [hratio]
    _ =
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β := by
          ring

/-- Ratio form restricted to the positive spectral support of the arbitrary
left state. This is the source-aligned form: all ratios are formed only where
the `ρ` eigenvalue is strictly positive. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_support_eigenvalue_ratio_sum
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) (hβ : 0 < β) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) ^ β := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hall :=
    conditionalPetzRenyiTraceTerm_one_add_eq_eigenvalue_ratio_sum_psdLeft
      (ρ := ρ) (σ := σ) hσ β hβ
  rw [hall]
  apply Finset.sum_congr rfl
  intro i _
  have hsupport :=
    posSemidef_eigenvalue_mul_sum_eq_support_sum
      (M := ρ.matrix) hρpsd
      (fun j =>
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i) *
        (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hsupport

/-- The `α = 1/2` trace term in support-ratio variables.

This is the negative-half counterpart needed for the arbitrary-left `Upsilon`.
The statement is specialized because the all-eigenvalue ratio theorem cannot
form negative powers at zero left eigenvalues. -/
theorem conditionalPetzRenyiTraceTerm_half_eq_support_inv_sqrt_sum
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 / 2) =
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          (Real.sqrt
            (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹ := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hdouble :=
    conditionalPetzRenyiTraceTerm_one_add_eq_double_eigenbasis_sum_psdLeft
      (ρ := ρ) (σ := σ) hσ (β := -(1 / 2 : ℝ))
  have hrestrict (i : Prod a b) :
      ∑ j,
        hρpsd.isHermitian.eigenvalues j ^ (1 / 2 : ℝ) *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i) =
        ∑ j : psdSupportIndex ρ.matrix hρpsd,
          hρpsd.isHermitian.eigenvalues j.1 ^ (1 / 2 : ℝ) *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i) := by
    let d : Prod a b → ℝ := hρpsd.isHermitian.eigenvalues
    let g : Prod a b → ℝ := fun j =>
      d j ^ (1 / 2 : ℝ) *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)
    have hsub :
        (∑ j : psdSupportIndex ρ.matrix hρpsd,
          d j.1 ^ (1 / 2 : ℝ) *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) =
          ∑ j ∈ (Finset.univ : Finset (Prod a b)) with 0 < d j, g j := by
      simpa [d, g] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset (Prod a b)))
          (p := fun j => 0 < d j)
          (f := g))
    have hfilter :
        (∑ j ∈ (Finset.univ : Finset (Prod a b)) with 0 < d j, g j) =
          ∑ j, g j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hpos : 0 < d j
      · simp [hpos]
      · have hzero : d j = 0 :=
          le_antisymm (not_lt.mp hpos) (by simpa [d] using hρpsd.eigenvalues_nonneg j)
        simp [hzero, g]
    rw [hsub, hfilter]
  change
    ρ.conditionalPetzRenyiTraceTerm σ (1 / 2) =
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          (Real.sqrt
            (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹
  rw [show (1 / 2 : ℝ) = 1 + -(1 / 2 : ℝ) by ring]
  rw [hdouble]
  norm_num
  apply Finset.sum_congr rfl
  intro i _
  rw [hrestrict i]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues j.1 := j.2
  have hτeig_pos : 0 < hτ.isHermitian.eigenvalues i := by
    simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos i
  have hratio_pos :
      0 < hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i :=
    div_pos hρeig_pos hτeig_pos
  have hsqrt_pos :
      0 < Real.sqrt (hρpsd.isHermitian.eigenvalues j.1 /
        hτ.isHermitian.eigenvalues i) :=
    Real.sqrt_pos.2 hratio_pos
  calc
    (hρpsd.isHermitian.eigenvalues j.1 ^ (1 / 2 : ℝ) *
      Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
        (Uτ : CMatrix (Prod a b))) j.1 i)) *
        hτ.isHermitian.eigenvalues i ^ (1 / 2 : ℝ)
        =
      (Real.sqrt (hρpsd.isHermitian.eigenvalues j.1) *
        Real.sqrt (hτ.isHermitian.eigenvalues i)) *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i) := by
          rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
          ring
    _ =
      (hρpsd.isHermitian.eigenvalues j.1 *
        (Real.sqrt
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹) *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i) := by
          have hsqrt_div :
              Real.sqrt (hρpsd.isHermitian.eigenvalues j.1 /
                hτ.isHermitian.eigenvalues i) =
                Real.sqrt (hρpsd.isHermitian.eigenvalues j.1) /
                  Real.sqrt (hτ.isHermitian.eigenvalues i) := by
            rw [Real.sqrt_div hρeig_pos.le]
          rw [hsqrt_div]
          field_simp [Real.sqrt_pos.2 hρeig_pos, Real.sqrt_pos.2 hτeig_pos,
            hsqrt_pos]
          rw [Real.sq_sqrt hρeig_pos.le]
          ring_nf
    _ =
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        (Real.sqrt
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹ := by
          ring

/-- Fixed-reference Petz trace at `α = 1 + β`, expanded in the eigenbases of
both the state `ρ` and the side reference `τ = I_A ⊗ σ_B`.

The coefficients are the squared overlaps between the two eigenbases. This is
the finite matrix-route replacement for the source proof's purification
spectral random variable. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_double_eigenbasis_sum
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      ∑ i,
        (∑ j,
          hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
          hτ.isHermitian.eigenvalues i ^ (-β) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have htrace :
      ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
        ∑ i,
          ((star (Uτ : CMatrix (Prod a b)) *
            CFC.rpow ρ.matrix (1 + β) *
              (Uτ : CMatrix (Prod a b))) i i).re *
            hτ.isHermitian.eigenvalues i ^ (-β) := by
    have h :=
      trace_mul_cMatrix_rpow_eq_conjugate_diag_sum
        (M := CFC.rpow ρ.matrix (1 + β)) (N := τ) hτ (-β)
    simpa [conditionalPetzRenyiTraceTerm, τ, hτ, Uτ, sub_eq_add_neg] using h
  have hdiag (i : Prod a b) :
      ((star (Uτ : CMatrix (Prod a b)) *
        CFC.rpow ρ.matrix (1 + β) *
          (Uτ : CMatrix (Prod a b))) i i).re =
        ∑ j,
          hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i) := by
    simpa [hρpsd, Uρ] using
      unitary_conj_rpow_diagonal_re_eq_eigenvalue_sum
        (M := ρ.matrix) hρpsd Uτ (1 + β) i
  rw [htrace]
  simp_rw [hdiag]
  change
    (∑ i,
      (∑ j,
        hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
        hτ.isHermitian.eigenvalues i ^ (-β)) =
    (∑ i,
      (∑ j,
        hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
        hτ.isHermitian.eigenvalues i ^ (-β))
  rfl

private theorem rpow_one_add_mul_rpow_neg_eq_mul_div_rpow
    {x y β : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ (1 + β) * y ^ (-β) = x * (x / y) ^ β := by
  have hxy : 0 < x / y := div_pos hx hy
  calc
    x ^ (1 + β) * y ^ (-β)
        = Real.exp ((1 + β) * Real.log x) *
            Real.exp ((-β) * Real.log y) := by
          rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy]
          ring_nf
    _ = Real.exp (Real.log x + β * (Real.log x - Real.log y)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ = x * Real.exp (β * Real.log (x / y)) := by
          rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy), Real.exp_add,
            Real.exp_log hx]
    _ = x * (x / y) ^ β := by
          rw [Real.rpow_def_of_pos hxy]
          ring_nf

/-- Ratio form of
`conditionalPetzRenyiTraceTerm_one_add_eq_double_eigenbasis_sum`.

The finite sum now exposes the scalar ratios `λ_ρ / λ_τ`, the variables to
which the TCR scalar remainder `r_β` is applied in the next step. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_eigenvalue_ratio_sum
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      ∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hdouble :=
    conditionalPetzRenyiTraceTerm_one_add_eq_double_eigenbasis_sum
      (ρ := ρ) hρ (σ := σ) hσ β
  change
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      ∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β
  rw [hdouble]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues j := by
    simpa [hρpsd] using hρ.eigenvalues_pos j
  have hτeig_pos : 0 < hτ.isHermitian.eigenvalues i := by
    simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos i
  have hratio :=
    rpow_one_add_mul_rpow_neg_eq_mul_div_rpow
      (x := hρpsd.isHermitian.eigenvalues j)
      (y := hτ.isHermitian.eigenvalues i)
      (β := β) hρeig_pos hτeig_pos
  change
    (hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
      Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
        (Uτ : CMatrix (Prod a b))) j i)) *
        hτ.isHermitian.eigenvalues i ^ (-β) =
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β
  calc
    (hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
      Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
        (Uτ : CMatrix (Prod a b))) j i)) *
        hτ.isHermitian.eigenvalues i ^ (-β)
        =
      (hρpsd.isHermitian.eigenvalues j ^ (1 + β) *
        hτ.isHermitian.eigenvalues i ^ (-β)) *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i) := by
          ring
    _ =
      (hρpsd.isHermitian.eigenvalues j *
        (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β) *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i) := by
          rw [hratio]
    _ =
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β := by
          ring

/-- The overlap weights used in the double-eigenbasis expansion of the Petz
trace form a probability distribution. -/
theorem conditionalPetzRenyi_eigenbasis_weight_sum_eq_one
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j,
      hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i) = 1 := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  let W : Matrix.unitaryGroup (Prod a b) ℂ := Uρ⁻¹ * Uτ
  have hW (j i : Prod a b) :
      ((W : CMatrix (Prod a b)) j i) =
        ((star (Uρ : CMatrix (Prod a b)) * (Uτ : CMatrix (Prod a b))) j i) := by
    simp [W, Uρ, Uτ]
  have heig_sum : ∑ j : Prod a b, hρpsd.isHermitian.eigenvalues j = 1 := by
    have htrace := congrArg Complex.re hρpsd.isHermitian.trace_eq_sum_eigenvalues
    rw [ρ.trace_eq_one] at htrace
    norm_num at htrace
    exact htrace.symm
  calc
    ∑ i, ∑ j,
      hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)
        =
      ∑ j, hρpsd.isHermitian.eigenvalues j *
        ∑ i, Complex.normSq ((W : CMatrix (Prod a b)) j i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          simp_rw [← hW j]
          rw [Finset.mul_sum]
    _ = ∑ j : Prod a b, hρpsd.isHermitian.eigenvalues j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [unitary_row_normSq_sum W j]
          ring
    _ = 1 := heig_sum

/-- The `ρ`-eigenvalue part of the weighted log-ratio sum is `Tr ρ log ρ`. -/
theorem conditionalPetzRenyi_eigenbasis_weight_log_state_sum
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        Real.log (hρpsd.isHermitian.eigenvalues j) =
      ((ρ.matrix * psdLog ρ.matrix hρ).trace).re := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  let W : Matrix.unitaryGroup (Prod a b) ℂ := Uρ⁻¹ * Uτ
  have hW (j i : Prod a b) :
      ((W : CMatrix (Prod a b)) j i) =
        ((star (Uρ : CMatrix (Prod a b)) * (Uτ : CMatrix (Prod a b))) j i) := by
    simp [W, Uρ, Uτ]
  have htrace := trace_mul_psdLog_eq_sum_eigenvalues_mul_log ρ hρ
  calc
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        Real.log (hρpsd.isHermitian.eigenvalues j)
        =
      ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Real.log (hρpsd.isHermitian.eigenvalues j)) *
          ∑ i, Complex.normSq ((W : CMatrix (Prod a b)) j i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          simp_rw [← hW j]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ =
      ∑ j : Prod a b,
        hρpsd.isHermitian.eigenvalues j *
          Real.log (hρpsd.isHermitian.eigenvalues j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [unitary_row_normSq_sum W j]
          ring
    _ = ((ρ.matrix * psdLog ρ.matrix hρ).trace).re := by
          rw [htrace]

/-- The reference-eigenvalue part of the weighted log-ratio sum is
`Tr ρ log (I_A ⊗ σ_B)`. -/
theorem conditionalPetzRenyi_eigenbasis_weight_log_reference_sum
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        Real.log (hτ.isHermitian.eigenvalues i) =
      ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have href :=
    trace_mul_psdLog_identityTensorStateMatrix_eq_reference_eigenbasis_sum
      (ρ := ρ) (σ := σ) hσ
  have hdiag (i : Prod a b) :
      ((star (Uτ : CMatrix (Prod a b)) * ρ.matrix *
        (Uτ : CMatrix (Prod a b))) i i).re =
        ∑ j,
          hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i) := by
    have h :=
      unitary_conj_rpow_diagonal_re_eq_eigenvalue_sum
        (M := ρ.matrix) hρpsd Uτ (1 : ℝ) i
    simpa [hρpsd, Uρ, Real.rpow_one,
      CFC.rpow_one ρ.matrix (ha := Matrix.nonneg_iff_posSemidef.mpr hρpsd)] using h
  calc
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        Real.log (hτ.isHermitian.eigenvalues i)
        =
      ∑ i,
        ((star (Uτ : CMatrix (Prod a b)) * ρ.matrix *
          (Uτ : CMatrix (Prod a b))) i i).re *
          Real.log (hτ.isHermitian.eigenvalues i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hdiag i]
          rw [Finset.sum_mul]
    _ = ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re := by
          rw [href]

/-- Weighted logarithms of eigenvalue ratios give the matrix-log numerator
`Tr ρ log ρ - Tr ρ log(I_A ⊗ σ_B)`. -/
theorem conditionalPetzRenyi_eigenbasis_weight_log_ratio_sum
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        Real.log
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) =
      ((ρ.matrix * psdLog ρ.matrix hρ).trace).re -
        ((ρ.matrix *
          psdLog (identityTensorStateMatrix (a := a) σ)
            (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hstate :=
    conditionalPetzRenyi_eigenbasis_weight_log_state_sum
      (ρ := ρ) hρ (σ := σ) hσ
  have href :=
    conditionalPetzRenyi_eigenbasis_weight_log_reference_sum
      (ρ := ρ) hρ (σ := σ) hσ
  have hsplit :
      ∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          Real.log
            (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) =
        (∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            Real.log (hρpsd.isHermitian.eigenvalues j)) -
          (∑ i, ∑ j,
            (hρpsd.isHermitian.eigenvalues j *
              Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                (Uτ : CMatrix (Prod a b))) j i)) *
              Real.log (hτ.isHermitian.eigenvalues i)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues j := by
      simpa [hρpsd] using hρ.eigenvalues_pos j
    have hτeig_pos : 0 < hτ.isHermitian.eigenvalues i := by
      simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos i
    rw [Real.log_div (ne_of_gt hρeig_pos) (ne_of_gt hτeig_pos)]
    ring
  change
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        Real.log
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) =
      ((ρ.matrix * psdLog ρ.matrix hρ).trace).re -
        ((ρ.matrix *
          psdLog (identityTensorStateMatrix (a := a) σ)
            (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re
  rw [hsplit, hstate, href]

/-- The support-restricted overlap weights used in the arbitrary-left
double-eigenbasis expansion form a probability distribution. -/
theorem conditionalPetzRenyi_eigenbasis_support_weight_sum_eq_one
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i) = 1 := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  let W : Matrix.unitaryGroup (Prod a b) ℂ := Uρ⁻¹ * Uτ
  have hW (j i : Prod a b) :
      ((W : CMatrix (Prod a b)) j i) =
        ((star (Uρ : CMatrix (Prod a b)) * (Uτ : CMatrix (Prod a b))) j i) := by
    simp [W, Uρ, Uτ]
  have heig_sum : ∑ j : Prod a b, hρpsd.isHermitian.eigenvalues j = 1 := by
    have htrace := congrArg Complex.re hρpsd.isHermitian.trace_eq_sum_eigenvalues
    rw [ρ.trace_eq_one] at htrace
    norm_num at htrace
    exact htrace.symm
  calc
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)
        =
      ∑ j : psdSupportIndex ρ.matrix hρpsd,
        hρpsd.isHermitian.eigenvalues j.1 *
          ∑ i, Complex.normSq ((W : CMatrix (Prod a b)) j.1 i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          simp_rw [← hW j.1]
          rw [Finset.mul_sum]
    _ = ∑ j : psdSupportIndex ρ.matrix hρpsd,
        hρpsd.isHermitian.eigenvalues j.1 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [unitary_row_normSq_sum W j.1]
          ring
    _ = ∑ j : Prod a b, hρpsd.isHermitian.eigenvalues j := by
          simpa using
            (posSemidef_eigenvalue_mul_sum_eq_support_sum
              (M := ρ.matrix) hρpsd (fun _ => 1)).symm
    _ = 1 := heig_sum

/-- The support-restricted `ρ`-eigenvalue logarithm part of the weighted
log-ratio sum is the arbitrary-state support entropy trace. -/
theorem conditionalPetzRenyi_eigenbasis_support_weight_log_state_sum
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        Real.log (hρpsd.isHermitian.eigenvalues j.1) =
      ρ.supportEntropyTraceTerm := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  let W : Matrix.unitaryGroup (Prod a b) ℂ := Uρ⁻¹ * Uτ
  have hW (j i : Prod a b) :
      ((W : CMatrix (Prod a b)) j i) =
        ((star (Uρ : CMatrix (Prod a b)) * (Uτ : CMatrix (Prod a b))) j i) := by
    simp [W, Uρ, Uτ]
  calc
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        Real.log (hρpsd.isHermitian.eigenvalues j.1)
        =
      ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Real.log (hρpsd.isHermitian.eigenvalues j.1)) *
          ∑ i, Complex.normSq ((W : CMatrix (Prod a b)) j.1 i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          simp_rw [← hW j.1]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ =
      ∑ j : psdSupportIndex ρ.matrix hρpsd,
        hρpsd.isHermitian.eigenvalues j.1 *
          Real.log (hρpsd.isHermitian.eigenvalues j.1) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [unitary_row_normSq_sum W j.1]
          ring
    _ = ρ.supportEntropyTraceTerm := by
          rfl

/-- The support-restricted reference-eigenvalue part of the weighted
log-ratio sum is `Tr ρ log (I_A ⊗ σ_B)`. -/
theorem conditionalPetzRenyi_eigenbasis_support_weight_log_reference_sum
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        Real.log (hτ.isHermitian.eigenvalues i) =
      ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have href :=
    trace_mul_psdLog_identityTensorStateMatrix_eq_reference_eigenbasis_sum
      (ρ := ρ) (σ := σ) hσ
  have hdiag (i : Prod a b) :
      ((star (Uτ : CMatrix (Prod a b)) * ρ.matrix *
        (Uτ : CMatrix (Prod a b))) i i).re =
        ∑ j,
          hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i) := by
    have h :=
      unitary_conj_rpow_diagonal_re_eq_eigenvalue_sum
        (M := ρ.matrix) hρpsd Uτ (1 : ℝ) i
    simpa [hρpsd, Uρ, Real.rpow_one,
      CFC.rpow_one ρ.matrix (ha := Matrix.nonneg_iff_posSemidef.mpr hρpsd)] using h
  calc
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        Real.log (hτ.isHermitian.eigenvalues i)
        =
      ∑ i,
        ((star (Uτ : CMatrix (Prod a b)) * ρ.matrix *
          (Uτ : CMatrix (Prod a b))) i i).re *
          Real.log (hτ.isHermitian.eigenvalues i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hdiag i]
          have hsupport :=
            posSemidef_eigenvalue_mul_sum_eq_support_sum
              (M := ρ.matrix) hρpsd
              (fun j =>
                Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                  (Uτ : CMatrix (Prod a b))) j i) *
                Real.log (hτ.isHermitian.eigenvalues i))
          calc
            ∑ j : psdSupportIndex ρ.matrix hρpsd,
              (hρpsd.isHermitian.eigenvalues j.1 *
                Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                  (Uτ : CMatrix (Prod a b))) j.1 i)) *
                Real.log (hτ.isHermitian.eigenvalues i)
                =
              ∑ j : psdSupportIndex ρ.matrix hρpsd,
                hρpsd.isHermitian.eigenvalues j.1 *
                  (Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                    (Uτ : CMatrix (Prod a b))) j.1 i) *
                  Real.log (hτ.isHermitian.eigenvalues i)) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
            _ =
              ∑ j : Prod a b,
                hρpsd.isHermitian.eigenvalues j *
                  (Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                    (Uτ : CMatrix (Prod a b))) j i) *
                  Real.log (hτ.isHermitian.eigenvalues i)) := hsupport.symm
            _ =
              (∑ j : Prod a b,
                hρpsd.isHermitian.eigenvalues j *
                  Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                    (Uτ : CMatrix (Prod a b))) j i)) *
                Real.log (hτ.isHermitian.eigenvalues i) := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
    _ = ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re := by
          rw [href]

/-- Support-restricted weighted logarithms of eigenvalue ratios give the
support-aware matrix-log numerator. -/
theorem conditionalPetzRenyi_eigenbasis_support_weight_log_ratio_sum
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        Real.log
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) =
      ρ.supportEntropyTraceTerm -
        ((ρ.matrix *
          psdLog (identityTensorStateMatrix (a := a) σ)
            (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hstate :=
    conditionalPetzRenyi_eigenbasis_support_weight_log_state_sum
      (ρ := ρ) (σ := σ) hσ
  have href :=
    conditionalPetzRenyi_eigenbasis_support_weight_log_reference_sum
      (ρ := ρ) (σ := σ) hσ
  have hsplit :
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          Real.log
            (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) =
        (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
            Real.log (hρpsd.isHermitian.eigenvalues j.1)) -
          (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
            (hρpsd.isHermitian.eigenvalues j.1 *
              Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                (Uτ : CMatrix (Prod a b))) j.1 i)) *
              Real.log (hτ.isHermitian.eigenvalues i)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues j.1 := j.2
    have hτeig_pos : 0 < hτ.isHermitian.eigenvalues i := by
      simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos i
    rw [Real.log_div (ne_of_gt hρeig_pos) (ne_of_gt hτeig_pos)]
    ring
  change
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        Real.log
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) =
      ρ.supportEntropyTraceTerm -
        ((ρ.matrix *
          psdLog (identityTensorStateMatrix (a := a) σ)
            (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re
  rw [hsplit, hstate, href]

private theorem unitary_conj_diagonal_re_le_of_le
    {n : Type u} [Fintype n] [DecidableEq n]
    {M N : CMatrix n} (hMN : M ≤ N)
    (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ((star (U : CMatrix n) * M * (U : CMatrix n)) i i).re ≤
      ((star (U : CMatrix n) * N * (U : CMatrix n)) i i).re := by
  have hdiff : (N - M).PosSemidef := Matrix.le_iff.mp hMN
  have hconj : (star (U : CMatrix n) * (N - M) * (U : CMatrix n)).PosSemidef :=
    posSemidef_unitary_conj hdiff U
  have hnonneg := posSemidef_diagonal_re_nonneg hconj i
  have hexpand :
      star (U : CMatrix n) * (N - M) * (U : CMatrix n) =
        star (U : CMatrix n) * N * (U : CMatrix n) -
          star (U : CMatrix n) * M * (U : CMatrix n) := by
    noncomm_ring
  rw [hexpand] at hnonneg
  simpa using hnonneg

private theorem cMatrix_mul_inv_mul_self_le_smul_of_posSemidef_le_posDef
    {n : Type u} [Fintype n] [DecidableEq n]
    {A σ : CMatrix n} {c : ℝ}
    (hA : A.PosSemidef) (hσ : σ.PosDef) (hc : 0 < c)
    (hAσ : A ≤ (c : ℂ) • σ) :
    A * σ⁻¹ * A ≤ (c : ℂ) • A := by
  classical
  rw [Matrix.le_iff]
  let C : CMatrix n := (c : ℂ) • σ
  have hcC : (0 : ℂ) < (c : ℂ) := by
    exact_mod_cast hc
  have hC : C.PosDef := by
    simpa [C] using hσ.smul hcC
  have hCminusA : (C - A).PosSemidef := by
    simpa [C, Matrix.le_iff] using hAσ
  have hblock :
      (Matrix.fromBlocks A A A C : CMatrix (Sum n n)).PosSemidef :=
    cMatrix_fromBlocks_self_le_posSemidef hA hCminusA
  letI : Invertible C := hC.isUnit.invertible
  have hblock' :
      (Matrix.fromBlocks A A A.conjTranspose C : CMatrix (Sum n n)).PosSemidef := by
    simpa [hA.isHermitian.eq] using hblock
  have hschur :
      (A - A * C⁻¹ * A.conjTranspose).PosSemidef :=
    (Matrix.PosDef.fromBlocks₂₂ A A (D := C) hC).mp hblock'
  have hC_le :
      A * C⁻¹ * A ≤ A := by
    rw [Matrix.le_iff]
    simpa [hA.isHermitian.eq] using hschur
  have hcne : (c : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  letI : Invertible (c : ℂ) := invertibleOfNonzero hcne
  have hσdet : IsUnit σ.det := (Matrix.isUnit_iff_isUnit_det σ).mp hσ.isUnit
  have hCinv : C⁻¹ = ((c : ℂ)⁻¹) • σ⁻¹ := by
    calc
      C⁻¹ = (((c : ℂ) • σ))⁻¹ := by rfl
      _ = ⅟(c : ℂ) • σ⁻¹ := by
        simpa using Matrix.inv_smul σ (c : ℂ) hσdet
      _ = ((c : ℂ)⁻¹) • σ⁻¹ := by
        simp [invOf_eq_inv]
  have hinvScaled :
      ((c : ℂ)⁻¹) • (A * σ⁻¹ * A) ≤ A := by
    simpa [hCinv, Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul] using hC_le
  rw [Matrix.le_iff] at hinvScaled
  have hcNonneg : (0 : ℂ) ≤ (c : ℂ) := le_of_lt hcC
  have hscaled := hinvScaled.smul hcNonneg
  have hscale_eq :
      (c : ℂ) • (A - ((c : ℂ)⁻¹) • (A * σ⁻¹ * A)) =
        (c : ℂ) • A - A * σ⁻¹ * A := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hcne, one_smul]
  simpa [hscale_eq] using hscaled

private theorem posDef_unitary_conj_diag_re_pos
    {n : Type u} [Fintype n] [DecidableEq n]
    {A : CMatrix n} (hA : A.PosDef)
    (U : Matrix.unitaryGroup n ℂ) (i : n) :
    0 < ((star (U : CMatrix n) * A * (U : CMatrix n)) i i).re := by
  let A' : CMatrix n := star (U : CMatrix n) * A * (U : CMatrix n)
  have hA' : A'.PosDef := by
    dsimp [A']
    rw [Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (U : CMatrix n))]
    exact hA
  exact (Complex.pos_iff.mp (hA'.diag_pos (i := i))).1

private theorem posSemidef_eigenbasis_conj_eq_diagonal
    {n : Type u} [Fintype n] [DecidableEq n]
    {M : CMatrix n} (hM : M.PosSemidef) :
    star (hM.isHermitian.eigenvectorUnitary : CMatrix n) * M *
        (hM.isHermitian.eigenvectorUnitary : CMatrix n) =
      Matrix.diagonal fun j => ((hM.isHermitian.eigenvalues j : ℝ) : ℂ) := by
  classical
  let U : Matrix.unitaryGroup n ℂ := hM.isHermitian.eigenvectorUnitary
  let D : CMatrix n :=
    Matrix.diagonal fun j => ((hM.isHermitian.eigenvalues j : ℝ) : ℂ)
  have hMdiag : M = (U : CMatrix n) * D * star (U : CMatrix n) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hM.isHermitian.spectral_theorem
  change star (U : CMatrix n) * M * (U : CMatrix n) = D
  rw [hMdiag]
  have hUU : star (U : CMatrix n) * (U : CMatrix n) = 1 :=
    Unitary.coe_star_mul_self U
  calc
    star (U : CMatrix n) *
        ((U : CMatrix n) * D * star (U : CMatrix n)) * (U : CMatrix n)
        = (star (U : CMatrix n) * (U : CMatrix n)) * D *
            (star (U : CMatrix n) * (U : CMatrix n)) := by
          noncomm_ring
    _ = D := by
          rw [hUU]
          simp

private theorem posSemidef_eigenbasis_diagonal_re_eq_eigenvalue
    {n : Type u} [Fintype n] [DecidableEq n]
    {M : CMatrix n} (hM : M.PosSemidef) (i : n) :
    ((star (hM.isHermitian.eigenvectorUnitary : CMatrix n) * M *
        (hM.isHermitian.eigenvectorUnitary : CMatrix n)) i i).re =
      hM.isHermitian.eigenvalues i := by
  rw [posSemidef_eigenbasis_conj_eq_diagonal hM]
  simp

private theorem unitary_star_mul_normSq_comm
    {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n ℂ) (i j : n) :
    Complex.normSq ((star (U : CMatrix n) * (V : CMatrix n)) i j) =
      Complex.normSq ((star (V : CMatrix n) * (U : CMatrix n)) j i) := by
  have hentry :
      ((star (V : CMatrix n) * (U : CMatrix n)) j i) =
        star ((star (U : CMatrix n) * (V : CMatrix n)) i j) := by
    calc
      ((star (V : CMatrix n) * (U : CMatrix n)) j i)
          = (star (star (U : CMatrix n) * (V : CMatrix n))) j i := by
              rw [star_mul, star_star]
      _ = star ((star (U : CMatrix n) * (V : CMatrix n)) i j) := by
              simp [Matrix.star_apply]
  rw [hentry]
  simp [Complex.normSq_apply]

private theorem unitary_conj_posSemidef_diagonal_re_eq_eigenvalue_weighted_sum
    {n : Type u} [Fintype n] [DecidableEq n]
    {M : CMatrix n} (hM : M.PosSemidef)
    (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ((star (U : CMatrix n) * M * (U : CMatrix n)) i i).re =
      ∑ j, hM.isHermitian.eigenvalues j *
        Complex.normSq
          ((star (U : CMatrix n) *
            (hM.isHermitian.eigenvectorUnitary : CMatrix n)) i j) := by
  classical
  have h :=
    unitary_conj_rpow_diagonal_re_eq_eigenvalue_sum
      (M := M) hM U (1 : ℝ) i
  have hpow : CFC.rpow M (1 : ℝ) = M :=
    CFC.rpow_one M (ha := Matrix.nonneg_iff_posSemidef.mpr hM)
  rw [hpow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.rpow_one]
  rw [← unitary_star_mul_normSq_comm U hM.isHermitian.eigenvectorUnitary i j]

private theorem unitary_conj_posDef_inv_diagonal_re_eq_eigenvalue_inv_weighted_sum
    {n : Type u} [Fintype n] [DecidableEq n]
    {M : CMatrix n} (hM : M.PosDef)
    (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ((star (U : CMatrix n) * M⁻¹ * (U : CMatrix n)) i i).re =
      ∑ j, (hM.posSemidef.isHermitian.eigenvalues j)⁻¹ *
        Complex.normSq
          ((star (U : CMatrix n) *
            (hM.posSemidef.isHermitian.eigenvectorUnitary : CMatrix n)) i j) := by
  classical
  have hinv_rpow : CFC.rpow M (-1 : ℝ) = M⁻¹ := by
    have h := cMatrix_rpow_nonsing_inv_eq_rpow_neg hM (1 : ℝ)
    have hone : CFC.rpow M⁻¹ (1 : ℝ) = M⁻¹ :=
      CFC.rpow_one M⁻¹
        (ha := Matrix.nonneg_iff_posSemidef.mpr hM.inv.posSemidef)
    rw [hone] at h
    exact h.symm
  have h :=
    unitary_conj_rpow_diagonal_re_eq_eigenvalue_sum
      (M := M) hM.posSemidef U (-1 : ℝ) i
  rw [hinv_rpow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.rpow_neg_one]
  rw [← unitary_star_mul_normSq_comm
    U hM.posSemidef.isHermitian.eigenvectorUnitary i j]

private theorem finset_weighted_log_le_log_weighted_sum
    {ι : Type u} [Fintype ι]
    (w x : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hx_pos : ∀ i, 0 < x i) :
    ∑ i, w i * Real.log (x i) ≤ Real.log (∑ i, w i * x i) := by
  classical
  have hconc : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hjensen :=
    hconc.le_map_sum
      (t := (Finset.univ : Finset ι))
      (w := w) (p := x)
      (by intro i _; exact hw_nonneg i)
      (by simpa using hw_sum)
      (by intro i _; exact hx_pos i)
  simpa [smul_eq_mul] using hjensen

/-- Conditional-min feasibility gives the support-aware trace-log residual. -/
theorem conditionalMinEntropyFeasible_supportTraceLog_residual_nonneg
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) {lam : ℝ}
    (hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    0 ≤
      (((ρ.matrix *
          psdLog (identityTensorStateMatrix (a := a) σ)
            (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re -
        ρ.supportEntropyTraceTerm) - lam * Real.log 2 := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let c : ℝ := Real.rpow 2 (-lam)
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hc : 0 < c :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lam)
  have hle : ρ.matrix ≤ (c : ℂ) • τ := by
    simpa [ConditionalMinEntropyFeasible, τ, c] using hfeas
  have hle_quad :
      ρ.matrix * τ⁻¹ * ρ.matrix ≤ (c : ℂ) • ρ.matrix :=
    cMatrix_mul_inv_mul_self_le_smul_of_posSemidef_le_posDef
      hρpsd hτpos hc hle
  have hρ_conj :
      star (Uρ : CMatrix (Prod a b)) * ρ.matrix *
          (Uρ : CMatrix (Prod a b)) =
        Matrix.diagonal
          (fun j => ((hρpsd.isHermitian.eigenvalues j : ℝ) : ℂ)) := by
    simpa [hρpsd, Uρ] using
      posSemidef_eigenbasis_conj_eq_diagonal (M := ρ.matrix) hρpsd
  have hρ_diag (j : Prod a b) :
      ((star (Uρ : CMatrix (Prod a b)) * ρ.matrix *
          (Uρ : CMatrix (Prod a b))) j j).re =
        hρpsd.isHermitian.eigenvalues j := by
    simpa [hρpsd, Uρ] using
      posSemidef_eigenbasis_diagonal_re_eq_eigenvalue
        (M := ρ.matrix) hρpsd j
  have hτ_diag (j : Prod a b) :
      ((star (Uρ : CMatrix (Prod a b)) * τ *
          (Uρ : CMatrix (Prod a b))) j j).re =
        ∑ i, hτ.isHermitian.eigenvalues i *
          Complex.normSq
            ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i) := by
    simpa [τ, hτpos, hτ, Uτ, Uρ] using
      unitary_conj_posSemidef_diagonal_re_eq_eigenvalue_weighted_sum
        (M := τ) hτ Uρ j
  have hscale_diag (j : Prod a b) :
      ((star (Uρ : CMatrix (Prod a b)) * ((c : ℝ) • τ) *
          (Uρ : CMatrix (Prod a b))) j j).re =
        c * ((star (Uρ : CMatrix (Prod a b)) * τ *
          (Uρ : CMatrix (Prod a b))) j j).re := by
    have hmat :
        star (Uρ : CMatrix (Prod a b)) * ((c : ℝ) • τ) *
            (Uρ : CMatrix (Prod a b)) =
          (c : ℝ) •
            (star (Uρ : CMatrix (Prod a b)) * τ *
              (Uρ : CMatrix (Prod a b))) := by
      simp [mul_assoc]
    rw [hmat]
    simp
  have hrow_sum (j : Prod a b) :
      ∑ i, Complex.normSq
        ((star (Uρ : CMatrix (Prod a b)) * (Uτ : CMatrix (Prod a b))) j i) = 1 := by
    let W : Matrix.unitaryGroup (Prod a b) ℂ := Uρ⁻¹ * Uτ
    simpa [W, Uρ, Uτ] using unitary_row_normSq_sum W j
  have hsupport_sum :
      ∑ j : psdSupportIndex ρ.matrix hρpsd,
        hρpsd.isHermitian.eigenvalues j.1 = 1 := by
    have heig_sum : ∑ j : Prod a b, hρpsd.isHermitian.eigenvalues j = 1 := by
      have htrace := congrArg Complex.re hρpsd.isHermitian.trace_eq_sum_eigenvalues
      rw [ρ.trace_eq_one] at htrace
      norm_num at htrace
      exact htrace.symm
    calc
      ∑ j : psdSupportIndex ρ.matrix hρpsd,
          hρpsd.isHermitian.eigenvalues j.1 =
        ∑ j : Prod a b, hρpsd.isHermitian.eigenvalues j := by
          simpa using
            (posSemidef_eigenvalue_mul_sum_eq_support_sum
              (M := ρ.matrix) hρpsd (fun _ => 1)).symm
      _ = 1 := heig_sum
  have hpoint (j : psdSupportIndex ρ.matrix hρpsd) :
      ∑ i,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq
            ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
          Real.log
            (hρpsd.isHermitian.eigenvalues j.1 /
              hτ.isHermitian.eigenvalues i) ≤
        hρpsd.isHermitian.eigenvalues j.1 * Real.log c := by
    let r : ℝ := hρpsd.isHermitian.eigenvalues j.1
    let p : Prod a b → ℝ := fun i =>
      Complex.normSq
        ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)
    let t : Prod a b → ℝ := fun i => hτ.isHermitian.eigenvalues i
    have hr_pos : 0 < r := by
      simpa [r] using j.2
    have hp_nonneg : ∀ i, 0 ≤ p i := by
      intro i
      exact Complex.normSq_nonneg _
    have hp_sum : ∑ i, p i = 1 := by
      simpa [p] using hrow_sum j.1
    have ht_pos : ∀ i, 0 < t i := by
      intro i
      simpa [t, τ, hτpos, hτ] using hτpos.eigenvalues_pos i
    let q : ℝ :=
      ((star (Uρ : CMatrix (Prod a b)) * τ⁻¹ *
        (Uρ : CMatrix (Prod a b))) j.1 j.1).re
    have hq_pos : 0 < q := by
      simpa [q, τ, Uρ] using
        posDef_unitary_conj_diag_re_pos (A := τ⁻¹) hτpos.inv Uρ j.1
    have hq_eq :
        q = ∑ i, (t i)⁻¹ * p i := by
      have hdiag :=
        unitary_conj_posDef_inv_diagonal_re_eq_eigenvalue_inv_weighted_sum
          (M := τ) hτpos Uρ j.1
      simpa [q, p, t, τ, hτpos, hτ, Uτ, Uρ, mul_comm] using hdiag
    have hdiag_quad_le :
        ((star (Uρ : CMatrix (Prod a b)) * (ρ.matrix * τ⁻¹ * ρ.matrix) *
            (Uρ : CMatrix (Prod a b))) j.1 j.1).re ≤
          ((star (Uρ : CMatrix (Prod a b)) * ((c : ℂ) • ρ.matrix) *
            (Uρ : CMatrix (Prod a b))) j.1 j.1).re :=
      unitary_conj_diagonal_re_le_of_le hle_quad Uρ j.1
    have hquad_left :
        ((star (Uρ : CMatrix (Prod a b)) * (ρ.matrix * τ⁻¹ * ρ.matrix) *
            (Uρ : CMatrix (Prod a b))) j.1 j.1).re =
          r ^ 2 * q := by
      have hfactor :
          star (Uρ : CMatrix (Prod a b)) * (ρ.matrix * τ⁻¹ * ρ.matrix) *
              (Uρ : CMatrix (Prod a b)) =
            (star (Uρ : CMatrix (Prod a b)) * ρ.matrix *
              (Uρ : CMatrix (Prod a b))) *
              (star (Uρ : CMatrix (Prod a b)) * τ⁻¹ *
                (Uρ : CMatrix (Prod a b))) *
              (star (Uρ : CMatrix (Prod a b)) * ρ.matrix *
                (Uρ : CMatrix (Prod a b))) := by
        have hUstarU : star (Uρ : CMatrix (Prod a b)) *
            (Uρ : CMatrix (Prod a b)) = 1 :=
          Unitary.coe_star_mul_self Uρ
        have hUUstar : (Uρ : CMatrix (Prod a b)) *
            star (Uρ : CMatrix (Prod a b)) = 1 :=
          Unitary.coe_mul_star_self Uρ
        calc
          star (Uρ : CMatrix (Prod a b)) * (ρ.matrix * τ⁻¹ * ρ.matrix) *
              (Uρ : CMatrix (Prod a b)) =
            star (Uρ : CMatrix (Prod a b)) * ρ.matrix *
                ((Uρ : CMatrix (Prod a b)) * star (Uρ : CMatrix (Prod a b))) *
              τ⁻¹ *
                ((Uρ : CMatrix (Prod a b)) * star (Uρ : CMatrix (Prod a b))) *
              ρ.matrix * (Uρ : CMatrix (Prod a b)) := by
                rw [hUUstar]
                simp [Matrix.mul_assoc]
          _ =
            (star (Uρ : CMatrix (Prod a b)) * ρ.matrix *
              (Uρ : CMatrix (Prod a b))) *
              (star (Uρ : CMatrix (Prod a b)) * τ⁻¹ *
                (Uρ : CMatrix (Prod a b))) *
              (star (Uρ : CMatrix (Prod a b)) * ρ.matrix *
                (Uρ : CMatrix (Prod a b))) := by
                noncomm_ring
      rw [hfactor, hρ_conj]
      let Dρ : CMatrix (Prod a b) :=
        Matrix.diagonal
          (fun k => ((hρpsd.isHermitian.eigenvalues k : ℝ) : ℂ))
      let Bq : CMatrix (Prod a b) :=
        star (Uρ : CMatrix (Prod a b)) * τ⁻¹ *
          (Uρ : CMatrix (Prod a b))
      have hentry :
          (Dρ * Bq * Dρ) j.1 j.1 =
            (r : ℂ) * Bq j.1 j.1 * (r : ℂ) := by
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      have hre :
          ((Dρ * Bq * Dρ) j.1 j.1).re = r ^ 2 * q := by
        rw [hentry]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, mul_zero, sub_zero, q]
        dsimp [Bq]
        ring_nf
      simpa [Dρ, Bq] using hre
    have hquad_right :
        ((star (Uρ : CMatrix (Prod a b)) * ((c : ℂ) • ρ.matrix) *
            (Uρ : CMatrix (Prod a b))) j.1 j.1).re =
          c * r := by
      have hmat :
          star (Uρ : CMatrix (Prod a b)) * ((c : ℂ) • ρ.matrix) *
              (Uρ : CMatrix (Prod a b)) =
            (c : ℂ) •
              (star (Uρ : CMatrix (Prod a b)) * ρ.matrix *
                (Uρ : CMatrix (Prod a b))) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [hmat]
      simp [hρ_diag j.1, r]
    have hrq_le : r * q ≤ c := by
      have htmp : r ^ 2 * q ≤ c * r := by
        linarith [hdiag_quad_le, hquad_left, hquad_right]
      nlinarith [hr_pos, htmp]
    have hratio_sum_eq :
        ∑ i, p i * (r / t i) = r * q := by
      calc
        ∑ i, p i * (r / t i) =
            r * ∑ i, (t i)⁻¹ * p i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              field_simp [(ne_of_gt (ht_pos i))]
        _ = r * q := by
              rw [← hq_eq]
    have hratio_sum_le : ∑ i, p i * (r / t i) ≤ c := by
      rw [hratio_sum_eq]
      exact hrq_le
    have hratio_sum_pos : 0 < ∑ i, p i * (r / t i) := by
      rw [hratio_sum_eq]
      exact mul_pos hr_pos hq_pos
    have hmean_log_ratio :
        ∑ i, p i * Real.log (r / t i) ≤
          Real.log (∑ i, p i * (r / t i)) :=
      finset_weighted_log_le_log_weighted_sum
        p (fun i => r / t i) hp_nonneg hp_sum
        (fun i => div_pos hr_pos (ht_pos i))
    have hlog_mean_le :
        Real.log (∑ i, p i * (r / t i)) ≤ Real.log c :=
      Real.log_le_log hratio_sum_pos hratio_sum_le
    have hweighted_log_le :
        ∑ i, p i * Real.log (r / t i) ≤ Real.log c :=
      hmean_log_ratio.trans hlog_mean_le
    have hrewrite :
        ∑ i,
          (r * p i) * Real.log (r / t i) =
            r * ∑ i, p i * Real.log (r / t i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simpa [r, p, t, hrewrite] using
      mul_le_mul_of_nonneg_left hweighted_log_le hr_pos.le
  have hlog_ratio_le :
      (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq
            ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
          Real.log
            (hρpsd.isHermitian.eigenvalues j.1 /
              hτ.isHermitian.eigenvalues i)) ≤ Real.log c := by
    calc
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq
            ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
          Real.log
            (hρpsd.isHermitian.eigenvalues j.1 /
              hτ.isHermitian.eigenvalues i)
          =
        ∑ j : psdSupportIndex ρ.matrix hρpsd, ∑ i,
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq
              ((star (Uρ : CMatrix (Prod a b)) *
                (Uτ : CMatrix (Prod a b))) j.1 i)) *
            Real.log
              (hρpsd.isHermitian.eigenvalues j.1 /
                hτ.isHermitian.eigenvalues i) := by
            rw [Finset.sum_comm]
      _ ≤
        ∑ j : psdSupportIndex ρ.matrix hρpsd,
          hρpsd.isHermitian.eigenvalues j.1 * Real.log c := by
            exact Finset.sum_le_sum fun j _ => hpoint j
      _ = Real.log c := by
            rw [← Finset.sum_mul, hsupport_sum]
            ring
  have hlog_ratio_eq :
      (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq
            ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
          Real.log
            (hρpsd.isHermitian.eigenvalues j.1 /
              hτ.isHermitian.eigenvalues i)) =
        ρ.supportEntropyTraceTerm -
          ((ρ.matrix *
            psdLog (identityTensorStateMatrix (a := a) σ)
              (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re := by
    simpa [hρpsd, τ, hτpos, hτ, Uτ, Uρ] using
      conditionalPetzRenyi_eigenbasis_support_weight_log_ratio_sum
        (ρ := ρ) (σ := σ) hσ
  have hsupport_minus_trace :
      ρ.supportEntropyTraceTerm -
          ((ρ.matrix *
            psdLog (identityTensorStateMatrix (a := a) σ)
              (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re ≤
        Real.log c := by
    rw [← hlog_ratio_eq]
    exact hlog_ratio_le
  have hlogc : Real.log c = -lam * Real.log 2 := by
    simp [c, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  rw [hlogc] at hsupport_minus_trace
  linarith

/-- Remainder decomposition of the fixed-reference Petz trace for arbitrary
left state, with all logarithms and ratios restricted to `supp ρ`. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_one_add_beta_support_log_ratio_sum_add_remainder
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) (hβ : 0 < β) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      1 + β *
        (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
            Real.log
              (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i)) +
        ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
            alphaRemainder β
              (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hratio :=
    conditionalPetzRenyiTraceTerm_one_add_eq_support_eigenvalue_ratio_sum
      (ρ := ρ) (σ := σ) hσ β hβ
  have hweights :=
    conditionalPetzRenyi_eigenbasis_support_weight_sum_eq_one
      (ρ := ρ) (σ := σ) hσ
  have hexpand :
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) ^ β =
        (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) +
          β *
            (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
              (hρpsd.isHermitian.eigenvalues j.1 *
                Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                  (Uτ : CMatrix (Prod a b))) j.1 i)) *
                Real.log
                  (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i)) +
          ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
            (hρpsd.isHermitian.eigenvalues j.1 *
              Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                (Uτ : CMatrix (Prod a b))) j.1 i)) *
              alphaRemainder β
                (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) := by
    calc
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) ^ β
          =
        ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          (
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) +
            β *
              ((hρpsd.isHermitian.eigenvalues j.1 *
                Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                  (Uτ : CMatrix (Prod a b))) j.1 i)) *
                Real.log
                  (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i)) +
            (hρpsd.isHermitian.eigenvalues j.1 *
              Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                (Uτ : CMatrix (Prod a b))) j.1 i)) *
              alphaRemainder β
                (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [alphaRemainder]
            ring
      _ =
        (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) +
          β *
            (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
              (hρpsd.isHermitian.eigenvalues j.1 *
                Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                  (Uτ : CMatrix (Prod a b))) j.1 i)) *
                Real.log
                  (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i)) +
          ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
            (hρpsd.isHermitian.eigenvalues j.1 *
              Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                (Uτ : CMatrix (Prod a b))) j.1 i)) *
              alphaRemainder β
                (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) := by
            simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hratio, hexpand, hweights]

/-- Remainder decomposition with the support-aware logarithmic numerator
rewritten as `Tr_supp ρ log ρ - Tr ρ log(I_A ⊗ σ_B)`. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_one_add_beta_support_entropy_trace_add_remainder
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) (hβ : 0 < β) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      1 + β *
        (ρ.supportEntropyTraceTerm -
          ((ρ.matrix *
            psdLog (identityTensorStateMatrix (a := a) σ)
              (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re) +
        ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
            alphaRemainder β
              (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hremainder :=
    conditionalPetzRenyiTraceTerm_one_add_eq_one_add_beta_support_log_ratio_sum_add_remainder
      (ρ := ρ) (σ := σ) hσ β hβ
  have hlog :=
    conditionalPetzRenyi_eigenbasis_support_weight_log_ratio_sum
      (ρ := ρ) (σ := σ) hσ
  rw [hremainder, hlog]

/-- Remainder decomposition of the fixed-reference Petz trace in the double
eigenbasis variables.

This is the finite matrix-route analogue of expanding
`t^β = 1 + β log t + r_β(t)` in the source proof. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_one_add_beta_log_ratio_sum_add_remainder
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      1 + β *
        (∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            Real.log
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)) +
        ∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            alphaRemainder β
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hratio :=
    conditionalPetzRenyiTraceTerm_one_add_eq_eigenvalue_ratio_sum
      (ρ := ρ) hρ (σ := σ) hσ β
  have hweights :=
    conditionalPetzRenyi_eigenbasis_weight_sum_eq_one
      (ρ := ρ) hρ (σ := σ) hσ
  have hexpand :
      ∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β =
        (∑ i, ∑ j,
          hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) +
          β *
            (∑ i, ∑ j,
              (hρpsd.isHermitian.eigenvalues j *
                Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                  (Uτ : CMatrix (Prod a b))) j i)) *
                Real.log
                  (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)) +
          ∑ i, ∑ j,
            (hρpsd.isHermitian.eigenvalues j *
              Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                (Uτ : CMatrix (Prod a b))) j i)) *
              alphaRemainder β
                (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) := by
    calc
      ∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ β
          =
        ∑ i, ∑ j,
          (
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) +
            β *
              ((hρpsd.isHermitian.eigenvalues j *
                Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                  (Uτ : CMatrix (Prod a b))) j i)) *
                Real.log
                  (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)) +
            (hρpsd.isHermitian.eigenvalues j *
              Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                (Uτ : CMatrix (Prod a b))) j i)) *
              alphaRemainder β
                (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [alphaRemainder]
            ring
      _ =
        (∑ i, ∑ j,
          hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) +
          β *
            (∑ i, ∑ j,
              (hρpsd.isHermitian.eigenvalues j *
                Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                  (Uτ : CMatrix (Prod a b))) j i)) *
                Real.log
                  (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)) +
          ∑ i, ∑ j,
            (hρpsd.isHermitian.eigenvalues j *
              Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
                (Uτ : CMatrix (Prod a b))) j i)) *
              alphaRemainder β
                (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) := by
            simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
  change
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      1 + β *
        (∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            Real.log
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)) +
        ∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            alphaRemainder β
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)
  rw [hratio, hexpand, hweights]

/-- Remainder decomposition with the logarithmic numerator already rewritten
as the fixed-reference matrix-log expression. -/
theorem conditionalPetzRenyiTraceTerm_one_add_eq_one_add_beta_matrix_log_add_remainder
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      1 + β *
        (((ρ.matrix * psdLog ρ.matrix hρ).trace).re -
          ((ρ.matrix *
            psdLog (identityTensorStateMatrix (a := a) σ)
              (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re) +
        ∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            alphaRemainder β
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hremainder :=
    conditionalPetzRenyiTraceTerm_one_add_eq_one_add_beta_log_ratio_sum_add_remainder
      (ρ := ρ) hρ (σ := σ) hσ β
  have hlog :=
    conditionalPetzRenyi_eigenbasis_weight_log_ratio_sum
      (ρ := ρ) hρ (σ := σ) hσ
  change
    ρ.conditionalPetzRenyiTraceTerm σ (1 + β) =
      1 + β *
        (((ρ.matrix * psdLog ρ.matrix hρ).trace).re -
          ((ρ.matrix *
            psdLog (identityTensorStateMatrix (a := a) σ)
              (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re) +
        ∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            alphaRemainder β
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)
  rw [hremainder, hlog]

/-- Positivity of the fixed-reference Petz trace kernel in the full-rank domain. -/
theorem conditionalPetzRenyiTraceTerm_pos_of_posDef
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) (α : ℝ) :
    0 < ρ.conditionalPetzRenyiTraceTerm σ α := by
  dsimp [conditionalPetzRenyiTraceTerm]
  haveI : Nonempty (Prod a b) := ρ.nonempty
  exact trace_mul_posDef_re_pos
    (ρ.rpowMatrix_posDef_of_posDef hρ α)
    (cMatrix_rpow_posDef_of_posDef
      (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ) (1 - α))

/-- Exponentiating the fixed-reference Petz candidate recovers its trace term. -/
theorem rpow_two_one_sub_alpha_mul_conditionalPetzRenyiEntropyCandidate
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    Real.rpow 2
        ((1 - α) *
          ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α hα_pos hα_ne_one) =
      ρ.conditionalPetzRenyiTraceTerm σ α := by
  have htrace_pos :
      0 < ρ.conditionalPetzRenyiTraceTerm σ α :=
    conditionalPetzRenyiTraceTerm_pos_of_posDef (ρ := ρ) hρ (σ := σ) hσ α
  have hden : 1 - α ≠ 0 := sub_ne_zero.mpr hα_ne_one.symm
  dsimp [conditionalPetzRenyiEntropyCandidate, conditionalPetzRenyiTraceTerm]
  change
    Real.rpow 2
      ((1 - α) *
          ((1 / (1 - α)) *
            log2
              ((CFC.rpow ρ.matrix α *
                CFC.rpow (identityTensorStateMatrix (a := a) σ) (1 - α)).trace).re)) =
      ((CFC.rpow ρ.matrix α *
        CFC.rpow (identityTensorStateMatrix (a := a) σ) (1 - α)).trace).re
  have hmul :
      (1 - α) *
          ((1 / (1 - α)) *
            log2
              ((CFC.rpow ρ.matrix α *
                CFC.rpow (identityTensorStateMatrix (a := a) σ) (1 - α)).trace).re) =
        log2
          ((CFC.rpow ρ.matrix α *
            CFC.rpow (identityTensorStateMatrix (a := a) σ) (1 - α)).trace).re := by
    field_simp [hden]
  rw [hmul]
  exact rpow_two_log2_pos htrace_pos

/-- The `α = 3/2` term in `Υ` is the Petz trace at `3/2`. -/
theorem rpow_two_neg_half_conditionalPetzRenyiEntropyCandidate_three_halves
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    Real.rpow 2
        (-(1 / 2 : ℝ) *
          ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (3 / 2)
            (by norm_num) (by norm_num)) =
      ρ.conditionalPetzRenyiTraceTerm σ (3 / 2) := by
  convert
    (rpow_two_one_sub_alpha_mul_conditionalPetzRenyiEntropyCandidate
      (ρ := ρ) hρ (σ := σ) hσ (α := 3 / 2)
      (by norm_num) (by norm_num)) using 2
  ring

/-- The `α = 1/2` term in `Υ` is the Petz trace at `1/2`. -/
theorem rpow_two_half_conditionalPetzRenyiEntropyCandidate_one_half
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    Real.rpow 2
        ((1 / 2 : ℝ) *
          ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (1 / 2)
            (by norm_num) (by norm_num)) =
      ρ.conditionalPetzRenyiTraceTerm σ (1 / 2) := by
  convert
    (rpow_two_one_sub_alpha_mul_conditionalPetzRenyiEntropyCandidate
      (ρ := ρ) hρ (σ := σ) hσ (α := 1 / 2)
      (by norm_num) (by norm_num)) using 2
  ring

/-- The TCR alpha-entropy convergence parameter
`Υ(A|B)_{ρ|σ} = 2^{-1/2 H_{3/2}(A|B)_{ρ|σ}}
  + 2^{1/2 H_{1/2}(A|B)_{ρ|σ}} + 1`.

The `H_α` terms use the fixed-reference conditional Petz candidate from
`ConditionalPetzRenyi`.
-/
def conditionalAlphaConvergenceParameter
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) : ℝ :=
  Real.rpow 2
      (-(1 / 2 : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (3 / 2)
          (by norm_num) (by norm_num)) +
    Real.rpow 2
      ((1 / 2 : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (1 / 2)
          (by norm_num) (by norm_num)) +
    1

/-- Trace-term spelling of the TCR alpha-entropy convergence parameter.

At the special exponents used in the finite-AEP error term, the source
quantity
`2^(-H_{3/2}/2) + 2^(H_{1/2}/2) + 1`
is exactly the sum of the two Petz trace terms at `3/2` and `1/2`.
This definition is available for arbitrary finite states, using the CFC
zero-on-kernel convention for the negative half-power. -/
def conditionalAlphaConvergenceParameterTrace
    (ρ : State (Prod a b)) (σ : State b) : ℝ :=
  ρ.conditionalPetzRenyiTraceTerm σ (3 / 2) +
    ρ.conditionalPetzRenyiTraceTerm σ (1 / 2) + 1

/-- The trace-term `Upsilon` is at least `1` for arbitrary states. -/
theorem one_le_conditionalAlphaConvergenceParameterTrace
    (ρ : State (Prod a b)) (σ : State b) :
    1 ≤ ρ.conditionalAlphaConvergenceParameterTrace σ := by
  unfold conditionalAlphaConvergenceParameterTrace
  have h32 : 0 ≤ ρ.conditionalPetzRenyiTraceTerm σ (3 / 2) :=
    ρ.conditionalPetzRenyiTraceTerm_nonneg σ (3 / 2)
  have h12 : 0 ≤ ρ.conditionalPetzRenyiTraceTerm σ (1 / 2) :=
    ρ.conditionalPetzRenyiTraceTerm_nonneg σ (1 / 2)
  linarith

/-- The canonical side reference of a grouped IID tensor power is full-rank
when the one-copy side marginal is full-rank. -/
theorem tensorPowerBipartite_marginalB_posDef_fullReference
    (ρ : State (Prod a b))
    (hρB : ρ.marginalB.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).marginalB.matrix.PosDef := by
  rw [State.tensorPowerBipartite_marginalB ρ n]
  exact State.tensorPower_posDef hρB n

/-- Successor grouping of IID bipartite tensor powers as a product of one copy
and the remaining `n` copies. -/
theorem tensorPowerBipartite_succ_grouped_forAlphaContinuity
    (ρ : State (Prod a b)) (n : ℕ) :
    ρ.tensorPowerBipartite (n + 1) =
      (ρ.prod (ρ.tensorPowerBipartite n)).reindex
        (conditionalPetzRenyiProductGroupingEquiv
          a b (TensorPower a n) (TensorPower b n)) := by
  ext x y
  rcases x with ⟨⟨xA, xsA⟩, ⟨xB, xsB⟩⟩
  rcases y with ⟨⟨yA, ysA⟩, ⟨yB, ysB⟩⟩
  simp [State.tensorPowerBipartite, State.tensorPower_succ,
    conditionalPetzRenyiProductGroupingEquiv, tensorPowerProdEquiv,
    State.prod, State.reindex, Matrix.kronecker, Matrix.kroneckerMap_apply]

/-- The side marginal of the successor grouping is the product of the one-copy
side marginal and the `n`-copy side marginal. -/
theorem tensorPowerBipartite_succ_grouped_marginalB_forAlphaContinuity
    (ρ : State (Prod a b)) (n : ℕ) :
    (((ρ.prod (ρ.tensorPowerBipartite n)).reindex
        (conditionalPetzRenyiProductGroupingEquiv
          a b (TensorPower a n) (TensorPower b n))).marginalB) =
      ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB := by
  ext x y
  rcases x with ⟨xB, xsB⟩
  rcases y with ⟨yB, ysB⟩
  simp [State.marginalB, partialTraceA, State.prod, State.reindex,
    conditionalPetzRenyiProductGroupingEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Zeroth tensor power Petz trace for the canonical reference. -/
theorem tensorPowerBipartite_conditionalPetzRenyiTraceTerm_zero
    (ρ : State (Prod a b)) (α : ℝ) :
    (ρ.tensorPowerBipartite 0).conditionalPetzRenyiTraceTerm
        (ρ.tensorPowerBipartite 0).marginalB α = 1 := by
  have hmat :
      (ρ.tensorPowerBipartite 0).matrix =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    simp [State.tensorPowerBipartite, State.tensorPower, State.reindex,
      State.unit, TensorPower, tensorPowerProdEquiv]
  have hBmat :
      (ρ.tensorPowerBipartite 0).marginalB.matrix =
        (1 : CMatrix (TensorPower b 0)) := by
    ext x y
    cases x
    cases y
    change partialTraceA (a := TensorPower a 0) (b := TensorPower b 0)
        (ρ.tensorPowerBipartite 0).matrix PUnit.unit PUnit.unit =
      (1 : CMatrix (TensorPower b 0)) PUnit.unit PUnit.unit
    rw [hmat]
    simp [partialTraceA, TensorPower]
    change (1 : ℂ) = 1
    norm_num
  have href :
      identityTensorStateMatrix (a := TensorPower a 0)
          (ρ.tensorPowerBipartite 0).marginalB =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) := by
    ext x y
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    cases xA
    cases xB
    cases yA
    cases yB
    change
      (Matrix.kronecker (1 : CMatrix (TensorPower a 0))
          (ρ.tensorPowerBipartite 0).marginalB.matrix)
        (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) =
        (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0)))
          (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit)
    rw [hBmat]
    simp [TensorPower, Matrix.kronecker, Matrix.kroneckerMap_apply]
    change (1 : ℂ) * 1 = 1
    norm_num
  unfold conditionalPetzRenyiTraceTerm
  rw [hmat, href]
  rw [show CFC.rpow (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) α = 1 by
      exact CFC.one_rpow,
    show CFC.rpow (1 : CMatrix (Prod (TensorPower a 0) (TensorPower b 0))) (1 - α) = 1 by
      exact CFC.one_rpow,
    one_mul, Matrix.trace_one]
  have hcard : Fintype.card (Prod (TensorPower a 0) (TensorPower b 0)) = 1 := by
    change Fintype.card (PUnit × PUnit) = 1
    simp
  simp [hcard]

/-- One-step multiplicativity of the canonical full-reference Petz trace along
the grouped IID tensor-power decomposition. -/
theorem tensorPowerBipartite_conditionalPetzRenyiTraceTerm_succ_fullReference
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_nonneg : 0 ≤ α) (n : ℕ) :
    (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiTraceTerm
        (ρ.tensorPowerBipartite (n + 1)).marginalB α =
      ρ.conditionalPetzRenyiTraceTerm ρ.marginalB α *
        (ρ.tensorPowerBipartite n).conditionalPetzRenyiTraceTerm
          (ρ.tensorPowerBipartite n).marginalB α := by
  let τ : State (Prod (Prod a (TensorPower a n)) (Prod b (TensorPower b n))) :=
    (ρ.prod (ρ.tensorPowerBipartite n)).reindex
      (conditionalPetzRenyiProductGroupingEquiv
        a b (TensorPower a n) (TensorPower b n))
  have hτ :
      ρ.tensorPowerBipartite (n + 1) = τ :=
    tensorPowerBipartite_succ_grouped_forAlphaContinuity ρ n
  have hτB :
      τ.marginalB = ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB := by
    simpa [τ] using
      tensorPowerBipartite_succ_grouped_marginalB_forAlphaContinuity ρ n
  have hregroup :
      (ρ.tensorPowerBipartite (n + 1)).conditionalPetzRenyiTraceTerm
          (ρ.tensorPowerBipartite (n + 1)).marginalB α =
        τ.conditionalPetzRenyiTraceTerm
          (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB) α := by
    have hτ_matrix :
        (ρ.tensorPowerBipartite (n + 1)).matrix = τ.matrix :=
      congrArg State.matrix hτ
    have hτ_matrix' :
        Matrix.submatrix (ρ.tensorPower (n + 1)).matrix
            (tensorPowerProdEquiv a b (n + 1)).symm
            (tensorPowerProdEquiv a b (n + 1)).symm =
          Matrix.submatrix (ρ.prod (ρ.tensorPowerBipartite n)).matrix
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm := by
      simpa [State.tensorPowerBipartite_matrix, τ, State.reindex_matrix] using hτ_matrix
    have hτ_matrix_def :
        τ.matrix =
          Matrix.submatrix (ρ.prod (ρ.tensorPowerBipartite n)).matrix
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm
            (conditionalPetzRenyiProductGroupingEquiv
              a b (TensorPower a n) (TensorPower b n)).symm := by
      simp [τ, State.reindex_matrix]
    have hτB_matrix :
        (ρ.tensorPowerBipartite (n + 1)).marginalB.matrix =
          (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB).matrix := by
      simpa [← hτ] using congrArg State.matrix hτB
    have hτB_ref :
        identityTensorStateMatrix (a := TensorPower a (n + 1))
            (ρ.tensorPowerBipartite (n + 1)).marginalB =
          identityTensorStateMatrix (a := Prod a (TensorPower a n))
            (ρ.marginalB.prod (ρ.tensorPowerBipartite n).marginalB) := by
      ext i j
      by_cases hij : i.1 = j.1
      · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.one_apply, hij]
        exact congrFun (congrFun hτB_matrix i.2) j.2
      · simp [identityTensorStateMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.one_apply, hij]
        intro h
        exact False.elim (hij h)
    dsimp [conditionalPetzRenyiTraceTerm]
    rw [hτ_matrix', hτB_ref, hτ_matrix_def]
    rfl
  have hprod :=
    conditionalPetzRenyiTraceTerm_prod_grouped_fullReference
      (ρ₁ := ρ) (σ₁ := ρ.marginalB)
      (ρ₂ := ρ.tensorPowerBipartite n)
      (σ₂ := (ρ.tensorPowerBipartite n).marginalB)
      hρB (tensorPowerBipartite_marginalB_posDef_fullReference ρ hρB n)
      α hα_nonneg
  exact hregroup.trans hprod

/-- Canonical full-reference Petz trace is multiplicative on grouped IID
tensor powers. -/
theorem tensorPowerBipartite_conditionalPetzRenyiTraceTerm_fullReference_pow
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (α : ℝ) (hα_nonneg : 0 ≤ α) (n : ℕ) :
    (ρ.tensorPowerBipartite n).conditionalPetzRenyiTraceTerm
        (ρ.tensorPowerBipartite n).marginalB α =
      (ρ.conditionalPetzRenyiTraceTerm ρ.marginalB α) ^ n := by
  induction n with
  | zero =>
      rw [tensorPowerBipartite_conditionalPetzRenyiTraceTerm_zero]
      simp
  | succ n ih =>
      rw [tensorPowerBipartite_conditionalPetzRenyiTraceTerm_succ_fullReference
        ρ hρB α hα_nonneg n, ih]
      rw [pow_succ']

/-- Exact tensor-power spelling of the trace-style convergence parameter:
the two Petz trace summands multiply separately. -/
theorem tensorPowerBipartite_conditionalAlphaConvergenceParameterTrace_canonical_eq_pow_terms
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).conditionalAlphaConvergenceParameterTrace
        (ρ.tensorPowerBipartite n).marginalB =
      (ρ.conditionalPetzRenyiTraceTerm ρ.marginalB (3 / 2)) ^ n +
        (ρ.conditionalPetzRenyiTraceTerm ρ.marginalB (1 / 2)) ^ n + 1 := by
  unfold conditionalAlphaConvergenceParameterTrace
  rw [
    tensorPowerBipartite_conditionalPetzRenyiTraceTerm_fullReference_pow
      (ρ := ρ) hρB (α := 3 / 2) (by norm_num) n,
    tensorPowerBipartite_conditionalPetzRenyiTraceTerm_fullReference_pow
      (ρ := ρ) hρB (α := 1 / 2) (by norm_num) n]

/-- The witness-based positive-definite `Upsilon` agrees with its trace-term
spelling. -/
theorem conditionalAlphaConvergenceParameter_eq_trace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ρ.conditionalAlphaConvergenceParameter hρ σ hσ =
      ρ.conditionalAlphaConvergenceParameterTrace σ := by
  unfold conditionalAlphaConvergenceParameter conditionalAlphaConvergenceParameterTrace
  rw [
    rpow_two_neg_half_conditionalPetzRenyiEntropyCandidate_three_halves
      (ρ := ρ) hρ (σ := σ) hσ,
    rpow_two_half_conditionalPetzRenyiEntropyCandidate_one_half
      (ρ := ρ) hρ (σ := σ) hσ]

@[simp]
theorem conditionalAlphaConvergenceParameter_eq
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ρ.conditionalAlphaConvergenceParameter hρ σ hσ =
      Real.rpow 2
          (-(1 / 2 : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (3 / 2)
              (by norm_num) (by norm_num)) +
        Real.rpow 2
          ((1 / 2 : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (1 / 2)
              (by norm_num) (by norm_num)) +
        1 :=
  rfl

/-- The convergence parameter `Υ` expanded in the double-eigenbasis weights.

This is the finite matrix-route version of the source expectation
`E[X^{1/2}] + E[X^{-1/2}] + 1`. -/
theorem conditionalAlphaConvergenceParameter_eq_eigenbasis_rpow_sum
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalAlphaConvergenceParameter hρ σ hσ =
      (∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ (1 / 2 : ℝ)) +
      (∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^ (-(1 / 2 : ℝ))) +
      1 := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hthree_trace :
      Real.rpow 2
          (-(1 / 2 : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (3 / 2)
              (by norm_num) (by norm_num)) =
        ρ.conditionalPetzRenyiTraceTerm σ (3 / 2) :=
    rpow_two_neg_half_conditionalPetzRenyiEntropyCandidate_three_halves
      (ρ := ρ) hρ (σ := σ) hσ
  have hhalf_trace :
      Real.rpow 2
          ((1 / 2 : ℝ) *
            ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (1 / 2)
              (by norm_num) (by norm_num)) =
        ρ.conditionalPetzRenyiTraceTerm σ (1 / 2) :=
    rpow_two_half_conditionalPetzRenyiEntropyCandidate_one_half
      (ρ := ρ) hρ (σ := σ) hσ
  have hthree_ratio :
      ρ.conditionalPetzRenyiTraceTerm σ (3 / 2) =
        ∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^
              (1 / 2 : ℝ) := by
    convert
      (conditionalPetzRenyiTraceTerm_one_add_eq_eigenvalue_ratio_sum
        (ρ := ρ) hρ (σ := σ) hσ (β := 1 / 2)) using 2
    ring
  have hhalf_ratio :
      ρ.conditionalPetzRenyiTraceTerm σ (1 / 2) =
        ∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ^
              (-(1 / 2 : ℝ)) := by
    convert
      (conditionalPetzRenyiTraceTerm_one_add_eq_eigenvalue_ratio_sum
        (ρ := ρ) hρ (σ := σ) hσ (β := -(1 / 2 : ℝ))) using 2
    ring
  rw [conditionalAlphaConvergenceParameter_eq, hthree_trace, hhalf_trace,
    hthree_ratio, hhalf_ratio]

/-- The convergence parameter `Υ` as
`E[√X] + E[(√X)⁻¹] + 1` in the double-eigenbasis weights. -/
theorem conditionalAlphaConvergenceParameter_eq_eigenbasis_sqrt_sum
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalAlphaConvergenceParameter hρ σ hσ =
      (∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          Real.sqrt
            (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)) +
      (∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          (Real.sqrt
            (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i))⁻¹) +
      1 := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  rw [conditionalAlphaConvergenceParameter_eq_eigenbasis_rpow_sum (ρ := ρ) hρ (σ := σ) hσ]
  congr 2
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.sqrt_eq_rpow]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues j := by
      simpa [hρpsd] using hρ.eigenvalues_pos j
    have hτeig_pos : 0 < hτ.isHermitian.eigenvalues i := by
      simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos i
    have hratio_nonneg :
        0 ≤ hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i :=
      (div_pos hρeig_pos hτeig_pos).le
    rw [Real.rpow_neg hratio_nonneg, ← Real.sqrt_eq_rpow]

/-- The arbitrary-left trace-style convergence parameter `Upsilon` as
`E[√X] + E[(√X)⁻¹] + 1` over the positive spectral support of `ρ`. -/
theorem conditionalAlphaConvergenceParameterTrace_eq_support_eigenbasis_sqrt_sum
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ρ.conditionalAlphaConvergenceParameterTrace σ =
      (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          Real.sqrt
            (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i)) +
      (∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          (Real.sqrt
            (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹) +
      1 := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hthree_ratio :
      ρ.conditionalPetzRenyiTraceTerm σ (3 / 2) =
        ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
            (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) ^
              (1 / 2 : ℝ) := by
    convert
      (conditionalPetzRenyiTraceTerm_one_add_eq_support_eigenvalue_ratio_sum
        (ρ := ρ) (σ := σ) hσ (β := 1 / 2) (by norm_num)) using 2
    ring
  have hthree_sqrt :
      ρ.conditionalPetzRenyiTraceTerm σ (3 / 2) =
        ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
            Real.sqrt
              (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) := by
    rw [hthree_ratio]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.sqrt_eq_rpow]
  have hhalf :=
    conditionalPetzRenyiTraceTerm_half_eq_support_inv_sqrt_sum
      (ρ := ρ) (σ := σ) hσ
  unfold conditionalAlphaConvergenceParameterTrace
  rw [hthree_sqrt, hhalf]

/-- The convergence parameter is at least `3`.  In the double-eigenbasis
expansion, this is the weighted AM-GM estimate
`√x + (√x)⁻¹ + 1 ≥ 3`. -/
theorem conditionalAlphaConvergenceParameter_ge_three
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    3 ≤ ρ.conditionalAlphaConvergenceParameter hρ σ hσ := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  let w : Prod (Prod a b) (Prod a b) → ℝ := fun x =>
    hρpsd.isHermitian.eigenvalues x.2 *
      Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
        (Uτ : CMatrix (Prod a b))) x.2 x.1)
  let p : Prod (Prod a b) (Prod a b) → ℝ := fun x =>
    Real.sqrt (hρpsd.isHermitian.eigenvalues x.2 / hτ.isHermitian.eigenvalues x.1) +
      (Real.sqrt
        (hρpsd.isHermitian.eigenvalues x.2 / hτ.isHermitian.eigenvalues x.1))⁻¹ +
      1
  have hweights :=
    conditionalPetzRenyi_eigenbasis_weight_sum_eq_one
      (ρ := ρ) hρ (σ := σ) hσ
  have hweights_local :
      ∑ i, ∑ j,
        hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i) = 1 := by
    simpa [hρpsd, τ, hτpos, hτ, Uτ, Uρ] using hweights
  have heta :=
    conditionalAlphaConvergenceParameter_eq_eigenbasis_sqrt_sum
      (ρ := ρ) hρ (σ := σ) hσ
  have hweight_nonneg :
      ∀ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), 0 ≤ w x := by
    intro x _
    have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues x.2 := by
      simpa [hρpsd] using hρ.eigenvalues_pos x.2
    exact mul_nonneg hρeig_pos.le (Complex.normSq_nonneg _)
  have hweight_sum :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x = 1 := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simpa [w] using hweights_local
  have hpoint :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x * 3 ≤
        ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x * p x := by
    apply Finset.sum_le_sum
    intro x hx
    have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues x.2 := by
      simpa [hρpsd] using hρ.eigenvalues_pos x.2
    have hτeig_pos : 0 < hτ.isHermitian.eigenvalues x.1 := by
      simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos x.1
    exact mul_le_mul_of_nonneg_left
      (three_le_sqrt_add_inv_add_one (div_pos hρeig_pos hτeig_pos))
      (hweight_nonneg x hx)
  have hthree :
      (3 : ℝ) =
        ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x * 3 := by
    rw [← Finset.sum_mul, hweight_sum, one_mul]
  have harg :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x * p x =
        ρ.conditionalAlphaConvergenceParameter hρ σ hσ := by
    rw [heta]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp [w, p]
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp_rw [mul_one]
    rw [hweights_local]
  calc
    (3 : ℝ) =
        ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x * 3 := hthree
    _ ≤ ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x * p x := hpoint
    _ = ρ.conditionalAlphaConvergenceParameter hρ σ hσ := harg

/-- Weighted remainder bound after the scalar step, parameterized by the
remaining Jensen/concavity step.

The hypothesis `hJensen` is the precise finite Jensen inequality needed to
turn the weighted `s_{2β}` expectation into `s_{2β}(Υ)`. -/
theorem conditionalPetzRenyi_weighted_remainder_le_of_jensen
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) (hβ : 0 ≤ β)
    (hJensen :
      (let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
       let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
       let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
       let hτ : τ.PosSemidef := hτpos.posSemidef
       let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
       let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
       ∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          alphaCoshMajorant (2 * β)
            (Real.sqrt
                (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) +
              (Real.sqrt
                (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i))⁻¹ +
              1)) ≤
        alphaCoshMajorant (2 * β)
          (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        alphaRemainder β
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameter hρ σ hσ) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hpoint :
      ∑ i, ∑ j,
        (hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i)) *
          alphaRemainder β
            (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ≤
        ∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            alphaCoshMajorant (2 * β)
              (Real.sqrt
                  (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) +
                (Real.sqrt
                  (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i))⁻¹ +
                1) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues j := by
      simpa [hρpsd] using hρ.eigenvalues_pos j
    have hτeig_pos : 0 < hτ.isHermitian.eigenvalues i := by
      simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos i
    have hratio_pos :
        0 < hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i :=
      div_pos hρeig_pos hτeig_pos
    have hweight_nonneg :
        0 ≤ hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i) :=
      mul_nonneg hρeig_pos.le (Complex.normSq_nonneg _)
    exact mul_le_mul_of_nonneg_left
      (alphaRemainder_le_alphaCoshMajorant_sqrt_add_inv_add_one hratio_pos hβ)
      hweight_nonneg
  exact hpoint.trans hJensen

/-- The finite Jensen step for the weighted `s_{2β}` term, assuming the scalar
concavity of `s_{2β}` on `[3, ∞)`.

This discharges the matrix/probability part of the Jensen bridge; the remaining
analytic input is the one-variable concavity hypothesis. -/
theorem conditionalPetzRenyi_weighted_alphaCoshMajorant_le_of_concaveOn
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ)
    (hconc :
      ConcaveOn ℝ (Set.Ici (3 : ℝ))
        (fun x : ℝ => alphaCoshMajorant (2 * β) x)) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        alphaCoshMajorant (2 * β)
          (Real.sqrt
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) +
            (Real.sqrt
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i))⁻¹ +
            1) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameter hρ σ hσ) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  let w : Prod (Prod a b) (Prod a b) → ℝ := fun x =>
    hρpsd.isHermitian.eigenvalues x.2 *
      Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
        (Uτ : CMatrix (Prod a b))) x.2 x.1)
  let p : Prod (Prod a b) (Prod a b) → ℝ := fun x =>
    Real.sqrt (hρpsd.isHermitian.eigenvalues x.2 / hτ.isHermitian.eigenvalues x.1) +
      (Real.sqrt
        (hρpsd.isHermitian.eigenvalues x.2 / hτ.isHermitian.eigenvalues x.1))⁻¹ +
      1
  let f : ℝ → ℝ := fun x => alphaCoshMajorant (2 * β) x
  have hweights :=
    conditionalPetzRenyi_eigenbasis_weight_sum_eq_one
      (ρ := ρ) hρ (σ := σ) hσ
  have hweights_local :
      ∑ i, ∑ j,
        hρpsd.isHermitian.eigenvalues j *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j i) = 1 := by
    simpa [hρpsd, τ, hτpos, hτ, Uτ, Uρ] using hweights
  have heta :=
    conditionalAlphaConvergenceParameter_eq_eigenbasis_sqrt_sum
      (ρ := ρ) hρ (σ := σ) hσ
  have hweight_nonneg :
      ∀ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), 0 ≤ w x := by
    intro x _
    have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues x.2 := by
      simpa [hρpsd] using hρ.eigenvalues_pos x.2
    exact mul_nonneg hρeig_pos.le (Complex.normSq_nonneg _)
  have hweight_sum :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x = 1 := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simpa [w] using hweights_local
  have hp_mem :
      ∀ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), p x ∈ Set.Ici (3 : ℝ) := by
    intro x _
    have hρeig_pos : 0 < hρpsd.isHermitian.eigenvalues x.2 := by
      simpa [hρpsd] using hρ.eigenvalues_pos x.2
    have hτeig_pos : 0 < hτ.isHermitian.eigenvalues x.1 := by
      simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos x.1
    exact three_le_sqrt_add_inv_add_one (div_pos hρeig_pos hτeig_pos)
  have hjensen :=
    hconc.le_map_sum
      (t := (Finset.univ.product Finset.univ :
        Finset (Prod (Prod a b) (Prod a b))))
      (w := w) (p := p) hweight_nonneg hweight_sum hp_mem
  have hleft :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x * f (p x) =
        ∑ i, ∑ j,
          (hρpsd.isHermitian.eigenvalues j *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j i)) *
            alphaCoshMajorant (2 * β)
              (Real.sqrt
                  (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) +
                (Real.sqrt
                  (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i))⁻¹ +
                1) := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
  have harg :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (Prod a b))), w x * p x =
        ρ.conditionalAlphaConvergenceParameter hρ σ hσ := by
    rw [heta]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp [w, p]
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp_rw [mul_one]
    rw [hweights_local]
  change
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        alphaCoshMajorant (2 * β)
          (Real.sqrt
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) +
            (Real.sqrt
              (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i))⁻¹ +
            1) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)
  rw [← hleft, ← harg]
  simpa [f, smul_eq_mul] using hjensen

/-- Weighted remainder upper bound with the finite Jensen step discharged from
the scalar concavity hypothesis. -/
theorem conditionalPetzRenyi_weighted_remainder_le_of_concaveOn
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) (hβ : 0 ≤ β)
    (hconc :
      ConcaveOn ℝ (Set.Ici (3 : ℝ))
        (fun x : ℝ => alphaCoshMajorant (2 * β) x)) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        alphaRemainder β
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameter hρ σ hσ) := by
  exact
    conditionalPetzRenyi_weighted_remainder_le_of_jensen
      (ρ := ρ) hρ (σ := σ) hσ β hβ
      (conditionalPetzRenyi_weighted_alphaCoshMajorant_le_of_concaveOn
        (ρ := ρ) hρ (σ := σ) hσ β hconc)

/-- Weighted remainder upper bound in the TCR small-parameter range
`0 ≤ β ≤ 1/4`, with the scalar concavity prerequisite discharged. -/
theorem conditionalPetzRenyi_weighted_remainder_le
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβquarter : β ≤ 1 / 4) :
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        alphaRemainder β
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameter hρ σ hσ) := by
  exact
    conditionalPetzRenyi_weighted_remainder_le_of_concaveOn
      (ρ := ρ) hρ (σ := σ) hσ β hβ0
      (alphaCoshMajorant_concaveOn_Ici_three
        (γ := 2 * β) (mul_nonneg zero_le_two hβ0) (by nlinarith))

/-- The arbitrary trace-style convergence parameter is at least `3`.

This is the support-indexed weighted AM-GM estimate
`E[√X + (√X)⁻¹ + 1] ≥ 3`. -/
theorem conditionalAlphaConvergenceParameterTrace_ge_three
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) :
    3 ≤ ρ.conditionalAlphaConvergenceParameterTrace σ := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  let w : Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd) → ℝ := fun x =>
    hρpsd.isHermitian.eigenvalues x.2.1 *
      Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
        (Uτ : CMatrix (Prod a b))) x.2.1 x.1)
  let p : Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd) → ℝ := fun x =>
    Real.sqrt (hρpsd.isHermitian.eigenvalues x.2.1 / hτ.isHermitian.eigenvalues x.1) +
      (Real.sqrt
        (hρpsd.isHermitian.eigenvalues x.2.1 / hτ.isHermitian.eigenvalues x.1))⁻¹ +
      1
  have hweights :=
    conditionalPetzRenyi_eigenbasis_support_weight_sum_eq_one
      (ρ := ρ) (σ := σ) hσ
  have hweights_local :
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i) = 1 := by
    simpa [hρpsd, τ, hτpos, hτ, Uτ, Uρ] using hweights
  have heta :=
    conditionalAlphaConvergenceParameterTrace_eq_support_eigenbasis_sqrt_sum
      (ρ := ρ) (σ := σ) hσ
  have hweight_nonneg :
      ∀ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), 0 ≤ w x := by
    intro x _
    exact mul_nonneg x.2.2.le (Complex.normSq_nonneg _)
  have hweight_sum :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x = 1 := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simpa [w] using hweights_local
  have hpoint :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x * 3 ≤
        ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x * p x := by
    apply Finset.sum_le_sum
    intro x hx
    have hτeig_pos : 0 < hτ.isHermitian.eigenvalues x.1 := by
      simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos x.1
    exact mul_le_mul_of_nonneg_left
      (three_le_sqrt_add_inv_add_one (div_pos x.2.2 hτeig_pos))
      (hweight_nonneg x hx)
  have hthree :
      (3 : ℝ) =
        ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x * 3 := by
    rw [← Finset.sum_mul, hweight_sum, one_mul]
  have harg :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x * p x =
        ρ.conditionalAlphaConvergenceParameterTrace σ := by
    rw [heta]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp [w, p]
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp_rw [mul_one]
    rw [hweights_local]
  calc
    (3 : ℝ) =
        ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x * 3 := hthree
    _ ≤ ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x * p x := hpoint
    _ = ρ.conditionalAlphaConvergenceParameterTrace σ := harg

/-- Support-indexed weighted remainder bound after the scalar step, assuming
the finite Jensen/concavity bridge for the trace-style `Upsilon`. -/
theorem conditionalPetzRenyi_weighted_remainder_le_support_of_jensen
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) (hβ : 0 ≤ β)
    (hJensen :
      (let hρpsd : ρ.matrix.PosSemidef := ρ.pos
       let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
       let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
       let hτ : τ.PosSemidef := hτpos.posSemidef
       let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
       let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
       ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          alphaCoshMajorant (2 * β)
            (Real.sqrt
                (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) +
              (Real.sqrt
                (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹ +
              1)) ≤
        alphaCoshMajorant (2 * β)
          (ρ.conditionalAlphaConvergenceParameterTrace σ)) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        alphaRemainder β
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameterTrace σ) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  have hpoint :
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        (hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i)) *
          alphaRemainder β
            (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) ≤
        ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
            alphaCoshMajorant (2 * β)
              (Real.sqrt
                  (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) +
                (Real.sqrt
                  (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹ +
                1) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hτeig_pos : 0 < hτ.isHermitian.eigenvalues i := by
      simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos i
    have hratio_pos :
        0 < hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i :=
      div_pos j.2 hτeig_pos
    have hweight_nonneg :
        0 ≤ hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i) :=
      mul_nonneg j.2.le (Complex.normSq_nonneg _)
    exact mul_le_mul_of_nonneg_left
      (alphaRemainder_le_alphaCoshMajorant_sqrt_add_inv_add_one hratio_pos hβ)
      hweight_nonneg
  exact hpoint.trans hJensen

/-- Support-indexed finite Jensen step for the weighted `s_{2β}` term,
assuming scalar concavity on `[3, ∞)`. -/
theorem conditionalPetzRenyi_weighted_alphaCoshMajorant_le_support_of_concaveOn
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ)
    (hconc :
      ConcaveOn ℝ (Set.Ici (3 : ℝ))
        (fun x : ℝ => alphaCoshMajorant (2 * β) x)) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        alphaCoshMajorant (2 * β)
          (Real.sqrt
              (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) +
            (Real.sqrt
              (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹ +
            1) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameterTrace σ) := by
  classical
  let hρpsd : ρ.matrix.PosSemidef := ρ.pos
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
  let hτ : τ.PosSemidef := hτpos.posSemidef
  let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
  let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
  let w : Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd) → ℝ := fun x =>
    hρpsd.isHermitian.eigenvalues x.2.1 *
      Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
        (Uτ : CMatrix (Prod a b))) x.2.1 x.1)
  let p : Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd) → ℝ := fun x =>
    Real.sqrt (hρpsd.isHermitian.eigenvalues x.2.1 / hτ.isHermitian.eigenvalues x.1) +
      (Real.sqrt
        (hρpsd.isHermitian.eigenvalues x.2.1 / hτ.isHermitian.eigenvalues x.1))⁻¹ +
      1
  let f : ℝ → ℝ := fun x => alphaCoshMajorant (2 * β) x
  have hweights :=
    conditionalPetzRenyi_eigenbasis_support_weight_sum_eq_one
      (ρ := ρ) (σ := σ) hσ
  have hweights_local :
      ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
        hρpsd.isHermitian.eigenvalues j.1 *
          Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
            (Uτ : CMatrix (Prod a b))) j.1 i) = 1 := by
    simpa [hρpsd, τ, hτpos, hτ, Uτ, Uρ] using hweights
  have heta :=
    conditionalAlphaConvergenceParameterTrace_eq_support_eigenbasis_sqrt_sum
      (ρ := ρ) (σ := σ) hσ
  have hweight_nonneg :
      ∀ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), 0 ≤ w x := by
    intro x _
    exact mul_nonneg x.2.2.le (Complex.normSq_nonneg _)
  have hweight_sum :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x = 1 := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simpa [w] using hweights_local
  have hp_mem :
      ∀ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), p x ∈ Set.Ici (3 : ℝ) := by
    intro x _
    have hτeig_pos : 0 < hτ.isHermitian.eigenvalues x.1 := by
      simpa [τ, hτpos, hτ] using hτpos.eigenvalues_pos x.1
    exact three_le_sqrt_add_inv_add_one (div_pos x.2.2 hτeig_pos)
  have hjensen :=
    hconc.le_map_sum
      (t := (Finset.univ.product Finset.univ :
        Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))))
      (w := w) (p := p) hweight_nonneg hweight_sum hp_mem
  have hleft :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x * f (p x) =
        ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
          (hρpsd.isHermitian.eigenvalues j.1 *
            Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
              (Uτ : CMatrix (Prod a b))) j.1 i)) *
            alphaCoshMajorant (2 * β)
              (Real.sqrt
                  (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) +
                (Real.sqrt
                  (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹ +
                1) := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
  have harg :
      ∑ x ∈ (Finset.univ.product Finset.univ :
          Finset (Prod (Prod a b) (psdSupportIndex ρ.matrix hρpsd))), w x * p x =
        ρ.conditionalAlphaConvergenceParameterTrace σ := by
    rw [heta]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp [w, p]
    simp_rw [mul_add, Finset.sum_add_distrib]
    simp_rw [mul_one]
    rw [hweights_local]
  change
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        alphaCoshMajorant (2 * β)
          (Real.sqrt
              (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) +
            (Real.sqrt
              (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i))⁻¹ +
            1) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameterTrace σ)
  rw [← hleft, ← harg]
  simpa [f, smul_eq_mul] using hjensen

/-- Support-indexed weighted remainder upper bound with scalar concavity as
the only remaining analytic input. -/
theorem conditionalPetzRenyi_weighted_remainder_le_support_of_concaveOn
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ) (hβ : 0 ≤ β)
    (hconc :
      ConcaveOn ℝ (Set.Ici (3 : ℝ))
        (fun x : ℝ => alphaCoshMajorant (2 * β) x)) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        alphaRemainder β
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameterTrace σ) := by
  exact
    conditionalPetzRenyi_weighted_remainder_le_support_of_jensen
      (ρ := ρ) (σ := σ) hσ β hβ
      (conditionalPetzRenyi_weighted_alphaCoshMajorant_le_support_of_concaveOn
        (ρ := ρ) (σ := σ) hσ β hconc)

/-- Support-indexed weighted remainder upper bound in the TCR small-parameter
range `0 ≤ β ≤ 1/4`, with the scalar concavity prerequisite discharged. -/
theorem conditionalPetzRenyi_weighted_remainder_le_support
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβquarter : β ≤ 1 / 4) :
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        alphaRemainder β
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i) ≤
      alphaCoshMajorant (2 * β)
        (ρ.conditionalAlphaConvergenceParameterTrace σ) := by
  exact
    conditionalPetzRenyi_weighted_remainder_le_support_of_concaveOn
      (ρ := ρ) (σ := σ) hσ β hβ0
      (alphaCoshMajorant_concaveOn_Ici_three
        (γ := 2 * β) (mul_nonneg zero_le_two hβ0) (by nlinarith))

/-- Finite-AEP eta specialized to the canonical side reference `ρ_B`. -/
def finiteAEPEta
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) : ℝ :=
  ρ.conditionalAlphaConvergenceParameter hρ ρ.marginalB hρB

/-- Arbitrary-state trace-term spelling of the canonical finite-AEP eta
`Upsilon(A|B)_{rho|rho}`. -/
def finiteAEPEtaTrace (ρ : State (Prod a b)) : ℝ :=
  ρ.conditionalAlphaConvergenceParameterTrace ρ.marginalB

/-- Compressing the conditioning register to the support of the canonical
reference preserves the trace-term finite-AEP eta. -/
theorem finiteAEPEtaTrace_conditioningSupportCompressedState
    (ρ : State (Prod a b)) :
    ρ.conditioningSupportCompressedState.finiteAEPEtaTrace = ρ.finiteAEPEtaTrace := by
  rw [finiteAEPEtaTrace, finiteAEPEtaTrace, conditionalAlphaConvergenceParameterTrace,
    conditionalAlphaConvergenceParameterTrace]
  rw [
    conditionalPetzRenyiTraceTerm_conditioningSupportCompressedState
      (ρ := ρ) (α := 3 / 2) (by norm_num) (by norm_num),
    conditionalPetzRenyiTraceTerm_conditioningSupportCompressedState
      (ρ := ρ) (α := 1 / 2) (by norm_num) (by norm_num)]

/-- The finite-AEP trace eta of a tensor power, stated through the exact Petz
trace powers. -/
theorem tensorPowerBipartite_finiteAEPEtaTrace_canonical_eq_pow_terms
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef) (n : ℕ) :
    (ρ.tensorPowerBipartite n).finiteAEPEtaTrace =
      (ρ.conditionalPetzRenyiTraceTerm ρ.marginalB (3 / 2)) ^ n +
        (ρ.conditionalPetzRenyiTraceTerm ρ.marginalB (1 / 2)) ^ n + 1 := by
  rw [finiteAEPEtaTrace,
    tensorPowerBipartite_conditionalAlphaConvergenceParameterTrace_canonical_eq_pow_terms
      (ρ := ρ) hρB n]

/-- The arbitrary trace-term canonical finite-AEP eta is at least `1`. -/
theorem one_le_finiteAEPEtaTrace (ρ : State (Prod a b)) :
    1 ≤ ρ.finiteAEPEtaTrace :=
  ρ.one_le_conditionalAlphaConvergenceParameterTrace ρ.marginalB

private theorem scalar_pow_terms_le_pow_sum
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) (hn : 0 < n) :
    x ^ n + y ^ n + 1 ≤ (x + y + 1) ^ n := by
  let s : ℝ := x + y + 1
  have hsx : x ≤ s := by
    dsimp [s]
    linarith
  have hsy : y ≤ s := by
    dsimp [s]
    linarith
  have hs1 : (1 : ℝ) ≤ s := by
    dsimp [s]
    linarith
  have hs_nonneg : 0 ≤ s := le_trans zero_le_one hs1
  have hsucc : ∀ k : ℕ, x ^ (k + 1) + y ^ (k + 1) + 1 ≤ s ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
        dsimp [s]
        ring_nf
        exact le_rfl
    | succ k ih =>
        have hxpow : 0 ≤ x ^ (k + 1) := pow_nonneg hx _
        have hypow : 0 ≤ y ^ (k + 1) := pow_nonneg hy _
        have hxle : x ^ (k + 1 + 1) ≤ x ^ (k + 1) * s := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left hsx hxpow
        have hyle : y ^ (k + 1 + 1) ≤ y ^ (k + 1) * s := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left hsy hypow
        have h1le : (1 : ℝ) ≤ 1 * s := by
          simpa using hs1
        have hterm :
            x ^ (k + 1 + 1) + y ^ (k + 1 + 1) + 1 ≤
              (x ^ (k + 1) + y ^ (k + 1) + 1) * s := by
          calc
            x ^ (k + 1 + 1) + y ^ (k + 1 + 1) + 1 ≤
                x ^ (k + 1) * s + y ^ (k + 1) * s + 1 * s := by
              linarith
            _ = (x ^ (k + 1) + y ^ (k + 1) + 1) * s := by
              ring
        have hmul :
            (x ^ (k + 1) + y ^ (k + 1) + 1) * s ≤
              s ^ (k + 1) * s :=
          mul_le_mul_of_nonneg_right ih hs_nonneg
        calc
          x ^ (k + 1 + 1) + y ^ (k + 1 + 1) + 1 ≤
              (x ^ (k + 1) + y ^ (k + 1) + 1) * s := hterm
          _ ≤ s ^ (k + 1) * s := hmul
          _ = s ^ (k + 1 + 1) := by
            exact (pow_succ s (k + 1)).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa [s] using hsucc k

/-- The tensor-power finite-AEP trace eta is bounded by the tensor power of
the one-copy finite-AEP trace eta. -/
theorem tensorPowerBipartite_finiteAEPEtaTrace_le_pow
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (n : ℕ) (hn : 0 < n) :
    (ρ.tensorPowerBipartite n).finiteAEPEtaTrace ≤
      ρ.finiteAEPEtaTrace ^ n := by
  rw [tensorPowerBipartite_finiteAEPEtaTrace_canonical_eq_pow_terms
    (ρ := ρ) hρB n]
  have h32 : 0 ≤ ρ.conditionalPetzRenyiTraceTerm ρ.marginalB (3 / 2) :=
    ρ.conditionalPetzRenyiTraceTerm_nonneg ρ.marginalB (3 / 2)
  have h12 : 0 ≤ ρ.conditionalPetzRenyiTraceTerm ρ.marginalB (1 / 2) :=
    ρ.conditionalPetzRenyiTraceTerm_nonneg ρ.marginalB (1 / 2)
  simpa [finiteAEPEtaTrace, conditionalAlphaConvergenceParameterTrace] using
    scalar_pow_terms_le_pow_sum (x := ρ.conditionalPetzRenyiTraceTerm ρ.marginalB (3 / 2))
      (y := ρ.conditionalPetzRenyiTraceTerm ρ.marginalB (1 / 2)) h32 h12 n hn

/-- Base-two logarithmic form of the tensor-power finite-AEP trace eta
subadditivity bound. -/
theorem log2_tensorPowerBipartite_finiteAEPEtaTrace_le
    (ρ : State (Prod a b)) (hρB : ρ.marginalB.matrix.PosDef)
    (n : ℕ) (hn : 0 < n) :
    log2 ((ρ.tensorPowerBipartite n).finiteAEPEtaTrace) ≤
      (n : ℝ) * log2 ρ.finiteAEPEtaTrace := by
  have hle :
      (ρ.tensorPowerBipartite n).finiteAEPEtaTrace ≤
        ρ.finiteAEPEtaTrace ^ n :=
    ρ.tensorPowerBipartite_finiteAEPEtaTrace_le_pow hρB n hn
  have hleft_pos :
      0 < (ρ.tensorPowerBipartite n).finiteAEPEtaTrace :=
    lt_of_lt_of_le zero_lt_one
      (one_le_finiteAEPEtaTrace (ρ.tensorPowerBipartite n))
  have hlog_le :
      Real.log ((ρ.tensorPowerBipartite n).finiteAEPEtaTrace) ≤
        Real.log (ρ.finiteAEPEtaTrace ^ n) :=
    Real.log_le_log hleft_pos hle
  have hdiv := div_le_div_of_nonneg_right hlog_le
    (le_of_lt (Real.log_pos one_lt_two))
  unfold log2
  calc
    Real.log ((ρ.tensorPowerBipartite n).finiteAEPEtaTrace) / Real.log 2 ≤
        Real.log (ρ.finiteAEPEtaTrace ^ n) / Real.log 2 := hdiv
    _ = (n : ℝ) * (Real.log ρ.finiteAEPEtaTrace / Real.log 2) := by
      rw [Real.log_pow]
      ring

@[simp]
theorem finiteAEPEta_eq
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) :
    ρ.finiteAEPEta hρ hρB =
      ρ.conditionalAlphaConvergenceParameter hρ ρ.marginalB hρB :=
  rfl

/-- The positive-definite finite-AEP eta agrees with the arbitrary trace-term
spelling. -/
theorem finiteAEPEta_eq_trace
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) :
    ρ.finiteAEPEta hρ hρB = ρ.finiteAEPEtaTrace := by
  rw [finiteAEPEta_eq, finiteAEPEtaTrace,
    conditionalAlphaConvergenceParameter_eq_trace]

private theorem rpow_two_pos (x : ℝ) : 0 < Real.rpow 2 x :=
  Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x

/-- The TCR convergence parameter is strictly larger than `1`. -/
theorem one_lt_conditionalAlphaConvergenceParameter
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    1 < ρ.conditionalAlphaConvergenceParameter hρ σ hσ := by
  unfold conditionalAlphaConvergenceParameter
  have h₁ : 0 < Real.rpow 2
      (-(1 / 2 : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (3 / 2)
          (by norm_num) (by norm_num)) :=
    rpow_two_pos _
  have h₂ : 0 < Real.rpow 2
      ((1 / 2 : ℝ) *
        ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ (1 / 2)
          (by norm_num) (by norm_num)) :=
    rpow_two_pos _
  linarith

/-- The TCR convergence parameter is at least `1`. -/
theorem one_le_conditionalAlphaConvergenceParameter
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    1 ≤ ρ.conditionalAlphaConvergenceParameter hρ σ hσ :=
  le_of_lt (ρ.one_lt_conditionalAlphaConvergenceParameter hρ σ hσ)

/-- The TCR convergence parameter is positive. -/
theorem conditionalAlphaConvergenceParameter_pos
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    0 < ρ.conditionalAlphaConvergenceParameter hρ σ hσ :=
  lt_trans zero_lt_one (ρ.one_lt_conditionalAlphaConvergenceParameter hρ σ hσ)

/-- The natural logarithm of the TCR convergence parameter is positive. -/
theorem log_conditionalAlphaConvergenceParameter_pos
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    0 < Real.log (ρ.conditionalAlphaConvergenceParameter hρ σ hσ) :=
  Real.log_pos (ρ.one_lt_conditionalAlphaConvergenceParameter hρ σ hσ)

/-- The base-two logarithm of the TCR convergence parameter is positive. -/
theorem log2_conditionalAlphaConvergenceParameter_pos
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef) :
    0 < log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ) := by
  unfold log2
  exact div_pos (ρ.log_conditionalAlphaConvergenceParameter_pos hρ σ hσ)
    (Real.log_pos one_lt_two)

private theorem log_three_sq_div_eight_le_one_sub_log_two :
    ((Real.log 3 / 2) ^ 2) / 2 ≤ 1 - Real.log 2 := by
  have hlog3_nonneg : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  have hlog3_lt : Real.log 3 < 1.0986122888 := Real.log_three_lt_d9
  have hlog2_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  nlinarith

private theorem alpha_sub_one_le_quarter_of_alpha_lt
    {α η : ℝ} (hη3 : 3 ≤ η)
    (hα_lt : α < 1 + log2 3 / (4 * log2 η)) :
    α - 1 ≤ 1 / 4 := by
  have hlog2η_pos : 0 < log2 η := by
    unfold log2
    exact div_pos (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hη3))
      (Real.log_pos one_lt_two)
  have hlog2η_ge_log2_three : log2 3 ≤ log2 η := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hη3)
      (le_of_lt (Real.log_pos one_lt_two))
  have hquot : log2 3 / (4 * log2 η) ≤ 1 / 4 := by
    rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hlog2η_pos)]
    nlinarith
  have hβlt : α - 1 < log2 3 / (4 * log2 η) := by
    linarith
  exact (le_of_lt hβlt).trans hquot

private theorem alpha_window_taylor_small
    {α η : ℝ} (hα_gt : 1 < α) (hη1 : 1 < η)
    (hα_lt : α < 1 + log2 3 / (4 * log2 η)) :
    (((2 * (α - 1) * Real.log η) ^ 2) / 2) ≤ 1 - Real.log 2 := by
  have hlogη_pos : 0 < Real.log η := Real.log_pos hη1
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hβ_pos : 0 < α - 1 := sub_pos.mpr hα_gt
  have hquot_eq :
      log2 3 / (4 * log2 η) = Real.log 3 / (4 * Real.log η) := by
    unfold log2
    field_simp [(Real.log_pos one_lt_two).ne', hlogη_pos.ne']
  have hβ_lt : α - 1 < Real.log 3 / (4 * Real.log η) := by
    simpa [hquot_eq] using sub_lt_iff_lt_add'.mpr hα_lt
  have hβlog_lt : (α - 1) * Real.log η < Real.log 3 / 4 := by
    have hmul := mul_lt_mul_of_pos_right hβ_lt hlogη_pos
    have hright :
        Real.log 3 / (4 * Real.log η) * Real.log η = Real.log 3 / 4 := by
      field_simp [hlogη_pos.ne']
    simpa [hright, mul_comm, mul_left_comm, mul_assoc] using hmul
  have harg_nonneg : 0 ≤ 2 * (α - 1) * Real.log η := by positivity
  have harg_le : 2 * (α - 1) * Real.log η ≤ Real.log 3 / 2 := by
    nlinarith
  have hright_nonneg : 0 ≤ Real.log 3 / 2 := by positivity
  have hsq :
      (2 * (α - 1) * Real.log η) ^ 2 ≤ (Real.log 3 / 2) ^ 2 := by
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg harg_nonneg, abs_of_nonneg hright_nonneg]
      exact harg_le)
  exact (div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2)).trans
    log_three_sq_div_eight_le_one_sub_log_two

/-- Positive-definite alpha-to-von-Neumann lower bound for the fixed-reference
conditional Petz candidate in the TCR small-parameter window. -/
theorem conditionalPetzRenyiEntropyCandidate_alpha_bound_posDef
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ)
    (hα_gt : 1 < α)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ))) :
    ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt)
        ((ne_of_lt hα_gt).symm) ≥
      ρ.conditionalEntropyRelative hρ σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameter hρ σ hσ)) ^ 2 := by
  classical
  let β : ℝ := α - 1
  let η : ℝ := ρ.conditionalAlphaConvergenceParameter hρ σ hσ
  let H : ℝ := ρ.conditionalEntropyRelative hρ σ hσ
  let L : ℝ :=
    ((ρ.matrix * psdLog ρ.matrix hρ).trace).re -
      ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re
  let R : ℝ :=
    let hρpsd : ρ.matrix.PosSemidef := hρ.posSemidef
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j,
      (hρpsd.isHermitian.eigenvalues j *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j i)) *
        alphaRemainder β
          (hρpsd.isHermitian.eigenvalues j / hτ.isHermitian.eigenvalues i)
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact sub_pos.mpr hα_gt
  have hβ_nonneg : 0 ≤ β := le_of_lt hβ_pos
  have hα_eq : α = 1 + β := by
    dsimp [β]
    ring
  have hη_ge_three : 3 ≤ η := by
    dsimp [η]
    exact conditionalAlphaConvergenceParameter_ge_three (ρ := ρ) hρ (σ := σ) hσ
  have hη_one : 1 < η := by
    linarith
  have hβ_quarter : β ≤ 1 / 4 := by
    dsimp [β, η]
    exact alpha_sub_one_le_quarter_of_alpha_lt hη_ge_three hα_lt
  have hsmall :
      ((2 * β * Real.log η) ^ 2) / 2 ≤ 1 - Real.log 2 := by
    dsimp [β, η]
    exact alpha_window_taylor_small hα_gt hη_one hα_lt
  have htrace_pos :
      0 < ρ.conditionalPetzRenyiTraceTerm σ α :=
    conditionalPetzRenyiTraceTerm_pos_of_posDef (ρ := ρ) hρ (σ := σ) hσ α
  have hremainder :
      R ≤ alphaCoshMajorant (2 * β) η := by
    dsimp [R, η]
    exact conditionalPetzRenyi_weighted_remainder_le
      (ρ := ρ) hρ (σ := σ) hσ β hβ_nonneg hβ_quarter
  have htail_scaled :
      (1 / (β * Real.log 2)) * R ≤ 4 * β * (log2 η) ^ 2 := by
    exact (mul_le_mul_of_nonneg_left hremainder (by positivity)).trans
      (alphaCoshMajorant_two_mul_taylor_bound hβ_pos hη_one hsmall)
  have hL_eq : L = -H * Real.log 2 := by
    dsimp [L, H, conditionalEntropyRelative]
    field_simp [(Real.log_pos one_lt_two).ne']
  have htrace_expand :
      ρ.conditionalPetzRenyiTraceTerm σ α = 1 + β * L + R := by
    rw [hα_eq]
    dsimp [L, R, β]
    simpa using
      conditionalPetzRenyiTraceTerm_one_add_eq_one_add_beta_matrix_log_add_remainder
        (ρ := ρ) hρ (σ := σ) hσ (α - 1)
  have hlog_bound :
      log2 (ρ.conditionalPetzRenyiTraceTerm σ α) ≤
        β * (-H * Real.log 2) / Real.log 2 + R / Real.log 2 := by
    unfold log2
    have hlog_le :
        Real.log (ρ.conditionalPetzRenyiTraceTerm σ α) ≤
          ρ.conditionalPetzRenyiTraceTerm σ α - 1 :=
      Real.log_le_sub_one_of_pos htrace_pos
    have hsub :
        ρ.conditionalPetzRenyiTraceTerm σ α - 1 = β * L + R := by
      rw [htrace_expand]
      ring
    have hdiv := div_le_div_of_nonneg_right hlog_le
      (le_of_lt (Real.log_pos one_lt_two))
    calc
      Real.log (ρ.conditionalPetzRenyiTraceTerm σ α) / Real.log 2 ≤
          (ρ.conditionalPetzRenyiTraceTerm σ α - 1) / Real.log 2 := hdiv
      _ = (β * L + R) / Real.log 2 := by rw [hsub]
      _ = β * (-H * Real.log 2) / Real.log 2 + R / Real.log 2 := by
        rw [hL_eq]
        ring
  have hcandidate_eq :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) =
        -(1 / β) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) := by
    dsimp [conditionalPetzRenyiEntropyCandidate, conditionalPetzRenyiTraceTerm]
    change (1 / (1 - α)) *
        log2 ((CFC.rpow ρ.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := a) σ) (1 - α)).trace).re =
      -(1 / β) *
        log2 ((CFC.rpow ρ.matrix α *
          CFC.rpow (identityTensorStateMatrix (a := a) σ) (1 - α)).trace).re
    have hone : 1 - α = -β := by
      dsimp [β]
      ring
    rw [hone]
    field_simp [hβ_pos.ne']
  have hmain :
      ρ.conditionalPetzRenyiEntropyCandidate hρ σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        H - 4 * β * (log2 η) ^ 2 := by
    rw [hcandidate_eq]
    have hneg :
        -(1 / β) *
            (β * (-H * Real.log 2) / Real.log 2 + R / Real.log 2) ≤
          -(1 / β) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) := by
      have hfactor_nonpos : -(1 / β) ≤ 0 := by
        exact neg_nonpos.mpr (one_div_nonneg.mpr hβ_nonneg)
      exact mul_le_mul_of_nonpos_left hlog_bound hfactor_nonpos
    have htail :
        R / (β * Real.log 2) ≤ 4 * β * (log2 η) ^ 2 := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htail_scaled
    calc
      H - 4 * β * (log2 η) ^ 2 ≤ H - R / (β * Real.log 2) := by
        linarith
      _ = -(1 / β) *
            (β * (-H * Real.log 2) / Real.log 2 + R / Real.log 2) := by
        field_simp [hβ_pos.ne', (Real.log_pos one_lt_two).ne']
        ring
      _ ≤ -(1 / β) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) := hneg
  simpa [β, η, H] using hmain

/-- Arbitrary-left, full-reference alpha-to-von-Neumann lower bound for the
fixed-reference conditional Petz candidate in the TCR small-parameter window. -/
theorem conditionalPetzRenyiEntropyCandidateFullReference_alpha_bound
    (ρ : State (Prod a b))
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ)
    (hα_gt : 1 < α)
    (hα_lt :
      α < 1 + log2 3 /
        (4 * log2 (ρ.conditionalAlphaConvergenceParameterTrace σ))) :
    ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
        (lt_trans zero_lt_one hα_gt)
        ((ne_of_lt hα_gt).symm) ≥
      ρ.conditionalEntropyRelativeFullReference σ hσ -
        4 * (α - 1) *
          (log2 (ρ.conditionalAlphaConvergenceParameterTrace σ)) ^ 2 := by
  classical
  let β : ℝ := α - 1
  let η : ℝ := ρ.conditionalAlphaConvergenceParameterTrace σ
  let H : ℝ := ρ.conditionalEntropyRelativeFullReference σ hσ
  let L : ℝ :=
    ρ.supportEntropyTraceTerm -
      ((ρ.matrix *
        psdLog (identityTensorStateMatrix (a := a) σ)
          (identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ)).trace).re
  let R : ℝ :=
    let hρpsd : ρ.matrix.PosSemidef := ρ.pos
    let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
    let hτpos : τ.PosDef := identityTensorStateMatrix_posDef_of_posDef (a := a) σ hσ
    let hτ : τ.PosSemidef := hτpos.posSemidef
    let Uτ : Matrix.unitaryGroup (Prod a b) ℂ := hτ.isHermitian.eigenvectorUnitary
    let Uρ : Matrix.unitaryGroup (Prod a b) ℂ := hρpsd.isHermitian.eigenvectorUnitary
    ∑ i, ∑ j : psdSupportIndex ρ.matrix hρpsd,
      (hρpsd.isHermitian.eigenvalues j.1 *
        Complex.normSq ((star (Uρ : CMatrix (Prod a b)) *
          (Uτ : CMatrix (Prod a b))) j.1 i)) *
        alphaRemainder β
          (hρpsd.isHermitian.eigenvalues j.1 / hτ.isHermitian.eigenvalues i)
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact sub_pos.mpr hα_gt
  have hβ_nonneg : 0 ≤ β := le_of_lt hβ_pos
  have hα_eq : α = 1 + β := by
    dsimp [β]
    ring
  have hη_ge_three : 3 ≤ η := by
    dsimp [η]
    exact conditionalAlphaConvergenceParameterTrace_ge_three (ρ := ρ) (σ := σ) hσ
  have hη_one : 1 < η := by
    linarith
  have hβ_quarter : β ≤ 1 / 4 := by
    dsimp [β, η]
    exact alpha_sub_one_le_quarter_of_alpha_lt hη_ge_three hα_lt
  have hsmall :
      ((2 * β * Real.log η) ^ 2) / 2 ≤ 1 - Real.log 2 := by
    dsimp [β, η]
    exact alpha_window_taylor_small hα_gt hη_one hα_lt
  have htrace_pos :
      0 < ρ.conditionalPetzRenyiTraceTerm σ α :=
    conditionalPetzRenyiTraceTerm_pos_of_fullReference (ρ := ρ) (σ := σ) hσ α
  have hremainder :
      R ≤ alphaCoshMajorant (2 * β) η := by
    dsimp [R, η]
    exact conditionalPetzRenyi_weighted_remainder_le_support
      (ρ := ρ) (σ := σ) hσ β hβ_nonneg hβ_quarter
  have htail_scaled :
      (1 / (β * Real.log 2)) * R ≤ 4 * β * (log2 η) ^ 2 := by
    exact (mul_le_mul_of_nonneg_left hremainder (by positivity)).trans
      (alphaCoshMajorant_two_mul_taylor_bound hβ_pos hη_one hsmall)
  have hL_eq : L = -H * Real.log 2 := by
    dsimp [L, H, conditionalEntropyRelativeFullReference]
    field_simp [(Real.log_pos one_lt_two).ne']
  have htrace_expand :
      ρ.conditionalPetzRenyiTraceTerm σ α = 1 + β * L + R := by
    rw [hα_eq]
    dsimp [L, R, β]
    simpa using
      conditionalPetzRenyiTraceTerm_one_add_eq_one_add_beta_support_entropy_trace_add_remainder
        (ρ := ρ) (σ := σ) hσ (α - 1) hβ_pos
  have hlog_bound :
      log2 (ρ.conditionalPetzRenyiTraceTerm σ α) ≤
        β * (-H * Real.log 2) / Real.log 2 + R / Real.log 2 := by
    unfold log2
    have hlog_le :
        Real.log (ρ.conditionalPetzRenyiTraceTerm σ α) ≤
          ρ.conditionalPetzRenyiTraceTerm σ α - 1 :=
      Real.log_le_sub_one_of_pos htrace_pos
    have hsub :
        ρ.conditionalPetzRenyiTraceTerm σ α - 1 = β * L + R := by
      rw [htrace_expand]
      ring
    have hdiv := div_le_div_of_nonneg_right hlog_le
      (le_of_lt (Real.log_pos one_lt_two))
    calc
      Real.log (ρ.conditionalPetzRenyiTraceTerm σ α) / Real.log 2 ≤
          (ρ.conditionalPetzRenyiTraceTerm σ α - 1) / Real.log 2 := hdiv
      _ = (β * L + R) / Real.log 2 := by rw [hsub]
      _ = β * (-H * Real.log 2) / Real.log 2 + R / Real.log 2 := by
        rw [hL_eq]
        ring
  have hcandidate_eq :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) =
        -(1 / β) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) := by
    dsimp [conditionalPetzRenyiEntropyCandidateFullReference]
    change (1 / (1 - α)) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) =
      -(1 / β) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α)
    have hone : 1 - α = -β := by
      dsimp [β]
      ring
    rw [hone]
    field_simp [hβ_pos.ne']
  have hmain :
      ρ.conditionalPetzRenyiEntropyCandidateFullReference σ hσ α
          (lt_trans zero_lt_one hα_gt) ((ne_of_lt hα_gt).symm) ≥
        H - 4 * β * (log2 η) ^ 2 := by
    rw [hcandidate_eq]
    have hneg :
        -(1 / β) *
            (β * (-H * Real.log 2) / Real.log 2 + R / Real.log 2) ≤
          -(1 / β) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) := by
      have hfactor_nonpos : -(1 / β) ≤ 0 := by
        exact neg_nonpos.mpr (one_div_nonneg.mpr hβ_nonneg)
      exact mul_le_mul_of_nonpos_left hlog_bound hfactor_nonpos
    have htail :
        R / (β * Real.log 2) ≤ 4 * β * (log2 η) ^ 2 := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htail_scaled
    calc
      H - 4 * β * (log2 η) ^ 2 ≤ H - R / (β * Real.log 2) := by
        linarith
      _ = -(1 / β) *
            (β * (-H * Real.log 2) / Real.log 2 + R / Real.log 2) := by
        field_simp [hβ_pos.ne', (Real.log_pos one_lt_two).ne']
        ring
      _ ≤ -(1 / β) * log2 (ρ.conditionalPetzRenyiTraceTerm σ α) := hneg
  simpa [β, η, H] using hmain

/-- The canonical finite-AEP eta is strictly larger than `1`. -/
theorem one_lt_finiteAEPEta
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) :
    1 < ρ.finiteAEPEta hρ hρB := by
  rw [finiteAEPEta_eq]
  exact ρ.one_lt_conditionalAlphaConvergenceParameter hρ ρ.marginalB hρB

/-- The canonical finite-AEP eta is at least `1`. -/
theorem one_le_finiteAEPEta
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) :
    1 ≤ ρ.finiteAEPEta hρ hρB :=
  le_of_lt (ρ.one_lt_finiteAEPEta hρ hρB)

/-- The canonical finite-AEP eta is at least `3`, the numerical lower bound
used in the TCR alpha-window estimates. -/
theorem three_le_finiteAEPEta
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) :
    3 ≤ ρ.finiteAEPEta hρ hρB := by
  rw [finiteAEPEta_eq]
  exact conditionalAlphaConvergenceParameter_ge_three (ρ := ρ) hρ
    (σ := ρ.marginalB) hρB

/-- The canonical finite-AEP eta is positive. -/
theorem finiteAEPEta_pos
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) :
    0 < ρ.finiteAEPEta hρ hρB :=
  lt_trans zero_lt_one (ρ.one_lt_finiteAEPEta hρ hρB)

/-- The natural logarithm of the canonical finite-AEP eta is positive. -/
theorem log_finiteAEPEta_pos
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) :
    0 < Real.log (ρ.finiteAEPEta hρ hρB) :=
  Real.log_pos (ρ.one_lt_finiteAEPEta hρ hρB)

/-- The base-two logarithm of the canonical finite-AEP eta is positive. -/
theorem log2_finiteAEPEta_pos
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (hρB : ρ.marginalB.matrix.PosDef) :
    0 < log2 (ρ.finiteAEPEta hρ hρB) := by
  unfold log2
  exact div_pos (ρ.log_finiteAEPEta_pos hρ hρB) (Real.log_pos one_lt_two)

end State

end

end QIT
