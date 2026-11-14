/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.ConditionalRenyiMinimax

/-!
# Singular-boundary completion of the conditional Renyi minimax step

This module removes the compact full-support cutoff from the Sion minimax
step in Tomamichel's proof of upward sandwiched conditional Renyi duality.

Source: [Tomamichel2015FiniteResources, cond.tex:361-397], the proof of
Proposition `pr:dual-new`. The support restriction and compact
positive-eigenvalue cutoff are described in `cond.tex`, lines 100-103.

The formal boundary argument keeps the source's common Holder bracket, support
restriction, positive spectral cutoff, Sion exchange, and identity
regularization. Since Sion only needs one optimization domain to be compact,
the final exchange uses the compact `tau` density domain and the convex
full-rank `sigma` domain; the proved cutoff theorem records the source's
compact restriction explicitly. Pointwise identity regularization then removes
the full-rank boundary inside each fixed-`tau` infimum.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QIT

universe u v w

noncomputable section

private theorem ereal_neg_iInf_eq_iSup_neg_boundary {i : Sort _} (f : i -> EReal) :
    -(⨅ x, f x) = ⨆ x, -f x := by
  have h := OrderIso.map_iInf EReal.negOrderIso f
  change OrderDual.ofDual (EReal.negOrderIso (⨅ x, f x)) = _
  rw [h]
  rfl

private theorem ereal_neg_iSup_eq_iInf_neg_boundary {i : Sort _} (f : i -> EReal) :
    -(⨆ x, f x) = ⨅ x, -f x := by
  have h := OrderIso.map_iSup EReal.negOrderIso f
  change OrderDual.ofDual (EReal.negOrderIso (⨆ x, f x)) = _
  rw [h]
  rfl

private theorem ereal_sion_from_neg_boundary
    {i k : Sort _} (F : i -> k -> EReal)
    (h : (⨅ y : k, ⨆ x : i, -F x y) = ⨆ x : i, ⨅ y : k, -F x y) :
    (⨅ x : i, ⨆ y : k, F x y) = ⨆ y : k, ⨅ x : i, F x y := by
  have hneg := congrArg Neg.neg h
  rw [ereal_neg_iInf_eq_iSup_neg_boundary,
    ereal_neg_iSup_eq_iInf_neg_boundary] at hneg
  simp_rw [ereal_neg_iSup_eq_iInf_neg_boundary,
    ereal_neg_iInf_eq_iSup_neg_boundary, neg_neg] at hneg
  exact hneg.symm

private theorem antitone_ereal_neg_coe_boundary :
    Antitone (fun x : Real => -((x : EReal))) := by
  intro x y hxy
  exact EReal.neg_le_neg_iff.mpr (EReal.coe_le_coe_iff.mpr hxy)

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

/-- Sion exchange on the full-rank `sigma` domain. The compact variable is
the `tau` density domain; applying Sion to the negative bracket gives the
source `inf_sigma sup_tau` orientation without assuming compactness of the
open full-rank set. -/
theorem fullRankDensityMatrixSet_sion_abcSidePowerTraceRe_EReal_boundary
    [Nonempty c] {p : Real}
    {R : CMatrix (Prod (Prod a b) c)} (hR : R.PosSemidef)
    (hp0 : 0 < p) (hp1 : p <= 1) :
    (⨅ sigma : CMatrix b,
      ⨅ _hSigma : fullRankDensityMatrixSet b sigma,
        ⨆ tau : CMatrix c,
          ⨆ _hTau : densityMatrixSet c tau,
            (abcSidePowerTraceRe (a := a) R sigma tau p : EReal)) =
      ⨆ tau : CMatrix c,
        ⨆ _hTau : densityMatrixSet c tau,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : fullRankDensityMatrixSet b sigma,
              (abcSidePowerTraceRe (a := a) R sigma tau p : EReal) := by
  let F : {sigma : CMatrix b // fullRankDensityMatrixSet b sigma} ->
      {tau : CMatrix c // densityMatrixSet c tau} -> EReal :=
    fun sigma tau => (abcSidePowerTraceRe (a := a) R sigma.1 tau.1 p : EReal)
  have hnegMem :
      (⨅ tau : CMatrix c,
        ⨅ _hTau : densityMatrixSet c tau,
          ⨆ sigma : CMatrix b,
            ⨆ _hSigma : fullRankDensityMatrixSet b sigma,
              -((abcSidePowerTraceRe (a := a) R sigma tau p : EReal))) =
        ⨆ sigma : CMatrix b,
          ⨆ _hSigma : fullRankDensityMatrixSet b sigma,
            ⨅ tau : CMatrix c,
              ⨅ _hTau : densityMatrixSet c tau,
                -((abcSidePowerTraceRe (a := a) R sigma tau p : EReal)) := by
    exact sion_iInf_iSup_eq_iSup_iInf
      (densityMatrixSet_nonempty (a := c))
      (densityMatrixSet_convex (a := c))
      (densityMatrixSet_isCompact (a := c))
      (fun sigma hSigma => by
        have hcontReal : ContinuousOn
            (fun tau : CMatrix c => abcSidePowerTraceRe (a := a) R sigma tau p)
            (densityMatrixSet c) :=
          (abcSidePowerTraceRe_continuousOn_tau_posSemidef
            (a := a) R sigma hp0).mono (fun tau hTau => hTau.1)
        have hcontE : ContinuousOn
            (fun tau : CMatrix c =>
              (abcSidePowerTraceRe (a := a) R sigma tau p : EReal))
            (densityMatrixSet c) :=
          continuous_coe_real_ereal.comp_continuousOn hcontReal
        exact ContinuousOn.lowerSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun sigma hSigma => by
        simpa [Function.comp_def] using
          (Convex.quasiconcaveOn_restrict
            (abcSidePowerTraceRe_quasiconcaveOn_tau
              (a := a) hR hSigma.1.posSemidef hp0 hp1)
            (fun tau hTau => hTau.1)
            (densityMatrixSet_convex (a := c))).antitone_comp
              antitone_ereal_neg_coe_boundary)
      (fullRankDensityMatrixSet_convex (a := b))
      (fun tau hTau => by
        have hcontReal : ContinuousOn
            (fun sigma : CMatrix b => abcSidePowerTraceRe (a := a) R sigma tau p)
            (fullRankDensityMatrixSet b) :=
          (abcSidePowerTraceRe_continuousOn_sigma_posDef
            (a := a) R tau p).mono (fun sigma hSigma => hSigma.1)
        have hcontE : ContinuousOn
            (fun sigma : CMatrix b =>
              (abcSidePowerTraceRe (a := a) R sigma tau p : EReal))
            (fullRankDensityMatrixSet b) :=
          continuous_coe_real_ereal.comp_continuousOn hcontReal
        exact ContinuousOn.upperSemicontinuousOn
          (continuous_neg.comp_continuousOn hcontE))
      (fun tau hTau => by
        simpa [Function.comp_def] using
          (Convex.quasiconvexOn_restrict
            (abcSidePowerTraceRe_quasiconvexOn_sigma_posDef
              (a := a) hR hTau.1 hp0 hp1)
            (fun sigma hSigma => hSigma.1)
            (fullRankDensityMatrixSet_convex (a := b))).antitone_comp
              antitone_ereal_neg_coe_boundary)
  have hnegSub :
      (⨅ tau : {tau : CMatrix c // densityMatrixSet c tau},
        ⨆ sigma : {sigma : CMatrix b // fullRankDensityMatrixSet b sigma},
          -F sigma tau) =
        ⨆ sigma : {sigma : CMatrix b // fullRankDensityMatrixSet b sigma},
          ⨅ tau : {tau : CMatrix c // densityMatrixSet c tau},
            -F sigma tau := by
    simpa [F, iInf_subtype', iSup_subtype'] using hnegMem
  have hsub := ereal_sion_from_neg_boundary F hnegSub
  simpa [F, iInf_subtype', iSup_subtype'] using hsub

/-- Normalized identity regularization of a density state.

For `epsilon > 0`, this is `(sigma + epsilon I) / Tr(sigma + epsilon I)`.
The fallback branch only makes the path total away from the source filter. -/
def densityIdentityRegularization [Nonempty b]
    (sigma : State b) (epsilon : Real) : State b :=
  if hepsilon : 0 < epsilon then
    stateOfPosDefReference
      (sigma.matrix + epsilon • (1 : CMatrix b))
      (cMatrix_posSemidef_add_pos_smul_one_posDef sigma.pos hepsilon)
  else
    sigma

@[simp]
theorem densityIdentityRegularization_eq_of_pos [Nonempty b]
    (sigma : State b) {epsilon : Real} (hepsilon : 0 < epsilon) :
    densityIdentityRegularization sigma epsilon =
      stateOfPosDefReference
        (sigma.matrix + epsilon • (1 : CMatrix b))
        (cMatrix_posSemidef_add_pos_smul_one_posDef sigma.pos hepsilon) := by
  simp [densityIdentityRegularization, hepsilon]

/-- The normalized identity regularization is full rank for positive
regularization parameter. -/
theorem densityIdentityRegularization_posDef_of_pos [Nonempty b]
    (sigma : State b) {epsilon : Real} (hepsilon : 0 < epsilon) :
    (densityIdentityRegularization sigma epsilon).matrix.PosDef := by
  rw [densityIdentityRegularization_eq_of_pos sigma hepsilon]
  exact stateOfPosDefReference_posDef
    (sigma.matrix + epsilon • (1 : CMatrix b))
    (cMatrix_posSemidef_add_pos_smul_one_posDef sigma.pos hepsilon)

/-- Trace of the unnormalized identity regularization. -/
theorem add_smul_one_trace_re (sigma : State b) (epsilon : Real) :
    ((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re =
      1 + epsilon * (Fintype.card b : Real) := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  simp [Complex.add_re, Complex.real_smul, sigma.trace_eq_one]

/-- The normalizing scalar of identity regularization tends to one as the
positive regularization parameter tends to zero. -/
theorem densityIdentityRegularization_scale_tendsto [Nonempty b]
    (sigma : State b) :
    Filter.Tendsto
      (fun epsilon : Real =>
        (((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re)⁻¹)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (1 : Real)) := by
  have htrace :
      Filter.Tendsto
        (fun epsilon : Real =>
          ((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (1 : Real)) := by
    have hpath :
        (fun epsilon : Real =>
          ((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re) =
        (fun epsilon : Real => 1 + epsilon * (Fintype.card b : Real)) := by
      funext epsilon
      exact add_smul_one_trace_re sigma epsilon
    have hcont : Continuous fun epsilon : Real =>
        1 + epsilon * (Fintype.card b : Real) := by
      fun_prop
    rw [hpath]
    simpa using
      (hcont.continuousWithinAt (x := (0 : Real))
        (s := Set.Ioi (0 : Real))).tendsto
  simpa using htrace.inv₀ one_ne_zero

/-- Explicit lower spectral cutoff carried by normalized identity
regularization. -/
def densityIdentityRegularizationCutoff
    (sigma : State b) (epsilon : Real) : Real :=
  (((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re)⁻¹ * epsilon

/-- The explicit cutoff is positive for a positive regularization parameter. -/
theorem densityIdentityRegularizationCutoff_pos [Nonempty b]
    (sigma : State b) {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 < densityIdentityRegularizationCutoff sigma epsilon := by
  have hpd : (sigma.matrix + epsilon • (1 : CMatrix b)).PosDef :=
    cMatrix_posSemidef_add_pos_smul_one_posDef sigma.pos hepsilon
  have htrace :
      0 < ((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpd)).1
  exact mul_pos (inv_pos.mpr htrace) hepsilon

/-- Every positive identity regularization belongs to the compact density
domain with its explicit positive lower spectral cutoff. -/
theorem densityIdentityRegularization_mem_uniformlyPositive [Nonempty b]
    (sigma : State b) {epsilon : Real} (hepsilon : 0 < epsilon) :
    (densityIdentityRegularization sigma epsilon).matrix ∈
      uniformlyPositiveDensityMatrixSet
        (densityIdentityRegularizationCutoff sigma epsilon) b := by
  let raw : CMatrix b := sigma.matrix + epsilon • (1 : CMatrix b)
  have hpd : raw.PosDef := by
    exact cMatrix_posSemidef_add_pos_smul_one_posDef sigma.pos hepsilon
  have htrace : 0 < raw.trace.re :=
    (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpd)).1
  have hscale : 0 <= raw.trace.re⁻¹ := inv_nonneg.mpr htrace.le
  have hmatrix :
      (densityIdentityRegularization sigma epsilon).matrix =
        raw.trace.re⁻¹ • raw := by
    rw [densityIdentityRegularization_eq_of_pos sigma hepsilon]
    exact stateOfPosDefReference_matrix raw hpd
  refine ⟨state_matrix_mem_densityMatrixSet
    (densityIdentityRegularization sigma epsilon), ?_⟩
  rw [hmatrix, Matrix.le_iff]
  have hscaled : (raw.trace.re⁻¹ • sigma.matrix).PosSemidef :=
    Matrix.PosSemidef.smul sigma.pos hscale
  have heq :
      raw.trace.re⁻¹ • raw -
          densityIdentityRegularizationCutoff sigma epsilon • (1 : CMatrix b) =
        raw.trace.re⁻¹ • sigma.matrix := by
    ext i j
    simp [raw, densityIdentityRegularizationCutoff, Matrix.smul_apply]
    ring
  rw [heq]
  exact hscaled

end State

namespace PureVector

/-- The positive `AC` weight `I_A tensor tau_C^p` in the common bracket. -/
def upwardRenyiDualityACWeight (tau : CMatrix c) (p : Real) : CMatrix (Prod a c) :=
  Matrix.kronecker (1 : CMatrix a) (CFC.rpow tau p)

/-- Reorder the `ABC` amplitude as an `AC:B` amplitude. -/
def upwardRenyiDualityACBAmplitude
    (psi : PureVector (Prod (Prod a b) c)) : Prod (Prod a c) b -> Complex :=
  fun x => psi.amp ((x.1.1, x.2), x.1.2)

/-- The `B`-amplitude slice at fixed `A,C` coordinates. -/
def upwardRenyiDualityBSlice
    (psi : PureVector (Prod (Prod a b) c)) (i : a) (k : c) : b -> Complex :=
  fun j => psi.amp ((i, j), k)

/-- The `B` marginal is the finite sum of the rank-one matrices associated
with the `A,C` amplitude slices. -/
theorem marginalBOfABC_matrix_eq_sum_rankOne_BSlice
    (psi : PureVector (Prod (Prod a b) c)) :
    psi.state.marginalBOfABC.matrix =
      ∑ x : Prod a c,
        rankOneMatrix (psi.upwardRenyiDualityBSlice x.1 x.2) := by
  ext j j'
  simp [State.marginalBOfABC, State.marginalAB, State.marginalA,
    State.marginalB, partialTraceA, partialTraceB, PureVector.state_matrix,
    Matrix.sum_apply, rankOneMatrix_apply, upwardRenyiDualityBSlice,
    Fintype.sum_prod_type]

/-- Every rank-one `B` amplitude slice is supported by the `B` marginal. -/
theorem rankOne_BSlice_supports_marginalBOfABC
    (psi : PureVector (Prod (Prod a b) c)) (i : a) (k : c) :
    Matrix.Supports
      (rankOneMatrix (psi.upwardRenyiDualityBSlice i k))
      psi.state.marginalBOfABC.matrix := by
  classical
  let x : Prod a c := (i, k)
  let rest : CMatrix b :=
    ∑ y ∈ (Finset.univ.erase x),
      rankOneMatrix (psi.upwardRenyiDualityBSlice y.1 y.2)
  have hrest : rest.PosSemidef := by
    dsimp [rest]
    let s : Finset (Prod a c) := Finset.univ.erase x
    change (∑ y ∈ s,
      rankOneMatrix (psi.upwardRenyiDualityBSlice y.1 y.2)).PosSemidef
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : CMatrix b).PosSemidef)
    | @insert y s hy ih =>
        simpa [Finset.sum_insert hy] using
          (rankOneMatrix_pos (psi.upwardRenyiDualityBSlice y.1 y.2)).add ih
  have hdecomp :
      psi.state.marginalBOfABC.matrix =
        rankOneMatrix (psi.upwardRenyiDualityBSlice i k) + rest := by
    rw [psi.marginalBOfABC_matrix_eq_sum_rankOne_BSlice]
    have hx : x ∈ (Finset.univ : Finset (Prod a c)) := Finset.mem_univ x
    rw [← Finset.add_sum_erase _ _ hx]
  rw [hdecomp]
  exact Matrix.Supports.left_of_posSemidef_add
    (rankOneMatrix_pos (psi.upwardRenyiDualityBSlice i k)) hrest

private theorem rankOneMatrix_mulVec_eq_dotProduct_smul_boundary
    {d : Type*} [Fintype d] (u v : d -> Complex) :
    (rankOneMatrix u).mulVec v = dotProduct (star u) v • u := by
  ext i
  simp [Matrix.mulVec, rankOneMatrix_apply, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm]

/-- Vanishing of a rank-one action forces the corresponding amplitude
pairing to vanish. -/
private theorem dotProduct_star_eq_zero_of_rankOne_mulVec_eq_zero_boundary
    {d : Type*} [Fintype d] (u v : d -> Complex)
    (h : (rankOneMatrix u).mulVec v = 0) :
    dotProduct (star u) v = 0 := by
  rw [rankOneMatrix_mulVec_eq_dotProduct_smul_boundary] at h
  by_cases hu : u = 0
  · simp [hu, dotProduct]
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := Function.ne_iff.mp hu
    have hi0 := congrFun h i
    simpa [hi] using (mul_eq_zero.mp hi0).resolve_right hi

/-- Apply the square root of `I_A tensor tau_C^p` to the `AC` leg. -/
def upwardRenyiDualityACWeightedAmplitude
    (psi : PureVector (Prod (Prod a b) c)) (tau : CMatrix c) (p : Real) :
    Prod (Prod a c) b -> Complex :=
  Matrix.mulVec
    (Matrix.kronecker (CFC.sqrt (upwardRenyiDualityACWeight (a := a) tau p))
      (1 : CMatrix b))
    psi.upwardRenyiDualityACBAmplitude

/-- The effective `B`-side PSD matrix paired with `sigma_B^{-p}` in the
source common bracket. -/
def upwardRenyiDualityEffectiveBMatrix
    (psi : PureVector (Prod (Prod a b) c)) (tau : CMatrix c) (p : Real) : CMatrix b :=
  partialTraceA (a := Prod a c) (b := b)
    (rankOneMatrix (psi.upwardRenyiDualityACWeightedAmplitude tau p))

private theorem partialTraceA_rankOne_kron_left_mulVec_eq_weight_mul_boundary
    {d : Type u} {e : Type v} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (S : CMatrix d) (hS : S.IsHermitian) (v : Prod d e -> Complex) :
    partialTraceA (a := d) (b := e)
        (rankOneMatrix (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix e)) v)) =
      partialTraceA (a := d) (b := e)
        (Matrix.kronecker (S * S) (1 : CMatrix e) * rankOneMatrix v) := by
  ext j j'
  have hstar : forall x y : d, star (S x y) = S y x := by
    intro x y
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS.eq y) x
  have hstar' : forall x y : d, (starRingEnd Complex) (S x y) = S y x := hstar
  simp [partialTraceA, rankOneMatrix_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simp_rw [hstar']
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, z]
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x _
  refine Finset.sum_congr rfl ?_
  intro x_1 _
  refine Finset.sum_congr rfl ?_
  intro x_2 _
  ring_nf

/-- The effective matrix can be computed by applying the positive `AC`
weight before tracing out `AC`. -/
theorem upwardRenyiDualityEffectiveBMatrix_eq_partialTrace_weight_mul
    (psi : PureVector (Prod (Prod a b) c)) (tau : CMatrix c) (p : Real)
    (htau : tau.PosSemidef) :
    psi.upwardRenyiDualityEffectiveBMatrix tau p =
      partialTraceA (a := Prod a c) (b := b)
        (Matrix.kronecker (upwardRenyiDualityACWeight (a := a) tau p) (1 : CMatrix b) *
          rankOneMatrix psi.upwardRenyiDualityACBAmplitude) := by
  let W : CMatrix (Prod a c) := upwardRenyiDualityACWeight (a := a) tau p
  let S : CMatrix (Prod a c) := CFC.sqrt W
  have hW : W.PosSemidef := by
    simpa [W, upwardRenyiDualityACWeight] using
      Matrix.PosSemidef.one.kronecker
        (cMatrix_rpow_posSemidef (A := tau) (s := p) htau)
  have hS : S.IsHermitian := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg W)).isHermitian
  have hSS : S * S = W := by
    exact CFC.sqrt_mul_sqrt_self W hW.nonneg
  calc
    psi.upwardRenyiDualityEffectiveBMatrix tau p =
        partialTraceA (a := Prod a c) (b := b)
          (rankOneMatrix
            (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b))
              psi.upwardRenyiDualityACBAmplitude)) := by
          simp [upwardRenyiDualityEffectiveBMatrix,
            upwardRenyiDualityACWeightedAmplitude, S, W]
    _ = partialTraceA (a := Prod a c) (b := b)
          (Matrix.kronecker (S * S) (1 : CMatrix b) *
            rankOneMatrix psi.upwardRenyiDualityACBAmplitude) :=
      partialTraceA_rankOne_kron_left_mulVec_eq_weight_mul_boundary
        S hS psi.upwardRenyiDualityACBAmplitude
    _ = partialTraceA (a := Prod a c) (b := b)
          (Matrix.kronecker W (1 : CMatrix b) *
            rankOneMatrix psi.upwardRenyiDualityACBAmplitude) := by rw [hSS]

/-- Coordinate form of the effective `B`-side matrix. -/
theorem upwardRenyiDualityEffectiveBMatrix_apply
    (psi : PureVector (Prod (Prod a b) c)) (tau : CMatrix c) (p : Real)
    (htau : tau.PosSemidef) (j j' : b) :
    psi.upwardRenyiDualityEffectiveBMatrix tau p j j' =
      ∑ i : a, ∑ k : c, ∑ k' : c,
        CFC.rpow tau p k k' * psi.amp ((i, j), k') * star (psi.amp ((i, j'), k)) := by
  rw [upwardRenyiDualityEffectiveBMatrix_eq_partialTrace_weight_mul psi tau p htau]
  simp [upwardRenyiDualityACWeight, upwardRenyiDualityACBAmplitude,
    partialTraceA, rankOneMatrix_apply, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_assoc]

private theorem sum_a_b_c_b_c_reorder
    {aa bb cc : Type*} [Fintype aa] [Fintype bb] [Fintype cc]
    (f : aa -> bb -> cc -> bb -> cc -> Complex) :
    (∑ i : aa, ∑ j : bb, ∑ k : cc, ∑ j' : bb, ∑ k' : cc, f i j k j' k') =
      ∑ j : bb, ∑ j' : bb, ∑ i : aa, ∑ k : cc, ∑ k' : cc, f i j k j' k' := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ i : aa, ∑ k : cc, ∑ j' : bb, ∑ k' : cc, f i j k j' k') =
        ∑ i : aa, ∑ j' : bb, ∑ k : cc, ∑ k' : cc, f i j k j' k' := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ j' : bb, ∑ i : aa, ∑ k : cc, ∑ k' : cc, f i j k j' k' := by
      rw [Finset.sum_comm]

/-- Trace-pairing form of the common source bracket. This is the handoff to
the support-aware reverse-Holder objective. -/
theorem abcSidePowerTraceRe_eq_effectiveBMatrix_pairing
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : Real)
    (htau : tau.PosSemidef) :
    State.abcSidePowerTraceRe (a := a) psi.state.matrix sigma tau p =
      ((CFC.rpow sigma (-p) * psi.upwardRenyiDualityEffectiveBMatrix tau p).trace).re := by
  classical
  rw [show psi.state.matrix = rankOneMatrix psi.amp by rfl]
  unfold State.abcSidePowerTraceRe
  congr 1
  simpa [Matrix.trace, Matrix.mul_apply,
      upwardRenyiDualityEffectiveBMatrix_apply psi tau p htau,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, rankOneMatrix_apply,
      Fintype.sum_prod_type, Finset.mul_sum, mul_assoc] using
    (sum_a_b_c_b_c_reorder
      (f := fun i j k j' k' =>
        CFC.rpow sigma (-p) j j' *
          (CFC.rpow tau p k k' *
            (psi.amp ((i, j'), k') * star (psi.amp ((i, j), k))))))

/-- The effective `B`-side matrix is positive semidefinite. -/
theorem upwardRenyiDualityEffectiveBMatrix_posSemidef
    (psi : PureVector (Prod (Prod a b) c)) (tau : CMatrix c) (p : Real) :
    (psi.upwardRenyiDualityEffectiveBMatrix tau p).PosSemidef :=
  partialTraceA_posSemidef
    (rankOneMatrix_pos (psi.upwardRenyiDualityACWeightedAmplitude tau p))

/-- Every induced effective matrix is supported by the physical `B`
marginal. This is the forward half of the source support restriction. -/
theorem upwardRenyiDualityEffectiveBMatrix_supports_marginalBOfABC
    (psi : PureVector (Prod (Prod a b) c)) (tau : CMatrix c) (p : Real)
    (htau : tau.PosSemidef) :
    Matrix.Supports
      (psi.upwardRenyiDualityEffectiveBMatrix tau p)
      psi.state.marginalBOfABC.matrix := by
  intro v hv
  have hpair : ∀ i : a, ∀ k : c,
      dotProduct (star (psi.upwardRenyiDualityBSlice i k)) v = 0 := by
    intro i k
    exact dotProduct_star_eq_zero_of_rankOne_mulVec_eq_zero_boundary
      (psi.upwardRenyiDualityBSlice i k) v
      (psi.rankOne_BSlice_supports_marginalBOfABC i k v hv)
  ext j
  simp only [Matrix.mulVec, dotProduct,
    psi.upwardRenyiDualityEffectiveBMatrix_apply tau p htau]
  change (∑ x : b,
    (∑ i : a, ∑ k : c, ∑ k' : c,
      CFC.rpow tau p k k' * psi.amp ((i, j), k') *
        star (psi.amp ((i, x), k))) * v x) = 0
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k' _ => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  have hpair' := hpair i k
  have hzero :
      (∑ x : b, star (psi.amp ((i, x), k)) * v x) = 0 := by
    simpa [upwardRenyiDualityBSlice, dotProduct] using hpair'
  rw [hzero]
  simp

/-- The power of the maximally mixed state is the corresponding scalar
multiple of the identity. -/
theorem maximallyMixed_rpow_eq_smul_one_boundary [Nonempty c]
    (p : Real) :
    CFC.rpow (State.maximallyMixed c).matrix p =
      (((Fintype.card c : Real)⁻¹ ^ p : Real) • (1 : CMatrix c)) := by
  have hcard : 0 <= (Fintype.card c : Real)⁻¹ := by positivity
  rw [State.maximallyMixed_matrix]
  change CFC.rpow (((Fintype.card c : Real)⁻¹ : Real) • (1 : CMatrix c)) p =
    (((Fintype.card c : Real)⁻¹ ^ p : Real) • (1 : CMatrix c))
  rw [cMatrix_rpow_real_smul_posSemidef_schatten Matrix.PosSemidef.one hcard]
  rw [show CFC.rpow (1 : CMatrix c) p = 1 by exact CFC.one_rpow]

/-- At the maximally mixed `C` state, the effective matrix is a strictly
positive scalar multiple of the physical `B` marginal. -/
theorem upwardRenyiDualityEffectiveBMatrix_maximallyMixed_eq
    [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c)) (p : Real) :
    psi.upwardRenyiDualityEffectiveBMatrix (State.maximallyMixed c).matrix p =
      ((Fintype.card c : Real)⁻¹ ^ p : Real) •
        psi.state.marginalBOfABC.matrix := by
  ext j j'
  rw [psi.upwardRenyiDualityEffectiveBMatrix_apply
    (State.maximallyMixed c).matrix p (State.maximallyMixed c).pos]
  rw [maximallyMixed_rpow_eq_smul_one_boundary (c := c) p]
  simp [Matrix.smul_apply, Matrix.one_apply, State.marginalBOfABC,
    State.marginalAB, State.marginalA, State.marginalB, partialTraceA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply,
    Finset.mul_sum, mul_assoc]

/-- A side matrix supports the physical `B` marginal exactly when it supports
all effective matrices induced by normalized `C` states. This identifies the
support extension with Tomamichel's source restriction on `sigma_B`. -/
theorem marginalBOfABC_supports_iff_forall_effectiveBMatrix_supports
    [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c)) (sigma : CMatrix b) (p : Real) :
    Matrix.Supports psi.state.marginalBOfABC.matrix sigma ↔
      ∀ tau : CMatrix c, tau ∈ State.densityMatrixSet c ->
        Matrix.Supports
          (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma := by
  constructor
  · intro hMarginal tau hTau
    exact (psi.upwardRenyiDualityEffectiveBMatrix_supports_marginalBOfABC
      tau p hTau.1).trans hMarginal
  · intro hAll
    have hMixed := hAll (State.maximallyMixed c).matrix
      (State.state_matrix_mem_densityMatrixSet (State.maximallyMixed c))
    rw [psi.upwardRenyiDualityEffectiveBMatrix_maximallyMixed_eq p] at hMixed
    intro v hv
    have hscaled := hMixed v hv
    have hcard : 0 < (Fintype.card c : Real) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card c)
    have hscalar : 0 < (Fintype.card c : Real)⁻¹ ^ p :=
      Real.rpow_pos_of_pos (inv_pos.mpr hcard) p
    rw [Matrix.smul_mulVec] at hscaled
    exact (smul_eq_zero.mp hscaled).resolve_left hscalar.ne'

/-- Support-aware extended-real common bracket. Unsupported side states have
value `top`, exactly as in the reverse-Holder variational convention. -/
def upwardRenyiDualitySourceBracketEReal
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : Real) : EReal := by
  classical
  exact if Matrix.Supports (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma then
      (State.abcSidePowerTraceRe (a := a) psi.state.matrix sigma tau p : EReal)
    else
      ⊤

@[simp]
theorem upwardRenyiDualitySourceBracketEReal_of_supports
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : Real)
    (h : Matrix.Supports (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma) :
    psi.upwardRenyiDualitySourceBracketEReal sigma tau p =
      (State.abcSidePowerTraceRe (a := a) psi.state.matrix sigma tau p : EReal) := by
  simp [upwardRenyiDualitySourceBracketEReal, h]

@[simp]
theorem upwardRenyiDualitySourceBracketEReal_of_not_supports
    (psi : PureVector (Prod (Prod a b) c))
    (sigma : CMatrix b) (tau : CMatrix c) (p : Real)
    (h : ¬ Matrix.Supports (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma) :
    psi.upwardRenyiDualitySourceBracketEReal sigma tau p = ⊤ := by
  simp [upwardRenyiDualitySourceBracketEReal, h]

/-- The source Sion equality on the explicit compact cutoff domain generated
by a positive identity regularization. -/
theorem upwardRenyiDualitySource_regularizationCutoff_sion
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c)) (sigma0 : State b)
    {epsilon p : Real} (hepsilon : 0 < epsilon)
    (hp0 : 0 < p) (hp1 : p <= 1) :
    (⨅ sigma ∈ State.uniformlyPositiveDensityMatrixSet
        (State.densityIdentityRegularizationCutoff sigma0 epsilon) b,
      ⨆ tau ∈ State.densityMatrixSet c,
        (State.abcSidePowerTraceRe (a := a)
          psi.state.matrix sigma tau p : EReal)) =
      ⨆ tau ∈ State.densityMatrixSet c,
        ⨅ sigma ∈ State.uniformlyPositiveDensityMatrixSet
          (State.densityIdentityRegularizationCutoff sigma0 epsilon) b,
          (State.abcSidePowerTraceRe (a := a)
            psi.state.matrix sigma tau p : EReal) := by
  exact State.uniformlyPositiveDensityMatrixSet_sion_abcSidePowerTraceRe_EReal
    (State.densityIdentityRegularizationCutoff_pos sigma0 hepsilon)
    ⟨(State.densityIdentityRegularization sigma0 epsilon).matrix,
      State.densityIdentityRegularization_mem_uniformlyPositive sigma0 hepsilon⟩
    psi.state.pos hp0 hp1

/-- The source bracket converges along normalized full-rank identity
regularization whenever its effective matrix is supported by the limiting
side state. This is the `delta -> 0` boundary step in Tomamichel's proof. -/
theorem abcSidePowerTraceRe_densityIdentityRegularization_tendsto
    [Nonempty b]
    (psi : PureVector (Prod (Prod a b) c)) (sigma : State b)
    (tau : CMatrix c) {p : Real} (htau : tau.PosSemidef)
    (hSupport : Matrix.Supports
      (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma.matrix) :
    Filter.Tendsto
      (fun epsilon : Real =>
        State.abcSidePowerTraceRe (a := a) psi.state.matrix
          (State.densityIdentityRegularization sigma epsilon).matrix tau p)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (State.abcSidePowerTraceRe (a := a) psi.state.matrix
        sigma.matrix tau p)) := by
  let M : CMatrix b := psi.upwardRenyiDualityEffectiveBMatrix tau p
  have hraw :
      Filter.Tendsto
        (fun epsilon : Real =>
          ((M * CFC.rpow (sigma.matrix + epsilon • (1 : CMatrix b)) (-p)).trace).re)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds ((M * CFC.rpow sigma.matrix (-p)).trace).re) :=
    trace_mul_cMatrix_rpow_add_pos_smul_one_tendsto_of_support
      sigma.pos (by simpa [M] using hSupport) (-p)
  have hscale :
      Filter.Tendsto
        (fun epsilon : Real =>
          (((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re)⁻¹ ^ (-p))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (1 : Real)) := by
    have hs := State.densityIdentityRegularization_scale_tendsto sigma
    have hcont : ContinuousAt (fun x : Real => x ^ (-p)) (1 : Real) :=
      Real.continuousAt_rpow_const 1 (-p) (Or.inl one_ne_zero)
    simpa using hcont.tendsto.comp hs
  have hprod :
      Filter.Tendsto
        (fun epsilon : Real =>
          (((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re)⁻¹ ^ (-p) *
            ((M * CFC.rpow
              (sigma.matrix + epsilon • (1 : CMatrix b)) (-p)).trace).re)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds ((M * CFC.rpow sigma.matrix (-p)).trace).re) := by
    simpa [one_mul] using hscale.mul hraw
  rw [abcSidePowerTraceRe_eq_effectiveBMatrix_pairing psi sigma.matrix tau p htau]
  rw [Matrix.trace_mul_comm (CFC.rpow sigma.matrix (-p)) M]
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  have hpos : 0 < epsilon := hepsilon
  have hpd :
      (sigma.matrix + epsilon • (1 : CMatrix b)).PosDef :=
    State.cMatrix_posSemidef_add_pos_smul_one_posDef sigma.pos hpos
  rw [abcSidePowerTraceRe_eq_effectiveBMatrix_pairing psi
    (State.densityIdentityRegularization sigma epsilon).matrix tau p htau]
  rw [State.densityIdentityRegularization_eq_of_pos sigma hpos]
  change _ =
    ((CFC.rpow
      (State.stateOfPosDefReference
        (sigma.matrix + epsilon • (1 : CMatrix b)) hpd).matrix (-p) * M).trace).re
  have hscale_nonneg :
      0 <= (((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re)⁻¹ := by
    have htr_pos :
        0 < ((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re :=
      (Complex.pos_iff.mp (Matrix.PosDef.trace_pos hpd)).1
    exact inv_nonneg.mpr htr_pos.le
  have hpow :
      CFC.rpow
          (State.stateOfPosDefReference
            (sigma.matrix + epsilon • (1 : CMatrix b)) hpd).matrix (-p) =
        ((((sigma.matrix + epsilon • (1 : CMatrix b)).trace).re)⁻¹ ^ (-p) : Real) •
          CFC.rpow (sigma.matrix + epsilon • (1 : CMatrix b)) (-p) := by
    rw [State.stateOfPosDefReference_matrix]
    exact cMatrix_rpow_real_smul_posSemidef_schatten
      hpd.posSemidef hscale_nonneg
  rw [hpow]
  rw [Matrix.smul_mul, Matrix.trace_smul]
  rw [Matrix.trace_mul_comm
    (CFC.rpow (sigma.matrix + epsilon • (1 : CMatrix b)) (-p)) M]
  simp [Complex.real_smul]

/-- For fixed `tau`, the source support extension makes the infimum over all
density matrices equal to the infimum over full-rank density matrices.

The nontrivial direction is the normalized identity-regularization limit;
unsupported candidates have value `top` and therefore cannot lower the
infimum. -/
theorem upwardRenyiDualitySourceBracketEReal_fullRank_iInf_eq_density_iInf
    [Nonempty b]
    (psi : PureVector (Prod (Prod a b) c)) (tau : CMatrix c)
    (htau : tau ∈ State.densityMatrixSet c) (p : Real) :
    (⨅ sigma : CMatrix b,
      ⨅ _hSigma : sigma ∈ State.fullRankDensityMatrixSet b,
        (State.abcSidePowerTraceRe (a := a) psi.state.matrix sigma tau p : EReal)) =
      ⨅ sigma : CMatrix b,
        ⨅ _hSigma : sigma ∈ State.densityMatrixSet b,
          psi.upwardRenyiDualitySourceBracketEReal sigma tau p := by
  apply le_antisymm
  · refine le_iInf fun sigma => ?_
    refine le_iInf fun hSigma => ?_
    by_cases hSupport : Matrix.Supports
        (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma
    · rw [psi.upwardRenyiDualitySourceBracketEReal_of_supports sigma tau p hSupport]
      let sigmaState : State b := State.densityMatrixSetState sigma hSigma
      have htendReal :=
        psi.abcSidePowerTraceRe_densityIdentityRegularization_tendsto
          sigmaState tau htau.1 hSupport
      have htendE :
          Filter.Tendsto
            (fun epsilon : Real =>
              (State.abcSidePowerTraceRe (a := a) psi.state.matrix
                (State.densityIdentityRegularization sigmaState epsilon).matrix
                tau p : EReal))
            (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhds (State.abcSidePowerTraceRe (a := a) psi.state.matrix
              sigma tau p : EReal)) := by
        simpa [sigmaState, State.densityMatrixSetState_matrix] using
          EReal.tendsto_coe.mpr htendReal
      refine ge_of_tendsto htendE ?_
      filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
      have hpos : 0 < epsilon := hepsilon
      let sigmaEpsilon : State b :=
        State.densityIdentityRegularization sigmaState epsilon
      have hFull : sigmaEpsilon.matrix ∈ State.fullRankDensityMatrixSet b := by
        exact ⟨State.densityIdentityRegularization_posDef_of_pos sigmaState hpos,
          sigmaEpsilon.trace_eq_one⟩
      exact iInf_le_of_le sigmaEpsilon.matrix
        (iInf_le_of_le hFull le_rfl)
    · rw [psi.upwardRenyiDualitySourceBracketEReal_of_not_supports
        sigma tau p hSupport]
      exact le_top
  · refine le_iInf fun sigma => ?_
    refine le_iInf fun hSigma => ?_
    have hDensity : sigma ∈ State.densityMatrixSet b :=
      State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma
    have hSupport : Matrix.Supports
        (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma :=
      Matrix.Supports.of_right_posDef
        (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma hSigma.1
    calc
      (⨅ sigma' : CMatrix b,
        ⨅ _hSigma' : sigma' ∈ State.densityMatrixSet b,
          psi.upwardRenyiDualitySourceBracketEReal sigma' tau p) <=
          psi.upwardRenyiDualitySourceBracketEReal sigma tau p :=
        iInf_le_of_le sigma (iInf_le_of_le hDensity le_rfl)
      _ = (State.abcSidePowerTraceRe (a := a) psi.state.matrix sigma tau p : EReal) :=
        psi.upwardRenyiDualitySourceBracketEReal_of_supports sigma tau p hSupport

/-- Tomamichel's source minimax equality on the complete density domains.

The proof first applies Sion on the full-rank side-state domain, then removes
the full-support restriction by normalized identity regularization. The
support-aware extended bracket assigns `top` to precisely the candidates
excluded by the source reverse-Holder convention. -/
theorem upwardRenyiDualitySource_minimax
    [Nonempty b] [Nonempty c]
    (psi : PureVector (Prod (Prod a b) c))
    {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    (⨅ sigma : CMatrix b,
      ⨅ _hSigma : sigma ∈ State.densityMatrixSet b,
        ⨆ tau : CMatrix c,
          ⨆ _hTau : tau ∈ State.densityMatrixSet c,
            psi.upwardRenyiDualitySourceBracketEReal sigma tau p) =
      ⨆ tau : CMatrix c,
        ⨆ _hTau : tau ∈ State.densityMatrixSet c,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : sigma ∈ State.densityMatrixSet b,
              psi.upwardRenyiDualitySourceBracketEReal sigma tau p := by
  let F :
      {tau : CMatrix c // tau ∈ State.densityMatrixSet c} ->
      {sigma : CMatrix b // sigma ∈ State.densityMatrixSet b} -> EReal :=
    fun tau sigma =>
      psi.upwardRenyiDualitySourceBracketEReal sigma.1 tau.1 p
  have hgeneralSub :
      (⨆ tau : {tau : CMatrix c // tau ∈ State.densityMatrixSet c},
        ⨅ sigma : {sigma : CMatrix b // sigma ∈ State.densityMatrixSet b},
          F tau sigma) <=
        ⨅ sigma : {sigma : CMatrix b // sigma ∈ State.densityMatrixSet b},
          ⨆ tau : {tau : CMatrix c // tau ∈ State.densityMatrixSet c},
            F tau sigma :=
    iSup_iInf_le_iInf_iSup F
  have hgeneral :
      (⨆ tau : CMatrix c,
        ⨆ _hTau : tau ∈ State.densityMatrixSet c,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : sigma ∈ State.densityMatrixSet b,
              psi.upwardRenyiDualitySourceBracketEReal sigma tau p) <=
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ State.densityMatrixSet b,
            ⨆ tau : CMatrix c,
              ⨆ _hTau : tau ∈ State.densityMatrixSet c,
                psi.upwardRenyiDualitySourceBracketEReal sigma tau p := by
    simpa [F, iInf_subtype', iSup_subtype'] using hgeneralSub
  have hleft :
      (⨅ sigma : CMatrix b,
        ⨅ _hSigma : sigma ∈ State.densityMatrixSet b,
          ⨆ tau : CMatrix c,
            ⨆ _hTau : tau ∈ State.densityMatrixSet c,
              psi.upwardRenyiDualitySourceBracketEReal sigma tau p) <=
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : sigma ∈ State.fullRankDensityMatrixSet b,
            ⨆ tau : CMatrix c,
              ⨆ _hTau : tau ∈ State.densityMatrixSet c,
                (State.abcSidePowerTraceRe (a := a)
                  psi.state.matrix sigma tau p : EReal) := by
    refine le_iInf fun sigma => ?_
    refine le_iInf fun hSigma => ?_
    have hDensity : sigma ∈ State.densityMatrixSet b :=
      State.fullRankDensityMatrixSet_subset_densityMatrixSet hSigma
    calc
      (⨅ sigma' : CMatrix b,
        ⨅ _hSigma' : sigma' ∈ State.densityMatrixSet b,
          ⨆ tau : CMatrix c,
            ⨆ _hTau : tau ∈ State.densityMatrixSet c,
              psi.upwardRenyiDualitySourceBracketEReal sigma' tau p) <=
          ⨆ tau : CMatrix c,
            ⨆ _hTau : tau ∈ State.densityMatrixSet c,
              psi.upwardRenyiDualitySourceBracketEReal sigma tau p :=
        iInf_le_of_le sigma (iInf_le_of_le hDensity le_rfl)
      _ = ⨆ tau : CMatrix c,
          ⨆ _hTau : tau ∈ State.densityMatrixSet c,
            (State.abcSidePowerTraceRe (a := a)
              psi.state.matrix sigma tau p : EReal) := by
        apply iSup_congr
        intro tau
        apply iSup_congr
        intro hTau
        have hSupport : Matrix.Supports
            (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma :=
          Matrix.Supports.of_right_posDef
            (psi.upwardRenyiDualityEffectiveBMatrix tau p) sigma hSigma.1
        exact psi.upwardRenyiDualitySourceBracketEReal_of_supports
          sigma tau p hSupport
  have hsion :=
    State.fullRankDensityMatrixSet_sion_abcSidePowerTraceRe_EReal_boundary
      (a := a) (b := b) (c := c) psi.state.pos hp0 hp1.le
  have hright :
      (⨆ tau : CMatrix c,
        ⨆ _hTau : tau ∈ State.densityMatrixSet c,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : sigma ∈ State.fullRankDensityMatrixSet b,
              (State.abcSidePowerTraceRe (a := a)
                psi.state.matrix sigma tau p : EReal)) =
        ⨆ tau : CMatrix c,
          ⨆ _hTau : tau ∈ State.densityMatrixSet c,
            ⨅ sigma : CMatrix b,
              ⨅ _hSigma : sigma ∈ State.densityMatrixSet b,
                psi.upwardRenyiDualitySourceBracketEReal sigma tau p := by
    apply iSup_congr
    intro tau
    apply iSup_congr
    intro hTau
    exact psi.upwardRenyiDualitySourceBracketEReal_fullRank_iInf_eq_density_iInf
      tau hTau p
  apply le_antisymm
  · exact hleft.trans_eq (hsion.trans hright)
  · exact hgeneral

end PureVector

end

end QIT
