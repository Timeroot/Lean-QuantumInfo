/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Topology.Bases
public import QIT.Information.Entropy.Entropy
public import QIT.OneShot.Smooth
public import QIT.Symmetry.UnitaryTwirl
import QIT.States.TraceNorm.Spectral
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.L2Space

/-!
# One-shot decoupling theorem

One-shot decoupling bound (theo:oneshot). This module reserves the import
surface for the decoupling statement and proof dependencies.
-/

@[expose] public section

namespace QIT

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
open MeasureTheory

universe u v w x

noncomputable section

variable {a : Type u} {e : Type v}

local instance decouplingCMatrixContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) :=
  SeminormedAddGroup.toContinuousENorm

noncomputable local instance decouplingMatrixCStarAlgebra {ι : Type u}
    [Fintype ι] [DecidableEq ι] :
    CStarAlgebra (Matrix ι ι ℂ) where

noncomputable local instance decouplingMatrixNormalCFC {ι : Type u}
    [Fintype ι] [DecidableEq ι] :
    ContinuousFunctionalCalculus ℂ (Matrix ι ι ℂ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance decouplingMatrixNormalIsometricCFC {ι : Type u}
    [Fintype ι] [DecidableEq ι] :
    IsometricContinuousFunctionalCalculus ℂ (Matrix ι ι ℂ) IsStarNormal :=
  IsStarNormal.instIsometricContinuousFunctionalCalculus

noncomputable local instance decouplingMatrixSelfAdjointCFC {ι : Type u}
    [Fintype ι] [DecidableEq ι] :
    ContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable local instance decouplingMatrixSelfAdjointIsometricCFC {ι : Type u}
    [Fintype ι] [DecidableEq ι] :
    IsometricContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

/-- First-moment selection over finite-dimensional unitary Haar measure:
some unitary attains at most the Haar average of an integrable real-valued
quantity.  This is the abstract selection step used in ADHW fqsw.tex lines
796-818 after the averaged decoupling estimate is obtained. -/
theorem unitaryHaar_exists_le_integral
    [Fintype a] [DecidableEq a] [Nonempty a]
    {f : Matrix.unitaryGroup a ℂ → ℝ}
    (hf : Integrable f (unitaryHaarMeasure (a := a))) :
    ∃ U : Matrix.unitaryGroup a ℂ,
      f U ≤ ∫ U, f U ∂unitaryHaarMeasure (a := a) :=
  MeasureTheory.exists_le_integral (μ := unitaryHaarMeasure (a := a)) hf

/-- First-moment selection with an explicit upper bound on the Haar average. -/
theorem unitaryHaar_exists_le_of_integral_le
    [Fintype a] [DecidableEq a] [Nonempty a]
    {f : Matrix.unitaryGroup a ℂ → ℝ} {B : ℝ}
    (hf : Integrable f (unitaryHaarMeasure (a := a)))
    (hB : (∫ U, f U ∂unitaryHaarMeasure (a := a)) ≤ B) :
    ∃ U : Matrix.unitaryGroup a ℂ, f U ≤ B := by
  rcases unitaryHaar_exists_le_integral (a := a) hf with ⟨U, hU⟩
  exact ⟨U, hU.trans hB⟩

private instance unitaryGroupSecondCountableTopology {ι : Type u} [Fintype ι] [DecidableEq ι] :
    SecondCountableTopology (Matrix.unitaryGroup ι ℂ) := by
  haveI : SecondCountableTopology (Matrix ι ι ℂ) := by
    change SecondCountableTopology (ι → ι → ℂ)
    infer_instance
  change SecondCountableTopology ({x // x ∈ (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ))})
  infer_instance

private instance unitaryHaarMeasure_isMulRightInvariant {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Measure.IsMulRightInvariant (unitaryHaarMeasure (a := ι)) := by
  refine ⟨?_⟩
  intro g
  let K0 : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup ι ℂ) := ⊤
  have hmass : (Measure.map (fun U : Matrix.unitaryGroup ι ℂ => U * g)
        (unitaryHaarMeasure (a := ι))) K0 = 1 := by
    rw [Measure.map_apply]
    · change (unitaryHaarMeasure (a := ι)) Set.univ = 1
      exact unitaryHaarMeasure_univ (a := ι)
    · exact continuous_mul_const g |>.measurable
    · exact K0.isCompact.measurableSet
  have hhaar := (Measure.haarMeasure_eq_iff K0
    (Measure.map (fun U : Matrix.unitaryGroup ι ℂ => U * g)
      (unitaryHaarMeasure (a := ι)))).2 hmass
  simpa [unitaryHaarMeasure, K0] using hhaar.symm

private instance unitaryHaarMeasure_isInvInvariant {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Measure.IsInvInvariant (unitaryHaarMeasure (a := ι)) := by
  refine ⟨?_⟩
  let K0 : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup ι ℂ) := ⊤
  have hmass : (unitaryHaarMeasure (a := ι)).inv K0 = 1 := by
    rw [Measure.inv_def, Measure.map_apply]
    · change (unitaryHaarMeasure (a := ι)) Set.univ = 1
      exact unitaryHaarMeasure_univ (a := ι)
    · exact measurable_inv
    · exact K0.isCompact.measurableSet
  have hhaar := (Measure.haarMeasure_eq_iff K0 (unitaryHaarMeasure (a := ι)).inv).2 hmass
  simpa [unitaryHaarMeasure, K0] using hhaar.symm

/-! ## Hayden projected-state moment API -/

/-- Hayden's projected ambient `A × E` matrix
`(|A| / d) • ((P U ⊗ 1_E) ρ (U† P ⊗ 1_E))`.

The parameter `d` is kept as a real scalar, matching the source proof's
dimension of the selected subspace/projection. -/
def haydenProjectedAE [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (ρ : CMatrix (Prod a e))
    (U : Matrix.unitaryGroup a ℂ) : CMatrix (Prod a e) :=
  (((Fintype.card a : ℝ) / d : ℝ) : ℂ) •
    (Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) * ρ *
      Matrix.kronecker (star (U : CMatrix a) * P) (1 : CMatrix e))

/-- The source mean target `d⁻¹ • (P ⊗ φ^E)` for the projected state. -/
def haydenProjectedAE_meanTarget [Fintype a] [Fintype e]
    (P : CMatrix a) (d : ℝ) (ρ : CMatrix (Prod a e)) : CMatrix (Prod a e) :=
  (((1 : ℝ) / d : ℝ) : ℂ) • Matrix.kronecker P (partialTraceA (a := a) (b := e) ρ)

/-! ## Source setup bridge -/

/-- Regroup the post-Stinespring source system `A × (B × E)` as `(A × B) × E`. -/
def haydenPostStinespringToABEEquiv (a : Type u) (b : Type w) (e : Type v) :
    Prod a (Prod b e) ≃ Prod (Prod a b) e where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun x := (x.1.1, (x.1.2, x.2))
  left_inv x := by
    cases x with
    | mk a be =>
      cases be
      rfl
  right_inv x := by
    cases x with
    | mk ab e =>
      cases ab
      rfl

/-- Pure post-Stinespring `ABE` vector obtained from a source pure state
`phi^{AA'}` and a Stinespring isometry `W : A' -> B × E`. -/
def haydenPostStinespringABEPureVector {ap : Type x} {b : Type w}
    [Fintype a] [Fintype ap] [Fintype b] [Fintype e]
    [DecidableEq a] [DecidableEq ap] [DecidableEq b] [DecidableEq e]
    (phi : PureVector (Prod a ap)) (W : ReferenceIsometry ap (Prod b e)) :
    PureVector (Prod (Prod a b) e) :=
  (W.applyPureVectorRight phi).reindex (haydenPostStinespringToABEEquiv a b e)

/-- Source `phi^{AE}` obtained by applying the Stinespring isometry and tracing out `B`. -/
def haydenPostStinespringAEState {ap : Type x} {b : Type w}
    [Fintype a] [Fintype ap] [Fintype b] [Fintype e]
    [DecidableEq a] [DecidableEq ap] [DecidableEq b] [DecidableEq e]
    (phi : PureVector (Prod a ap)) (W : ReferenceIsometry ap (Prod b e)) :
    State (Prod a e) :=
  (haydenPostStinespringABEPureVector (a := a) (e := e) phi W).state.marginalAC

/-- Source projected `RE` matrix after the random projection on Alice's side.
The projected `R` label is represented by the `P`-supported subspace of the
ambient `A` basis, matching the post-Stinespring matrix bound below. -/
def haydenSourceProjectedRE {ap : Type x} {b : Type w}
    [Fintype a] [Fintype ap] [Fintype b] [Fintype e]
    [DecidableEq a] [DecidableEq ap] [DecidableEq b] [DecidableEq e]
    (P : CMatrix a) (d : ℝ)
    (phi : PureVector (Prod a ap)) (W : ReferenceIsometry ap (Prod b e))
    (U : Matrix.unitaryGroup a ℂ) : CMatrix (Prod a e) :=
  haydenProjectedAE (a := a) (e := e) P d
    (haydenPostStinespringAEState (a := a) (e := e) phi W).matrix U

/-- The source projected `RE` matrix is exactly the existing post-Stinespring
projected `AE` matrix expression. -/
theorem haydenSourceProjectedRE_eq_haydenProjectedAE {ap : Type x} {b : Type w}
    [Fintype a] [Fintype ap] [Fintype b] [Fintype e]
    [DecidableEq a] [DecidableEq ap] [DecidableEq b] [DecidableEq e]
    (P : CMatrix a) (d : ℝ)
    (phi : PureVector (Prod a ap)) (W : ReferenceIsometry ap (Prod b e))
    (U : Matrix.unitaryGroup a ℂ) :
    haydenSourceProjectedRE (a := a) (e := e) P d phi W U =
      haydenProjectedAE (a := a) (e := e) P d
        (haydenPostStinespringAEState (a := a) (e := e) phi W).matrix U :=
  rfl

private theorem finrank_range_toEuclideanLin_le_of_left_fixed [Fintype a] [DecidableEq a]
    {K M : CMatrix a} (hKM : K * M = M) :
    Module.finrank ℂ (LinearMap.range M.toEuclideanLin) ≤
      Module.finrank ℂ (LinearMap.range K.toEuclideanLin) := by
  have hlin : K.toEuclideanLin.comp M.toEuclideanLin = M.toEuclideanLin := by
    have h := congrArg Matrix.toEuclideanLin hKM
    rw [Matrix.toLpLin_mul] at h
    exact h
  refine Submodule.finrank_mono ?_
  intro v hv
  rcases hv with ⟨x, rfl⟩
  exact ⟨M.toEuclideanLin x, DFunLike.congr_fun hlin x⟩

private theorem finrank_range_toEuclideanLin_eq_trace_of_idempotent
    [Fintype a] [DecidableEq a] (P : CMatrix a) (hPid : P * P = P) :
    (Module.finrank ℂ (LinearMap.range P.toEuclideanLin) : ℂ) = P.trace := by
  have hlin_idem : IsIdempotentElem P.toEuclideanLin := by
    rw [IsIdempotentElem]
    ext x i
    have h := congrArg Matrix.toEuclideanLin hPid
    rw [Matrix.toLpLin_mul] at h
    exact congrArg
      (fun f : EuclideanSpace ℂ a →ₗ[ℂ] EuclideanSpace ℂ a => f x i) h
  have hproj : LinearMap.IsProj (LinearMap.range P.toEuclideanLin) P.toEuclideanLin :=
    LinearMap.IsIdempotentElem.isProj_range P.toEuclideanLin hlin_idem
  have htrace := hproj.trace
  have hlintrace : LinearMap.trace ℂ (EuclideanSpace ℂ a) P.toEuclideanLin = P.trace := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ a)]
    change (LinearMap.toMatrix (PiLp.basisFun 2 ℂ a) (PiLp.basisFun 2 ℂ a)
      (Matrix.toLin (PiLp.basisFun 2 ℂ a) (PiLp.basisFun 2 ℂ a) P)).trace = P.trace
    rw [LinearMap.toMatrix_toLin]
  rw [hlintrace] at htrace
  exact htrace.symm

private theorem kronecker_projection_one_finrank_range_toEuclideanLin_eq
    [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (hPid : P * P = P) (hPtr : P.trace = (d : ℂ)) :
    (Module.finrank ℂ
        (LinearMap.range (Matrix.kronecker P (1 : CMatrix e)).toEuclideanLin) : ℝ) =
      d * (Fintype.card e : ℝ) := by
  let K : CMatrix (Prod a e) := Matrix.kronecker P (1 : CMatrix e)
  have hKidem : K * K = K := by
    dsimp [K]
    calc
      Matrix.kronecker P (1 : CMatrix e) * Matrix.kronecker P (1 : CMatrix e) =
          Matrix.kronecker (P * P) ((1 : CMatrix e) * 1) := by
            exact (Matrix.mul_kronecker_mul P P (1 : CMatrix e) (1 : CMatrix e)).symm
      _ = Matrix.kronecker P (1 : CMatrix e) := by
          rw [hPid, Matrix.mul_one]
  have hKrankC := finrank_range_toEuclideanLin_eq_trace_of_idempotent K hKidem
  have hKtrace : K.trace = ((d * (Fintype.card e : ℝ) : ℝ) : ℂ) := by
    dsimp [K]
    rw [Matrix.trace_kronecker, hPtr, Matrix.trace_one]
    norm_num [Complex.ofReal_mul, Complex.ofReal_natCast]
  have hC : (Module.finrank ℂ (LinearMap.range K.toEuclideanLin) : ℂ) =
      ((d * (Fintype.card e : ℝ) : ℝ) : ℂ) := hKrankC.trans hKtrace
  have hR := congrArg Complex.re hC
  simpa [K, Complex.ofReal_mul, Complex.ofReal_natCast] using hR

private theorem haydenProjectedAE_diff_left_supported [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (U : Matrix.unitaryGroup a ℂ) (hPid : P * P = P) :
    Matrix.kronecker P (1 : CMatrix e) *
      (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) =
      haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho := by
  rw [Matrix.mul_sub]
  congr 1
  · unfold haydenProjectedAE
    rw [Matrix.mul_smul]
    congr 1
    have hleft : Matrix.kronecker P (1 : CMatrix e) *
        Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) =
        Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) := by
      calc
        Matrix.kronecker P (1 : CMatrix e) *
            Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) =
          Matrix.kronecker (P * (P * (U : CMatrix a))) ((1 : CMatrix e) * 1) := by
            exact (Matrix.mul_kronecker_mul P (P * (U : CMatrix a))
              (1 : CMatrix e) (1 : CMatrix e)).symm
        _ = Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) := by
            rw [Matrix.mul_one]
            congr 1
            rw [← Matrix.mul_assoc, hPid]
    calc
      Matrix.kronecker P (1 : CMatrix e) *
          (Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) * rho *
            Matrix.kronecker (star (U : CMatrix a) * P) (1 : CMatrix e)) =
        (Matrix.kronecker P (1 : CMatrix e) *
          Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e)) * rho *
            Matrix.kronecker (star (U : CMatrix a) * P) (1 : CMatrix e) := by
          noncomm_ring
      _ = Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) * rho *
            Matrix.kronecker (star (U : CMatrix a) * P) (1 : CMatrix e) := by
          rw [hleft]
  · unfold haydenProjectedAE_meanTarget
    rw [Matrix.mul_smul]
    congr 1
    calc
      Matrix.kronecker P (1 : CMatrix e) *
          Matrix.kronecker P (partialTraceA (a := a) (b := e) rho) =
        Matrix.kronecker (P * P) ((1 : CMatrix e) *
          partialTraceA (a := a) (b := e) rho) := by
          exact (Matrix.mul_kronecker_mul P P (1 : CMatrix e)
            (partialTraceA (a := a) (b := e) rho)).symm
      _ = Matrix.kronecker P (partialTraceA (a := a) (b := e) rho) := by
          rw [hPid, Matrix.one_mul]

private theorem haydenProjectedAE_diff_finrank_range_le_projected_dim
    [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (U : Matrix.unitaryGroup a ℂ)
    (hPid : P * P = P) (hPtr : P.trace = (d : ℂ)) :
    (Module.finrank ℂ (LinearMap.range
      (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho).toEuclideanLin) : ℝ) ≤
      d * (Fintype.card e : ℝ) := by
  let Delta : CMatrix (Prod a e) :=
    haydenProjectedAE (a := a) (e := e) P d rho U -
      haydenProjectedAE_meanTarget (a := a) (e := e) P d rho
  let K : CMatrix (Prod a e) := Matrix.kronecker P (1 : CMatrix e)
  have hsupport : K * Delta = Delta := by
    simpa [K, Delta] using
      haydenProjectedAE_diff_left_supported (a := a) (e := e) P d rho U hPid
  have hrange :=
    finrank_range_toEuclideanLin_le_of_left_fixed (a := Prod a e) hsupport
  have hKrank :=
    kronecker_projection_one_finrank_range_toEuclideanLin_eq
      (a := a) (e := e) P d hPid hPtr
  have hrange_real :
      (Module.finrank ℂ (LinearMap.range Delta.toEuclideanLin) : ℝ) ≤
        (Module.finrank ℂ (LinearMap.range K.toEuclideanLin) : ℝ) := by
    exact_mod_cast hrange
  simpa [Delta, K] using hrange_real.trans_eq hKrank

/-- On a probability space, the integral of a nonnegative real function is at
most the square root of its second moment. -/
theorem integral_le_sqrt_integral_sq_of_nonneg
    {α : Type w} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hf_int : Integrable f μ)
    (hf_sq_int : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have hf_memLp_two : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    convert (memLp_two_iff_integrable_sq hf_int.aestronglyMeasurable).2
      (by simpa [pow_two] using hf_sq_int) using 1
    norm_num
  have hone_memLp_two : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ :=
    memLp_const (1 : ℝ)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    (f := fun _ : α => (1 : ℝ)) (g := f)
    (by filter_upwards with _; norm_num) hf_nonneg hone_memLp_two hf_memLp_two
  have hleft : (∫ x, (1 : ℝ) * f x ∂μ) = ∫ x, f x ∂μ := by simp
  rw [hleft] at hholder
  have hone_int : (∫ _ : α, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = 1 := by
    simp [measureReal_def]
  rw [hone_int, one_mul] at hholder
  simpa [Real.rpow_natCast, Real.sqrt_eq_rpow] using hholder

/-- Real-valued integral form of the elementary ADHW estimate
`(x + y)^2 ≤ 2x^2 + 2y^2`, used to combine two averaged square-error
bounds after a pointwise triangle-inequality step. -/
theorem integral_sq_le_two_add_two_of_ae_le_add
    {α : Type w} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ}
    (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hh_nonneg : ∀ᵐ x ∂μ, 0 ≤ h x)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x + h x)
    (hf_int : Integrable (fun x => f x ^ 2) μ)
    (hg_int : Integrable (fun x => g x ^ 2) μ)
    (hh_int : Integrable (fun x => h x ^ 2) μ) :
    (∫ x, f x ^ 2 ∂μ) ≤
      2 * (∫ x, g x ^ 2 ∂μ) + 2 * (∫ x, h x ^ 2 ∂μ) := by
  have hpoint :
      (fun x => f x ^ 2) ≤ᵐ[μ]
        fun x => 2 * (g x ^ 2) + 2 * (h x ^ 2) := by
    filter_upwards [hf_nonneg, hg_nonneg, hh_nonneg, hfg] with x hf0 hg0 hh0 hle
    have hsum_nonneg : 0 ≤ g x + h x := add_nonneg hg0 hh0
    have hf_sq_le : f x ^ 2 ≤ (g x + h x) ^ 2 := by
      nlinarith [hf0, hsum_nonneg, hle]
    have hsum_sq_le : (g x + h x) ^ 2 ≤ 2 * (g x ^ 2) + 2 * (h x ^ 2) := by
      nlinarith [sq_nonneg (g x - h x)]
    exact hf_sq_le.trans hsum_sq_le
  have hright_int :
      Integrable (fun x => 2 * (g x ^ 2) + 2 * (h x ^ 2)) μ :=
    (hg_int.const_mul 2).add (hh_int.const_mul 2)
  calc
    (∫ x, f x ^ 2 ∂μ) ≤
        ∫ x, 2 * (g x ^ 2) + 2 * (h x ^ 2) ∂μ :=
      integral_mono_ae hf_int hright_int hpoint
    _ = 2 * (∫ x, g x ^ 2 ∂μ) + 2 * (∫ x, h x ^ 2 ∂μ) := by
      rw [integral_add (hg_int.const_mul 2) (hh_int.const_mul 2)]
      rw [integral_const_mul, integral_const_mul]

private theorem haydenProjectedAE_isHermitian [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (U : Matrix.unitaryGroup a ℂ)
    (hP : P.IsHermitian) (hrho : rho.IsHermitian) :
    (haydenProjectedAE (a := a) (e := e) P d rho U).IsHermitian := by
  rw [Matrix.IsHermitian]
  unfold haydenProjectedAE
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    hP.eq, hrho.eq, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

private theorem haydenProjectedAE_meanTarget_isHermitian [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (hP : P.IsHermitian) (hrho : rho.IsHermitian) :
    (haydenProjectedAE_meanTarget (a := a) (e := e) P d rho).IsHermitian := by
  have hrhoE : (partialTraceA (a := a) (b := e) rho).IsHermitian :=
    partialTraceA_isHermitian hrho
  rw [Matrix.IsHermitian]
  unfold haydenProjectedAE_meanTarget
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker, hP.eq, hrhoE.eq]

private theorem haydenProjectedAE_meanTarget_hilbertSchmidtSq [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (hPherm : P.IsHermitian) (hPid : P * P = P)
    (hPtr : P.trace = (d : ℂ)) (hd : d ≠ 0) :
    hilbertSchmidtSq (haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) =
      (1 / d) * hilbertSchmidtSq (partialTraceA (a := a) (b := e) rho) := by
  let R : CMatrix e := partialTraceA (a := a) (b := e) rho
  unfold haydenProjectedAE_meanTarget hilbertSchmidtSq
  dsimp [R]
  simp only [Matrix.star_eq_conjTranspose]
  rw [Matrix.conjTranspose_smul]
  rw [Matrix.smul_mul]
  rw [Matrix.mul_smul]
  rw [Matrix.trace_smul]
  rw [Matrix.trace_smul]
  rw [Matrix.conjTranspose_kronecker]
  rw [hPherm.eq]
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.trace_kronecker]
  rw [hPid, hPtr]
  simp [Complex.ofReal_inv, Complex.ofReal_re]
  field_simp [hd]
  -- The mean-target scalar `(1/d : ℝ) : ℂ` makes `field_simp` leave a trivial
  -- `True ∨ _` residue (cf. the sibling proofs in this file, which close with a
  -- bare `ring_nf` because they carry the full nonzero-hypothesis set).
  tauto

private theorem hilbertSchmidtSq_sub_of_isHermitian [Fintype a] [DecidableEq a]
    (X M : CMatrix a) (hX : X.IsHermitian) (hM : M.IsHermitian) :
    hilbertSchmidtSq (X - M) =
      (X * X).trace.re - (2 : ℝ) * (X * M).trace.re + hilbertSchmidtSq M := by
  unfold hilbertSchmidtSq
  simp only [Matrix.star_eq_conjTranspose]
  rw [Matrix.conjTranspose_sub]
  rw [hX.eq, hM.eq]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [Matrix.trace_sub]
  rw [Matrix.trace_sub]
  rw [Matrix.trace_sub]
  have hcomm : (M * X).trace = (X * M).trace := Matrix.trace_mul_comm M X
  rw [hcomm]
  simp [Complex.sub_re]
  ring

private noncomputable def decouplingTraceRightRealCLM [Fintype a] [DecidableEq a]
    (M : CMatrix a) : CMatrix a →L[ℝ] ℝ :=
  Complex.reCLM.comp (LinearMap.toContinuousLinearMap
    ({ toFun := fun X : CMatrix a => (X * M).trace
       map_add' := by
        intro X Y
        simp [Matrix.add_mul, Matrix.trace_add]
       map_smul' := by
        intro c X
        simp [Matrix.trace_smul] } :
      CMatrix a →ₗ[ℝ] ℂ))

private theorem decouplingTraceRightRealCLM_apply [Fintype a] [DecidableEq a]
    (M X : CMatrix a) :
    decouplingTraceRightRealCLM M X = ((X * M).trace).re :=
  rfl

private theorem haydenProjectedAE_variance_identity [Fintype a] [DecidableEq a]
    {α : Type w} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : α → CMatrix a) (M : CMatrix a)
    (hf : Integrable f μ)
    (hsecond : Integrable (fun x => (f x * f x).trace.re) μ)
    (hM : M.IsHermitian)
    (hfHerm : ∀ x, (f x).IsHermitian)
    (hmean : (∫ x, f x ∂μ) = M) :
    (∫ x, hilbertSchmidtSq (f x - M) ∂μ) =
      (∫ x, (f x * f x).trace.re ∂μ) - hilbertSchmidtSq M := by
  let cross : α → ℝ := fun x => ((f x * M).trace).re
  have hcross : Integrable cross μ := by
    simpa [cross, decouplingTraceRightRealCLM_apply] using
      (decouplingTraceRightRealCLM M).integrable_comp hf
  have hcross_integral : (∫ x, cross x ∂μ) = hilbertSchmidtSq M := by
    have hlin := (decouplingTraceRightRealCLM M).integral_comp_comm hf
    rw [hmean] at hlin
    simpa [cross, decouplingTraceRightRealCLM_apply,
      hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian hM] using hlin
  calc
    (∫ x, hilbertSchmidtSq (f x - M) ∂μ) =
        ∫ x, ((f x * f x).trace.re - (2 : ℝ) * cross x + hilbertSchmidtSq M) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [cross, hilbertSchmidtSq_sub_of_isHermitian (f x) M (hfHerm x) hM]
    _ = (∫ x, (f x * f x).trace.re ∂μ) - (2 : ℝ) * (∫ x, cross x ∂μ) +
        hilbertSchmidtSq M := by
      rw [integral_add]
      · rw [integral_sub]
        · rw [integral_const_mul, integral_const]
          simp [measureReal_def]
        · exact hsecond
        · exact hcross.const_mul (2 : ℝ)
      · exact hsecond.sub (hcross.const_mul (2 : ℝ))
      · exact integrable_const (hilbertSchmidtSq M)
    _ = (∫ x, (f x * f x).trace.re ∂μ) - hilbertSchmidtSq M := by
      rw [hcross_integral]
      ring

private theorem haydenProjectedAE_hilbertSchmidt_variance_integrable [Fintype a] [DecidableEq a]
    {α : Type w} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (f : α → CMatrix a) (M : CMatrix a)
    (hf : Integrable f μ)
    (hsecond : Integrable (fun x => (f x * f x).trace.re) μ)
    (hM : M.IsHermitian)
    (hfHerm : ∀ x, (f x).IsHermitian) :
    Integrable (fun x => hilbertSchmidtSq (f x - M)) μ := by
  let cross : α → ℝ := fun x => ((f x * M).trace).re
  have hcross : Integrable cross μ := by
    simpa [cross, decouplingTraceRightRealCLM_apply] using
      (decouplingTraceRightRealCLM M).integrable_comp hf
  have hrepr : (fun x => hilbertSchmidtSq (f x - M)) =
      fun x => (f x * f x).trace.re - (2 : ℝ) * cross x + hilbertSchmidtSq M := by
    funext x
    simp [cross, hilbertSchmidtSq_sub_of_isHermitian (f x) M (hfHerm x) hM]
  rw [hrepr]
  exact (hsecond.sub (hcross.const_mul (2 : ℝ))).add
    (integrable_const (hilbertSchmidtSq M))

theorem haydenProjectedAE_oneShotDecoupling_traceNorm_expectation_le_of_variance
    [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e] [Nonempty a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (hPid : P * P = P) (hPtr : P.trace = (d : ℂ))
    (hd : 1 ≤ d)
    (htrace : Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho))
      (unitaryHaarMeasure (a := a)))
    (hhs : Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho))
      (unitaryHaarMeasure (a := a)))
    (hvar :
      (∫ U : Matrix.unitaryGroup a ℂ,
        hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
          haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
        ∂unitaryHaarMeasure (a := a)) ≤ hilbertSchmidtSq rho) :
    (∫ U : Matrix.unitaryGroup a ℂ,
      traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
      ∂unitaryHaarMeasure (a := a)) ≤
      Real.sqrt (d * (Fintype.card e : ℝ) * hilbertSchmidtSq rho) := by
  have hrank : ∀ U : Matrix.unitaryGroup a ℂ,
      (Module.finrank ℂ (LinearMap.range
        (haydenProjectedAE (a := a) (e := e) P d rho U -
          haydenProjectedAE_meanTarget (a := a) (e := e) P d rho).toEuclideanLin) : ℝ) ≤
        d * (Fintype.card e : ℝ) := by
    intro U
    exact haydenProjectedAE_diff_finrank_range_le_projected_dim
      (a := a) (e := e) P d rho U hPid hPtr
  have hbridge := integral_traceNorm_le_sqrt_integral_hilbertSchmidtSq_of_rank_bound
    (μ := unitaryHaarMeasure (a := a))
    (f := fun U : Matrix.unitaryGroup a ℂ =>
      haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
    hrank htrace hhs
  have hmono :
      (d * (Fintype.card e : ℝ)) *
          (∫ U : Matrix.unitaryGroup a ℂ,
            hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
              haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
            ∂unitaryHaarMeasure (a := a)) ≤
        (d * (Fintype.card e : ℝ)) * hilbertSchmidtSq rho :=
    mul_le_mul_of_nonneg_left hvar (mul_nonneg (le_trans zero_le_one hd) (Nat.cast_nonneg _))
  exact hbridge.trans (Real.sqrt_le_sqrt hmono)

private theorem tensorPowerKroneckerTwo_smul [Fintype a] [DecidableEq a]
    (c : ℂ) (M : CMatrix a) :
    tensorPowerKroneckerTwo (a := a) (c • M) =
      c ^ 2 • tensorPowerKroneckerTwo (a := a) M := by
  ext x y
  simp [tensorPowerKroneckerTwo, pow_two]
  ring

private theorem tensorPowerKroneckerTwo_star [Fintype a] [DecidableEq a]
    (M : CMatrix a) :
    tensorPowerKroneckerTwo (a := a) (star M) =
      star (tensorPowerKroneckerTwo (a := a) M) := by
  ext x y
  simp [tensorPowerKroneckerTwo, Matrix.star_apply]

private theorem tensorPowerKroneckerTwo_one [Fintype a] [DecidableEq a] :
    tensorPowerKroneckerTwo (a := a) (1 : CMatrix a) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensorPowerKroneckerTwo]
  · have hcoord :
        tensorPowerEquiv (a := a) 2 x 0 ≠ tensorPowerEquiv (a := a) 2 y 0 ∨
          tensorPowerEquiv (a := a) 2 x 1 ≠ tensorPowerEquiv (a := a) 2 y 1 := by
      by_contra h
      push Not at h
      apply hxy
      apply (tensorPowerEquiv (a := a) 2).injective
      funext i
      fin_cases i <;> simp [h]
    rcases hcoord with h0 | h1
    · simp [tensorPowerKroneckerTwo, Matrix.one_apply, h0, hxy]
    · by_cases h0 : tensorPowerEquiv (a := a) 2 x 0 = tensorPowerEquiv (a := a) 2 y 0
      · simp [tensorPowerKroneckerTwo, Matrix.one_apply, h0, h1, hxy]
      · simp [tensorPowerKroneckerTwo, Matrix.one_apply, h0, hxy]

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

/-! ## Side-register Haar twirl plumbing -/

private theorem decoupling_unitaryTensorPowerMatrix_continuous [Fintype a] [DecidableEq a] (n : ℕ) :
    Continuous fun U : Matrix.unitaryGroup a ℂ =>
      (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) := by
  induction n with
  | zero =>
      exact continuous_const
  | succ n ih =>
      change Continuous fun U : Matrix.unitaryGroup a ℂ =>
        Matrix.kronecker (U : CMatrix a)
          (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))
      refine continuous_pi ?_
      intro i
      refine continuous_pi ?_
      intro j
      exact ((continuous_apply j.1).comp ((continuous_apply i.1).comp continuous_subtype_val)).mul
        ((continuous_apply j.2).comp ((continuous_apply i.2).comp ih))

private theorem decoupling_continuous_kronecker_one {α : Type*} [TopologicalSpace α]
    {ι : Type u} {κ : Type v} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {f : α → CMatrix ι} (hf : Continuous f) :
    Continuous fun x => Matrix.kronecker (f x) (1 : CMatrix κ) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  simp [Matrix.kronecker]
  exact ((continuous_apply j.1).comp ((continuous_apply i.1).comp hf)).mul continuous_const

/-- A fixed side-register block of an operator on `A^n × E`. -/
private def sideBlock [Fintype a] [Fintype e] (n : ℕ)
    (X : CMatrix (Prod (TensorPower a n) e)) (r s : e) : CMatrix (TensorPower a n) :=
  fun i j => X (i, r) (j, s)

@[simp]
private theorem sideBlock_apply [Fintype a] [Fintype e] (n : ℕ)
    (X : CMatrix (Prod (TensorPower a n) e)) (r s : e)
    (i j : TensorPower a n) :
    sideBlock (a := a) (e := e) n X r s i j = X (i, r) (j, s) := rfl

/-- The pointwise Haar integrand that twirls only the `A^n` register. -/
private def sideTwirlIntegrand [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    (n : ℕ) (X : CMatrix (Prod (TensorPower a n) e))
    (U : Matrix.unitaryGroup a ℂ) : CMatrix (Prod (TensorPower a n) e) :=
  Matrix.kronecker (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) (1 : CMatrix e) *
    X *
    Matrix.kronecker (star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)))
      (1 : CMatrix e)

private theorem sideTwirl_integrand_continuous [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    (n : ℕ) (X : CMatrix (Prod (TensorPower a n) e)) :
    Continuous (sideTwirlIntegrand (a := a) (e := e) n X) := by
  unfold sideTwirlIntegrand
  simpa [mul_assoc] using
    ((decoupling_continuous_kronecker_one (ι := TensorPower a n) (κ := e)
      (hf := decoupling_unitaryTensorPowerMatrix_continuous (a := a) n)).matrix_mul
        continuous_const).matrix_mul
        (decoupling_continuous_kronecker_one (ι := TensorPower a n) (κ := e)
          (hf := Continuous.star (decoupling_unitaryTensorPowerMatrix_continuous (a := a) n)))

private theorem sideTwirl_integrand_integrable [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    [Nonempty a] (n : ℕ) (X : CMatrix (Prod (TensorPower a n) e)) :
    Integrable (sideTwirlIntegrand (a := a) (e := e) n X) (unitaryHaarMeasure (a := a)) :=
  (sideTwirl_integrand_continuous (a := a) (e := e) n X).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private noncomputable def decouplingCMatrixEntryCLM {ι : Type w} [Fintype ι] [DecidableEq ι]
    (i j : ι) : CMatrix ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A i j
       map_add' := by
        intro A B
        rfl
       map_smul' := by
        intro c A
        simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℝ] ℂ)

private theorem decoupling_integral_apply_apply {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type w} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) (i j : ι) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  simpa [decouplingCMatrixEntryCLM] using
    ((decouplingCMatrixEntryCLM (ι := ι) i j).integral_comp_comm hf).symm

private theorem decoupling_integrable_apply_apply {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type w} [Fintype ι] [DecidableEq ι]
    {f : α → CMatrix ι} (hf : Integrable f μ) (i j : ι) :
    Integrable (fun x => f x i j) μ :=
  (decouplingCMatrixEntryCLM (ι := ι) i j).integrable_comp hf

private theorem decoupling_integral_matrix_mul_left [Fintype a] [DecidableEq a] [Nonempty a]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (C : CMatrix ι) {f : Matrix.unitaryGroup a ℂ → CMatrix ι}
    (hf : Integrable f (unitaryHaarMeasure (a := a))) :
    ∫ U, C * f U ∂unitaryHaarMeasure (a := a) =
      C * ∫ U, f U ∂unitaryHaarMeasure (a := a) := by
  ext i j
  rw [decoupling_integral_apply_apply (hf := hf.const_mul C)]
  simp only [Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [integral_const_mul, ← decoupling_integral_apply_apply (hf := hf) k j]
  intro k _
  exact (decoupling_integrable_apply_apply (hf := hf) k j).const_mul _

private theorem decoupling_integral_matrix_mul_right [Fintype a] [DecidableEq a] [Nonempty a]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    {f : Matrix.unitaryGroup a ℂ → CMatrix ι}
    (hf : Integrable f (unitaryHaarMeasure (a := a))) (C : CMatrix ι) :
    ∫ U, f U * C ∂unitaryHaarMeasure (a := a) =
      (∫ U, f U ∂unitaryHaarMeasure (a := a)) * C := by
  ext i j
  rw [decoupling_integral_apply_apply (hf := hf.mul_const C)]
  simp only [Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [integral_mul_const, ← decoupling_integral_apply_apply (hf := hf) i k]
  intro k _
  exact (decoupling_integrable_apply_apply (hf := hf) i k).mul_const _

private noncomputable def sideBlockCLM [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (n : ℕ) (r s : e) :
    CMatrix (Prod (TensorPower a n) e) →L[ℝ] CMatrix (TensorPower a n) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun X => sideBlock (a := a) (e := e) n X r s
       map_add' := by
        intro X Y
        rfl
       map_smul' := by
        intro c X
        ext i j
        simp [Matrix.smul_apply] } :
      CMatrix (Prod (TensorPower a n) e) →ₗ[ℝ] CMatrix (TensorPower a n))

private theorem sideBlock_integral [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {f : α → CMatrix (Prod (TensorPower a n) e)} (hf : Integrable f μ) (r s : e) :
    sideBlock (a := a) (e := e) n (∫ x, f x ∂μ) r s =
      ∫ x, sideBlock (a := a) (e := e) n (f x) r s ∂μ := by
  simpa [sideBlockCLM] using
    ((sideBlockCLM (a := a) (e := e) n r s).integral_comp_comm hf).symm

private theorem sideBlock_sideTwirlIntegrand [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    (n : ℕ) (X : CMatrix (Prod (TensorPower a n) e)) (r s : e)
    (U : Matrix.unitaryGroup a ℂ) :
    sideBlock (a := a) (e := e) n (sideTwirlIntegrand (a := a) (e := e) n X U) r s =
      unitaryTwirlIntegrand (a := a) n (sideBlock (a := a) (e := e) n X r s) U := by
  ext i j
  simp [sideBlock, sideTwirlIntegrand, unitaryTwirlIntegrand, Matrix.mul_apply,
    Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type]

/-- Haar twirling only the `A^n` register twirls each fixed side block by the
ordinary `unitaryTwirl` on `A^n`. -/
private theorem sideTwirl_integral_block [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    [Nonempty a] (n : ℕ) (X : CMatrix (Prod (TensorPower a n) e)) (r s : e) :
    sideBlock (a := a) (e := e) n
        (∫ U : Matrix.unitaryGroup a ℂ,
          sideTwirlIntegrand (a := a) (e := e) n X U ∂unitaryHaarMeasure (a := a))
        r s =
      unitaryTwirl n (sideBlock (a := a) (e := e) n X r s) := by
  rw [sideBlock_integral
    (hf := sideTwirl_integrand_integrable (a := a) (e := e) n X)]
  apply integral_congr_ae
  filter_upwards with U
  rw [sideBlock_sideTwirlIntegrand]

/-- Second-moment side-block specialization used to feed the two-copy twirl
decomposition. -/
private theorem sideTwirl_integral_block_two [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a]
    (X : CMatrix (Prod (TensorPower a 2) e)) (r s : e) :
    sideBlock (a := a) (e := e) 2
        (∫ U : Matrix.unitaryGroup a ℂ,
          sideTwirlIntegrand (a := a) (e := e) 2 X U ∂unitaryHaarMeasure (a := a))
        r s =
      unitaryTwirl 2 (sideBlock (a := a) (e := e) 2 X r s) := by
  rw [sideTwirl_integral_block]

/-- Drop the terminal unit register in a one-fold tensor power. -/
private def decouplingTensorPowerOneEquiv (q : Type*) : TensorPower q 1 ≃ q where
  toFun x := x.1
  invFun y := (y, PUnit.unit)
  left_inv x := by
    rcases x with ⟨q, u⟩
    cases u
    rfl
  right_inv y := rfl

private theorem sum_tensorPower_one [Fintype a] {β : Type*} [AddCommMonoid β]
    (f : TensorPower a 1 → β) :
    (∑ x : TensorPower a 1, f x) =
      ∑ i : a, f ((decouplingTensorPowerOneEquiv a).symm i) := by
  exact (Fintype.sum_equiv (decouplingTensorPowerOneEquiv a).symm
    (fun i : a => f ((decouplingTensorPowerOneEquiv a).symm i))
    (fun x : TensorPower a 1 => f x)
    (fun _ => rfl)).symm

/-- Move an ambient `A × E` operator into one-copy tensor-power coordinates. -/
private def oneCopyTensorPowerLift [Fintype a] [Fintype e]
    (M : CMatrix (Prod a e)) : CMatrix (Prod (TensorPower a 1) e) :=
  M.submatrix
    (fun x => (decouplingTensorPowerOneEquiv a x.1, x.2))
    (fun x => (decouplingTensorPowerOneEquiv a x.1, x.2))

/-- Move a one-copy tensor-power operator back to ambient `A × E` coordinates. -/
private def oneCopyTensorPowerDrop [Fintype a] [Fintype e]
    (M : CMatrix (Prod (TensorPower a 1) e)) : CMatrix (Prod a e) :=
  M.submatrix
    (fun x => ((decouplingTensorPowerOneEquiv a).symm x.1, x.2))
    (fun x => ((decouplingTensorPowerOneEquiv a).symm x.1, x.2))

@[simp]
private theorem oneCopyTensorPowerDrop_lift [Fintype a] [Fintype e]
    (M : CMatrix (Prod a e)) :
    oneCopyTensorPowerDrop (a := a) (e := e)
      (oneCopyTensorPowerLift (a := a) (e := e) M) = M := by
  ext x y
  rfl

/-- Side-register trace of a one-copy operator. -/
private def sideTraceOne [Fintype a] [Fintype e]
    (X : CMatrix (Prod (TensorPower a 1) e)) : CMatrix e :=
  fun r s => (sideBlock (a := a) (e := e) 1 X r s).trace

@[simp]
private theorem sideTraceOne_lift [Fintype a] [Fintype e]
    (M : CMatrix (Prod a e)) :
    sideTraceOne (a := a) (e := e)
        (oneCopyTensorPowerLift (a := a) (e := e) M) =
      partialTraceA (a := a) (b := e) M := by
  ext r s
  simp only [sideTraceOne, oneCopyTensorPowerLift, partialTraceA, Matrix.trace]
  exact Fintype.sum_equiv (decouplingTensorPowerOneEquiv a)
    (fun x : TensorPower a 1 => M ((decouplingTensorPowerOneEquiv a) x, r)
      ((decouplingTensorPowerOneEquiv a) x, s))
    (fun i : a => M (i, r) (i, s))
    (fun _ => rfl)

/-- Ambient one-copy Haar twirl on the `A` register. -/
private def ambientSideTwirlIntegrand [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e]
    (M : CMatrix (Prod a e)) (U : Matrix.unitaryGroup a ℂ) : CMatrix (Prod a e) :=
  Matrix.kronecker (U : CMatrix a) (1 : CMatrix e) * M *
    Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix e)

private theorem haydenProjectedAE_eq_projected_ambientSideTwirl [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (U : Matrix.unitaryGroup a ℂ) :
    haydenProjectedAE (a := a) (e := e) P d rho U =
      (((Fintype.card a : ℝ) / d : ℝ) : ℂ) •
        (Matrix.kronecker P (1 : CMatrix e) *
          ambientSideTwirlIntegrand (a := a) (e := e) rho U *
          Matrix.kronecker P (1 : CMatrix e)) := by
  unfold haydenProjectedAE ambientSideTwirlIntegrand
  congr 1
  have hKU :
      Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) =
        Matrix.kronecker P (1 : CMatrix e) *
          Matrix.kronecker (U : CMatrix a) (1 : CMatrix e) := by
    calc
      Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) =
          Matrix.kronecker (P * (U : CMatrix a)) ((1 : CMatrix e) * 1) := by rw [Matrix.mul_one]
      _ = Matrix.kronecker P (1 : CMatrix e) *
            Matrix.kronecker (U : CMatrix a) (1 : CMatrix e) := by
          exact Matrix.mul_kronecker_mul P (U : CMatrix a) (1 : CMatrix e) (1 : CMatrix e)
  have hKSU :
      Matrix.kronecker (star (U : CMatrix a) * P) (1 : CMatrix e) =
        Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix e) *
          Matrix.kronecker P (1 : CMatrix e) := by
    calc
      Matrix.kronecker (star (U : CMatrix a) * P) (1 : CMatrix e) =
          Matrix.kronecker (star (U : CMatrix a) * P) ((1 : CMatrix e) * 1) := by
            rw [Matrix.mul_one]
      _ = Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix e) *
            Matrix.kronecker P (1 : CMatrix e) := by
          exact Matrix.mul_kronecker_mul (star (U : CMatrix a)) P
            (1 : CMatrix e) (1 : CMatrix e)
  calc
    Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e) * rho *
        Matrix.kronecker (star (U : CMatrix a) * P) (1 : CMatrix e) =
      (Matrix.kronecker P (1 : CMatrix e) * Matrix.kronecker (U : CMatrix a) (1 : CMatrix e)) *
          rho *
        (Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix e) *
          Matrix.kronecker P (1 : CMatrix e)) := by
        rw [hKU, hKSU]
    _ =
      Matrix.kronecker P (1 : CMatrix e) *
        (Matrix.kronecker (U : CMatrix a) (1 : CMatrix e) * rho *
          Matrix.kronecker (star (U : CMatrix a)) (1 : CMatrix e)) *
        Matrix.kronecker P (1 : CMatrix e) := by
        noncomm_ring

/-- Reindex an operator on `A² × E²` to the recursive `(A × E)²` convention. -/
def twoCopyProdReindex [Fintype a] [Fintype e]
    (M : CMatrix (Prod (TensorPower a 2) (TensorPower e 2))) :
    CMatrix (TensorPower (Prod a e) 2) :=
  M.submatrix (tensorPowerProdEquiv a e 2) (tensorPowerProdEquiv a e 2)

/-- Source-side product operator `G ⊗ H`, read on recursive `(A × E)²`. -/
def twoCopySideOperator [Fintype a] [Fintype e]
    (G : CMatrix (TensorPower a 2)) (H : CMatrix (TensorPower e 2)) :
    CMatrix (TensorPower (Prod a e) 2) :=
  twoCopyProdReindex (a := a) (e := e) (Matrix.kronecker G H)

@[simp]
theorem twoCopySideOperator_apply [Fintype a] [Fintype e]
    (G : CMatrix (TensorPower a 2)) (H : CMatrix (TensorPower e 2))
    (x y : TensorPower (Prod a e) 2) :
    twoCopySideOperator (a := a) (e := e) G H x y =
      G ((tensorPowerProdEquiv a e 2) x).1 ((tensorPowerProdEquiv a e 2) y).1 *
        H ((tensorPowerProdEquiv a e 2) x).2 ((tensorPowerProdEquiv a e 2) y).2 := by
  rfl

theorem twoCopySideOperator_add_left [Fintype a] [Fintype e]
    (G G' : CMatrix (TensorPower a 2)) (H : CMatrix (TensorPower e 2)) :
    twoCopySideOperator (a := a) (e := e) (G + G') H =
      twoCopySideOperator (a := a) (e := e) G H +
        twoCopySideOperator (a := a) (e := e) G' H := by
  ext x y
  simp [twoCopySideOperator, twoCopyProdReindex, Matrix.kronecker]
  ring

theorem twoCopySideOperator_smul_left [Fintype a] [Fintype e]
    (c : ℂ) (G : CMatrix (TensorPower a 2)) (H : CMatrix (TensorPower e 2)) :
    twoCopySideOperator (a := a) (e := e) (c • G) H =
      c • twoCopySideOperator (a := a) (e := e) G H := by
  ext x y
  simp [twoCopySideOperator, twoCopyProdReindex, Matrix.kronecker]
  ring

private theorem tensorPowerKroneckerTwo_kronecker_one_tensorPower [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (A : CMatrix a) :
    tensorPowerKroneckerTwo (a := Prod a e) (Matrix.kronecker A (1 : CMatrix e)) =
      twoCopySideOperator (a := a) (e := e) (tensorPowerKroneckerTwo (a := a) A)
        (tensorPowerKroneckerTwo (a := e) (1 : CMatrix e)) := by
  ext x y
  simp [twoCopySideOperator, twoCopyProdReindex, Matrix.kronecker,
    tensorPowerKroneckerTwo, tensorPowerProdEquiv_fst_apply]
  rw [tensorPowerProdEquiv_snd_apply (a := a) (b := e) 2 x 0,
    tensorPowerProdEquiv_snd_apply (a := a) (b := e) 2 y 0,
    tensorPowerProdEquiv_snd_apply (a := a) (b := e) 2 x 1,
    tensorPowerProdEquiv_snd_apply (a := a) (b := e) 2 y 1]
  ring

private theorem tensorPowerKroneckerTwo_kronecker_one [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (A : CMatrix a) :
    tensorPowerKroneckerTwo (a := Prod a e) (Matrix.kronecker A (1 : CMatrix e)) =
      twoCopySideOperator (a := a) (e := e) (tensorPowerKroneckerTwo (a := a) A)
        (1 : CMatrix (TensorPower e 2)) := by
  rw [tensorPowerKroneckerTwo_kronecker_one_tensorPower,
    tensorPowerKroneckerTwo_one]

/-- Enumerate a two-copy tensor power by its first and second tensor words. -/
private theorem sum_tensorPower_twoCopyTensorWord [Fintype a] {β : Type*} [AddCommMonoid β]
    (f : TensorPower a 2 → β) :
    (∑ x : TensorPower a 2, f x) =
      ∑ i : a, ∑ j : a, f (twoCopyTensorWord (a := a) i j) := by
  let e : (a × a) ≃ TensorPower a 2 :=
  { toFun p := twoCopyTensorWord (a := a) p.1 p.2
    invFun x :=
      (tensorPowerEquiv (a := a) 2 x 0, tensorPowerEquiv (a := a) 2 x 1)
    left_inv := by
      intro p
      ext <;> simp
    right_inv := by
      intro x
      exact (twoCopyTensorWord_coords (a := a) x).symm }
  calc
    (∑ x : TensorPower a 2, f x) =
        ∑ p : a × a, f (e p) := by
          exact (Fintype.sum_equiv e
            (fun p : a × a => f (e p))
            (fun x : TensorPower a 2 => f x)
            (fun _ => rfl)).symm
    _ = ∑ i : a, ∑ j : a, f (twoCopyTensorWord (a := a) i j) := by
          rw [Fintype.sum_prod_type]
          rfl

@[simp]
theorem tensorPowerProdEquiv_twoCopyTensorWord [Fintype a] [Fintype e]
    (i j : a) (k l : e) :
    tensorPowerProdEquiv a e 2
        (twoCopyTensorWord (a := Prod a e) (i, k) (j, l)) =
      (twoCopyTensorWord (a := a) i j, twoCopyTensorWord (a := e) k l) := by
  rfl

@[simp]
theorem twoCopySideOperator_apply_twoCopyTensorWord [Fintype a] [Fintype e]
    (G : CMatrix (TensorPower a 2)) (H : CMatrix (TensorPower e 2))
    (i j i' j' : a) (k l k' l' : e) :
    twoCopySideOperator (a := a) (e := e) G H
        (twoCopyTensorWord (a := Prod a e) (i, k) (j, l))
        (twoCopyTensorWord (a := Prod a e) (i', k') (j', l')) =
      G (twoCopyTensorWord (a := a) i j) (twoCopyTensorWord (a := a) i' j') *
        H (twoCopyTensorWord (a := e) k l) (twoCopyTensorWord (a := e) k' l') := by
  simp

private theorem twoCopySideOperator_mul [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (G G' : CMatrix (TensorPower a 2)) (H H' : CMatrix (TensorPower e 2)) :
    twoCopySideOperator (a := a) (e := e) G H * twoCopySideOperator (a := a) (e := e) G' H' =
      twoCopySideOperator (a := a) (e := e) (G * G') (H * H') := by
  ext x y
  rw [← twoCopyTensorWord_coords (a := Prod a e) x,
    ← twoCopyTensorWord_coords (a := Prod a e) y]
  simp [twoCopySideOperator, twoCopyProdReindex, Matrix.mul_apply, Matrix.kronecker,
    Finset.mul_sum, Finset.sum_mul]
  let X := tensorPowerProdEquiv a e 2 x
  let Y := tensorPowerProdEquiv a e 2 y
  calc
    (∑ z : TensorPower (Prod a e) 2,
      G X.1 ((tensorPowerProdEquiv a e 2 z).1) *
          H X.2 ((tensorPowerProdEquiv a e 2 z).2) *
        (G' ((tensorPowerProdEquiv a e 2 z).1) Y.1 *
          H' ((tensorPowerProdEquiv a e 2 z).2) Y.2)) =
      ∑ p : TensorPower a 2 × TensorPower e 2,
        G X.1 p.1 * H X.2 p.2 * (G' p.1 Y.1 * H' p.2 Y.2) := by
        exact Fintype.sum_equiv (tensorPowerProdEquiv a e 2)
          (fun z : TensorPower (Prod a e) 2 =>
            G X.1 ((tensorPowerProdEquiv a e 2 z).1) *
                H X.2 ((tensorPowerProdEquiv a e 2 z).2) *
              (G' ((tensorPowerProdEquiv a e 2 z).1) Y.1 *
                H' ((tensorPowerProdEquiv a e 2 z).2) Y.2))
          (fun p : TensorPower a 2 × TensorPower e 2 =>
            G X.1 p.1 * H X.2 p.2 * (G' p.1 Y.1 * H' p.2 Y.2))
          (fun _ => rfl)
    _ = ∑ j : TensorPower e 2, ∑ i : TensorPower a 2,
        G X.1 i * G' i Y.1 * (H X.2 j * H' j Y.2) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        simp [mul_comm, mul_left_comm]

private theorem unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) :
    (unitaryTensorPowerMatrix U 2 : CMatrix (TensorPower a 2)) =
      tensorPowerKroneckerTwo (a := a) (U : CMatrix a) := by
  ext x y
  rw [unitaryTensorPowerMatrix_apply_eq_fin_prod]
  simp [tensorPowerKroneckerTwo]

@[simp]
theorem one_apply_twoCopyTensorWord [Fintype a] [DecidableEq a]
    (i j k l : a) :
    (1 : CMatrix (TensorPower a 2))
        (twoCopyTensorWord (a := a) i j) (twoCopyTensorWord (a := a) k l) =
      if i = k then if j = l then 1 else 0 else 0 := by
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [Matrix.one_apply, twoCopyTensorWord_eq_iff, hik, hjl]

@[simp]
theorem tensorPowerSwapMatrix_two_apply_twoCopyTensorWord [Fintype a] [DecidableEq a]
    (i j k l : a) :
    tensorPowerSwapMatrix_two (a := a)
        (twoCopyTensorWord (a := a) i j) (twoCopyTensorWord (a := a) k l) =
      if j = k then if i = l then 1 else 0 else 0 := by
  by_cases hjk : j = k <;> by_cases hil : i = l <;>
    simp [tensorPowerSwapMatrix_two, permutationMatrix, Equiv.Perm.permMatrix,
      PEquiv.toMatrix, permEquiv_twoCopySwapPerm_twoCopyTensorWord,
      twoCopyTensorWord_eq_iff, hjk, hil]

private theorem partialTraceA_flip_entry_sum [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (rho : CMatrix (Prod a e))
    (i j : a) (k l : e) :
    (∑ x : a, ∑ x_1 : e, ∑ x_2 : a, ∑ x_3 : e,
      if x_3 = k ∧ x_1 = l then
        if x = i ∧ x_2 = j then
          rho (i, k) (x, x_1) * rho (j, l) (x_2, x_3)
        else 0
      else 0) =
      rho (i, k) (i, l) * rho (j, l) (j, k) := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single l]
    · rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single k]
        · simp
        · intro x _ hx
          simp [hx]
        · intro h
          exact False.elim (h (Finset.mem_univ k))
      · intro x _ hx
        simp [hx]
      · intro h
        exact False.elim (h (Finset.mem_univ j))
    · intro x _ hx
      simp [hx]
    · intro h
      exact False.elim (h (Finset.mem_univ l))
  · intro x _ hx
    simp [hx]
  · intro h
    exact False.elim (h (Finset.mem_univ i))

private theorem partialTraceB_flip_entry_sum [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (rho : CMatrix (Prod a e))
    (i j : a) (k l : e) :
    (∑ x : a, ∑ x_1 : e, ∑ x_2 : a, ∑ x_3 : e,
      if x_1 = k ∧ x_3 = l then
        if x_2 = i ∧ x = j then
          rho (i, k) (x, x_1) * rho (j, l) (x_2, x_3)
        else 0
      else 0) =
      rho (i, k) (j, k) * rho (j, l) (i, l) := by
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single l]
        · simp
        · intro x _ hx
          simp [hx]
        · intro h
          exact False.elim (h (Finset.mem_univ l))
      · intro x _ hx
        simp [hx]
      · intro h
        exact False.elim (h (Finset.mem_univ i))
    · intro x _ hx
      simp [hx]
    · intro h
      exact False.elim (h (Finset.mem_univ k))
  · intro x _ hx
    simp [hx]
  · intro h
    exact False.elim (h (Finset.mem_univ j))

theorem tensorPowerProdEquiv_twoCopySwap_fst [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (x : TensorPower (Prod a e) 2) :
    (tensorPowerProdEquiv a e 2
        (permEquiv (a := Prod a e) 2 twoCopySwapPerm x)).1 =
      permEquiv (a := a) 2 twoCopySwapPerm ((tensorPowerProdEquiv a e 2 x).1) := by
  apply (tensorPowerEquiv (a := a) 2).injective
  funext r
  have hperm := tensorPowerEquiv_permEquiv (a := Prod a e) 2 twoCopySwapPerm x
  fin_cases r
  · have h := congrFun hperm 0
    change (tensorPowerEquiv (a := Prod a e) 2
        (permEquiv (a := Prod a e) 2 twoCopySwapPerm x) 0).1 =
      (tensorPowerEquiv (a := Prod a e) 2 x 1).1
    simp [twoCopySwapPerm]
  · have h := congrFun hperm 1
    change (tensorPowerEquiv (a := Prod a e) 2
        (permEquiv (a := Prod a e) 2 twoCopySwapPerm x) 1).1 =
      (tensorPowerEquiv (a := Prod a e) 2 x 0).1
    simp [twoCopySwapPerm]

theorem tensorPowerProdEquiv_twoCopySwap_snd [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (x : TensorPower (Prod a e) 2) :
    (tensorPowerProdEquiv a e 2
        (permEquiv (a := Prod a e) 2 twoCopySwapPerm x)).2 =
      permEquiv (a := e) 2 twoCopySwapPerm ((tensorPowerProdEquiv a e 2 x).2) := by
  apply (tensorPowerEquiv (a := e) 2).injective
  funext r
  have hperm := tensorPowerEquiv_permEquiv (a := Prod a e) 2 twoCopySwapPerm x
  fin_cases r
  · have h := congrFun hperm 0
    change (tensorPowerEquiv (a := Prod a e) 2
        (permEquiv (a := Prod a e) 2 twoCopySwapPerm x) 0).2 =
      (tensorPowerEquiv (a := Prod a e) 2 x 1).2
    simp [twoCopySwapPerm]
  · have h := congrFun hperm 1
    change (tensorPowerEquiv (a := Prod a e) 2
        (permEquiv (a := Prod a e) 2 twoCopySwapPerm x) 1).2 =
      (tensorPowerEquiv (a := Prod a e) 2 x 0).2
    simp [twoCopySwapPerm]

theorem tensorPowerSwapMatrix_two_prod_eq_twoCopySideOperator [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] :
    tensorPowerSwapMatrix_two (a := Prod a e) =
      twoCopySideOperator (a := a) (e := e)
        (tensorPowerSwapMatrix_two (a := a)) (tensorPowerSwapMatrix_two (a := e)) := by
  ext x y
  by_cases hxy : permEquiv (a := Prod a e) 2 twoCopySwapPerm x = y
  · have hfst :
        permEquiv (a := a) 2 twoCopySwapPerm ((tensorPowerProdEquiv a e 2 x).1) =
          ((tensorPowerProdEquiv a e 2 y).1) := by
      rw [← tensorPowerProdEquiv_twoCopySwap_fst (a := a) (e := e) x, hxy]
    have hsnd :
        permEquiv (a := e) 2 twoCopySwapPerm ((tensorPowerProdEquiv a e 2 x).2) =
          ((tensorPowerProdEquiv a e 2 y).2) := by
      rw [← tensorPowerProdEquiv_twoCopySwap_snd (a := a) (e := e) x, hxy]
    simp [twoCopySideOperator, twoCopyProdReindex, tensorPowerSwapMatrix_two,
      permutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix, hxy, hfst, hsnd]
  · have hsplit :
        ¬ (permEquiv (a := a) 2 twoCopySwapPerm ((tensorPowerProdEquiv a e 2 x).1) =
              ((tensorPowerProdEquiv a e 2 y).1) ∧
            permEquiv (a := e) 2 twoCopySwapPerm ((tensorPowerProdEquiv a e 2 x).2) =
              ((tensorPowerProdEquiv a e 2 y).2)) := by
      intro h
      apply hxy
      apply (tensorPowerProdEquiv a e 2).injective
      ext
      · simpa [tensorPowerProdEquiv_twoCopySwap_fst (a := a) (e := e) x] using h.1
      · simpa [tensorPowerProdEquiv_twoCopySwap_snd (a := a) (e := e) x] using h.2
    simp [twoCopySideOperator, twoCopyProdReindex, tensorPowerSwapMatrix_two,
      permutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix, hxy]
    by_cases hfst :
        permEquiv (a := a) 2 twoCopySwapPerm ((tensorPowerProdEquiv a e 2 x).1) =
          ((tensorPowerProdEquiv a e 2 y).1)
    · have hsnd :
          ¬ permEquiv (a := e) 2 twoCopySwapPerm ((tensorPowerProdEquiv a e 2 x).2) =
            ((tensorPowerProdEquiv a e 2 y).2) := by
        intro hsnd
        exact hsplit ⟨hfst, hsnd⟩
      simp [hfst, hsnd]
    · simp [hfst]

theorem tensorPowerKroneckerTwo_prod_mul_full_swap_trace [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (rho : CMatrix (Prod a e)) :
    (tensorPowerKroneckerTwo (a := Prod a e) rho *
        twoCopySideOperator (a := a) (e := e)
          (tensorPowerSwapMatrix_two (a := a)) (tensorPowerSwapMatrix_two (a := e))).trace =
      (rho * rho).trace := by
  rw [← tensorPowerSwapMatrix_two_prod_eq_twoCopySideOperator (a := a) (e := e)]
  exact tensorPowerKroneckerTwo_mul_tensorPowerSwapMatrix_two_trace (a := Prod a e) rho

theorem tensorPowerKroneckerTwo_prod_mul_one_swap_trace [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (rho : CMatrix (Prod a e)) :
    (tensorPowerKroneckerTwo (a := Prod a e) rho *
        twoCopySideOperator (a := a) (e := e)
          (1 : CMatrix (TensorPower a 2))
          (tensorPowerSwapMatrix_two (a := e))).trace =
      (partialTraceA (a := a) (b := e) rho *
        partialTraceA (a := a) (b := e) rho).trace := by
  calc
    (tensorPowerKroneckerTwo (a := Prod a e) rho *
        twoCopySideOperator (a := a) (e := e)
          (1 : CMatrix (TensorPower a 2))
          (tensorPowerSwapMatrix_two (a := e))).trace =
        ∑ i : a, ∑ k : e, ∑ j : a, ∑ l : e,
          rho (i, k) (i, l) * rho (j, l) (j, k) := by
      rw [Matrix.trace, sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      change (tensorPowerKroneckerTwo (a := Prod a e) rho *
          twoCopySideOperator (a := a) (e := e)
            (1 : CMatrix (TensorPower a 2))
            (tensorPowerSwapMatrix_two (a := e)))
          (twoCopyTensorWord (a := Prod a e) (i, k) (j, l))
          (twoCopyTensorWord (a := Prod a e) (i, k) (j, l)) =
        rho (i, k) (i, l) * rho (j, l) (j, k)
      rw [Matrix.mul_apply, sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      simp_rw [Fintype.sum_prod_type]
      simpa [Matrix.one_apply, permEquiv_twoCopySwapPerm_twoCopyTensorWord,
        twoCopyTensorWord_eq_iff, mul_comm] using
          partialTraceA_flip_entry_sum (a := a) (e := e) rho i j k l
    _ = ∑ k : e, ∑ l : e, ∑ i : a, ∑ j : a,
          rho (i, k) (i, l) * rho (j, l) (j, k) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      calc
        (∑ i : a, ∑ j : a, ∑ l : e,
            rho (i, k) (i, l) * rho (j, l) (j, k)) =
            ∑ i : a, ∑ l : e, ∑ j : a,
              rho (i, k) (i, l) * rho (j, l) (j, k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
        _ = ∑ l : e, ∑ i : a, ∑ j : a,
              rho (i, k) (i, l) * rho (j, l) (j, k) := by
          rw [Finset.sum_comm]
    _ = ∑ l : e, ∑ k : e, ∑ i : a, ∑ j : a,
          rho (i, k) (i, l) * rho (j, l) (j, k) := by
      rw [Finset.sum_comm]
    _ = (partialTraceA (a := a) (b := e) rho *
        partialTraceA (a := a) (b := e) rho).trace := by
      rw [Matrix.trace]
      simp [Matrix.mul_apply, partialTraceA, Finset.mul_sum, mul_comm]

theorem tensorPowerKroneckerTwo_prod_mul_swap_one_trace [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (rho : CMatrix (Prod a e)) :
    (tensorPowerKroneckerTwo (a := Prod a e) rho *
        twoCopySideOperator (a := a) (e := e)
          (tensorPowerSwapMatrix_two (a := a))
          (1 : CMatrix (TensorPower e 2))).trace =
      (partialTraceB (a := a) (b := e) rho *
        partialTraceB (a := a) (b := e) rho).trace := by
  calc
    (tensorPowerKroneckerTwo (a := Prod a e) rho *
        twoCopySideOperator (a := a) (e := e)
          (tensorPowerSwapMatrix_two (a := a))
          (1 : CMatrix (TensorPower e 2))).trace =
        ∑ i : a, ∑ k : e, ∑ j : a, ∑ l : e,
          rho (i, k) (j, k) * rho (j, l) (i, l) := by
      rw [Matrix.trace, sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      change (tensorPowerKroneckerTwo (a := Prod a e) rho *
          twoCopySideOperator (a := a) (e := e)
            (tensorPowerSwapMatrix_two (a := a))
            (1 : CMatrix (TensorPower e 2)))
          (twoCopyTensorWord (a := Prod a e) (i, k) (j, l))
          (twoCopyTensorWord (a := Prod a e) (i, k) (j, l)) =
        rho (i, k) (j, k) * rho (j, l) (i, l)
      rw [Matrix.mul_apply, sum_tensorPower_twoCopyTensorWord (β := ℂ)]
      simp_rw [Fintype.sum_prod_type]
      simpa [Matrix.one_apply, permEquiv_twoCopySwapPerm_twoCopyTensorWord,
        twoCopyTensorWord_eq_iff, mul_comm] using
          partialTraceB_flip_entry_sum (a := a) (e := e) rho i j k l
    _ = ∑ i : a, ∑ j : a, ∑ k : e, ∑ l : e,
          rho (i, k) (j, k) * rho (j, l) (i, l) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    _ = ∑ j : a, ∑ i : a, ∑ k : e, ∑ l : e,
          rho (i, k) (j, k) * rho (j, l) (i, l) := by
      rw [Finset.sum_comm]
    _ = (partialTraceB (a := a) (b := e) rho *
        partialTraceB (a := a) (b := e) rho).trace := by
      rw [Matrix.trace]
      simp [Matrix.mul_apply, partialTraceB, Finset.mul_sum, mul_comm]

theorem hayden_secondMomentTwirl_trace_decomposition [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nontrivial a]
    (P : CMatrix a) (hP : P * P = P) (rho : CMatrix (Prod a e)) :
    (tensorPowerKroneckerTwo (a := Prod a e) rho *
      twoCopySideOperator (a := a) (e := e)
        (unitaryTwirl 2 (haydenRestrictedFlip (a := a) P))
        (tensorPowerSwapMatrix_two (a := e))).trace =
      (((1 : ℂ) / 2) *
        (((P.trace * P.trace + P.trace) / 2 /
            Matrix.trace (symmetricProjectionMatrix (a := a) 2)) +
          ((P.trace * (P.trace - 1) / 2) /
            Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
          (rho * rho).trace +
        (((1 : ℂ) / 2) *
          (((P.trace * P.trace + P.trace) / 2 /
              Matrix.trace (symmetricProjectionMatrix (a := a) 2)) -
            ((P.trace * (P.trace - 1) / 2) /
              Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
          (partialTraceA (a := a) (b := e) rho *
            partialTraceA (a := a) (b := e) rho).trace := by
  rw [hayden_secondMomentTwirl_restrictedFlip (a := a) P hP]
  rw [twoCopySideOperator_smul_left]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  rw [twoCopySideOperator_add_left]
  rw [twoCopySideOperator_smul_left, twoCopySideOperator_smul_left]
  rw [Matrix.mul_add, Matrix.trace_add]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  rw [tensorPowerKroneckerTwo_prod_mul_full_swap_trace]
  rw [tensorPowerKroneckerTwo_prod_mul_one_swap_trace]
  ring

/-- Hayden's second-moment trace decomposition with the source normalization
factor `(|A| / d)^2` attached. -/
theorem hayden_secondMomentTwirl_scaled_trace_decomposition [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nontrivial a]
    (P : CMatrix a) (hP : P * P = P) (rho : CMatrix (Prod a e)) (d : ℝ) :
    ((((Fintype.card a : ℝ) / d) ^ 2 : ℝ) : ℂ) *
        (tensorPowerKroneckerTwo (a := Prod a e) rho *
          twoCopySideOperator (a := a) (e := e)
            (unitaryTwirl 2 (haydenRestrictedFlip (a := a) P))
            (tensorPowerSwapMatrix_two (a := e))).trace =
      ((((Fintype.card a : ℝ) / d) ^ 2 : ℝ) : ℂ) *
        ((((1 : ℂ) / 2) *
          (((P.trace * P.trace + P.trace) / 2 /
              Matrix.trace (symmetricProjectionMatrix (a := a) 2)) +
            ((P.trace * (P.trace - 1) / 2) /
              Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
            (rho * rho).trace +
          (((1 : ℂ) / 2) *
            (((P.trace * P.trace + P.trace) / 2 /
                Matrix.trace (symmetricProjectionMatrix (a := a) 2)) -
              ((P.trace * (P.trace - 1) / 2) /
                Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
            (partialTraceA (a := a) (b := e) rho *
              partialTraceA (a := a) (b := e) rho).trace) := by
  rw [hayden_secondMomentTwirl_trace_decomposition (a := a) (e := e) P hP rho]

/-- Pointwise flip trick for the actual projected state: its square trace is
the two-copy trace against the full `(A × E)` swap. -/
theorem haydenProjectedAE_square_trace_eq_twoCopy_full_swap [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (U : Matrix.unitaryGroup a ℂ) :
    (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace =
      (tensorPowerKroneckerTwo (a := Prod a e)
          (haydenProjectedAE (a := a) (e := e) P d rho U) *
        tensorPowerSwapMatrix_two (a := Prod a e)).trace := by
  rw [tensorPowerKroneckerTwo_mul_tensorPowerSwapMatrix_two_trace]

/-- Pointwise flip trick for the actual projected state, reindexed into the
source-side `A² × E²` convention. -/
theorem haydenProjectedAE_square_trace_eq_twoCopy_side_swaps [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (U : Matrix.unitaryGroup a ℂ) :
    (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace =
      (tensorPowerKroneckerTwo (a := Prod a e)
          (haydenProjectedAE (a := a) (e := e) P d rho U) *
        twoCopySideOperator (a := a) (e := e)
          (tensorPowerSwapMatrix_two (a := a))
          (tensorPowerSwapMatrix_two (a := e))).trace := by
  rw [haydenProjectedAE_square_trace_eq_twoCopy_full_swap]
  rw [tensorPowerSwapMatrix_two_prod_eq_twoCopySideOperator]

private theorem haydenProjectedAE_square_trace_eq_restrictedFlip_inv_integrand [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (U : Matrix.unitaryGroup a ℂ) :
    (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace =
      ((((Fintype.card a : ℝ) / d) ^ 2 : ℝ) : ℂ) *
        (tensorPowerKroneckerTwo (a := Prod a e) rho *
          twoCopySideOperator (a := a) (e := e)
            (unitaryTwirlIntegrand (a := a) 2 (haydenRestrictedFlip (a := a) P) U⁻¹)
            (tensorPowerSwapMatrix_two (a := e))).trace := by
  rw [haydenProjectedAE_square_trace_eq_twoCopy_side_swaps]
  let c : ℂ := (((Fintype.card a : ℝ) / d : ℝ) : ℂ)
  let L : CMatrix (Prod a e) := Matrix.kronecker (P * (U : CMatrix a)) (1 : CMatrix e)
  let R : CMatrix (Prod a e) := Matrix.kronecker (star (U : CMatrix a) * P) (1 : CMatrix e)
  let LA : CMatrix (TensorPower a 2) := tensorPowerKroneckerTwo (a := a) (P * (U : CMatrix a))
  let RA : CMatrix (TensorPower a 2) := tensorPowerKroneckerTwo (a := a) (star (U : CMatrix a) * P)
  let FAE : CMatrix (TensorPower (Prod a e) 2) :=
    twoCopySideOperator (a := a) (e := e)
      (tensorPowerSwapMatrix_two (a := a)) (tensorPowerSwapMatrix_two (a := e))
  have hstate :
      haydenProjectedAE (a := a) (e := e) P d rho U = c • (L * rho * R) := by
    rfl
  have hL :
      tensorPowerKroneckerTwo (a := Prod a e) L =
        twoCopySideOperator (a := a) (e := e) LA (1 : CMatrix (TensorPower e 2)) := by
    simpa [L, LA] using
      tensorPowerKroneckerTwo_kronecker_one (a := a) (e := e) (P * (U : CMatrix a))
  have hR :
      tensorPowerKroneckerTwo (a := Prod a e) R =
        twoCopySideOperator (a := a) (e := e) RA (1 : CMatrix (TensorPower e 2)) := by
    simpa [R, RA] using
      tensorPowerKroneckerTwo_kronecker_one (a := a) (e := e) (star (U : CMatrix a) * P)
  have htensor :
      tensorPowerKroneckerTwo (a := Prod a e) (L * rho * R) =
        twoCopySideOperator (a := a) (e := e) LA (1 : CMatrix (TensorPower e 2)) *
          (tensorPowerKroneckerTwo (a := Prod a e) rho *
          twoCopySideOperator (a := a) (e := e) RA (1 : CMatrix (TensorPower e 2))) := by
    calc
      tensorPowerKroneckerTwo (a := Prod a e) (L * rho * R) =
          tensorPowerKroneckerTwo (a := Prod a e) (L * rho) *
            tensorPowerKroneckerTwo (a := Prod a e) R := by
            exact (tensorPowerKroneckerTwo_mul (a := Prod a e) (L * rho) R).symm
      _ = (tensorPowerKroneckerTwo (a := Prod a e) L *
            tensorPowerKroneckerTwo (a := Prod a e) rho) *
            tensorPowerKroneckerTwo (a := Prod a e) R := by
            rw [tensorPowerKroneckerTwo_mul (a := Prod a e) L rho]
      _ = twoCopySideOperator (a := a) (e := e) LA (1 : CMatrix (TensorPower e 2)) *
          (tensorPowerKroneckerTwo (a := Prod a e) rho *
            twoCopySideOperator (a := a) (e := e) RA (1 : CMatrix (TensorPower e 2))) := by
            rw [hL, hR]
            simp [Matrix.mul_assoc]
  have hLA :
      LA = tensorPowerKroneckerTwo (a := a) P *
        tensorPowerKroneckerTwo (a := a) (U : CMatrix a) := by
    simp [LA, tensorPowerKroneckerTwo_mul]
  have hRA :
      RA = star (tensorPowerKroneckerTwo (a := a) (U : CMatrix a)) *
        tensorPowerKroneckerTwo (a := a) P := by
    calc
      RA = tensorPowerKroneckerTwo (a := a) (star (U : CMatrix a)) *
          tensorPowerKroneckerTwo (a := a) P := by
          exact (tensorPowerKroneckerTwo_mul (a := a) (star (U : CMatrix a)) P).symm
      _ = star (tensorPowerKroneckerTwo (a := a) (U : CMatrix a)) *
          tensorPowerKroneckerTwo (a := a) P := by
          rw [tensorPowerKroneckerTwo_star]
  have hside :
      twoCopySideOperator (a := a) (e := e) RA (1 : CMatrix (TensorPower e 2)) * FAE *
          twoCopySideOperator (a := a) (e := e) LA (1 : CMatrix (TensorPower e 2)) =
        twoCopySideOperator (a := a) (e := e)
          (unitaryTwirlIntegrand (a := a) 2 (haydenRestrictedFlip (a := a) P) U⁻¹)
          (tensorPowerSwapMatrix_two (a := e)) := by
    rw [hLA, hRA]
    simp [FAE, twoCopySideOperator_mul, unitaryTwirlIntegrand,
      haydenRestrictedFlip, tensorPowerKroneckerTwo_mul,
      unitaryTensorPowerMatrix_two_eq_tensorPowerKroneckerTwo, Matrix.mul_assoc]
  calc
    (tensorPowerKroneckerTwo (a := Prod a e)
          (haydenProjectedAE (a := a) (e := e) P d rho U) * FAE).trace =
        (tensorPowerKroneckerTwo (a := Prod a e) (c • (L * rho * R)) * FAE).trace := by
          rw [hstate]
    _ = c ^ 2 *
        (tensorPowerKroneckerTwo (a := Prod a e) (L * rho * R) * FAE).trace := by
          rw [tensorPowerKroneckerTwo_smul, Matrix.smul_mul, Matrix.trace_smul]
          rfl
    _ = c ^ 2 *
        ((twoCopySideOperator (a := a) (e := e) LA (1 : CMatrix (TensorPower e 2)) *
            (tensorPowerKroneckerTwo (a := Prod a e) rho *
            twoCopySideOperator (a := a) (e := e) RA (1 : CMatrix (TensorPower e 2)))) *
          FAE).trace := by
          rw [htensor]
    _ = c ^ 2 *
        (tensorPowerKroneckerTwo (a := Prod a e) rho *
          (twoCopySideOperator (a := a) (e := e) RA (1 : CMatrix (TensorPower e 2)) * FAE *
            twoCopySideOperator (a := a) (e := e) LA (1 : CMatrix (TensorPower e 2)))).trace := by
          congr 1
          simpa [Matrix.mul_assoc] using
            Matrix.trace_mul_comm
              (twoCopySideOperator (a := a) (e := e) LA (1 : CMatrix (TensorPower e 2)))
              (tensorPowerKroneckerTwo (a := Prod a e) rho *
                twoCopySideOperator (a := a) (e := e) RA (1 : CMatrix (TensorPower e 2)) *
                FAE)
    _ = c ^ 2 *
        (tensorPowerKroneckerTwo (a := Prod a e) rho *
          twoCopySideOperator (a := a) (e := e)
            (unitaryTwirlIntegrand (a := a) 2 (haydenRestrictedFlip (a := a) P) U⁻¹)
            (tensorPowerSwapMatrix_two (a := e))).trace := by
          rw [hside]
    _ = ((((Fintype.card a : ℝ) / d) ^ 2 : ℝ) : ℂ) *
        (tensorPowerKroneckerTwo (a := Prod a e) rho *
          twoCopySideOperator (a := a) (e := e)
            (unitaryTwirlIntegrand (a := a) 2 (haydenRestrictedFlip (a := a) P) U⁻¹)
            (tensorPowerSwapMatrix_two (a := e))).trace := by
          simp [c, Complex.ofReal_pow]

private noncomputable def twoCopySideTraceCLM [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (rho : CMatrix (Prod a e)) (H : CMatrix (TensorPower e 2)) :
    CMatrix (TensorPower a 2) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun G =>
        (tensorPowerKroneckerTwo (a := Prod a e) rho *
          twoCopySideOperator (a := a) (e := e) G H).trace
       map_add' := by
        intro G G'
        rw [twoCopySideOperator_add_left, Matrix.mul_add, Matrix.trace_add]
       map_smul' := by
        intro c G
        change (tensorPowerKroneckerTwo (a := Prod a e) rho *
            twoCopySideOperator (a := a) (e := e) ((c : ℂ) • G) H).trace =
          c • (tensorPowerKroneckerTwo (a := Prod a e) rho *
            twoCopySideOperator (a := a) (e := e) G H).trace
        rw [twoCopySideOperator_smul_left, Matrix.mul_smul, Matrix.trace_smul]
        rfl } :
      CMatrix (TensorPower a 2) →ₗ[ℝ] ℂ)

/-- Integral-side bridge for the second-moment scalar trace: averaging the
restricted-flip trace integrand is exactly evaluating the trace functional on
the two-copy Haar twirl. -/
theorem hayden_secondMomentTwirl_trace_integral_bridge [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a]
    (P : CMatrix a) (rho : CMatrix (Prod a e)) :
    (∫ U : Matrix.unitaryGroup a ℂ,
        (tensorPowerKroneckerTwo (a := Prod a e) rho *
          twoCopySideOperator (a := a) (e := e)
            (unitaryTwirlIntegrand (a := a) 2 (haydenRestrictedFlip (a := a) P) U)
            (tensorPowerSwapMatrix_two (a := e))).trace
        ∂unitaryHaarMeasure (a := a)) =
      (tensorPowerKroneckerTwo (a := Prod a e) rho *
        twoCopySideOperator (a := a) (e := e)
          (unitaryTwirl 2 (haydenRestrictedFlip (a := a) P))
          (tensorPowerSwapMatrix_two (a := e))).trace := by
  let L := twoCopySideTraceCLM (a := a) (e := e) rho
    (tensorPowerSwapMatrix_two (a := e))
  have hf : Integrable
      (unitaryTwirlIntegrand (a := a) 2 (haydenRestrictedFlip (a := a) P))
      (unitaryHaarMeasure (a := a)) :=
    unitaryTwirl_integrand_integrable (a := a) 2 (haydenRestrictedFlip (a := a) P)
  change (∫ U : Matrix.unitaryGroup a ℂ,
        L (unitaryTwirlIntegrand (a := a) 2 (haydenRestrictedFlip (a := a) P) U)
        ∂unitaryHaarMeasure (a := a)) =
      L (unitaryTwirl 2 (haydenRestrictedFlip (a := a) P))
  simpa [L, unitaryTwirl] using
    ((twoCopySideTraceCLM (a := a) (e := e) rho
      (tensorPowerSwapMatrix_two (a := e))).integral_comp_comm hf)

/-- Scaled integral-side second-moment bridge, composed with the source trace
decomposition already proved for `unitaryTwirl 2 (haydenRestrictedFlip P)`. -/
theorem hayden_secondMomentTwirl_scaled_trace_integral_decomposition [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nontrivial a]
    (P : CMatrix a) (hP : P * P = P) (rho : CMatrix (Prod a e)) (d : ℝ) :
    ((((Fintype.card a : ℝ) / d) ^ 2 : ℝ) : ℂ) *
        (∫ U : Matrix.unitaryGroup a ℂ,
          (tensorPowerKroneckerTwo (a := Prod a e) rho *
            twoCopySideOperator (a := a) (e := e)
              (unitaryTwirlIntegrand (a := a) 2 (haydenRestrictedFlip (a := a) P) U)
              (tensorPowerSwapMatrix_two (a := e))).trace
          ∂unitaryHaarMeasure (a := a)) =
      ((((Fintype.card a : ℝ) / d) ^ 2 : ℝ) : ℂ) *
        ((((1 : ℂ) / 2) *
          (((P.trace * P.trace + P.trace) / 2 /
              Matrix.trace (symmetricProjectionMatrix (a := a) 2)) +
            ((P.trace * (P.trace - 1) / 2) /
              Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
            (rho * rho).trace +
          (((1 : ℂ) / 2) *
            (((P.trace * P.trace + P.trace) / 2 /
                Matrix.trace (symmetricProjectionMatrix (a := a) 2)) -
              ((P.trace * (P.trace - 1) / 2) /
                Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
            (partialTraceA (a := a) (b := e) rho *
              partialTraceA (a := a) (b := e) rho).trace) := by
  rw [hayden_secondMomentTwirl_trace_integral_bridge (a := a) (e := e) P rho]
  rw [hayden_secondMomentTwirl_scaled_trace_decomposition (a := a) (e := e) P hP rho d]

/-- Actual projected-state second moment in Hayden's Step 4 computation.
The pointwise flip trick naturally produces the inverse-orientation Haar
integrand; normalized compact Haar inversion invariance converts it to the
`unitaryTwirlIntegrand` orientation used by the reusable twirl API. -/
theorem haydenProjectedAE_secondMoment_trace_integral_decomposition [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nontrivial a]
    (P : CMatrix a) (hP : P * P = P) (rho : CMatrix (Prod a e)) (d : ℝ) :
    (∫ U : Matrix.unitaryGroup a ℂ,
        (haydenProjectedAE (a := a) (e := e) P d rho U *
          haydenProjectedAE (a := a) (e := e) P d rho U).trace
        ∂unitaryHaarMeasure (a := a)) =
      ((((Fintype.card a : ℝ) / d) ^ 2 : ℝ) : ℂ) *
        ((((1 : ℂ) / 2) *
          (((P.trace * P.trace + P.trace) / 2 /
              Matrix.trace (symmetricProjectionMatrix (a := a) 2)) +
            ((P.trace * (P.trace - 1) / 2) /
              Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
            (rho * rho).trace +
          (((1 : ℂ) / 2) *
            (((P.trace * P.trace + P.trace) / 2 /
                Matrix.trace (symmetricProjectionMatrix (a := a) 2)) -
              ((P.trace * (P.trace - 1) / 2) /
                Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
            (partialTraceA (a := a) (b := e) rho *
              partialTraceA (a := a) (b := e) rho).trace) := by
  let c2 : ℂ := ((((Fintype.card a : ℝ) / d) ^ 2 : ℝ) : ℂ)
  let f : Matrix.unitaryGroup a ℂ → ℂ := fun U =>
    (tensorPowerKroneckerTwo (a := Prod a e) rho *
      twoCopySideOperator (a := a) (e := e)
        (unitaryTwirlIntegrand (a := a) 2 (haydenRestrictedFlip (a := a) P) U)
        (tensorPowerSwapMatrix_two (a := e))).trace
  calc
    (∫ U : Matrix.unitaryGroup a ℂ,
        (haydenProjectedAE (a := a) (e := e) P d rho U *
          haydenProjectedAE (a := a) (e := e) P d rho U).trace
        ∂unitaryHaarMeasure (a := a)) =
      ∫ U : Matrix.unitaryGroup a ℂ, c2 * f U⁻¹ ∂unitaryHaarMeasure (a := a) := by
        apply integral_congr_ae
        filter_upwards with U
        simpa [c2, f] using
          haydenProjectedAE_square_trace_eq_restrictedFlip_inv_integrand
            (a := a) (e := e) P d rho U
    _ = c2 * (∫ U : Matrix.unitaryGroup a ℂ, f U⁻¹ ∂unitaryHaarMeasure (a := a)) := by
        rw [integral_const_mul]
    _ = c2 * (∫ U : Matrix.unitaryGroup a ℂ, f U ∂unitaryHaarMeasure (a := a)) := by
        rw [MeasureTheory.integral_inv_eq_self (f := f) (μ := unitaryHaarMeasure (a := a))]
    _ = ((((Fintype.card a : ℝ) / d) ^ 2 : ℝ) : ℂ) *
        ((((1 : ℂ) / 2) *
          (((P.trace * P.trace + P.trace) / 2 /
              Matrix.trace (symmetricProjectionMatrix (a := a) 2)) +
            ((P.trace * (P.trace - 1) / 2) /
              Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
            (rho * rho).trace +
          (((1 : ℂ) / 2) *
            (((P.trace * P.trace + P.trace) / 2 /
                Matrix.trace (symmetricProjectionMatrix (a := a) 2)) -
              ((P.trace * (P.trace - 1) / 2) /
                Matrix.trace (antisymmetricProjectionMatrix_two (a := a))))) *
            (partialTraceA (a := a) (b := e) rho *
              partialTraceA (a := a) (b := e) rho).trace) := by
        simpa [c2, f] using
          hayden_secondMomentTwirl_scaled_trace_integral_decomposition
            (a := a) (e := e) P hP rho d

private theorem symmetricProjectionMatrix_one_eq_one [Fintype a] [DecidableEq a] :
    symmetricProjectionMatrix (a := a) 1 = 1 := by
  rw [symmetricProjectionMatrix_eq_perm_average]
  ext x y
  simp [permutationMatrix, permEquiv_one, Matrix.one_apply]

private theorem unitaryTwirl_one_eq_trace_smul_one [Fintype a] [DecidableEq a] [Nonempty a]
    (A : CMatrix (TensorPower a 1)) :
    unitaryTwirl 1 A = (A.trace / (Fintype.card a : ℂ)) • 1 := by
  have h := unitaryTwirl_mul_symmetricProjectionMatrix_eq_trace_smul (a := a) 1 A
  rw [symmetricProjectionMatrix_one_eq_one (a := a), Matrix.mul_one] at h
  rw [h]
  congr 2
  · simp
  · simp [Matrix.trace_one, tensorPower_card]

private def oneCopyMatrixLift [Fintype a] (M : CMatrix a) : CMatrix (TensorPower a 1) :=
  M.submatrix (decouplingTensorPowerOneEquiv a) (decouplingTensorPowerOneEquiv a)

private theorem oneCopyMatrixLift_trace [Fintype a] (M : CMatrix a) :
    (oneCopyMatrixLift (a := a) M).trace = M.trace := by
  rw [Matrix.trace]
  exact Fintype.sum_equiv (decouplingTensorPowerOneEquiv a)
    (fun x : TensorPower a 1 =>
      M ((decouplingTensorPowerOneEquiv a) x) ((decouplingTensorPowerOneEquiv a) x))
    (fun i : a => M i i)
    (fun _ => rfl)

private theorem unitaryTwirlIntegrand_oneCopyMatrixLift_apply [Fintype a] [DecidableEq a]
    [Nonempty a] (M : CMatrix a) (U : Matrix.unitaryGroup a ℂ) (i j : a) :
    unitaryTwirlIntegrand (a := a) 1 (oneCopyMatrixLift (a := a) M) U
      ((decouplingTensorPowerOneEquiv a).symm i) ((decouplingTensorPowerOneEquiv a).symm j) =
    ((U : CMatrix a) * M * star (U : CMatrix a)) i j := by
  rw [unitaryTwirlIntegrand]
  simp_rw [Matrix.mul_apply]
  rw [sum_tensorPower_one]
  simp [unitaryTensorPowerMatrix, oneCopyMatrixLift, decouplingTensorPowerOneEquiv]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [sum_tensorPower_one]
  have hstar :
      star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix PUnit))
          (x, PUnit.unit) (j, PUnit.unit) = star ((U : CMatrix a) j x) := by
    simp [Matrix.star_apply, Matrix.kronecker]
  change (∑ x_1 : a,
        (U : CMatrix a) i x_1 * (1 : CMatrix PUnit) PUnit.unit PUnit.unit * M x_1 x) *
      star (Matrix.kronecker (U : CMatrix a) (1 : CMatrix PUnit)) (x, PUnit.unit)
        (j, PUnit.unit) =
    (∑ j_1 : a, (U : CMatrix a) i j_1 * M j_1 x) * star ((U : CMatrix a) j x)
  rw [hstar]
  simp

private def ambientUnitaryTwirlIntegrand [Fintype a] [DecidableEq a]
    (M : CMatrix a) (U : Matrix.unitaryGroup a ℂ) : CMatrix a :=
  (U : CMatrix a) * M * star (U : CMatrix a)

private theorem ambientUnitaryTwirl_integrand_continuous [Fintype a] [DecidableEq a]
    (M : CMatrix a) :
    Continuous (ambientUnitaryTwirlIntegrand (a := a) M) := by
  have hU : Continuous fun U : Matrix.unitaryGroup a ℂ => (U : CMatrix a) :=
    continuous_subtype_val
  unfold ambientUnitaryTwirlIntegrand
  simpa [mul_assoc] using
    ((hU.matrix_mul continuous_const).matrix_mul (Continuous.star hU))

private theorem ambientUnitaryTwirl_integrand_integrable [Fintype a] [DecidableEq a]
    [Nonempty a] (M : CMatrix a) :
    Integrable (ambientUnitaryTwirlIntegrand (a := a) M) (unitaryHaarMeasure (a := a)) :=
  (ambientUnitaryTwirl_integrand_continuous (a := a) M).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem ambientUnitaryTwirl_one_eq_trace_smul_one [Fintype a] [DecidableEq a]
    [Nonempty a] (M : CMatrix a) :
    (∫ U : Matrix.unitaryGroup a ℂ,
        ambientUnitaryTwirlIntegrand (a := a) M U ∂unitaryHaarMeasure (a := a)) =
      (M.trace / (Fintype.card a : ℂ)) • 1 := by
  ext i j
  let ML := oneCopyMatrixLift (a := a) M
  have htwirl := unitaryTwirl_one_eq_trace_smul_one (a := a) ML
  have hentry := congrFun (congrFun htwirl ((decouplingTensorPowerOneEquiv a).symm i))
    ((decouplingTensorPowerOneEquiv a).symm j)
  rw [unitaryTwirl] at hentry
  rw [decoupling_integral_apply_apply
    (hf := unitaryTwirl_integrand_integrable (a := a) 1 ML)
    ((decouplingTensorPowerOneEquiv a).symm i) ((decouplingTensorPowerOneEquiv a).symm j)]
    at hentry
  rw [decoupling_integral_apply_apply
    (hf := ambientUnitaryTwirl_integrand_integrable (a := a) M) i j]
  have hscalar :
      (∫ U : Matrix.unitaryGroup a ℂ,
          unitaryTwirlIntegrand (a := a) 1 ML U
            ((decouplingTensorPowerOneEquiv a).symm i)
            ((decouplingTensorPowerOneEquiv a).symm j) ∂unitaryHaarMeasure (a := a)) =
        ∫ U : Matrix.unitaryGroup a ℂ,
          ambientUnitaryTwirlIntegrand (a := a) M U i j ∂unitaryHaarMeasure (a := a) := by
    apply integral_congr_ae
    filter_upwards with U
    simp [ML, ambientUnitaryTwirlIntegrand,
      unitaryTwirlIntegrand_oneCopyMatrixLift_apply (a := a) M U i j]
  rw [hscalar] at hentry
  simpa [ML, oneCopyMatrixLift_trace, Matrix.smul_apply, Matrix.one_apply] using hentry

private def ambientSideBlock [Fintype a] [Fintype e]
    (M : CMatrix (Prod a e)) (r s : e) : CMatrix a :=
  fun i j => M (i, r) (j, s)

private theorem ambientSideBlock_trace [Fintype a] [Fintype e]
    (M : CMatrix (Prod a e)) (r s : e) :
    (ambientSideBlock (a := a) (e := e) M r s).trace =
      partialTraceA (a := a) (b := e) M r s := by
  rfl

private theorem ambientSideTwirlIntegrand_apply_block [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (M : CMatrix (Prod a e))
    (U : Matrix.unitaryGroup a ℂ) (i j : a) (r s : e) :
    ambientSideTwirlIntegrand (a := a) (e := e) M U (i, r) (j, s) =
      ambientUnitaryTwirlIntegrand (a := a)
        (ambientSideBlock (a := a) (e := e) M r s) U i j := by
  simp [ambientSideTwirlIntegrand, ambientUnitaryTwirlIntegrand, ambientSideBlock,
    Matrix.mul_apply, Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type]

private theorem ambientSideTwirl_integrand_continuous [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] (M : CMatrix (Prod a e)) :
    Continuous (ambientSideTwirlIntegrand (a := a) (e := e) M) := by
  have hU : Continuous fun U : Matrix.unitaryGroup a ℂ => (U : CMatrix a) :=
    continuous_subtype_val
  unfold ambientSideTwirlIntegrand
  simpa [mul_assoc] using
    ((decoupling_continuous_kronecker_one (ι := a) (κ := e) (hf := hU)).matrix_mul
      continuous_const).matrix_mul
      (decoupling_continuous_kronecker_one (ι := a) (κ := e) (hf := Continuous.star hU))

private theorem ambientSideTwirl_integrand_integrable [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a] (M : CMatrix (Prod a e)) :
    Integrable (ambientSideTwirlIntegrand (a := a) (e := e) M) (unitaryHaarMeasure (a := a)) :=
  (ambientSideTwirl_integrand_continuous (a := a) (e := e) M).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem haydenProjectedAE_continuous [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e)) :
    Continuous fun U : Matrix.unitaryGroup a ℂ =>
      haydenProjectedAE (a := a) (e := e) P d rho U := by
  let K : CMatrix (Prod a e) := Matrix.kronecker P (1 : CMatrix e)
  let c : ℂ := (((Fintype.card a : ℝ) / d : ℝ) : ℂ)
  have hambient := ambientSideTwirl_integrand_continuous (a := a) (e := e) rho
  have hcont : Continuous fun U : Matrix.unitaryGroup a ℂ =>
      c • (K * ambientSideTwirlIntegrand (a := a) (e := e) rho U * K) := by
    exact continuous_const.smul
      (((continuous_const.matrix_mul hambient).matrix_mul continuous_const))
  refine hcont.congr ?_
  intro U
  simpa [K, c] using
    (haydenProjectedAE_eq_projected_ambientSideTwirl
      (a := a) (e := e) P d rho U).symm

private theorem haydenProjectedAE_integrable [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e)) :
    Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      haydenProjectedAE (a := a) (e := e) P d rho U)
      (unitaryHaarMeasure (a := a)) :=
  (haydenProjectedAE_continuous (a := a) (e := e) P d rho).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem haydenProjectedAE_traceNorm_diff_integrable [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e)) :
    Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho))
      (unitaryHaarMeasure (a := a)) := by
  have hproj := haydenProjectedAE_continuous (a := a) (e := e) P d rho
  have hdiff : Continuous fun U : Matrix.unitaryGroup a ℂ =>
      haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho :=
    hproj.sub continuous_const
  exact (traceNorm_continuous.comp hdiff).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem haydenProjectedAE_secondMoment_trace_integrable [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e)) :
    Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace)
      (unitaryHaarMeasure (a := a)) := by
  have hproj := haydenProjectedAE_continuous (a := a) (e := e) P d rho
  have hcont : Continuous fun U : Matrix.unitaryGroup a ℂ =>
      (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace :=
    Continuous.matrix_trace (hproj.matrix_mul hproj)
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem ambientSideTwirl_integral_eq_kronecker_partialTrace [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a] (M : CMatrix (Prod a e)) :
    (∫ U : Matrix.unitaryGroup a ℂ,
        ambientSideTwirlIntegrand (a := a) (e := e) M U ∂unitaryHaarMeasure (a := a)) =
      (((1 : ℝ) / (Fintype.card a : ℝ) : ℝ) : ℂ) •
        Matrix.kronecker (1 : CMatrix a) (partialTraceA (a := a) (b := e) M) := by
  ext x y
  rw [decoupling_integral_apply_apply
    (hf := ambientSideTwirl_integrand_integrable (a := a) (e := e) M) x y]
  have hblock :=
    ambientUnitaryTwirl_one_eq_trace_smul_one (a := a)
      (ambientSideBlock (a := a) (e := e) M x.2 y.2)
  have hentry := congrFun (congrFun hblock x.1) y.1
  rw [decoupling_integral_apply_apply
    (hf := ambientUnitaryTwirl_integrand_integrable (a := a)
      (ambientSideBlock (a := a) (e := e) M x.2 y.2)) x.1 y.1] at hentry
  have hscalar :
      (∫ U : Matrix.unitaryGroup a ℂ,
        ambientUnitaryTwirlIntegrand (a := a)
          (ambientSideBlock (a := a) (e := e) M x.2 y.2) U x.1 y.1
          ∂unitaryHaarMeasure (a := a)) =
      ∫ U : Matrix.unitaryGroup a ℂ,
        ambientSideTwirlIntegrand (a := a) (e := e) M U x y
        ∂unitaryHaarMeasure (a := a) := by
    apply integral_congr_ae
    filter_upwards with U
    exact (ambientSideTwirlIntegrand_apply_block (a := a) (e := e) M U x.1 y.1 x.2 y.2).symm
  rw [hscalar] at hentry
  rw [hentry]
  simp [ambientSideBlock_trace, Matrix.smul_apply, Matrix.kronecker]
  ring

/-- First-moment side-block specialization: each block of the one-copy side
Haar average is the scalar trace block. -/
private theorem sideTwirl_integral_block_one_eq_trace_smul_one [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a]
    (X : CMatrix (Prod (TensorPower a 1) e)) (r s : e) :
    sideBlock (a := a) (e := e) 1
        (∫ U : Matrix.unitaryGroup a ℂ,
          sideTwirlIntegrand (a := a) (e := e) 1 X U ∂unitaryHaarMeasure (a := a))
        r s =
      ((sideBlock (a := a) (e := e) 1 X r s).trace / (Fintype.card a : ℂ)) • 1 := by
  rw [sideTwirl_integral_block]
  rw [unitaryTwirl_one_eq_trace_smul_one]

/-- First-moment side-twirl formula in whole-matrix form. -/
private theorem sideTwirl_integral_one_eq_kronecker_sideTrace [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a]
    (X : CMatrix (Prod (TensorPower a 1) e)) :
    (∫ U : Matrix.unitaryGroup a ℂ,
          sideTwirlIntegrand (a := a) (e := e) 1 X U ∂unitaryHaarMeasure (a := a)) =
      (((1 : ℝ) / (Fintype.card a : ℝ) : ℝ) : ℂ) •
        Matrix.kronecker (1 : CMatrix (TensorPower a 1))
          (sideTraceOne (a := a) (e := e) X) := by
  ext x y
  have hblock :=
    sideTwirl_integral_block_one_eq_trace_smul_one (a := a) (e := e) X x.2 y.2
  have happ := congrFun (congrFun hblock x.1) y.1
  have happ' :
      (∫ U : Matrix.unitaryGroup a ℂ,
          sideTwirlIntegrand (a := a) (e := e) 1 X U ∂unitaryHaarMeasure (a := a)) x y =
        ((Matrix.trace (sideBlock (a := a) (e := e) 1 X x.2 y.2) /
            (Fintype.card a : ℂ)) • (1 : CMatrix (TensorPower a 1))) x.1 y.1 := by
    simpa [sideBlock] using happ
  rw [happ']
  simp [sideTraceOne, Matrix.smul_apply, Matrix.kronecker]
  ring

/-- Algebraic assembly of the first-moment target after the Haar twirl has
produced `(1 / |A|) • (1_A ⊗ φ^E)`. -/
theorem haydenProjectedAE_meanTarget_sandwich_assembly [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (hP : P * P = P) (hd : d ≠ 0) :
    (((Fintype.card a : ℝ) / d : ℝ) : ℂ) •
        (Matrix.kronecker P (1 : CMatrix e) *
          ((((1 : ℝ) / (Fintype.card a : ℝ) : ℝ) : ℂ) •
            Matrix.kronecker (1 : CMatrix a) (partialTraceA (a := a) (b := e) rho)) *
          Matrix.kronecker P (1 : CMatrix e)) =
      haydenProjectedAE_meanTarget (a := a) (e := e) P d rho := by
  unfold haydenProjectedAE_meanTarget
  rw [Matrix.mul_smul]
  rw [Matrix.smul_mul]
  let R := partialTraceA (a := a) (b := e) rho
  have hmul₁ : Matrix.kronecker P (1 : CMatrix e) * Matrix.kronecker (1 : CMatrix a) R =
      Matrix.kronecker (P * 1) ((1 : CMatrix e) * R) := by
    exact (Matrix.mul_kronecker_mul P (1 : CMatrix a) (1 : CMatrix e) R).symm
  rw [hmul₁]
  have hmul₂ : Matrix.kronecker (P * 1) ((1 : CMatrix e) * R) *
      Matrix.kronecker P (1 : CMatrix e) =
        Matrix.kronecker ((P * 1) * P) (((1 : CMatrix e) * R) * 1) := by
    exact (Matrix.mul_kronecker_mul (P * 1) P ((1 : CMatrix e) * R)
      (1 : CMatrix e)).symm
  rw [hmul₂]
  rw [Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, hP]
  subst R
  rw [smul_smul]
  have hscalar :
      (((Fintype.card a : ℝ) / d : ℝ) : ℂ) *
          (((1 : ℝ) / (Fintype.card a : ℝ) : ℝ) : ℂ) =
        (((1 : ℝ) / d : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_div]
    field_simp [hd, Fintype.card_ne_zero]
  rw [hscalar]

theorem haydenProjectedAE_firstMoment_eq_meanTarget [Fintype a] [Fintype e]
    [DecidableEq a] [DecidableEq e] [Nonempty a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (hP : P * P = P) (hd : d ≠ 0) :
    (∫ U : Matrix.unitaryGroup a ℂ,
        haydenProjectedAE (a := a) (e := e) P d rho U ∂unitaryHaarMeasure (a := a)) =
      haydenProjectedAE_meanTarget (a := a) (e := e) P d rho := by
  let K : CMatrix (Prod a e) := Matrix.kronecker P (1 : CMatrix e)
  let c : ℂ := (((Fintype.card a : ℝ) / d : ℝ) : ℂ)
  have hf :=
    ambientSideTwirl_integrand_integrable (a := a) (e := e) rho
  calc
    (∫ U : Matrix.unitaryGroup a ℂ,
        haydenProjectedAE (a := a) (e := e) P d rho U ∂unitaryHaarMeasure (a := a)) =
      ∫ U : Matrix.unitaryGroup a ℂ,
        c • (K * ambientSideTwirlIntegrand (a := a) (e := e) rho U * K)
        ∂unitaryHaarMeasure (a := a) := by
        apply integral_congr_ae
        filter_upwards with U
        simp [K, c, haydenProjectedAE_eq_projected_ambientSideTwirl
          (a := a) (e := e) P d rho U]
    _ = c •
        (∫ U : Matrix.unitaryGroup a ℂ,
          K * ambientSideTwirlIntegrand (a := a) (e := e) rho U * K
          ∂unitaryHaarMeasure (a := a)) := by
        rw [integral_smul]
    _ = c •
        (K *
          (∫ U : Matrix.unitaryGroup a ℂ,
            ambientSideTwirlIntegrand (a := a) (e := e) rho U
            ∂unitaryHaarMeasure (a := a)) * K) := by
        have hright :
            (∫ U : Matrix.unitaryGroup a ℂ,
              K * ambientSideTwirlIntegrand (a := a) (e := e) rho U * K
              ∂unitaryHaarMeasure (a := a)) =
              (∫ U : Matrix.unitaryGroup a ℂ,
                K * ambientSideTwirlIntegrand (a := a) (e := e) rho U
                ∂unitaryHaarMeasure (a := a)) * K := by
          simpa [Matrix.mul_assoc] using
            decoupling_integral_matrix_mul_right (a := a) (hf := hf.const_mul K) K
        have hleft :
            (∫ U : Matrix.unitaryGroup a ℂ,
                K * ambientSideTwirlIntegrand (a := a) (e := e) rho U
                ∂unitaryHaarMeasure (a := a)) =
              K * (∫ U : Matrix.unitaryGroup a ℂ,
                ambientSideTwirlIntegrand (a := a) (e := e) rho U
                ∂unitaryHaarMeasure (a := a)) := by
          exact decoupling_integral_matrix_mul_left (a := a) K (hf := hf)
        rw [hright, hleft]
    _ = c •
        (K *
          ((((1 : ℝ) / (Fintype.card a : ℝ) : ℝ) : ℂ) •
            Matrix.kronecker (1 : CMatrix a) (partialTraceA (a := a) (b := e) rho)) * K) := by
        rw [ambientSideTwirl_integral_eq_kronecker_partialTrace (a := a) (e := e) rho]
    _ = haydenProjectedAE_meanTarget (a := a) (e := e) P d rho := by
        simpa [K, c] using
          haydenProjectedAE_meanTarget_sandwich_assembly
            (a := a) (e := e) P d rho hP hd

/-! ## Two-copy coefficient bounds from Hayden's source proof -/

def haydenDPlus (x : ℝ) : ℝ := (x ^ 2 + x) / 2

def haydenDMinus (x : ℝ) : ℝ := (x ^ 2 - x) / 2

theorem hayden_secondMoment_coeff_swap_simplify {D d : ℝ}
    (hD : D ≠ 0) (hd : d ≠ 0) (hDp : D + 1 ≠ 0) (hDm : D - 1 ≠ 0) :
    (1 / 2) * (D ^ 2 / d ^ 2) *
        (haydenDPlus d / haydenDPlus D + haydenDMinus d / haydenDMinus D) =
      D * (d * D - 1) / (d * (D ^ 2 - 1)) := by
  have hDsq : D ^ 2 - 1 ≠ 0 := by
    intro h
    have hprod : (D - 1) * (D + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hleft | hright
    · exact hDm hleft
    · exact hDp hright
  unfold haydenDPlus haydenDMinus
  field_simp [hD, hd, hDp, hDm, hDsq, sub_eq_add_neg]
  ring_nf

theorem hayden_secondMoment_coeff_identity_simplify {D d : ℝ}
    (hD : D ≠ 0) (hd : d ≠ 0) (hDp : D + 1 ≠ 0) (hDm : D - 1 ≠ 0) :
    (1 / 2) * (D ^ 2 / d ^ 2) *
        (haydenDPlus d / haydenDPlus D - haydenDMinus d / haydenDMinus D) =
      D * (D - d) / (d * (D ^ 2 - 1)) := by
  have hDsq : D ^ 2 - 1 ≠ 0 := by
    intro h
    have hprod : (D - 1) * (D + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hleft | hright
    · exact hDm hleft
    · exact hDp hright
  unfold haydenDPlus haydenDMinus
  field_simp [hD, hd, hDp, hDm, hDsq, sub_eq_add_neg]
  ring_nf

theorem hayden_secondMoment_coeff_swap_le_one {D d : ℝ}
    (hd : 1 ≤ d) (hdD : d ≤ D) (hD : 1 < D) :
    (1 / 2) * (D ^ 2 / d ^ 2) *
        (haydenDPlus d / haydenDPlus D + haydenDMinus d / haydenDMinus D) ≤ 1 := by
  have hDne : D ≠ 0 := by positivity
  have hdne : d ≠ 0 := by positivity
  have hDpne : D + 1 ≠ 0 := by positivity
  have hDmne : D - 1 ≠ 0 := by linarith
  rw [hayden_secondMoment_coeff_swap_simplify (D := D) (d := d) hDne hdne hDpne hDmne]
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hDpos : 0 < D := lt_trans zero_lt_one hD
  have hdenpos : 0 < d * (D ^ 2 - 1) := by
    nlinarith [sq_pos_of_ne_zero hDne, mul_pos hdpos (by nlinarith)]
  rw [div_le_one hdenpos]
  nlinarith [hd, hdD, hD]

theorem hayden_secondMoment_coeff_identity_le_inv {D d : ℝ}
    (hd : 1 ≤ d) (hdD : d ≤ D) (hD : 1 < D) :
    (1 / 2) * (D ^ 2 / d ^ 2) *
        (haydenDPlus d / haydenDPlus D - haydenDMinus d / haydenDMinus D) ≤ 1 / d := by
  have hDne : D ≠ 0 := by positivity
  have hdne : d ≠ 0 := by positivity
  have hDpne : D + 1 ≠ 0 := by positivity
  have hDmne : D - 1 ≠ 0 := by linarith
  rw [hayden_secondMoment_coeff_identity_simplify (D := D) (d := d) hDne hdne hDpne hDmne]
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hDpos : 0 < D := lt_trans zero_lt_one hD
  have hdenpos : 0 < d * (D ^ 2 - 1) := by
    nlinarith [sq_pos_of_ne_zero hDne, mul_pos hdpos (by nlinarith)]
  rw [div_le_iff₀ hdenpos]
  field_simp [hdne]
  nlinarith [hdD, hD]

/-- Hayden's scaled second-moment expression, after applying the source
`(|A|/d)^2` normalization, in real coefficient form. -/
def haydenScaledSecondMomentExpression (D d purityAE purityE : ℝ) : ℝ :=
  ((1 / 2) * (D ^ 2 / d ^ 2) *
      (haydenDPlus d / haydenDPlus D + haydenDMinus d / haydenDMinus D)) * purityAE +
    ((1 / 2) * (D ^ 2 / d ^ 2) *
      (haydenDPlus d / haydenDPlus D - haydenDMinus d / haydenDMinus D)) * purityE

private theorem hayden_secondMoment_complex_coeff_algebra
    (D d : ℝ) (A B : ℂ)
    (hD : D ≠ 0) (hd : d ≠ 0) (hDp : D + 1 ≠ 0) (hDm : D - 1 ≠ 0) :
    (((D / d) ^ 2 : ℝ) : ℂ) *
      (((1 : ℂ) / 2) *
          ((((d : ℂ) * (d : ℂ) + (d : ℂ)) / 2 /
              (((D : ℂ) * ((D : ℂ) + 1)) / 2)) +
            (((d : ℂ) * ((d : ℂ) - 1) / 2) /
              (((D : ℂ) * ((D : ℂ) - 1)) / 2))) * A +
        ((1 : ℂ) / 2) *
          ((((d : ℂ) * (d : ℂ) + (d : ℂ)) / 2 /
              (((D : ℂ) * ((D : ℂ) + 1)) / 2)) -
            (((d : ℂ) * ((d : ℂ) - 1) / 2) /
              (((D : ℂ) * ((D : ℂ) - 1)) / 2))) * B) =
      (((((1 / 2) * (D ^ 2 / d ^ 2) *
        (haydenDPlus d / haydenDPlus D + haydenDMinus d / haydenDMinus D)) : ℝ) : ℂ) * A +
       ((((1 / 2) * (D ^ 2 / d ^ 2) *
        (haydenDPlus d / haydenDPlus D - haydenDMinus d / haydenDMinus D)) : ℝ) : ℂ) * B) := by
  unfold haydenDPlus haydenDMinus
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_sub]
  have hDsq : D ^ 2 - 1 ≠ 0 := by
    intro h
    have hprod : (D - 1) * (D + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hleft | hright
    · exact hDm hleft
    · exact hDp hright
  field_simp [hD, hd, hDp, hDm, hDsq]
  norm_num
  ring_nf

private theorem hayden_secondMoment_complex_coeff_algebra_re
    (D d : ℝ) (A B : ℂ)
    (hD : D ≠ 0) (hd : d ≠ 0) (hDp : D + 1 ≠ 0) (hDm : D - 1 ≠ 0) :
    ((((D / d) ^ 2 : ℝ) : ℂ) *
      (((1 : ℂ) / 2) *
          ((((d : ℂ) * (d : ℂ) + (d : ℂ)) / 2 /
              (((D : ℂ) * ((D : ℂ) + 1)) / 2)) +
            (((d : ℂ) * ((d : ℂ) - 1) / 2) /
              (((D : ℂ) * ((D : ℂ) - 1)) / 2))) * A +
        ((1 : ℂ) / 2) *
          ((((d : ℂ) * (d : ℂ) + (d : ℂ)) / 2 /
              (((D : ℂ) * ((D : ℂ) + 1)) / 2)) -
            (((d : ℂ) * ((d : ℂ) - 1) / 2) /
              (((D : ℂ) * ((D : ℂ) - 1)) / 2))) * B)).re =
      haydenScaledSecondMomentExpression D d A.re B.re := by
  rw [hayden_secondMoment_complex_coeff_algebra D d A B hD hd hDp hDm]
  unfold haydenScaledSecondMomentExpression
  simp [Complex.mul_re, Complex.add_re, Complex.ofReal_div,
    Complex.ofReal_inv, Complex.ofReal_pow]
  have hpow : (↑D ^ 2 / ↑d ^ 2 : ℂ) = ((D ^ 2 / d ^ 2 : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_pow, Complex.ofReal_div]
  have hcoef_re : (↑D ^ 2 / ↑d ^ 2 : ℂ).re = D ^ 2 / d ^ 2 := by
    calc
      (↑D ^ 2 / ↑d ^ 2 : ℂ).re = (((D ^ 2 / d ^ 2 : ℝ) : ℂ)).re := by
        conv_lhs => rw [hpow]
      _ = D ^ 2 / d ^ 2 := by exact Complex.ofReal_re _
  have hcoef_im : (↑D ^ 2 / ↑d ^ 2 : ℂ).im = 0 := by
    calc
      (↑D ^ 2 / ↑d ^ 2 : ℂ).im = (((D ^ 2 / d ^ 2 : ℝ) : ℂ)).im := by
        conv_lhs => rw [hpow]
      _ = 0 := by exact Complex.ofReal_im _
  rw [hcoef_re, hcoef_im]
  ring_nf

private theorem haydenProjectedAE_secondMoment_real_integral_eq_scaled_expression
    [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e] [Nontrivial a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (hP : P * P = P) (hPtr : P.trace = (d : ℂ)) (hd : d ≠ 0)
    (hsecond_int : Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace)
      (unitaryHaarMeasure (a := a))) :
    (∫ U : Matrix.unitaryGroup a ℂ,
      (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace.re
      ∂unitaryHaarMeasure (a := a)) =
      haydenScaledSecondMomentExpression (Fintype.card a : ℝ) d
        (rho * rho).trace.re
        (partialTraceA (a := a) (b := e) rho *
          partialTraceA (a := a) (b := e) rho).trace.re := by
  let f : Matrix.unitaryGroup a ℂ → ℂ := fun U =>
      (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace
  have hre :
      (∫ U : Matrix.unitaryGroup a ℂ, (f U).re ∂unitaryHaarMeasure (a := a)) =
        (∫ U : Matrix.unitaryGroup a ℂ, f U ∂unitaryHaarMeasure (a := a)).re := by
    simpa [f] using (Complex.reCLM.integral_comp_comm hsecond_int)
  rw [hre]
  have hsecond := haydenProjectedAE_secondMoment_trace_integral_decomposition
    (a := a) (e := e) P hP rho d
  rw [hsecond]
  rw [symmetricProjectionMatrix_two_trace]
  rw [antisymmetricProjectionMatrix_two_trace]
  rw [hPtr]
  have hD : (Fintype.card a : ℝ) ≠ 0 := by positivity
  have hDp : (Fintype.card a : ℝ) + 1 ≠ 0 := by positivity
  have hDm : (Fintype.card a : ℝ) - 1 ≠ 0 := by
    have hcard : (1 : ℝ) < (Fintype.card a : ℝ) := by
      exact_mod_cast (Fintype.one_lt_card (α := a))
    linarith
  simpa using
    hayden_secondMoment_complex_coeff_algebra_re
      (D := (Fintype.card a : ℝ)) (d := d)
      (A := (rho * rho).trace)
      (B := (partialTraceA (a := a) (b := e) rho *
        partialTraceA (a := a) (b := e) rho).trace)
      hD hd hDp hDm

theorem hayden_variance_coeff_bound {D d purityAE purityE : ℝ}
    (hd : 1 ≤ d) (hdD : d ≤ D) (hD : 1 < D)
    (hAE : 0 ≤ purityAE) (hE : 0 ≤ purityE) :
    haydenScaledSecondMomentExpression D d purityAE purityE -
      (1 / d) * purityE ≤ purityAE := by
  unfold haydenScaledSecondMomentExpression
  have hswap :=
    hayden_secondMoment_coeff_swap_le_one (D := D) (d := d) hd hdD hD
  have hid :=
    hayden_secondMoment_coeff_identity_le_inv (D := D) (d := d) hd hdD hD
  have hswap_mul :
      ((1 / 2) * (D ^ 2 / d ^ 2) *
        (haydenDPlus d / haydenDPlus D + haydenDMinus d / haydenDMinus D)) *
          purityAE ≤ purityAE := by
    nlinarith [mul_le_mul_of_nonneg_right hswap hAE]
  have hid_mul :
      ((1 / 2) * (D ^ 2 / d ^ 2) *
        (haydenDPlus d / haydenDPlus D - haydenDMinus d / haydenDMinus D)) *
          purityE ≤ (1 / d) * purityE := by
    nlinarith [mul_le_mul_of_nonneg_right hid hE]
  nlinarith

/-- Step 4 variance assembly: the source second-moment expansion and the
mean-square term imply Hayden's Hilbert--Schmidt variance bound. -/
theorem haydenProjectedAE_variance_le_purity {D d secondMoment meanSq purityAE purityE : ℝ}
    (hd : 1 ≤ d) (hdD : d ≤ D) (hD : 1 < D)
    (hSecond :
      secondMoment ≤ haydenScaledSecondMomentExpression D d purityAE purityE)
    (hMean : meanSq = (1 / d) * purityE)
    (hAE : 0 ≤ purityAE) (hE : 0 ≤ purityE) :
    secondMoment - meanSq ≤ purityAE := by
  rw [hMean]
  exact le_trans (sub_le_sub_right hSecond ((1 / d) * purityE))
    (hayden_variance_coeff_bound (D := D) (d := d)
      (purityAE := purityAE) (purityE := purityE) hd hdD hD hAE hE)

theorem haydenProjectedAE_hilbertSchmidt_variance_le_purity
    [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e] [Nontrivial a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (hPid : P * P = P) (hPherm : P.IsHermitian)
    (hPtr : P.trace = (d : ℂ)) (hrho : rho.IsHermitian)
    (hd : 1 ≤ d) (hdD : d ≤ Fintype.card a) :
    (∫ U : Matrix.unitaryGroup a ℂ,
      hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
      ∂unitaryHaarMeasure (a := a)) ≤ hilbertSchmidtSq rho := by
  have hdne : d ≠ 0 := by positivity
  have hproj_int := haydenProjectedAE_integrable (a := a) (e := e) P d rho
  have hsecond_int :=
    haydenProjectedAE_secondMoment_trace_integrable (a := a) (e := e) P d rho
  have hD : 1 < (Fintype.card a : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card (α := a))
  have hsecond_real_int : Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace.re)
      (unitaryHaarMeasure (a := a)) :=
    Complex.reCLM.integrable_comp hsecond_int
  have hmean :=
    haydenProjectedAE_firstMoment_eq_meanTarget
      (a := a) (e := e) P d rho hPid hdne
  have hMherm :
      (haydenProjectedAE_meanTarget (a := a) (e := e) P d rho).IsHermitian :=
    haydenProjectedAE_meanTarget_isHermitian
      (a := a) (e := e) P d rho hPherm hrho
  have hvar_id :=
    haydenProjectedAE_variance_identity
      (μ := unitaryHaarMeasure (a := a))
      (f := fun U : Matrix.unitaryGroup a ℂ =>
        haydenProjectedAE (a := a) (e := e) P d rho U)
      (M := haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
      hproj_int hsecond_real_int hMherm
      (fun U => haydenProjectedAE_isHermitian
        (a := a) (e := e) P d rho U hPherm hrho)
      hmean
  rw [hvar_id]
  have hsecond_eq :=
    haydenProjectedAE_secondMoment_real_integral_eq_scaled_expression
      (a := a) (e := e) P d rho hPid hPtr hdne hsecond_int
  have hAEtrace :
      (rho * rho).trace.re = hilbertSchmidtSq rho := by
    exact (hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian hrho).symm
  have hEherm :
      (partialTraceA (a := a) (b := e) rho).IsHermitian :=
    partialTraceA_isHermitian hrho
  have hEtrace :
      (partialTraceA (a := a) (b := e) rho *
        partialTraceA (a := a) (b := e) rho).trace.re =
        hilbertSchmidtSq (partialTraceA (a := a) (b := e) rho) := by
    exact (hilbertSchmidtSq_eq_trace_mul_self_of_isHermitian hEherm).symm
  have hSecond :
      (∫ U : Matrix.unitaryGroup a ℂ,
        (haydenProjectedAE (a := a) (e := e) P d rho U *
          haydenProjectedAE (a := a) (e := e) P d rho U).trace.re
        ∂unitaryHaarMeasure (a := a)) ≤
        haydenScaledSecondMomentExpression (Fintype.card a : ℝ) d
          (hilbertSchmidtSq rho)
          (hilbertSchmidtSq (partialTraceA (a := a) (b := e) rho)) := by
    rw [hsecond_eq, hAEtrace, hEtrace]
  have hMean :
      hilbertSchmidtSq (haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) =
        (1 / d) * hilbertSchmidtSq (partialTraceA (a := a) (b := e) rho) :=
    haydenProjectedAE_meanTarget_hilbertSchmidtSq
      (a := a) (e := e) P d rho hPherm hPid hPtr hdne
  exact haydenProjectedAE_variance_le_purity
    (D := (Fintype.card a : ℝ)) (d := d)
    (secondMoment := ∫ U : Matrix.unitaryGroup a ℂ,
        (haydenProjectedAE (a := a) (e := e) P d rho U *
          haydenProjectedAE (a := a) (e := e) P d rho U).trace.re
        ∂unitaryHaarMeasure (a := a))
    (meanSq := hilbertSchmidtSq
      (haydenProjectedAE_meanTarget (a := a) (e := e) P d rho))
    (purityAE := hilbertSchmidtSq rho)
    (purityE := hilbertSchmidtSq (partialTraceA (a := a) (b := e) rho))
    hd (by exact_mod_cast hdD) hD hSecond hMean
    (hilbertSchmidtSq_nonneg rho)
    (hilbertSchmidtSq_nonneg (partialTraceA (a := a) (b := e) rho))

theorem haydenProjectedAE_oneShotDecoupling_traceNorm_sq_expectation_le
    [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e] [Nontrivial a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (hPid : P * P = P) (hPherm : P.IsHermitian)
    (hPtr : P.trace = (d : ℂ)) (hrho : rho.IsHermitian)
    (hd : 1 ≤ d) (hdD : d ≤ Fintype.card a) :
    (∫ U : Matrix.unitaryGroup a ℂ,
      traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) ^ 2
      ∂unitaryHaarMeasure (a := a)) ≤
      d * (Fintype.card e : ℝ) * hilbertSchmidtSq rho := by
  have hvar :=
    haydenProjectedAE_hilbertSchmidt_variance_le_purity
      (a := a) (e := e) P d rho hPid hPherm hPtr hrho hd hdD
  have htrace_sq : Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) ^ 2)
      (unitaryHaarMeasure (a := a)) := by
    have hproj := haydenProjectedAE_continuous (a := a) (e := e) P d rho
    have htarget : Continuous fun _ : Matrix.unitaryGroup a ℂ =>
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho :=
      continuous_const
    have htrace : Continuous fun U : Matrix.unitaryGroup a ℂ =>
        traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
          haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) :=
      traceNorm_continuous.comp (hproj.sub htarget)
    exact (htrace.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hproj_int := haydenProjectedAE_integrable (a := a) (e := e) P d rho
  have hsecond_int :=
    haydenProjectedAE_secondMoment_trace_integrable (a := a) (e := e) P d rho
  have hsecond_real_int : Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace.re)
      (unitaryHaarMeasure (a := a)) :=
    Complex.reCLM.integrable_comp hsecond_int
  have hMherm :
      (haydenProjectedAE_meanTarget (a := a) (e := e) P d rho).IsHermitian :=
    haydenProjectedAE_meanTarget_isHermitian
      (a := a) (e := e) P d rho hPherm hrho
  have hhs : Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho))
      (unitaryHaarMeasure (a := a)) :=
    haydenProjectedAE_hilbertSchmidt_variance_integrable
      (μ := unitaryHaarMeasure (a := a))
      (f := fun U : Matrix.unitaryGroup a ℂ =>
        haydenProjectedAE (a := a) (e := e) P d rho U)
      (M := haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
      hproj_int hsecond_real_int hMherm
      (fun U => haydenProjectedAE_isHermitian
        (a := a) (e := e) P d rho U hPherm hrho)
  have hpoint : ∀ᵐ U : Matrix.unitaryGroup a ℂ ∂unitaryHaarMeasure (a := a),
      traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) ^ 2 ≤
        (d * (Fintype.card e : ℝ)) *
          hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
            haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) := by
    filter_upwards with U
    exact traceNorm_sq_le_rankBound_mul_hilbertSchmidtSq
      (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
      (haydenProjectedAE_diff_finrank_range_le_projected_dim
        (a := a) (e := e) P d rho U hPid hPtr)
  have hmono :
      (∫ U : Matrix.unitaryGroup a ℂ,
        traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
          haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) ^ 2
        ∂unitaryHaarMeasure (a := a)) ≤
      ∫ U : Matrix.unitaryGroup a ℂ,
        (d * (Fintype.card e : ℝ)) *
          hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
            haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
        ∂unitaryHaarMeasure (a := a) := by
    exact integral_mono_ae htrace_sq
      (hhs.const_mul (d * (Fintype.card e : ℝ))) hpoint
  calc
    (∫ U : Matrix.unitaryGroup a ℂ,
      traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho) ^ 2
      ∂unitaryHaarMeasure (a := a)) ≤
        ∫ U : Matrix.unitaryGroup a ℂ,
          (d * (Fintype.card e : ℝ)) *
            hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
              haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
          ∂unitaryHaarMeasure (a := a) := hmono
    _ = (d * (Fintype.card e : ℝ)) *
        ∫ U : Matrix.unitaryGroup a ℂ,
          hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
            haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
          ∂unitaryHaarMeasure (a := a) := by
          rw [integral_const_mul]
    _ ≤ d * (Fintype.card e : ℝ) * hilbertSchmidtSq rho := by
          exact mul_le_mul_of_nonneg_left hvar
            (mul_nonneg (le_trans zero_le_one hd) (Nat.cast_nonneg _))

theorem haydenProjectedAE_oneShotDecoupling_traceNorm_expectation_le
    [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e] [Nontrivial a]
    (P : CMatrix a) (d : ℝ) (rho : CMatrix (Prod a e))
    (hPid : P * P = P) (hPherm : P.IsHermitian)
    (hPtr : P.trace = (d : ℂ)) (hrho : rho.IsHermitian)
    (hd : 1 ≤ d) (hdD : d ≤ Fintype.card a) :
    (∫ U : Matrix.unitaryGroup a ℂ,
      traceNorm (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
      ∂unitaryHaarMeasure (a := a)) ≤
      Real.sqrt (d * (Fintype.card e : ℝ) * hilbertSchmidtSq rho) := by
  have hvar :=
    haydenProjectedAE_hilbertSchmidt_variance_le_purity
      (a := a) (e := e) P d rho hPid hPherm hPtr hrho hd hdD
  have htrace :=
    haydenProjectedAE_traceNorm_diff_integrable (a := a) (e := e) P d rho
  have hproj_int := haydenProjectedAE_integrable (a := a) (e := e) P d rho
  have hsecond_int :=
    haydenProjectedAE_secondMoment_trace_integrable (a := a) (e := e) P d rho
  have hsecond_real_int : Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      (haydenProjectedAE (a := a) (e := e) P d rho U *
        haydenProjectedAE (a := a) (e := e) P d rho U).trace.re)
      (unitaryHaarMeasure (a := a)) :=
    Complex.reCLM.integrable_comp hsecond_int
  have hMherm :
      (haydenProjectedAE_meanTarget (a := a) (e := e) P d rho).IsHermitian :=
    haydenProjectedAE_meanTarget_isHermitian
      (a := a) (e := e) P d rho hPherm hrho
  have hhs : Integrable (fun U : Matrix.unitaryGroup a ℂ =>
      hilbertSchmidtSq (haydenProjectedAE (a := a) (e := e) P d rho U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rho))
      (unitaryHaarMeasure (a := a)) :=
    haydenProjectedAE_hilbertSchmidt_variance_integrable
      (μ := unitaryHaarMeasure (a := a))
      (f := fun U : Matrix.unitaryGroup a ℂ =>
        haydenProjectedAE (a := a) (e := e) P d rho U)
      (M := haydenProjectedAE_meanTarget (a := a) (e := e) P d rho)
      hproj_int hsecond_real_int hMherm
      (fun U => haydenProjectedAE_isHermitian
        (a := a) (e := e) P d rho U hPherm hrho)
  exact haydenProjectedAE_oneShotDecoupling_traceNorm_expectation_le_of_variance
    (a := a) (e := e) P d rho hPid hPtr hd htrace hhs hvar

/-- The post-Stinespring matrix representation of the one-shot decoupling theorem for
[HaydenHorodeckiWinterYard2007Decoupling, simple.tex:308-321].

This theorem starts after the source pure state and Stinespring isometry have
already produced the `A × E` density matrix.  Use
`hayden_oneShotDecoupling_traceNorm_expectation_le_of_stinespring` for the
source setup bridge. -/
theorem hayden_oneShotDecoupling_traceNorm_expectation_le
    [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e] [Nontrivial a]
    (P : CMatrix a) (d : ℝ) (rhoAE : CMatrix (Prod a e))
    (hP_idem : P * P = P) (hP_herm : P.IsHermitian)
    (hP_trace : P.trace = (d : ℂ)) (hrhoAE : rhoAE.IsHermitian)
    (hd_pos : 1 ≤ d) (hd_le_dimA : d ≤ Fintype.card a) :
    (∫ U : Matrix.unitaryGroup a ℂ,
      traceNorm (haydenProjectedAE (a := a) (e := e) P d rhoAE U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d rhoAE)
      ∂unitaryHaarMeasure (a := a)) ≤
      Real.sqrt (d * (Fintype.card e : ℝ) * hilbertSchmidtSq rhoAE) :=
  haydenProjectedAE_oneShotDecoupling_traceNorm_expectation_le
    (a := a) (e := e) P d rhoAE
    hP_idem hP_herm hP_trace hrhoAE hd_pos hd_le_dimA

/-- Source-facing one-shot decoupling theorem for
[HaydenHorodeckiWinterYard2007Decoupling, simple.tex:308-321].

Starting from the source pure state `phi^{AA'}` and a Stinespring isometry
`W : A' -> B × E`, this wrapper forms the source `phi^{AE}`, identifies the
projected `RE` matrix with the post-Stinespring matrix representation, and
reuses the existing matrix decoupling bound. -/
theorem hayden_oneShotDecoupling_traceNorm_expectation_le_of_stinespring
    {ap : Type x} {b : Type w}
    [Fintype a] [Fintype ap] [Fintype b] [Fintype e]
    [DecidableEq a] [DecidableEq ap] [DecidableEq b] [DecidableEq e]
    [Nontrivial a]
    (phi : PureVector (Prod a ap)) (W : ReferenceIsometry ap (Prod b e))
    (P : CMatrix a) (d : ℝ)
    (hP_idem : P * P = P) (hP_herm : P.IsHermitian)
    (hP_trace : P.trace = (d : ℂ))
    (hd_pos : 1 ≤ d) (hd_le_dimA : d ≤ Fintype.card a) :
    (∫ U : Matrix.unitaryGroup a ℂ,
      traceNorm (haydenSourceProjectedRE (a := a) (e := e) P d phi W U -
        haydenProjectedAE_meanTarget (a := a) (e := e) P d
          (haydenPostStinespringAEState (a := a) (e := e) phi W).matrix)
      ∂unitaryHaarMeasure (a := a)) ≤
      Real.sqrt (d * (Fintype.card e : ℝ) *
        hilbertSchmidtSq
          (haydenPostStinespringAEState (a := a) (e := e) phi W).matrix) := by
  simpa [haydenSourceProjectedRE] using
    hayden_oneShotDecoupling_traceNorm_expectation_le
      (a := a) (e := e) P d
      (haydenPostStinespringAEState (a := a) (e := e) phi W).matrix
      hP_idem hP_herm hP_trace
      (haydenPostStinespringAEState (a := a) (e := e) phi W).pos.isHermitian
      hd_pos hd_le_dimA

end

end QIT
