/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import QIT.Util.SDP.HermitianPSDTraceDuality
public import QIT.Util.SDP.PSDCone
public import QIT.Util.SDP.StrongDuality
public import QIT.States.Purification.ReferenceIsometry
public import QIT.OneShot.Smooth
public import QIT.States.Geometry.FuchsVdG
public import QIT.Information.Entropy.Entropy
public import QIT.Information.Renyi.Renyi
public import QIT.Information.Renyi.ConditionalRenyiTraceBridge
public import QIT.States.TraceNorm.BlockMatrix
import QIT.States.TraceNorm.Spectral
import QIT.States.TraceNorm.Variational
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Endpoint min/max entropy scales

This module separates the raw endpoint optimization values underneath the
definition-level conditional min/max entropies in `QIT.OneShot.Smooth`.

The declarations here are intentionally exponent/scale level.  The final
smooth min/max duality proof will need to connect these raw optimization values
to endpoint SDP duality before translating back through `log₂`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal Pointwise
open scoped Topology

open Matrix
open Set Filter

namespace QIT

universe u v w x

noncomputable section

theorem State.squaredFidelity_comm {a : Type u} [Fintype a] [DecidableEq a]
    (ρ σ : State a) :
    ρ.squaredFidelity σ = σ.squaredFidelity ρ := by
  rw [State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq,
    State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  congr 1
  have hconj :
      Matrix.conjTranspose (ρ.sqrtMatrix * σ.sqrtMatrix) =
        σ.sqrtMatrix * ρ.sqrtMatrix := by
    rw [Matrix.conjTranspose_mul, ρ.sqrtMatrix_isHermitian.eq,
      σ.sqrtMatrix_isHermitian.eq]
  rw [← hconj, traceNorm_conjTranspose]

theorem PureVector.overlapSq_comm_endpoint {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ Φ : PureVector a) :
    Ψ.overlapSq Φ = Φ.overlapSq Ψ := by
  rw [PureVector.overlapSq_eq_normSq, PureVector.overlapSq_eq_normSq]
  have hconj : Ψ.overlap Φ = star (Φ.overlap Ψ) := by
    simp [PureVector.overlap, mul_comm]
  rw [hconj]
  simp [Complex.normSq]

theorem PureVector.normSq_sum_star_mul_le_rankOne_trace
    {a : Type u} [Fintype a] [DecidableEq a]
    (v : a → ℂ) (η : PureVector a) :
    Complex.normSq (∑ i, star (v i) * η.amp i) ≤
      (rankOneMatrix v).trace.re := by
  classical
  let x : EuclideanSpace ℂ a := WithLp.toLp 2 v
  let y : EuclideanSpace ℂ a := WithLp.toLp 2 η.amp
  have hcs := norm_inner_le_norm (𝕜 := ℂ) x y
  have hinner :
      inner ℂ x y = ∑ i, star (v i) * η.amp i := by
    dsimp [x, y]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, mul_comm]
  have hxnorm : ‖x‖ ^ 2 = (rankOneMatrix v).trace.re := by
    rw [@norm_sq_eq_re_inner ℂ (EuclideanSpace ℂ a) _ _ _ x]
    dsimp [x]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [rankOneMatrix_trace, dotProduct]
  have hynorm : ‖y‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ (EuclideanSpace ℂ a) _ _ _ y]
    dsimp [y]
    rw [EuclideanSpace.inner_toLp_toLp]
    simpa [rankOneMatrix_trace, dotProduct, mul_comm] using
      congrArg Complex.re η.trace_rankOne_eq_one
  have hsq : Complex.normSq (inner ℂ x y) ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖inner ℂ x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by ring
  rw [hinner] at hsq
  rwa [hxnorm, hynorm, mul_one] at hsq

/-- A scalar phase can rotate any complex number so that its real part is its
absolute value. -/
theorem exists_complex_phase_mul_re_eq_abs (z : ℂ) :
    ∃ c : ℂ, c * star c = 1 ∧ (c * z).re = Complex.abs z := by
  by_cases hz : z = 0
  · refine ⟨1, ?_, ?_⟩
    · simp
    · simp [hz]
  · refine ⟨(Complex.abs z : ℂ) / z, ?_, ?_⟩
    · rw [div_eq_mul_inv]
      rw [star_mul]
      rw [show star ((Complex.abs z : ℂ)) = (Complex.abs z : ℂ) by
        apply Complex.ext <;> simp]
      have hzstar : star z ≠ 0 := by
        intro h
        apply hz
        simpa using congrArg star h
      have habs_ne : (Complex.abs z : ℂ) ≠ 0 := by
        exact_mod_cast (norm_ne_zero_iff.mpr hz : Complex.abs z ≠ 0)
      field_simp [hz, hzstar, habs_ne]
      rw [show star (1 / z) = (star z)⁻¹ by simp [div_eq_mul_inv]]
      field_simp [hzstar]
      have hnorm : (Complex.normSq z : ℂ) = star z * z := by
        simpa using (Complex.normSq_eq_conj_mul_self (z := z))
      rw [← hnorm]
      rw [Complex.normSq_eq_norm_sq]
      change ((‖z‖ : ℝ) : ℂ) ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ)
      norm_num
    · have hmul : (((Complex.abs z : ℂ) / z) * z) = (Complex.abs z : ℂ) := by
        field_simp [hz]
      rw [hmul]
      simp

theorem psdSqrt_kronecker {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {B : CMatrix b}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    psdSqrt (Matrix.kronecker A B) =
      Matrix.kronecker (psdSqrt A) (psdSqrt B) := by
  simp only [psdSqrt, CFC.sqrt_eq_rpow]
  exact cMatrix_rpow_kronecker_nonneg hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- A block-diagonal matrix with positive semidefinite diagonal blocks is
positive semidefinite.  This small local bridge is the block-cone constructor
needed for endpoint SDP feasibility. -/
theorem cMatrix_fromBlocks_diagonal_posSemidef {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {A : CMatrix a} {D : CMatrix b}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D : CMatrix (Sum a b)).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.IsHermitian.ext_iff.mp hA.isHermitian,
        Matrix.IsHermitian.ext_iff.mp hD.isHermitian]
  · intro x
    let xl : a → ℂ := fun i => x (Sum.inl i)
    let xr : b → ℂ := fun i => x (Sum.inr i)
    have hleft : 0 ≤ star xl ⬝ᵥ A.mulVec xl :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 xl
    have hright : 0 ≤ star xr ⬝ᵥ D.mulVec xr :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hD).2 xr
    have hsum : 0 ≤ star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr :=
      add_nonneg hleft hright
    have hquad :
        star x ⬝ᵥ (Matrix.fromBlocks A 0 0 D).mulVec x =
          star xl ⬝ᵥ A.mulVec xl + star xr ⬝ᵥ D.mulVec xr := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_fromBlocks, Matrix.dotProduct_block]
      simp [Matrix.dotProduct_mulVec, xl, xr]
      change
        Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr =
        Matrix.vecMul (star xl) A ⬝ᵥ xl + Matrix.vecMul (star xr) D ⬝ᵥ xr
      rfl
    simpa [hquad] using hsum

/-- The elementary unitary block matrix `[[I,U],[U†,I]]` is positive
semidefinite.  It factors as `T†T`, with `T = [[I,U],[0,0]]`. -/
theorem cMatrix_fromBlocks_unitary_posSemidef {a : Type u}
    [Fintype a] [DecidableEq a] (U : Matrix.unitaryGroup a ℂ) :
    (Matrix.fromBlocks (1 : CMatrix a) (U : CMatrix a) (star (U : CMatrix a)) 1 :
      CMatrix (Sum a a)).PosSemidef := by
  classical
  let T : CMatrix (Sum a a) :=
    Matrix.fromBlocks (1 : CMatrix a) (U : CMatrix a) 0 0
  have hpsd : (star T * T).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self T
  have hfactor :
      star T * T =
        (Matrix.fromBlocks (1 : CMatrix a) (U : CMatrix a) (star (U : CMatrix a)) 1 :
          CMatrix (Sum a a)) := by
    have hUconj : ((U : CMatrix a)ᴴ) * (U : CMatrix a) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        Matrix.UnitaryGroup.star_mul_self U
    dsimp [T]
    rw [Matrix.star_eq_conjTranspose]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;> simp [hUconj, Matrix.star_eq_conjTranspose]
  simpa [hfactor.symm] using hpsd

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace ReferenceIsometry

variable {r₁ : Type w} {r₂ : Type x}
variable [Fintype r₁] [DecidableEq r₁] [Fintype r₂] [DecidableEq r₂]

omit [DecidableEq a] [DecidableEq r₁] in
theorem rightBlock_mul (X Y : CMatrix (Prod a r₁)) (i j : a) :
    rightBlock (X * Y) i j =
      ∑ k : a, rightBlock X i k * rightBlock Y k j := by
  ext x y
  change (X * Y) (i, x) (j, y) =
    (∑ k : a, rightBlock X i k * rightBlock Y k j) x y
  rw [Matrix.mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  rw [Matrix.sum_apply]
  simp [rightBlock, Matrix.mul_apply]

omit [DecidableEq a] in
theorem applyMatrixRight_mul (V : ReferenceIsometry r₁ r₂)
    (X Y : CMatrix (Prod a r₁)) :
    V.applyMatrixRight X * V.applyMatrixRight Y = V.applyMatrixRight (X * Y) := by
  ext p q
  calc
    (V.applyMatrixRight X * V.applyMatrixRight Y) p q =
        (∑ k : a,
          ((V.matrix * rightBlock X p.1 k * Matrix.conjTranspose V.matrix) *
            (V.matrix * rightBlock Y k q.1 * Matrix.conjTranspose V.matrix)) p.2 q.2) := by
      change (∑ j : Prod a r₂, V.applyMatrixRight X p j * V.applyMatrixRight Y j q) = _
      rw [← Finset.univ_product_univ, Finset.sum_product]
      simp [applyMatrixRight, Matrix.mul_apply]
    _ = (∑ k : a,
          (V.matrix * (rightBlock X p.1 k * rightBlock Y k q.1) *
            Matrix.conjTranspose V.matrix) p.2 q.2) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := V.matrix_mul_conjTranspose_mul_matrix
        (rightBlock X p.1 k) (rightBlock Y k q.1)
      exact congrFun (congrFun h p.2) q.2
    _ = (V.matrix * (∑ k : a, rightBlock X p.1 k * rightBlock Y k q.1) *
            Matrix.conjTranspose V.matrix) p.2 q.2 := by
      have hsum :
          V.matrix * (∑ k : a, rightBlock X p.1 k * rightBlock Y k q.1) *
              Matrix.conjTranspose V.matrix =
            ∑ k : a, V.matrix * (rightBlock X p.1 k * rightBlock Y k q.1) *
              Matrix.conjTranspose V.matrix := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
      have hentry := congrFun (congrFun hsum p.2) q.2
      simpa [Matrix.sum_apply] using hentry.symm
    _ = V.applyMatrixRight (X * Y) p q := by
      rw [← rightBlock_mul X Y p.1 q.1]
      rfl

theorem applyMatrixRight_posSemidef (V : ReferenceIsometry r₁ r₂)
    {X : CMatrix (Prod a r₁)} (hX : X.PosSemidef) :
    (V.applyMatrixRight X).PosSemidef := by
  rw [← MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight]
  exact MatrixMap.isCompletelyPositive_mapsPositive
    (MatrixMap.kron (Channel.idChannel a).map (MatrixMap.ofReferenceIsometry V))
    (MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
      (MatrixMap.ofReferenceIsometry V)
      (Channel.idChannel a).completelyPositive
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V))
    X hX

theorem psdSqrt_applyMatrixRight (V : ReferenceIsometry r₁ r₂)
    {X : CMatrix (Prod a r₁)} (hX : X.PosSemidef) :
    psdSqrt (V.applyMatrixRight X) = V.applyMatrixRight (psdSqrt X) := by
  let S : CMatrix (Prod a r₂) := V.applyMatrixRight (psdSqrt X)
  have hSpos : S.PosSemidef := by
    simpa [S] using V.applyMatrixRight_posSemidef (a := a) (psdSqrt_pos X)
  have hSsq : S * S = V.applyMatrixRight X := by
    dsimp [S]
    rw [applyMatrixRight_mul, psdSqrt_mul_self_of_posSemidef hX]
  simpa [psdSqrt, S] using
    (CFC.sqrt_unique (a := V.applyMatrixRight X) (b := S) hSsq hSpos.nonneg)

/-- Concrete right-summand reference padding commutes with the positive square root. -/
theorem psdSqrt_applyMatrixRight_sumInr
    {extra : Type w} [Fintype extra] [DecidableEq extra]
    {X : CMatrix (Prod a b)} (hX : X.PosSemidef) :
    psdSqrt ((ReferenceIsometry.sumInr extra b).applyMatrixRight X) =
      (ReferenceIsometry.sumInr extra b).applyMatrixRight (psdSqrt X) :=
  (ReferenceIsometry.sumInr extra b).psdSqrt_applyMatrixRight hX

end ReferenceIsometry

namespace MatrixMap

variable {κ : Type x} [Fintype κ]

def smoothEndpointKrausStack (K : κ → Matrix b a ℂ) :
    Matrix (Prod κ b) a ℂ :=
  fun x i => K x.1 x.2 i

omit [Fintype a] [DecidableEq a] in
theorem smoothEndpointKrausStack_conjTranspose_mul
    (K : κ → Matrix b a ℂ) :
    Matrix.conjTranspose (smoothEndpointKrausStack K) *
        smoothEndpointKrausStack K =
      krausAdjoint K (1 : CMatrix b) := by
  classical
  ext i j
  calc
    (Matrix.conjTranspose (smoothEndpointKrausStack K) *
        smoothEndpointKrausStack K) i j =
        ∑ x : κ, ∑ y : b, star (K x y i) * K x y j := by
          simp [smoothEndpointKrausStack, Matrix.mul_apply,
            Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    _ = (∑ x : κ, Matrix.conjTranspose (K x) * K x) i j := by
          rw [Matrix.sum_apply]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    _ = (krausAdjoint K (1 : CMatrix b)) i j := by
          simp [krausAdjoint]

theorem smoothEndpointKrausStack_contraction_of_traceNonincreasing
    (K : κ → Matrix b a ℂ)
    (hTNI : IsTraceNonincreasing (ofKraus K)) :
    Matrix.conjTranspose (smoothEndpointKrausStack K) *
        smoothEndpointKrausStack K ≤ (1 : CMatrix a) := by
  rw [smoothEndpointKrausStack_conjTranspose_mul]
  exact krausAdjoint_one_le_of_traceNonincreasing K hTNI

end MatrixMap
end

end QIT
