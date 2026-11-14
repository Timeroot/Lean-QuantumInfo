/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.YangNavascues.BobSupport

/-!
# Bob-local state-supported orthogonalization

A Bob-local orthogonal projection family `Q_k : Projection HB` whose bipartite
lift `(1_A ⊗ Q_k)` has the same post-selected density action on the realization
state as Bob's original projections `P_B^(k)`. This strengthens the
bipartite witness (`StateSupportedBobOrthogonalization`) to local operators
suitable for the controlled-`Z_B` step of the CGS local-isometry construction.

Source: ColadangeloGohScarani2016SelfTesting, `all_pure_v2.tex` (Yang-Navascues
criterion `\label{YNcriterion}`; Bob's family need not be globally orthogonal).
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

namespace QIT

universe u v w

noncomputable section

namespace YangNavascues

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

namespace YNData

variable (data : YNData ι HA HB)

/--
The Bob-local replacement family obtained by projecting onto the reduced
supports of `(1_A ⊗ P_B^(k)) ψ`.
-/
def bobReducedSupportFamily (ψ : PureVector (HA × HB)) : ι → Projection HB :=
  fun k => data.bobProjectedReducedSupportProjection ψ k

@[simp]
theorem bobReducedSupportFamily_apply (ψ : PureVector (HA × HB)) (k : ι) :
    data.bobReducedSupportFamily ψ k =
      data.bobProjectedReducedSupportProjection ψ k :=
  rfl

end YNData

/-- The bipartite lift `(1_A ⊗ Q_k.matrix)` of a Bob-local projection family.

`HA` is explicit because it is not determined by the projection family `Q`
(which lives on `HB`). -/
def bobLocalOp (HA : Type v) [Fintype HA] [DecidableEq HA]
    {ι : Type u} {HB : Type w} [Fintype ι] [DecidableEq ι]
    [Fintype HB] [DecidableEq HB]
    (Q : ι → Projection HB) (k : ι) : CMatrix (HA × HB) :=
  Matrix.kronecker (1 : CMatrix HA) (Q k).matrix

@[simp]
theorem bobLocalOp_eq (Q : ι → Projection HB) (k : ι) :
    bobLocalOp HA Q k = (1 : CMatrix HA) ⊗ₖ (Q k).matrix :=
  rfl

namespace YNData

variable (data : YNData ι HA HB)

/--
Vector-level pure/rank-one replacement action for the reduced-support Bob
projection.

This is stronger than the post-matrix preservation field used by
`BobLocalOrthogonalization`, and is intentionally specialized to the concrete
reduced-support family built from a pure vector.
-/
theorem bobProjectedReducedSupportProjection_mulVec_eq_bobProjectionOp
    (ψ : PureVector (HA × HB)) (k : ι) :
    (YangNavascues.bobLocalOp HA (data.bobProjectedReducedSupportProjection ψ) k).mulVec ψ.amp =
      (data.bobProjectionOp k).mulVec ψ.amp := by
  rw [YangNavascues.bobLocalOp_eq, bobProjectionOp_eq]
  change
    (Matrix.kronecker (1 : CMatrix HA)
      (Matrix.rangeProjection
        (partialTraceA (a := HA) (b := HB)
          (rankOneMatrix ((Matrix.kronecker (1 : CMatrix HA)
            ((data.bobProjection k).matrix)).mulVec ψ.amp))))).mulVec ψ.amp =
      (Matrix.kronecker (1 : CMatrix HA) ((data.bobProjection k).matrix)).mulVec ψ.amp
  exact Matrix.kronecker_rangeProjection_partialTraceA_rankOne_projection_mulVec
    ((data.bobProjection k).matrix)
    (data.bobProjection k).isHermitian
    (data.bobProjection k).idempotent
    ψ.amp

end YNData

/--
A Bob-local orthogonal projection family with state-supported preservation.

The family `bobLocal` is genuinely local on `HB` and mutually orthogonal (unlike
`YNData.bobProjection`, which the source does not require to be orthogonal). The
`preserves` field records that the bipartite lift `(1_A ⊗ Q_k)` has the same
post-selected density action on `rho` as Bob's original `(1_A ⊗ P_B^(k))`.
-/
structure BobLocalOrthogonalization {ι : Type u} {HA : Type v} {HB : Type w}
    [Fintype ι] [DecidableEq ι]
    [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
    (data : YNData ι HA HB) (rho : State (HA × HB)) where
  /-- The Bob-local orthogonal projection family `Q_k`. -/
  bobLocal : ι → Projection HB
  /-- Distinct Bob-local projections are mutually orthogonal. -/
  orthogonal : ∀ i j, i ≠ j → (bobLocal i).matrix * (bobLocal j).matrix = 0
  /-- `(1_A ⊗ Q_k)` matches Bob's original post-selected density on `rho`. -/
  preserves :
    ∀ k, data.postMatrix rho (bobLocalOp HA bobLocal k) = data.bobProjectionAgreementMatrix rho k

namespace BobLocalOrthogonalization

variable {data : YNData ι HA HB} {rho : State (HA × HB)}
variable (W : BobLocalOrthogonalization data rho)

/-- The lifted `(1_A ⊗ Q_k)` is Hermitian. -/
theorem bobLocalOp_isHermitian (k : ι) :
    (bobLocalOp HA W.bobLocal k).IsHermitian := by
  simp only [bobLocalOp_eq]
  change Matrix.conjTranspose ((1 : CMatrix HA) ⊗ₖ (W.bobLocal k).matrix) =
    ((1 : CMatrix HA) ⊗ₖ (W.bobLocal k).matrix)
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  simp [(W.bobLocal k).matrix_conjTranspose]

/-- The lifted `(1_A ⊗ Q_k)` is idempotent. -/
theorem bobLocalOp_idempotent (k : ι) :
    bobLocalOp HA W.bobLocal k * bobLocalOp HA W.bobLocal k = bobLocalOp HA W.bobLocal k := by
  simp only [bobLocalOp_eq]
  rw [← Matrix.mul_kronecker_mul, (W.bobLocal k).idempotent, Matrix.one_mul]

/-- Distinct lifted Bob-local effects are orthogonal. -/
theorem bobLocalOp_orthogonal (i j : ι) (hij : i ≠ j) :
    bobLocalOp HA W.bobLocal i * bobLocalOp HA W.bobLocal j = 0 := by
  simp only [bobLocalOp_eq]
  rw [← Matrix.mul_kronecker_mul, W.orthogonal i j hij, Matrix.one_mul,
    Matrix.kronecker_zero]

/-- A Bob-local orthogonalization strengthens into the bipartite witness. -/
def toStateSupportedBobOrthogonalization : StateSupportedBobOrthogonalization data rho where
  effects := bobLocalOp HA W.bobLocal
  isHermitian := W.bobLocalOp_isHermitian
  idempotent := W.bobLocalOp_idempotent
  orthogonal := W.bobLocalOp_orthogonal
  preserves_postMatrix := W.preserves

end BobLocalOrthogonalization

namespace YNConditions

variable {data : YNData ι HA HB}
variable {ψ : PureVector (HA × HB)}

/--
The reduced-support projections form the exact Bob-local replacement family
for the pure/rank-one Yang-Navascues route.
-/
def bobReducedSupportOrthogonalization (h : YNConditions data ψ.state) :
    BobLocalOrthogonalization data ψ.state where
  bobLocal := data.bobReducedSupportFamily ψ
  orthogonal := by
    intro i j hij
    exact data.bobProjectedReducedSupportProjection_orthogonal ψ h i j hij
  preserves := by
    intro k
    change data.bobLocalPostMatrix ψ.state
        ((data.bobProjectedReducedSupportProjection ψ k).matrix) =
      data.bobProjectionAgreementMatrix ψ.state k
    rw [data.bobProjectionAgreementMatrix_eq_bobLocalPostMatrix ψ.state k]
    exact data.bobProjectedReducedSupportProjection_preserves_postMatrix ψ k

/--
The reduced-support orthogonalization supplied by `YNConditions` also has the
concrete vector-level action needed by the CGS branch-vector calculation.
-/
theorem bobReducedSupportOrthogonalization_mulVec_eq_bobProjectionOp
    (h : YNConditions data ψ.state) (k : ι) :
    (bobLocalOp HA (h.bobReducedSupportOrthogonalization.bobLocal) k).mulVec ψ.amp =
      (data.bobProjectionOp k).mulVec ψ.amp := by
  exact data.bobProjectedReducedSupportProjection_mulVec_eq_bobProjectionOp ψ k

end YNConditions

end YangNavascues

end

end QIT
