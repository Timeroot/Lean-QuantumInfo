/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Basic
public import QIT.Information.Entropy.EntropyTensorPower
public import QIT.States.MaximallyEntangled

/-!
# Completely bounded `1 -> alpha` norm API for EA sandwiched Renyi proofs

This module introduces the no-placeholder finite-dimensional API for the
completely bounded `1 -> alpha` norm that appears in the sandwiched-Renyi
entanglement-assisted converse route.

Source alignment:
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:1128-1165] defines the
  Choi/Gamma expression for the CB norm used in the channel sandwiched-Renyi
  mutual-information alternate expression.
* [KhatriWilde2024Principles, Chapters/EA_capacity.tex:2102-2140] states the
  alternate expression as a supremum over positive bipartite inputs divided by
  the Schatten norm of the input marginal.

The full equality between the two value sets uses CB norm multiplicativity in
the source proof.  This file supplies the exact domains, maps, value sets, and
positivity bridges; the multiplicativity-dependent equality is intentionally
left to the downstream proof layer.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

/-- The finite-dimensional identity channel acts as the identity matrix map. -/
theorem idChannel_map (X : CMatrix a) :
    (Channel.idChannel a).map X = X := by
  change MatrixMap.ofKraus (fun (_ : Unit) => (1 : CMatrix a)) X = X
  simp [MatrixMap.ofKraus]

end Channel

namespace MatrixMap

/-- Apply a matrix map to the second tensor factor, leaving the reference
system untouched.  For the CB norm below the reference system is a copy of the
input system, matching the source notation `R A`. -/
def referenceLift (Phi : MatrixMap a b) : MatrixMap (Prod a a) (Prod a b) :=
  MatrixMap.kron (Channel.idChannel a).map Phi

/-- Reference-lifted maps act componentwise on product matrices. -/
theorem referenceLift_apply_kronecker
    (Phi : MatrixMap a b) (X Y : CMatrix a) :
    Phi.referenceLift (Matrix.kronecker X Y) = Matrix.kronecker X (Phi Y) := by
  rw [referenceLift, MatrixMap.kron_apply_kronecker, Channel.idChannel_map]

/-- Complete positivity is preserved by reference lifting. -/
theorem referenceLift_isCompletelyPositive
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    MatrixMap.IsCompletelyPositive Phi.referenceLift :=
  MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map Phi
    (Channel.idChannel a).completelyPositive hPhi

/-- Reference-lifted completely positive maps preserve positive semidefinite
bipartite inputs. -/
theorem referenceLift_mapsPositive
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {Y : CMatrix (Prod a a)} (hY : Y.PosSemidef) :
    (Phi.referenceLift Y).PosSemidef :=
  MatrixMap.isCompletelyPositive_mapsPositive Phi.referenceLift
    (Phi.referenceLift_isCompletelyPositive hPhi) Y hY

/-- The unnormalized maximally entangled projector `|Gamma><Gamma|` is the
Choi matrix of the identity channel. -/
def unnormalizedMaximallyEntangledProjector (a : Type u) [Fintype a] [DecidableEq a] :
    CMatrix (Prod a a) :=
  MatrixMap.choi (Channel.idChannel a).map

/-- The unnormalized maximally entangled projector is positive semidefinite. -/
theorem unnormalizedMaximallyEntangledProjector_posSemidef :
    (unnormalizedMaximallyEntangledProjector a).PosSemidef :=
  (Channel.idChannel a).completelyPositive

/-- On a nonempty finite system, the unnormalized Choi/Gamma projector is the
dimension-scaled normalized canonical maximally entangled state. -/
theorem unnormalizedMaximallyEntangledProjector_eq_card_smul_state [Nonempty a] :
    unnormalizedMaximallyEntangledProjector a =
      (Fintype.card a : ℂ) • (State.maximallyEntangled (Equiv.refl a)).matrix := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  by_cases hij : i = j
  · by_cases hi'j' : i' = j'
    · subst j
      subst j'
      have hcard_pos : 0 < (Fintype.card a : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
      have hsqrt_ne : (Real.sqrt (Fintype.card a : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hcard_pos))
      simp [unnormalizedMaximallyEntangledProjector, MatrixMap.choi, Channel.idChannel_map,
        State.maximallyEntangled, PureVector.maximallyEntangled, PureVector.state,
        rankOneMatrix_apply, Matrix.single]
      field_simp [hsqrt_ne]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
      exact congrArg Complex.ofReal (Real.sq_sqrt hcard_pos.le)
    · simp [unnormalizedMaximallyEntangledProjector, MatrixMap.choi, Channel.idChannel_map,
        State.maximallyEntangled, PureVector.maximallyEntangled, PureVector.state,
        rankOneMatrix_apply, Matrix.single, hij, hi'j']
  · simp [unnormalizedMaximallyEntangledProjector, MatrixMap.choi, Channel.idChannel_map,
      State.maximallyEntangled, PureVector.maximallyEntangled, PureVector.state,
      rankOneMatrix_apply, Matrix.single, hij]

/-- The reference-side weight `Y_R^(1/(2 alpha)) tensor I_A` from the source CB
norm definition. -/
def cbOneToAlphaReferenceWeight (Y : CMatrix a) (alpha : ℝ) : CMatrix (Prod a a) :=
  Matrix.kronecker (CFC.rpow Y (1 / (2 * alpha))) (1 : CMatrix a)

/-- The reference-side weight is Hermitian for positive semidefinite `Y`. -/
theorem cbOneToAlphaReferenceWeight_isHermitian
    {Y : CMatrix a} (hY : Y.PosSemidef) (alpha : ℝ) :
    (cbOneToAlphaReferenceWeight Y alpha).IsHermitian := by
  unfold cbOneToAlphaReferenceWeight
  exact kronecker_isHermitian _ _
    (cMatrix_rpow_posSemidef (A := Y) (s := 1 / (2 * alpha)) hY).isHermitian
    (by simp [Matrix.IsHermitian])

/-- The source input
`Y_R^(1/(2 alpha)) |Gamma><Gamma|_{RA} Y_R^(1/(2 alpha))`
before applying `id_R tensor M`. -/
def cbOneToAlphaOriginalInput (Y : CMatrix a) (alpha : ℝ) : CMatrix (Prod a a) :=
  cbOneToAlphaReferenceWeight Y alpha *
    unnormalizedMaximallyEntangledProjector a *
      cbOneToAlphaReferenceWeight Y alpha

/-- The source CB-norm input is positive semidefinite whenever `Y` is. -/
theorem cbOneToAlphaOriginalInput_posSemidef
    {Y : CMatrix a} (hY : Y.PosSemidef) (alpha : ℝ) :
    (cbOneToAlphaOriginalInput Y alpha).PosSemidef := by
  let W : CMatrix (Prod a a) := cbOneToAlphaReferenceWeight Y alpha
  have hW : W.IsHermitian := cbOneToAlphaReferenceWeight_isHermitian hY alpha
  have h :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same
      (unnormalizedMaximallyEntangledProjector_posSemidef (a := a)) W
  simpa [cbOneToAlphaOriginalInput, W, hW.eq] using h

/-- Domain of the source Choi/Gamma CB norm expression. -/
structure CBOneToAlphaOriginalDomain (a : Type u) [Fintype a] where
  matrix : CMatrix a
  pos : matrix.PosSemidef
  trace_le_one : matrix.trace.re ≤ 1

/-- The zero input is a harmless member of the source CB-norm domain. -/
def CBOneToAlphaOriginalDomain.zero (a : Type u) [Fintype a] :
    CBOneToAlphaOriginalDomain a where
  matrix := 0
  pos := by
    simpa using (Matrix.PosSemidef.zero : (0 : CMatrix a).PosSemidef)
  trace_le_one := by
    simp

/-- Source CB `1 -> alpha` value for a single admissible reference-side input. -/
def cbOneToAlphaOriginalValue
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Y : CBOneToAlphaOriginalDomain a) (alpha : SchattenOrder) : ℝ :=
  psdSchattenPNorm
    (Phi.referenceLift (cbOneToAlphaOriginalInput Y.matrix alpha))
    (Phi.referenceLift_mapsPositive hPhi
      (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
    alpha

/-- Value set of the source Choi/Gamma CB `1 -> alpha` norm expression. -/
def cbOneToAlphaOriginalValueSet
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) : Set ℝ :=
  Set.range fun Y : CBOneToAlphaOriginalDomain a =>
    cbOneToAlphaOriginalValue Phi hPhi Y alpha

/-- Source-side CB `1 -> alpha` norm surface from `eq-operator_CB_alpha_norm`. -/
def cbOneToAlphaNorm
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) : ℝ :=
  sSup (cbOneToAlphaOriginalValueSet Phi hPhi alpha)

theorem cbOneToAlphaNorm_eq_sSup
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) :
    cbOneToAlphaNorm Phi hPhi alpha =
      sSup (cbOneToAlphaOriginalValueSet Phi hPhi alpha) := by
  rfl

theorem cbOneToAlphaOriginalValue_mem_valueSet
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Y : CBOneToAlphaOriginalDomain a) (alpha : SchattenOrder) :
    cbOneToAlphaOriginalValue Phi hPhi Y alpha ∈
      cbOneToAlphaOriginalValueSet Phi hPhi alpha := by
  exact ⟨Y, rfl⟩

theorem cbOneToAlphaOriginalValue_nonneg
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (Y : CBOneToAlphaOriginalDomain a) (alpha : SchattenOrder) :
    0 ≤ cbOneToAlphaOriginalValue Phi hPhi Y alpha :=
  psdSchattenPNorm_nonneg
    (Phi.referenceLift (cbOneToAlphaOriginalInput Y.matrix alpha))
    (Phi.referenceLift_mapsPositive hPhi
      (cbOneToAlphaOriginalInput_posSemidef Y.pos alpha))
    alpha

/-- Domain of the alternate CB-norm expression:
positive bipartite inputs whose reference marginal has nonzero Schatten
`alpha` expression. -/
structure CBOneToAlphaAlternateDomain (a : Type u) [Fintype a] [DecidableEq a]
    (alpha : SchattenOrder) where
  matrix : CMatrix (Prod a a)
  pos : matrix.PosSemidef
  marginal_norm_pos :
    0 < psdSchattenPNorm
      (partialTraceB (a := a) (b := a) matrix)
      (partialTraceB_posSemidef (a := a) (b := a) pos)
      alpha

/-- Source alternate-expression value for one positive bipartite input. -/
def cbOneToAlphaAlternateValue
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (Y : CBOneToAlphaAlternateDomain a alpha) : ℝ :=
  psdSchattenPNorm
      (Phi.referenceLift Y.matrix)
      (Phi.referenceLift_mapsPositive hPhi Y.pos)
      alpha /
    psdSchattenPNorm
      (partialTraceB (a := a) (b := a) Y.matrix)
      (partialTraceB_posSemidef (a := a) (b := a) Y.pos)
      alpha

/-- Value set of the alternate CB-norm expression from
`eq-eacc_CB_1alpha_norm_alt`. -/
def cbOneToAlphaAlternateValueSet
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) : Set ℝ :=
  Set.range fun Y : CBOneToAlphaAlternateDomain a alpha =>
    cbOneToAlphaAlternateValue Phi hPhi Y

/-- Right-hand side of the alternate CB `1 -> alpha` norm expression. -/
def cbOneToAlphaAlternateExpression
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) : ℝ :=
  sSup (cbOneToAlphaAlternateValueSet Phi hPhi alpha)

theorem cbOneToAlphaAlternateExpression_eq_sSup
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (alpha : SchattenOrder) :
    cbOneToAlphaAlternateExpression Phi hPhi alpha =
      sSup (cbOneToAlphaAlternateValueSet Phi hPhi alpha) := by
  rfl

theorem cbOneToAlphaAlternateValue_mem_valueSet
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (Y : CBOneToAlphaAlternateDomain a alpha) :
    cbOneToAlphaAlternateValue Phi hPhi Y ∈
      cbOneToAlphaAlternateValueSet Phi hPhi alpha := by
  exact ⟨Y, rfl⟩

theorem cbOneToAlphaAlternateValue_nonneg
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    {alpha : SchattenOrder} (Y : CBOneToAlphaAlternateDomain a alpha) :
    0 ≤ cbOneToAlphaAlternateValue Phi hPhi Y := by
  exact div_nonneg
    (psdSchattenPNorm_nonneg (Phi.referenceLift Y.matrix)
      (Phi.referenceLift_mapsPositive hPhi Y.pos) alpha)
    (le_of_lt Y.marginal_norm_pos)

end MatrixMap

end

end QIT
