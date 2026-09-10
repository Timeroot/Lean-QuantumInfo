/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.WeightedSion

/-!
# Ket bridge for sandwiched EA additivity

This module is part of the Khatri--Wilde sandwiched-Renyi additivity proof
spine for entanglement-assisted classical communication.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker Pointwise

namespace QIT

universe u1 v1 u2 v2

noncomputable section

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u1 v1 u2 v2

/-- Product purification arranged in the KW order
`((A1 x A2) x (B1 x B2)) x (C1 x C2)`.

This is the concrete product purification used in
`EA_capacity.tex:1200-1207` when the alternate expression is restricted to
product side-information states on the purifying systems. -/
def bipartiteProductPurification
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (psi : Ket ((a1 × b1) × c1))
    (phi : Ket ((a2 × b2) × c2)) :
    Ket (((a1 × a2) × (b1 × b2)) × (c1 × c2)) :=
  (psi.prod phi).reindex prodTripartiteZipEquiv

@[simp]
theorem bipartiteProductPurification_vec
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (psi : Ket ((a1 × b1) × c1))
    (phi : Ket ((a2 × b2) × c2))
    (p : ((a1 × a2) × (b1 × b2)) × (c1 × c2)) :
    (bipartiteProductPurification psi phi).vec p =
      psi.vec ((p.1.1.1, p.1.2.1), p.2.1) *
        phi.vec ((p.1.1.2, p.1.2.2), p.2.2) :=
  rfl

/-- Definition-level bridge from the source common bracket to the raw matrix
trace functional used by the Sion API. -/
theorem upwardRenyiDualityCommonBracket_re_eq_abcSidePowerTraceRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : Ket ((a × b) × c)) (σB : MState b) (τC : MState c)
    (alphaPrime : ℝ) :
    (ψ.upwardRenyiDualityCommonBracket σB τC alphaPrime).re =
      MState.abcSidePowerTraceRe (a := a) ψ.state.m σB.m τC.m
        alphaPrime := by
  rfl

/-- KW mutual-information Sion bracket with the fixed `rho_A` side weight from
`EA_capacity.tex:2020-2025`. -/
def sandwichedMutualInformationSionBracketRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c) (alpha : ℝ) : ℝ :=
  MState.abcWeightedSidePowerTraceRe
    (CFC.rpow rhoA.m ((1 - alpha) / alpha))
    ψ.state.m σB.m τC.m ((alpha - 1) / alpha)

/-- The KW sandwiched mutual-information Sion bracket is nonnegative. -/
theorem sandwichedMutualInformationSionBracketRe_nonneg
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c) (alpha : ℝ) :
    0 ≤ sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha := by
  unfold sandwichedMutualInformationSionBracketRe
  exact MState.abcWeightedSidePowerTraceRe_nonneg
    (cMatrix_rpow_posSemidef
      (A := rhoA.m) (s := (1 - alpha) / alpha) rhoA.psd)
    ψ.state.psd σB.psd τC.psd ((alpha - 1) / alpha)

/-- Definition-level source form of the KW fixed-`rho_A` Sion bracket. -/
theorem sandwichedMutualInformationSionBracketRe_eq_source
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      (((((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (CFC.rpow σB.m ((1 - alpha) / alpha))) ⊗ₖ
          (CFC.rpow τC.m ((alpha - 1) / alpha))) *
        ψ.state.m).trace).re := by
  unfold sandwichedMutualInformationSionBracketRe MState.abcWeightedSidePowerTraceRe
  have hsigma_exp : -((alpha - 1) / alpha) = (1 - alpha) / alpha := by
    ring
  rw [hsigma_exp]

/-- The `B`-system matrix obtained by tracing the `A` and `C` legs after
applying the fixed `rho_A` and `tau_C` powers from KW
`EA_capacity.tex:2028-2032`. -/
def sandwichedMutualInformationACTraceMatrix
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (alpha : ℝ) : CMatrix b :=
  fun j j' =>
    ∑ i : a, ∑ k : c,
      (((((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (1 : CMatrix b)) ⊗ₖ
          (CFC.rpow τC.m ((alpha - 1) / alpha))) *
        ψ.state.m) ((i, j), k) ((i, j'), k))

/-- The `AC`-side weight from KW `EA_capacity.tex:2028-2035`, after
grouping the traced systems together. -/
def sandwichedMutualInformationACWeight
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : MState a) (τC : MState c) (alpha : ℝ) : CMatrix (a × c) :=
  (CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
    (CFC.rpow τC.m ((alpha - 1) / alpha))

/-- Coordinate form of the KW trace-out-`AC` matrix. -/
theorem sandwichedMutualInformationACTraceMatrix_apply
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (alpha : ℝ) (j j' : b) :
    sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha j j' =
      ∑ i : a, ∑ k : c, ∑ i' : a, ∑ k' : c,
        sandwichedMutualInformationACWeight rhoA τC alpha (i, k) (i', k') *
          ψ.vec ((i', j), k') * star (ψ.vec ((i, j'), k)) := by
  simp [sandwichedMutualInformationACTraceMatrix, sandwichedMutualInformationACWeight,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Ket.state_matrix, rankOneMatrix_apply, Fintype.sum_prod_type, mul_assoc]

/-- The `AC`-grouped amplitude obtained by applying the square-root of the
KW `AC` weight and leaving the `B` system untouched.  Its rank-one matrix is
the PSD representative of the trace-cyclic expression in
KW `EA_capacity.tex:2028-2035`. -/
def sandwichedMutualInformationACWeightedAmp
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (alpha : ℝ) : (a × c) × b → ℂ :=
  Matrix.mulVec
    ((CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)) ⊗ₖ
      (1 : CMatrix b))
    (fun p : (a × c) × b => ψ.vec ((p.1.1, p.2), p.1.2))

/-- The KW `AC` weight is positive semidefinite. -/
theorem sandwichedMutualInformationACWeight_posSemidef
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : MState a) (τC : MState c) (alpha : ℝ) :
    (sandwichedMutualInformationACWeight rhoA τC alpha).PosSemidef := by
  exact
    (cMatrix_rpow_posSemidef
        (A := rhoA.m) (s := (1 - alpha) / alpha) rhoA.psd).kronecker
      (cMatrix_rpow_posSemidef
        (A := τC.m) (s := (alpha - 1) / alpha) τC.psd)

/-- The KW `AC` weight is positive definite when both side weights are full
rank. -/
theorem sandwichedMutualInformationACWeight_posDef
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : MState a) (τC : MState c)
    (hrhoA : rhoA.m.PosDef) (hτC : τC.m.PosDef) (alpha : ℝ) :
    (sandwichedMutualInformationACWeight rhoA τC alpha).PosDef := by
  exact
    (cMatrix_rpow_posDef_of_posDef hrhoA ((1 - alpha) / alpha)).kronecker
      (cMatrix_rpow_posDef_of_posDef hτC ((alpha - 1) / alpha))

/-- The square root of the KW `AC` weight squares back to the weight. -/
theorem sandwichedMutualInformationACWeight_sqrt_mul_self
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : MState a) (τC : MState c) (alpha : ℝ) :
    CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha) *
        CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha) =
      sandwichedMutualInformationACWeight rhoA τC alpha := by
  exact CFC.sqrt_mul_sqrt_self _
    (sandwichedMutualInformationACWeight_posSemidef rhoA τC alpha).nonneg

/-- The square root of the KW `AC` weight is Hermitian. -/
theorem sandwichedMutualInformationACWeight_sqrt_isHermitian
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : MState a) (τC : MState c) (alpha : ℝ) :
    (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)).IsHermitian := by
  exact (Matrix.nonneg_iff_posSemidef.mp
    (CFC.sqrt_nonneg (sandwichedMutualInformationACWeight rhoA τC alpha))).isHermitian

/-- The square root of a full-rank KW `AC` weight is invertible. -/
theorem sandwichedMutualInformationACWeight_sqrt_isUnit_posDef
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : MState a) (τC : MState c)
    (hrhoA : rhoA.m.PosDef) (hτC : τC.m.PosDef) (alpha : ℝ) :
    IsUnit (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)) := by
  have hW : (sandwichedMutualInformationACWeight rhoA τC alpha).PosDef :=
    sandwichedMutualInformationACWeight_posDef rhoA τC hrhoA hτC alpha
  have hsqrt :
      (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)).PosDef := by
    rw [CFC.sqrt_eq_rpow]
    exact cMatrix_rpow_posDef_of_posDef hW (1 / 2)
  exact hsqrt.isUnit

/-- The rank-one matrix built from the KW `AC` square-root-weighted amplitude is
positive semidefinite. -/
theorem sandwichedMutualInformationACWeightedAmp_rankOne_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (alpha : ℝ) :
    (rankOneMatrix
      (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha)).PosSemidef :=
  rankOneMatrix_pos (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha)

/-- A rank-one kernel is zero exactly when its generating vector is zero. -/
private theorem rankOneMatrix_eq_zero_iff
    {d : Type*} (v : d → ℂ) :
    rankOneMatrix v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hdiag := congrFun (congrFun h i) i
    simp [rankOneMatrix_apply] at hdiag
    exact hdiag
  · intro h
    ext i j
    simp [rankOneMatrix_apply, h]

/-- Repartitioning a normalized `ABC` ket as an `ACB` amplitude does not
make it zero. -/
private theorem ket_acb_amp_ne_zero
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : Ket ((a × b) × c)) :
    (fun p : (a × c) × b => ψ.vec ((p.1.1, p.2), p.1.2)) ≠ 0 := by
  intro hzero
  have hamp_zero : ψ.vec = 0 := by
    funext x
    rcases x with ⟨⟨i, j⟩, k⟩
    have hentry := congrFun hzero ((i, k), j)
    simpa using hentry
  have htrace_zero : (rankOneMatrix ψ.vec).trace = 0 := by
    rw [hamp_zero]
    simp [rankOneMatrix]
  rw [ψ.trace_rankOne_eq_one] at htrace_zero
  norm_num at htrace_zero

/-- Full-rank side weights keep the KW `AC` square-root-weighted amplitude
nonzero. -/
theorem sandwichedMutualInformationACWeightedAmp_ne_zero_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (hrhoA : rhoA.m.PosDef) (hτC : τC.m.PosDef)
    (alpha : ℝ) :
    sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha ≠ 0 := by
  let S : CMatrix (a × c) := CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)
  let psiACB : (a × c) × b → ℂ := fun p => ψ.vec ((p.1.1, p.2), p.1.2)
  have hpsi : psiACB ≠ 0 := by
    simpa [psiACB] using ket_acb_amp_ne_zero ψ
  have hS : IsUnit S := by
    simpa [S] using
      sandwichedMutualInformationACWeight_sqrt_isUnit_posDef rhoA τC hrhoA hτC alpha
  have hK : IsUnit (S ⊗ₖ (1 : CMatrix b)) := by
    exact Matrix.IsUnit.kronecker hS isUnit_one
  intro hzero
  have hmul :
      Matrix.mulVec (S ⊗ₖ (1 : CMatrix b)) psiACB = 0 := by
    simpa [sandwichedMutualInformationACWeightedAmp, S, psiACB] using hzero
  have hmul' :
      Matrix.mulVec (S ⊗ₖ (1 : CMatrix b)) psiACB =
        Matrix.mulVec (S ⊗ₖ (1 : CMatrix b)) 0 := by
    simpa using hmul
  exact hpsi ((Matrix.mulVec_injective_of_isUnit hK) hmul')

/-- Coordinate form of the KW `AC` square-root-weighted amplitude. -/
theorem sandwichedMutualInformationACWeightedAmp_apply
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (alpha : ℝ) (i : a) (k : c) (j : b) :
    sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha ((i, k), j) =
      ∑ i' : a, ∑ k' : c,
        (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)) (i, k) (i', k') *
          ψ.vec ((i', j), k') := by
  unfold sandwichedMutualInformationACWeightedAmp
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  simp [Fintype.sum_prod_type]

/-- The KW trace-out-`AC` matrix is the partial trace of the square-root
weighted rank-one vector.  This provides the PSD representative needed for the
reverse-Holder variational formula in `EA_capacity.tex:2032-2035`. -/
theorem traceLeft_rankOne_ACWeightedAmp_eq_ACTraceMatrix
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (alpha : ℝ) :
    Matrix.traceLeft
        (rankOneMatrix
          (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha)) =
      sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha := by
  let S : CMatrix (a × c) :=
    CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)
  let psiACB : (a × c) × b → ℂ := fun p => ψ.vec ((p.1.1, p.2), p.1.2)
  have hmove :
      Matrix.traceLeft
          (rankOneMatrix (Matrix.mulVec (S ⊗ₖ (1 : CMatrix b)) psiACB)) =
        Matrix.traceLeft
          (((S * S) ⊗ₖ (1 : CMatrix b)) * rankOneMatrix psiACB) := by
    exact traceLeft_rankOne_kron_left_mulVec_eq_weight_mul S
      (by
        simpa [S] using
          (sandwichedMutualInformationACWeight_sqrt_isHermitian rhoA τC alpha))
      psiACB
  have hsqrt :
      S * S = sandwichedMutualInformationACWeight rhoA τC alpha := by
    simpa [S] using
      (sandwichedMutualInformationACWeight_sqrt_mul_self rhoA τC alpha)
  calc
    Matrix.traceLeft
        (rankOneMatrix
          (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha))
        =
      Matrix.traceLeft
          (rankOneMatrix (Matrix.mulVec (S ⊗ₖ (1 : CMatrix b)) psiACB)) := by
        simp [sandwichedMutualInformationACWeightedAmp, S, psiACB]
    _ =
      Matrix.traceLeft
        (((S * S) ⊗ₖ (1 : CMatrix b)) * rankOneMatrix psiACB) := hmove
    _ =
      Matrix.traceLeft
        (((sandwichedMutualInformationACWeight rhoA τC alpha) ⊗ₖ
          (1 : CMatrix b)) * rankOneMatrix psiACB) := by
        rw [hsqrt]
    _ = sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha := by
        ext j j'
        rw [sandwichedMutualInformationACTraceMatrix_apply]
        simp [Matrix.traceLeft, rankOneMatrix_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
          Fintype.sum_prod_type,
          mul_assoc, psiACB]

/-- The KW trace-out-`AC` matrix is positive semidefinite, as required by the
positive reverse-Holder variational formula. -/
theorem sandwichedMutualInformationACTraceMatrix_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (alpha : ℝ) :
    (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha).PosSemidef := by
  have hpt :
      (Matrix.traceLeft
        (rankOneMatrix
          (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha))).PosSemidef :=
    traceLeft_posSemidef
      (sandwichedMutualInformationACWeightedAmp_rankOne_posSemidef rhoA ψ τC alpha)
  have heq := traceLeft_rankOne_ACWeightedAmp_eq_ACTraceMatrix rhoA ψ τC alpha
  simpa [heq] using hpt

/-- Full-rank side weights make the KW `AC` trace matrix nonzero. -/
theorem sandwichedMutualInformationACTraceMatrix_ne_zero_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (hrhoA : rhoA.m.PosDef) (hτC : τC.m.PosDef)
    (alpha : ℝ) :
    sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha ≠ 0 := by
  let v : (a × c) × b → ℂ :=
    sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha
  have hvne : v ≠ 0 := by
    simpa [v] using
      sandwichedMutualInformationACWeightedAmp_ne_zero_posDef
        rhoA ψ τC hrhoA hτC alpha
  intro hzero
  have hptzero :
      Matrix.traceLeft (rankOneMatrix v) = 0 := by
    rw [traceLeft_rankOne_ACWeightedAmp_eq_ACTraceMatrix]
    simpa [v] using hzero
  have htrace_zero : (rankOneMatrix v).trace = 0 := by
    have htrace := congrArg Matrix.trace hptzero
    simpa [Matrix.traceLeft_trace] using htrace
  have hrank_zero : rankOneMatrix v = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (rankOneMatrix_pos v)).mp htrace_zero
  exact hvne ((rankOneMatrix_eq_zero_iff v).mp hrank_zero)

/-- Positive Schatten order `alpha / (2 * alpha - 1)` used by the high-alpha
alternate-expression route. -/
def sandwichedAlternateSchattenOrder {alpha : ℝ} (halpha : 1 < alpha) :
    SchattenOrder := by
  refine ⟨alpha / (2 * alpha - 1), ?_⟩
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hden_pos : 0 < 2 * alpha - 1 := by linarith
  exact div_pos halpha_pos hden_pos

@[simp]
theorem sandwichedAlternateSchattenOrder_coe {alpha : ℝ}
    (halpha : 1 < alpha) :
    (sandwichedAlternateSchattenOrder halpha : ℝ) =
      alpha / (2 * alpha - 1) := rfl

/-- Full-rank side weights make the KW `AC` trace-matrix Schatten norm strictly
positive on the high-alpha branch. -/
theorem psdSchattenPNorm_ACTraceMatrix_pos_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (hrhoA : rhoA.m.PosDef) (hτC : τC.m.PosDef)
    {alpha : ℝ} (_halpha : 1 < alpha) :
    0 <
      psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (sandwichedAlternateSchattenOrder _halpha) := by
  exact psdSchattenPNorm_pos_of_ne_zero
    (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
    (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
    (sandwichedMutualInformationACTraceMatrix_ne_zero_posDef
      rhoA ψ τC hrhoA hτC alpha)

private theorem sum_b_a_c_a_b_c_reorder
    {aa bb cc : Type*} [Fintype aa] [Fintype bb] [Fintype cc]
    (f : bb → aa → cc → aa → bb → cc → ℂ) :
    (∑ j : bb, ∑ i : aa, ∑ k : cc, ∑ i' : aa, ∑ j' : bb, ∑ k' : cc,
        f j i k i' j' k') =
      ∑ k : cc, ∑ i : aa, ∑ j : bb, ∑ i' : aa, ∑ j' : bb, ∑ k' : cc,
        f j i k i' j' k' := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  conv_rhs =>
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
    rw [← Fintype.sum_prod_type']
  let e : (((((bb × aa) × cc) × aa) × bb) × cc) ≃
      (((((cc × aa) × bb) × aa) × bb) × cc) := {
    toFun := fun t =>
      (((((t.1.1.1.2, t.1.1.1.1.2), t.1.1.1.1.1), t.1.1.2), t.1.2), t.2)
    invFun := fun s =>
      (((((s.1.1.1.2, s.1.1.1.1.2), s.1.1.1.1.1), s.1.1.2), s.1.2), s.2)
    left_inv := by
      intro t
      rcases t with ⟨⟨⟨⟨⟨j, i⟩, k⟩, i'⟩, j'⟩, k'⟩
      rfl
    right_inv := by
      intro s
      rcases s with ⟨⟨⟨⟨⟨k, i⟩, j⟩, i'⟩, j'⟩, k'⟩
      rfl }
  simpa [e] using
    (Finset.sum_equiv e (s := Finset.univ) (t := Finset.univ)
      (fun _ => by simp)
      (fun t _ => by
        rcases t with ⟨⟨⟨⟨⟨j, i⟩, k⟩, i'⟩, j'⟩, k'⟩
        rfl))

/-- Trace-out-`AC` form of the KW Sion bracket.

This is the Lean trace-cyclic/partial-trace step in
`EA_capacity.tex:2026-2032`, before applying the positive reverse-Holder
variational formula in the `B` system. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_sigma_mul_ACTraceMatrix
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((CFC.rpow σB.m ((1 - alpha) / alpha) *
        sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha).trace).re := by
  rw [sandwichedMutualInformationSionBracketRe_eq_source]
  simp only [sandwichedMutualInformationACTraceMatrix, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  congr 1
  simp only [Fintype.sum_prod_type]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp_rw [Finset.mul_sum]
  conv_rhs =>
    enter [2, x]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, x, 2, y]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, x, 2, y, 2, y_1]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, x, 2, y, 2, y_1, 2, x_2]
    rw [Finset.sum_comm]
  conv_rhs =>
    enter [2, x, 2, y, 2, y_1, 2, x_2, 2, y_2]
    rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  conv_rhs =>
    rw [sum_b_a_c_a_b_c_reorder]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro i' _
  refine Finset.sum_congr rfl ?_
  intro j' _
  refine Finset.sum_congr rfl ?_
  intro k' _
  ring_nf

/-- Reverse-Holder-facing trace direction for the KW Sion bracket. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha *
        CFC.rpow σB.m ((1 - alpha) / alpha)).trace).re := by
  rw [sandwichedMutualInformationSionBracketRe_eq_trace_sigma_mul_ACTraceMatrix]
  exact congrArg Complex.re (Matrix.trace_mul_comm
    (CFC.rpow σB.m ((1 - alpha) / alpha))
    (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha))

/-- The `AB`-side weight in the proof of KW `eq-sand_rel_mut_inf_alt`. -/
def sandwichedMutualInformationABWeight
    {a : Type u1} {b : Type v1}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoA : MState a) (σB : MState b) (alpha : ℝ) : CMatrix (a × b) :=
  (CFC.rpow rhoA.m ((1 - alpha) / (2 * alpha))) ⊗ₖ
    (CFC.rpow σB.m ((1 - alpha) / (2 * alpha)))

/-- The weighted purification vector used in the proof of KW
`eq-sand_rel_mut_inf_alt`.

It is obtained from the purification `psi_ABC` by applying
`rho_A^((1-alpha)/(2 alpha)) ⊗ sigma_B^((1-alpha)/(2 alpha))` on the `AB`
legs and the identity on the purifying `C` leg. -/
def sandwichedMutualInformationWeightedPurificationAmp
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (σB : MState b)
    (ψ : Ket ((a × b) × c)) (alpha : ℝ) :
    (a × b) × c → ℂ :=
  Matrix.mulVec
    ((sandwichedMutualInformationABWeight rhoA σB alpha) ⊗ₖ
      (1 : CMatrix c))
    ψ.vec

/-- Partial tracing the KW weighted purification over the purifying system
produces the sandwich of the original `AB` marginal by the source weight.

This is the matrix identity behind KW `EA_capacity.tex:1989-1996`. -/
theorem traceRight_rankOne_weightedPurificationAmp_eq
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (σB : MState b)
    (ψ : Ket ((a × b) × c)) (alpha : ℝ) :
    Matrix.traceRight
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)) =
      sandwichedMutualInformationABWeight rhoA σB alpha *
        Matrix.traceRight (rankOneMatrix ψ.vec) *
        Matrix.conjTranspose (sandwichedMutualInformationABWeight rhoA σB alpha) := by
  exact traceRight_rankOne_kron_left_mulVec_eq
    (sandwichedMutualInformationABWeight rhoA σB alpha) ψ.vec

/-- Trace-pairing form of the KW weighted-purification bracket.

This is the cyclic trace/partial-trace bridge in `EA_capacity.tex:2006-2025`:
after applying the `AB` square weights to the purification, pairing the
purifying marginal with `tau_C^((alpha-1)/alpha)` is exactly the Sion trace
bracket on the full-rank side-reference branch. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_traceLeft_mul_tau
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c)
    (hrhoA : rhoA.m.PosDef) (hσB : σB.m.PosDef) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((Matrix.traceLeft
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)) *
        CFC.rpow τC.m ((alpha - 1) / alpha)).trace).re := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let T : CMatrix c := CFC.rpow τC.m ((alpha - 1) / alpha)
  let Wab : CMatrix (a × b) := sandwichedMutualInformationABWeight rhoA σB alpha
  let W : CMatrix ((a × b) × c) := Wab ⊗ₖ (1 : CMatrix c)
  let K : CMatrix ((a × b) × c) := (1 : CMatrix (a × b)) ⊗ₖ T
  have hρpow :
      CFC.rpow rhoA.m s * CFC.rpow rhoA.m s =
        CFC.rpow rhoA.m ((1 - alpha) / alpha) := by
    calc
      CFC.rpow rhoA.m s * CFC.rpow rhoA.m s =
          CFC.rpow rhoA.m (s + s) := by
            exact (CFC.rpow_add (a := rhoA.m) (x := s) (y := s) hrhoA.isUnit).symm
      _ = CFC.rpow rhoA.m ((1 - alpha) / alpha) := by
            congr 1
            simp [s]
            ring
  have hσpow :
      CFC.rpow σB.m s * CFC.rpow σB.m s =
        CFC.rpow σB.m ((1 - alpha) / alpha) := by
    calc
      CFC.rpow σB.m s * CFC.rpow σB.m s =
          CFC.rpow σB.m (s + s) := by
            exact (CFC.rpow_add (a := σB.m) (x := s) (y := s) hσB.isUnit).symm
      _ = CFC.rpow σB.m ((1 - alpha) / alpha) := by
            congr 1
            simp [s]
            ring
  have hWstar : Matrix.conjTranspose W = W := by
    have hWab : Wab.IsHermitian := by
      unfold Wab sandwichedMutualInformationABWeight
      exact kronecker_isHermitian
        (CFC.rpow rhoA.m s)
        (CFC.rpow σB.m s)
        (cMatrix_rpow_posSemidef (A := rhoA.m) (s := s) rhoA.psd).isHermitian
        (cMatrix_rpow_posSemidef (A := σB.m) (s := s) σB.psd).isHermitian
    unfold W
    exact (kronecker_isHermitian Wab (1 : CMatrix c) hWab (by simp)).eq
  have hWKW :
      W * K * W =
        ((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (CFC.rpow σB.m ((1 - alpha) / alpha))) ⊗ₖ
          T := by
    have hWK : W * K = Wab ⊗ₖ T := by
      unfold W K
      simpa using
        (Matrix.mul_kronecker_mul Wab (1 : CMatrix (a × b)) (1 : CMatrix c) T).symm
    have hWab2 :
        Wab * Wab =
          (CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (CFC.rpow σB.m ((1 - alpha) / alpha)) := by
      unfold Wab sandwichedMutualInformationABWeight
      let R : CMatrix a := CFC.rpow rhoA.m ((1 - alpha) / (2 * alpha))
      let S : CMatrix b := CFC.rpow σB.m ((1 - alpha) / (2 * alpha))
      have hR :
          R * R = CFC.rpow rhoA.m ((1 - alpha) / alpha) := by
        simpa [R, s, mul_comm] using hρpow
      have hS :
          S * S = CFC.rpow σB.m ((1 - alpha) / alpha) := by
        simpa [S, s, mul_comm] using hσpow
      calc
        (R ⊗ₖ S) * (R ⊗ₖ S) =
            (R * R) ⊗ₖ (S * S) := by
              exact (Matrix.mul_kronecker_mul R R S S).symm
        _ = (CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
              (CFC.rpow σB.m ((1 - alpha) / alpha)) := by
              rw [hR, hS]
    calc
      W * K * W = (Wab ⊗ₖ T) * W := by rw [hWK]
      _ = (Wab ⊗ₖ T) * (Wab ⊗ₖ (1 : CMatrix c)) := by
            rfl
      _ = (Wab * Wab) ⊗ₖ (T * (1 : CMatrix c)) := by
            exact (Matrix.mul_kronecker_mul Wab Wab T (1 : CMatrix c)).symm
      _ = ((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
              (CFC.rpow σB.m ((1 - alpha) / alpha))) ⊗ₖ
            T := by
            rw [hWab2]
            simp
  have hrank :
      rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) =
        W * rankOneMatrix ψ.vec * W := by
    unfold sandwichedMutualInformationWeightedPurificationAmp W Wab
    rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    rw [hWstar]
  rw [sandwichedMutualInformationSionBracketRe_eq_source]
  rw [traceLeft_mul_trace_eq_trace_mul_kronecker_one_right,
    Ket.state_matrix]
  change
    (((((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (CFC.rpow σB.m ((1 - alpha) / alpha))) ⊗ₖ
          T) *
        rankOneMatrix ψ.vec).trace).re =
      ((rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) *
        K).trace).re
  rw [hrank]
  calc
    (((((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (CFC.rpow σB.m ((1 - alpha) / alpha))) ⊗ₖ
          T) *
        rankOneMatrix ψ.vec).trace).re =
        ((W * K * W * rankOneMatrix ψ.vec).trace).re := by rw [hWKW]
    _ = (((W * rankOneMatrix ψ.vec * W) * K).trace).re := by
          congr 1
          simpa [Matrix.mul_assoc] using
            Matrix.trace_mul_cycle W K (W * rankOneMatrix ψ.vec)

/-- Support-convention trace-pairing form of the KW weighted-purification
bracket.

The older lemma
`sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_traceLeft_mul_tau`
used `CFC.rpow_add` and therefore required `rho_A` to be full rank.  KW
`EA_capacity.tex:2006-2025` does not impose that hypothesis.  This sibling
keeps the source statement: only the optimized side state `sigma_B` is
full-rank, while the fixed `rho_A` is an arbitrary state.  The `rho_A` square
weight is multiplied using the repository support convention for PSD real
powers. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_traceLeft_mul_tau_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c)
    (hσB : σB.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((Matrix.traceLeft
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)) *
        CFC.rpow τC.m ((alpha - 1) / alpha)).trace).re := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let T : CMatrix c := CFC.rpow τC.m ((alpha - 1) / alpha)
  let Wab : CMatrix (a × b) := sandwichedMutualInformationABWeight rhoA σB alpha
  let W : CMatrix ((a × b) × c) := Wab ⊗ₖ (1 : CMatrix c)
  let K : CMatrix ((a × b) × c) := (1 : CMatrix (a × b)) ⊗ₖ T
  have hρpow :
      CFC.rpow rhoA.m s * CFC.rpow rhoA.m s =
        CFC.rpow rhoA.m ((1 - alpha) / alpha) := by
    refine cMatrix_rpow_mul_rpow_of_posSemidef_scalar rhoA.psd ?_
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      have hs_ne : s ≠ 0 := by
        have hnum : 1 - alpha ≠ 0 := by linarith
        have hden : 2 * alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
        exact div_ne_zero hnum hden
      have ht_ne : (1 - alpha) / alpha ≠ 0 := by
        have hnum : 1 - alpha ≠ 0 := by linarith
        have hden : alpha ≠ 0 := by nlinarith [lt_trans zero_lt_one halpha]
        exact div_ne_zero hnum hden
      simp [Real.zero_rpow hs_ne, Real.zero_rpow ht_ne]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      rw [← Real.rpow_add hxpos]
      congr 1
      simp [s]
      ring
  have hσpow :
      CFC.rpow σB.m s * CFC.rpow σB.m s =
        CFC.rpow σB.m ((1 - alpha) / alpha) := by
    calc
      CFC.rpow σB.m s * CFC.rpow σB.m s =
          CFC.rpow σB.m (s + s) := by
            exact (CFC.rpow_add (a := σB.m) (x := s) (y := s) hσB.isUnit).symm
      _ = CFC.rpow σB.m ((1 - alpha) / alpha) := by
            congr 1
            simp [s]
            ring
  have hWstar : Matrix.conjTranspose W = W := by
    have hWab : Wab.IsHermitian := by
      unfold Wab sandwichedMutualInformationABWeight
      exact kronecker_isHermitian
        (CFC.rpow rhoA.m s)
        (CFC.rpow σB.m s)
        (cMatrix_rpow_posSemidef (A := rhoA.m) (s := s) rhoA.psd).isHermitian
        (cMatrix_rpow_posSemidef (A := σB.m) (s := s) σB.psd).isHermitian
    unfold W
    exact (kronecker_isHermitian Wab (1 : CMatrix c) hWab (by simp)).eq
  have hWKW :
      W * K * W =
        ((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (CFC.rpow σB.m ((1 - alpha) / alpha))) ⊗ₖ
          T := by
    have hWK : W * K = Wab ⊗ₖ T := by
      unfold W K
      simpa using
        (Matrix.mul_kronecker_mul Wab (1 : CMatrix (a × b)) (1 : CMatrix c) T).symm
    have hWab2 :
        Wab * Wab =
          (CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (CFC.rpow σB.m ((1 - alpha) / alpha)) := by
      unfold Wab sandwichedMutualInformationABWeight
      let R : CMatrix a := CFC.rpow rhoA.m ((1 - alpha) / (2 * alpha))
      let S : CMatrix b := CFC.rpow σB.m ((1 - alpha) / (2 * alpha))
      have hR :
          R * R = CFC.rpow rhoA.m ((1 - alpha) / alpha) := by
        simpa [R, s, mul_comm] using hρpow
      have hS :
          S * S = CFC.rpow σB.m ((1 - alpha) / alpha) := by
        simpa [S, s, mul_comm] using hσpow
      calc
        (R ⊗ₖ S) * (R ⊗ₖ S) =
            (R * R) ⊗ₖ (S * S) := by
              exact (Matrix.mul_kronecker_mul R R S S).symm
        _ = (CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
              (CFC.rpow σB.m ((1 - alpha) / alpha)) := by
              rw [hR, hS]
    calc
      W * K * W = (Wab ⊗ₖ T) * W := by rw [hWK]
      _ = (Wab ⊗ₖ T) * (Wab ⊗ₖ (1 : CMatrix c)) := by
            rfl
      _ = (Wab * Wab) ⊗ₖ (T * (1 : CMatrix c)) := by
            exact (Matrix.mul_kronecker_mul Wab Wab T (1 : CMatrix c)).symm
      _ = ((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
              (CFC.rpow σB.m ((1 - alpha) / alpha))) ⊗ₖ
            T := by
            rw [hWab2]
            simp
  have hrank :
      rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) =
        W * rankOneMatrix ψ.vec * W := by
    unfold sandwichedMutualInformationWeightedPurificationAmp W Wab
    rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    rw [hWstar]
  rw [sandwichedMutualInformationSionBracketRe_eq_source]
  rw [traceLeft_mul_trace_eq_trace_mul_kronecker_one_right,
    Ket.state_matrix]
  change
    (((((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (CFC.rpow σB.m ((1 - alpha) / alpha))) ⊗ₖ
          T) *
        rankOneMatrix ψ.vec).trace).re =
      ((rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) *
        K).trace).re
  rw [hrank]
  calc
    (((((CFC.rpow rhoA.m ((1 - alpha) / alpha)) ⊗ₖ
            (CFC.rpow σB.m ((1 - alpha) / alpha))) ⊗ₖ
          T) *
        rankOneMatrix ψ.vec).trace).re =
        ((W * K * W * rankOneMatrix ψ.vec).trace).re := by rw [hWKW]
    _ = (((W * rankOneMatrix ψ.vec * W) * K).trace).re := by
          congr 1
          simpa [Matrix.mul_assoc] using
            Matrix.trace_mul_cycle W K (W * rankOneMatrix ψ.vec)

/-- Every full-rank side-reference Sion bracket value lies below the Holder
unit-ball supremum of the KW weighted purification marginal.

This is the inequality direction of the variational step in
`EA_capacity.tex:2006-2025`, after the trace-pairing identity has moved the
`tau_C` power onto the purifying marginal. -/
theorem sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c)
    (hrhoA : rhoA.m.PosDef) (hσB : σB.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ≤
      sSup
        (psdTraceHolderUnitBallValueSet
          (Matrix.traceLeft
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    traceLeft_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let r : ℝ := (alpha - 1) / alpha
  have hpq : alpha.HolderConjugate (Real.conjExponent alpha) :=
    Real.HolderConjugate.conjExponent halpha
  have hr : r = 1 / Real.conjExponent alpha := by
    have halpha_ne : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
    have hsub_ne : alpha - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
    unfold r Real.conjExponent
    field_simp [halpha_ne, hsub_ne]
  have hτtrace : τC.m.trace.re = 1 := by
    simp
  have hvar :
      ((M * CFC.rpow τC.m r).trace).re ≤
        psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) := by
    exact psd_trace_rpow_holder_variational_upper
      (M := M) (N := τC.m) hM τC.psd hτtrace hpq hr
  have htrace :
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
        ((M * CFC.rpow τC.m r).trace).re := by
    simpa [M, r] using
      sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_traceLeft_mul_tau
        rhoA ψ σB τC hrhoA hσB alpha
  rw [htrace]
  rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
    (q := Real.conjExponent alpha) hpq]
  exact hvar

/-- Support-convention version of
`sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup`.

This removes the artificial full-rank assumption on the fixed source marginal
`rho_A`; the only full-rank assumption left is on the optimized side state
`sigma_B`, exactly as in the full-rank-side branch of KW
`EA_capacity.tex:2006-2025`. -/
theorem sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c) (hσB : σB.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ≤
      sSup
        (psdTraceHolderUnitBallValueSet
          (Matrix.traceLeft
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    traceLeft_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let r : ℝ := (alpha - 1) / alpha
  have hpq : alpha.HolderConjugate (Real.conjExponent alpha) :=
    Real.HolderConjugate.conjExponent halpha
  have hr : r = 1 / Real.conjExponent alpha := by
    have halpha_ne : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
    have hsub_ne : alpha - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
    unfold r Real.conjExponent
    field_simp [halpha_ne, hsub_ne]
  have hτtrace : τC.m.trace.re = 1 := by
    simp
  have hvar :
      ((M * CFC.rpow τC.m r).trace).re ≤
        psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) := by
    exact psd_trace_rpow_holder_variational_upper
      (M := M) (N := τC.m) hM τC.psd hτtrace hpq hr
  have htrace :
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
        ((M * CFC.rpow τC.m r).trace).re := by
    simpa [M, r] using
      sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_traceLeft_mul_tau_support
        rhoA ψ σB τC hσB halpha
  rw [htrace]
  rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
    (q := Real.conjExponent alpha) hpq]
  exact hvar

/-- The Holder unit-ball supremum in the KW variational step is controlled by
optimizing the trace bracket over normalized purifying side states.

This is the converse direction to
`sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup`
and formalizes the normalization step in KW `EA_capacity.tex:2010-2018`: a PSD
Holder witness `B` with `Tr B^q ≤ 1` is either zero, or its normalized
`q`-power is a state `tau_C` whose `q`-root dominates the original witness. -/
theorem weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b)
    (hrhoA : rhoA.m.PosDef) (hσB : σB.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup
        (psdTraceHolderUnitBallValueSet
          (Matrix.traceLeft
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) ≤
      sSup (Set.range fun τC : MState c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    traceLeft_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let q : ℝ := Real.conjExponent alpha
  let r : ℝ := (alpha - 1) / alpha
  have hpq : alpha.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent halpha
  have hq_pos : 0 < q := hpq.symm.pos
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hr : r = 1 / q := by
    have halpha_ne : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
    have hsub_ne : alpha - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
    unfold r q Real.conjExponent
    field_simp [halpha_ne, hsub_ne]
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    exact hpq.symm.one_div_nonneg
  have hqr : q * r = 1 := by
    rw [hr]
    exact mul_one_div_cancel hq_pos.ne'
  have hstateBdd :
      BddAbove (Set.range fun τC : MState c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
    refine ⟨psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha), ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle :=
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ σB τC hrhoA hσB halpha
    rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
      (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)] at hle
    exact hle
  have hholderNonempty :
      (psdTraceHolderUnitBallValueSet M q).Nonempty :=
    Set.nonempty_of_mem (psdTraceHolderUnitBall_isGreatest hM hpq).1
  change sSup (psdTraceHolderUnitBallValueSet M q) ≤
    sSup (Set.range fun τC : MState c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha)
  refine csSup_le hholderNonempty ?_
  intro x hx
  rcases hx with ⟨B, hB, hBq, rfl⟩
  by_cases hBzero : B = 0
  · have hvalue_zero : ((M * B).trace).re = 0 := by
      simp [hBzero]
    rw [hvalue_zero]
    let τ0 : MState c := (MState.uniform : MState c)
    have hτ0_nonneg :
        0 ≤ sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha := by
      have htrace :
          sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha =
            ((M * CFC.rpow τ0.m r).trace).re := by
        simpa [M, r] using
          sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_traceLeft_mul_tau
            rhoA ψ σB τ0 hrhoA hσB alpha
      rw [htrace]
      exact cMatrix_trace_mul_posSemidef_re_nonneg hM
        (cMatrix_rpow_posSemidef (A := τ0.m) (s := r) τ0.psd)
    exact hτ0_nonneg.trans (le_csSup hstateBdd ⟨τ0, rfl⟩)
  · let S : ℝ := psdTracePower B hB q
    have hSpos : 0 < S := by
      simpa [S] using psdTracePower_pos_of_ne_zero B hB hBzero
    have hSnonneg : 0 ≤ S := le_of_lt hSpos
    let scale : ℝ := S ^ (-(1 / q))
    have hscale_nonneg : 0 ≤ scale := by
      exact Real.rpow_nonneg hSnonneg (-(1 / q))
    let N : CMatrix c := scale • B
    have hN : N.PosSemidef := by
      simpa [N, scale] using Matrix.PosSemidef.smul hB hscale_nonneg
    have hNq : psdTracePower N hN q = 1 := by
      simpa [N, S, scale, hN] using
        psdTracePower_normalized_real_smul_eq_one_of_ne_zero hB hBzero hq_pos
    let T : CMatrix c := CFC.rpow N q
    have hT : T.PosSemidef := by
      simpa [T] using cMatrix_rpow_posSemidef (A := N) (s := q) hN
    have hTtrace_re : T.trace.re = 1 := by
      change psdTracePower N hN q = 1
      exact hNq
    have hTtrace : T.trace = 1 := by
      apply Complex.ext
      · exact hTtrace_re
      · simpa using (Matrix.PosSemidef.trace_nonneg hT).2.symm
    let τC : MState c := .ofMatrix (matrix := T) (pos := hT) (trace_eq_one := hTtrace)
    have hτpow : CFC.rpow τC.m r = N := by
      simp only [τC, MState.matrix_ofMatrix]
      dsimp [T]
      rw [CFC.rpow_rpow_of_exponent_nonneg N q r hq_nonneg hr_nonneg
        (Matrix.nonneg_iff_posSemidef.mpr hN)]
      rw [hqr]
      simp [CFC.rpow_one N (ha := Matrix.nonneg_iff_posSemidef.mpr hN)]
    have hbracket :
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
          ((M * N).trace).re := by
      have htrace :=
        sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_traceLeft_mul_tau
          rhoA ψ σB τC hrhoA hσB alpha
      rw [hτpow] at htrace
      simpa [M, r] using htrace
    have htrace_smul : ((M * N).trace).re = scale * ((M * B).trace).re := by
      simp [N, Matrix.trace_smul, Complex.mul_re, scale]
    have hscale_ge_one : 1 ≤ scale := by
      have hnonpos : -(1 / q) ≤ 0 := by
        have hone_div_pos : 0 < 1 / q := one_div_pos.mpr hq_pos
        linarith
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hSpos hBq hnonpos
    have hvalue_nonneg : 0 ≤ ((M * B).trace).re :=
      cMatrix_trace_mul_posSemidef_re_nonneg hM hB
    have hvalue_le : ((M * B).trace).re ≤ ((M * N).trace).re := by
      rw [htrace_smul]
      exact le_mul_of_one_le_left hvalue_nonneg hscale_ge_one
    exact hvalue_le.trans (by
      rw [← hbracket]
      exact le_csSup hstateBdd ⟨τC, rfl⟩)

/-- Support-convention converse direction to
`sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef`.

This is the normalized-witness step in KW `EA_capacity.tex:2010-2018` without a
full-rank assumption on the fixed `rho_A`.  A PSD Holder witness is normalized
through its `q`-power to a state `tau_C`, and the support-convention trace
bridge identifies the resulting value with the Sion bracket. -/
theorem weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup_of_side_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (hσB : σB.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup
        (psdTraceHolderUnitBallValueSet
          (Matrix.traceLeft
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) ≤
      sSup (Set.range fun τC : MState c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
  let M : CMatrix c :=
    Matrix.traceLeft
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    traceLeft_posSemidef
      (rankOneMatrix_pos
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let q : ℝ := Real.conjExponent alpha
  let r : ℝ := (alpha - 1) / alpha
  have hpq : alpha.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent halpha
  have hq_pos : 0 < q := hpq.symm.pos
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hr : r = 1 / q := by
    have halpha_ne : alpha ≠ 0 := ne_of_gt (lt_trans zero_lt_one halpha)
    have hsub_ne : alpha - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
    unfold r q Real.conjExponent
    field_simp [halpha_ne, hsub_ne]
  have hr_nonneg : 0 ≤ r := by
    rw [hr]
    exact hpq.symm.one_div_nonneg
  have hqr : q * r = 1 := by
    rw [hr]
    exact mul_one_div_cancel hq_pos.ne'
  have hstateBdd :
      BddAbove (Set.range fun τC : MState c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
    refine ⟨psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha), ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle :=
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ σB τC hσB halpha
    rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
      (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)] at hle
    exact hle
  have hholderNonempty :
      (psdTraceHolderUnitBallValueSet M q).Nonempty :=
    Set.nonempty_of_mem (psdTraceHolderUnitBall_isGreatest hM hpq).1
  change sSup (psdTraceHolderUnitBallValueSet M q) ≤
    sSup (Set.range fun τC : MState c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha)
  refine csSup_le hholderNonempty ?_
  intro x hx
  rcases hx with ⟨B, hB, hBq, rfl⟩
  by_cases hBzero : B = 0
  · have hvalue_zero : ((M * B).trace).re = 0 := by
      simp [hBzero]
    rw [hvalue_zero]
    let τ0 : MState c := (MState.uniform : MState c)
    have hτ0_nonneg :
        0 ≤ sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha := by
      have htrace :
          sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha =
            ((M * CFC.rpow τ0.m r).trace).re := by
        simpa [M, r] using
          sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_traceLeft_mul_tau_support
            rhoA ψ σB τ0 hσB halpha
      rw [htrace]
      exact cMatrix_trace_mul_posSemidef_re_nonneg hM
        (cMatrix_rpow_posSemidef (A := τ0.m) (s := r) τ0.psd)
    exact hτ0_nonneg.trans (le_csSup hstateBdd ⟨τ0, rfl⟩)
  · let S : ℝ := psdTracePower B hB q
    have hSpos : 0 < S := by
      simpa [S] using psdTracePower_pos_of_ne_zero B hB hBzero
    have hSnonneg : 0 ≤ S := le_of_lt hSpos
    let scale : ℝ := S ^ (-(1 / q))
    have hscale_nonneg : 0 ≤ scale := by
      exact Real.rpow_nonneg hSnonneg (-(1 / q))
    let N : CMatrix c := scale • B
    have hN : N.PosSemidef := by
      simpa [N, scale] using Matrix.PosSemidef.smul hB hscale_nonneg
    have hNq : psdTracePower N hN q = 1 := by
      simpa [N, S, scale, hN] using
        psdTracePower_normalized_real_smul_eq_one_of_ne_zero hB hBzero hq_pos
    let T : CMatrix c := CFC.rpow N q
    have hT : T.PosSemidef := by
      simpa [T] using cMatrix_rpow_posSemidef (A := N) (s := q) hN
    have hTtrace_re : T.trace.re = 1 := by
      change psdTracePower N hN q = 1
      exact hNq
    have hTtrace : T.trace = 1 := by
      apply Complex.ext
      · exact hTtrace_re
      · simpa using (Matrix.PosSemidef.trace_nonneg hT).2.symm
    let τC : MState c := .ofMatrix (matrix := T) (pos := hT) (trace_eq_one := hTtrace)
    have hτpow : CFC.rpow τC.m r = N := by
      simp only [τC, MState.matrix_ofMatrix]
      dsimp [T]
      rw [CFC.rpow_rpow_of_exponent_nonneg N q r hq_nonneg hr_nonneg
        (Matrix.nonneg_iff_posSemidef.mpr hN)]
      rw [hqr]
      simp [CFC.rpow_one N (ha := Matrix.nonneg_iff_posSemidef.mpr hN)]
    have hbracket :
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
          ((M * N).trace).re := by
      have htrace :=
        sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_traceLeft_mul_tau_support
          rhoA ψ σB τC hσB halpha
      rw [hτpow] at htrace
      simpa [M, r] using htrace
    have htrace_smul : ((M * N).trace).re = scale * ((M * B).trace).re := by
      simp [N, Matrix.trace_smul, Complex.mul_re, scale]
    have hscale_ge_one : 1 ≤ scale := by
      have hnonpos : -(1 / q) ≤ 0 := by
        have hone_div_pos : 0 < 1 / q := one_div_pos.mpr hq_pos
        linarith
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hSpos hBq hnonpos
    have hvalue_nonneg : 0 ≤ ((M * B).trace).re :=
      cMatrix_trace_mul_posSemidef_re_nonneg hM hB
    have hvalue_le : ((M * B).trace).re ≤ ((M * N).trace).re := by
      rw [htrace_smul]
      exact le_mul_of_one_le_left hvalue_nonneg hscale_ge_one
    exact hvalue_le.trans (by
      rw [← hbracket]
      exact le_csSup hstateBdd ⟨τC, rfl⟩)

/-- The `AB` marginal of the KW weighted purification is exactly the
sandwiched-Renyi inner operator for the source reference
`rho_A ⊗ sigma_B`.

This is the Lean matrix form of KW `EA_capacity.tex:1989-1996` in the
full-rank high-`alpha` branch. -/
theorem traceRight_rankOne_weightedPurificationAmp_eq_referenceInner
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c))
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    (hσ : σB.m.PosDef) (alpha : ℝ) :
    Matrix.traceRight
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.traceRight σB ψ alpha)) =
      MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.traceRight.prod σB).m alpha := by
  let W : CMatrix (a × b) :=
    sandwichedMutualInformationABWeight ψ.state.marginalAB.traceRight σB alpha
  have hW :
      Matrix.conjTranspose W = W := by
    unfold W sandwichedMutualInformationABWeight
    exact (kronecker_isHermitian
      (CFC.rpow ψ.state.marginalAB.traceRight.m ((1 - alpha) / (2 * alpha)))
      (CFC.rpow σB.m ((1 - alpha) / (2 * alpha)))
      (cMatrix_rpow_posSemidef
        (A := ψ.state.marginalAB.traceRight.m)
        (s := (1 - alpha) / (2 * alpha))
        ψ.state.marginalAB.traceRight.psd).isHermitian
      (cMatrix_rpow_posSemidef
        (A := σB.m)
        (s := (1 - alpha) / (2 * alpha))
        σB.psd).isHermitian).eq
  rw [traceRight_rankOne_weightedPurificationAmp_eq]
  unfold MState.sandwichedRenyiReferenceInner
  rw [MState.prod_m ψ.state.marginalAB.traceRight σB]
  change sandwichedMutualInformationABWeight ψ.state.marginalAB.traceRight σB alpha *
      Matrix.traceRight (rankOneMatrix ψ.vec) *
        Matrix.conjTranspose
          (sandwichedMutualInformationABWeight ψ.state.marginalAB.traceRight σB alpha) =
    CFC.rpow (ψ.state.marginalAB.traceRight.m ⊗ₖ σB.m)
        ((1 - alpha) / (2 * alpha)) *
      ψ.state.marginalAB.m *
      CFC.rpow (ψ.state.marginalAB.traceRight.m ⊗ₖ σB.m)
        ((1 - alpha) / (2 * alpha))
  rw [cMatrix_rpow_kronecker hA.posSemidef hσ.posSemidef ((1 - alpha) / (2 * alpha))]
  change W * Matrix.traceRight (rankOneMatrix ψ.vec) *
      Matrix.conjTranspose W =
    W * ψ.state.marginalAB.m * W
  rw [hW, MState.marginalAB_eq_traceRight, MState.traceRight_m, Ket.state_matrix]

/-- The two partial traces of the KW weighted purification rank-one operator
have equal Schatten `p` norms.

This is the Lean form of the same-nonzero-eigenvalues step in
KW `EA_capacity.tex:1990-2004`, before the reverse-Holder variational formula
is applied. -/
theorem psdSchattenPNorm_weightedPurification_partialTraceC_eq_traceLeftB
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (σB : MState b)
    (ψ : Ket ((a × b) × c)) (alpha : ℝ)
    {p : ℝ} (hp : 0 < p) :
    psdSchattenPNorm
        (Matrix.traceRight
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (traceRight_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (SchattenOrder.ofPositive hp) =
      psdSchattenPNorm
        (Matrix.traceLeft
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (traceLeft_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (SchattenOrder.ofPositive hp) := by
  exact psdSchattenPNorm_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix
    (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)
    (SchattenOrder.ofPositive hp)

/-- Schatten-norm form of the KW weighted-purification bridge.

The reference-inner Schatten expression on the `AB` system equals the Schatten
expression of the complementary `C` marginal of the weighted purification,
matching KW `EA_capacity.tex:1990-2004`. -/
theorem psdSchattenPNorm_referenceInner_eq_weightedPurification_traceLeft
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : MState b) (ψ : Ket ((a × b) × c))
    (hA : ψ.state.marginalAB.traceRight.m.PosDef)
    (hσ : σB.m.PosDef) (alpha : ℝ) {p : ℝ} (hp : 0 < p) :
    psdSchattenPNorm
        (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.traceRight.prod σB).m alpha)
        (MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
          (MState.PosDef.kron hA hσ).posSemidef alpha)
        (SchattenOrder.ofPositive hp) =
      psdSchattenPNorm
        (Matrix.traceLeft
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.traceRight σB ψ alpha)))
        (traceLeft_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.traceRight σB ψ alpha)))
        (SchattenOrder.ofPositive hp) := by
  let amp :=
    sandwichedMutualInformationWeightedPurificationAmp
      ψ.state.marginalAB.traceRight σB ψ alpha
  let hB : (Matrix.traceRight
      (rankOneMatrix amp)).PosSemidef :=
    traceRight_posSemidef (rankOneMatrix_pos amp)
  let hRef :
      (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.traceRight.prod σB).m alpha).PosSemidef :=
    MState.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
      (MState.PosDef.kron hA hσ).posSemidef alpha
  have hmatrix :
      Matrix.traceRight (rankOneMatrix amp) =
        MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.traceRight.prod σB).m alpha := by
    simpa [amp] using
      traceRight_rankOne_weightedPurificationAmp_eq_referenceInner
        σB ψ hA hσ alpha
  have hnormB :
      psdSchattenPNorm (Matrix.traceRight
          (rankOneMatrix amp)) hB (SchattenOrder.ofPositive hp) =
        psdSchattenPNorm
          (MState.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.traceRight.prod σB).m alpha)
          hRef (SchattenOrder.ofPositive hp) :=
    psdSchattenPNorm_congr hmatrix hB hRef (SchattenOrder.ofPositive hp)
  have hBA :
      psdSchattenPNorm (Matrix.traceRight
          (rankOneMatrix amp)) hB (SchattenOrder.ofPositive hp) =
        psdSchattenPNorm
          (Matrix.traceLeft (rankOneMatrix amp))
          (traceLeft_posSemidef (rankOneMatrix_pos amp))
          (SchattenOrder.ofPositive hp) := by
    simpa [amp, hB] using
      psdSchattenPNorm_weightedPurification_partialTraceC_eq_traceLeftB
        ψ.state.marginalAB.traceRight σB ψ alpha hp
  exact hnormB.symm.trans hBA

/-- Pure-state specialization of the KW high-`alpha` Sion exchange. -/
theorem sandwichedAlpha_sion_abcSidePowerTraceRe_state_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : Ket ((a × b) × c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b,
        ⨆ τ ∈ MState.densityMatrixSet c,
          (MState.abcSidePowerTraceRe (a := a) ψ.state.m σ τ
              ((alpha - 1) / alpha) : EReal)) =
      ⨆ τ ∈ MState.densityMatrixSet c,
        ⨅ σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b,
          (MState.abcSidePowerTraceRe (a := a) ψ.state.m σ τ
              ((alpha - 1) / alpha) : EReal) := by
  exact sandwichedAlpha_sion_abcSidePowerTraceRe_EReal
    (a := a) (b := b) (c := c)
    hdelta_pos hdelta_le ψ.state.psd halpha

/-- MState-domain form of the KW high-`alpha` Sion exchange.

The sigma side remains restricted to the compact full-support lower-bound
domain used by the already proved Sion theorem; the tau side is the ordinary
state domain. -/
theorem sandwichedAlpha_sion_uniformlyPositiveState_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : Ket ((a × b) × c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
        ⨆ τ : MState c,
          (MState.abcSidePowerTraceRe (a := a) ψ.state.m σ.val.m τ.m
              ((alpha - 1) / alpha) : EReal)) =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          (MState.abcSidePowerTraceRe (a := a) ψ.state.m σ.val.m τ.m
              ((alpha - 1) / alpha) : EReal) := by
  let F : CMatrix b → CMatrix c → EReal := fun σ τ =>
    (MState.abcSidePowerTraceRe (a := a) ψ.state.m σ τ ((alpha - 1) / alpha) :
      EReal)
  calc
    (⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
        ⨆ τ : MState c, F σ.val.m τ.m)
        =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : MState c, F σ τ.m := by
        exact uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf
          (fun σ => ⨆ τ : MState c, F σ τ.m)
    _ =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : CMatrix c, ⨆ hτ : τ ∈ MState.densityMatrixSet c, F σ τ := by
        simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ MState.densityMatrixSet c,
          ⨅ σ : CMatrix b,
            ⨅ hσ : σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b, F σ τ := by
        exact sandwichedAlpha_sion_abcSidePowerTraceRe_state_EReal
          (a := a) (b := b) (c := c) ψ hdelta_pos hdelta_le halpha
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ MState.densityMatrixSet c,
          ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
            F σ.val.m τ := by
        simp_rw [
          ← uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf]
    _ =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          F σ.val.m τ.m := by
        exact (state_iSup_matrix_eq_densityMatrixSet_iSup
          (fun τ => ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
            F σ.val.m τ)).symm

/-- Source-bracket form of the compact-domain Sion exchange in KW
`EA_capacity.tex:2020-2025`. -/
theorem sandwichedAlpha_sion_commonBracket_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : Ket ((a × b) × c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
        ⨆ τ : MState c,
          ((ψ.upwardRenyiDualityCommonBracket σ.val τ ((alpha - 1) / alpha)).re :
            EReal)) =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          ((ψ.upwardRenyiDualityCommonBracket σ.val τ ((alpha - 1) / alpha)).re :
            EReal) := by
  simpa [upwardRenyiDualityCommonBracket_re_eq_abcSidePowerTraceRe] using
    sandwichedAlpha_sion_uniformlyPositiveState_EReal
      (a := a) (b := b) (c := c) ψ hdelta_pos hdelta_le halpha

/-- Fixed-marginal source-bracket form of the compact-domain Sion exchange in
KW `EA_capacity.tex:2020-2025`. -/
theorem sandwichedAlpha_sion_mutualInformationBracket_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
        ⨆ τ : MState c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  let A : CMatrix a := CFC.rpow rhoA.m ((1 - alpha) / alpha)
  let F : CMatrix b → CMatrix c → EReal := fun σ τ =>
    (MState.abcWeightedSidePowerTraceRe (a := a) A ψ.state.m σ τ
      ((alpha - 1) / alpha) : EReal)
  have hA : A.PosSemidef :=
    cMatrix_rpow_posSemidef (A := rhoA.m) (s := (1 - alpha) / alpha) rhoA.psd
  calc
    (⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
        ⨆ τ : MState c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal))
        =
      ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
        ⨆ τ : MState c, F σ.val.m τ.m := by
        simp [sandwichedMutualInformationSionBracketRe, F, A]
    _ =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : MState c, F σ τ.m := by
        exact uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf
          (fun σ => ⨆ τ : MState c, F σ τ.m)
    _ =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : CMatrix c, ⨆ hτ : τ ∈ MState.densityMatrixSet c, F σ τ := by
        simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ MState.densityMatrixSet c,
          ⨅ σ : CMatrix b,
            ⨅ hσ : σ ∈ MState.uniformlyPositiveDensityMatrixSet delta b, F σ τ := by
        exact sandwichedAlpha_sion_abcWeightedSidePowerTraceRe_EReal
          (a := a) (b := b) (c := c) hdelta_pos hdelta_le hA ψ.state.psd halpha
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ MState.densityMatrixSet c,
          ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
            F σ.val.m τ := by
        simp_rw [
          ← uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf]
    _ =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          F σ.val.m τ.m := by
        exact (state_iSup_matrix_eq_densityMatrixSet_iSup
          (fun τ => ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
            F σ.val.m τ)).symm
    _ =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
        simp [sandwichedMutualInformationSionBracketRe, F, A]

/-- Full-rank state-domain Sion exchange for the KW sandwiched mutual
information bracket.

This is the state-language form of
`MState.fullRankDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal` and
matches the no-cutoff route in KW `EA_capacity.tex:2018-2035`. -/
theorem sandwichedAlpha_fullRank_sion_mutualInformationBracket_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    (⨅ σ : {σ : MState b // σ.m.PosDef},
        ⨆ τ : MState c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // σ.m.PosDef},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  let A : CMatrix a := CFC.rpow rhoA.m ((1 - alpha) / alpha)
  let F : CMatrix b → CMatrix c → EReal := fun sigma tau =>
    (MState.abcWeightedSidePowerTraceRe (a := a) A ψ.state.m sigma tau
      ((alpha - 1) / alpha) : EReal)
  have hA : A.PosSemidef :=
    cMatrix_rpow_posSemidef (A := rhoA.m) (s := (1 - alpha) / alpha) rhoA.psd
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  calc
    (⨅ σ : {σ : MState b // σ.m.PosDef},
        ⨆ τ : MState c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal))
        =
      ⨅ sigma : CMatrix b,
        ⨅ _hSigma : (MState.fullRankDensityMatrixSet b) sigma,
          ⨆ τ : MState c, F sigma τ.m := by
        exact fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
          (fun sigma => ⨆ τ : MState c, F sigma τ.m)
    _ =
      ⨅ sigma : CMatrix b,
        ⨅ _hSigma : (MState.fullRankDensityMatrixSet b) sigma,
          ⨆ tau : CMatrix c,
            ⨆ _hTau : (MState.densityMatrixSet c) tau, F sigma tau := by
        simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
        rfl
    _ =
      ⨆ tau : CMatrix c,
        ⨆ _hTau : (MState.densityMatrixSet c) tau,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : (MState.fullRankDensityMatrixSet b) sigma, F sigma tau := by
        exact MState.fullRankDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal
          (a := a) (b := b) (c := c) hA ψ.state.psd hp.1 (le_of_lt hp.2)
    _ =
      ⨆ τ : MState c,
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : (MState.fullRankDensityMatrixSet b) sigma, F sigma τ.m := by
        exact (state_iSup_matrix_eq_densityMatrixSet_iSup
          (fun tau => ⨅ sigma : CMatrix b,
            ⨅ _hSigma : (MState.fullRankDensityMatrixSet b) sigma, F sigma tau)).symm
    _ =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // σ.m.PosDef}, F σ.val.m τ.m := by
        apply iSup_congr
        intro τ
        exact (fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
          (fun sigma => F sigma τ.m)).symm
    _ =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // σ.m.PosDef},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
        simp [sandwichedMutualInformationSionBracketRe, F, A]

/-- Full-rank branch followed by the compact-domain Sion exchange.

KW first works on compact domains `delta • I ≤ sigma_B` and then removes the
regularization.  This lemma records the order direction that embeds the
uniformly-positive domain into the full-rank side-reference branch before
using `sandwichedAlpha_sion_mutualInformationBracket_EReal`. -/
theorem sandwichedAlpha_fullRank_iInf_iSup_le_uniformlyPositive_iSup_iInf
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : MState b // σ.m.PosDef},
        ⨆ τ : MState c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) ≤
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  calc
    (⨅ σ : {σ : MState b // σ.m.PosDef},
        ⨆ τ : MState c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal))
        ≤
      (⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
        ⨆ τ : MState c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) := by
        exact fullRankState_iInf_le_uniformlyPositiveState_iInf_EReal hdelta_pos
          (fun σ : MState b =>
            ⨆ τ : MState c,
              (sandwichedMutualInformationSionBracketRe rhoA ψ σ τ alpha : EReal))
    _ =
      ⨆ τ : MState c,
        ⨅ σ : {σ : MState b // delta • (1 : CMatrix b) ≤ σ.m},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) :=
        sandwichedAlpha_sion_mutualInformationBracket_EReal
          rhoA ψ hdelta_pos hdelta_le halpha

end

end Ket

namespace QIT
noncomputable section

universe u1 v1 u2 v2

/-- Every full-rank state belongs to some uniformly-positive compact Sion
domain with the source normalization bound `delta ≤ 1 / |B|`.

This is the local regularization bookkeeping used when the KW proof removes
the compact full-support cutoff after applying Sion: positive definiteness gives
a scalar lower spectral bound, and we shrink it if needed to meet the
`uniformlyPositiveDensityMatrixSet_nonempty` side condition. -/
theorem exists_uniformlyPositiveDensityMatrixSet_mem_of_posDef
    {b : Type v1} [Fintype b] [DecidableEq b]
    (σ : MState b) (hσ : σ.m.PosDef) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹ ∧
      σ.m ∈ MState.uniformlyPositiveDensityMatrixSet delta b := by
  classical
  have : Nonempty b := σ.nonempty
  rcases σ.exists_pos_scalar_smul_one_le_matrix_of_posDef hσ with ⟨c, hc_pos, hc_le⟩
  have hcard_pos : 0 < (Fintype.card b : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty b›
  let delta : ℝ := min (c / 2) ((Fintype.card b : ℝ)⁻¹)
  have hdelta_pos : 0 < delta := by
    exact lt_min (half_pos hc_pos) (inv_pos.mpr hcard_pos)
  have hdelta_le_card : delta ≤ (Fintype.card b : ℝ)⁻¹ := by
    exact min_le_right _ _
  have hdelta_le_c : delta ≤ c := by
    exact (min_le_left _ _).trans (by linarith)
  have hdelta_one_le_c_one :
      delta • (1 : CMatrix b) ≤ c • (1 : CMatrix b) := by
    rw [Matrix.le_iff]
    rw [← sub_smul]
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (sub_nonneg.mpr hdelta_le_c)
  refine ⟨delta, hdelta_pos, hdelta_le_card, ?_⟩
  exact ⟨MState.state_matrix_mem_densityMatrixSet σ, hdelta_one_le_c_one.trans hc_le⟩

/-- Pointwise removal of the compact uniformly-positive cutoff.

For a fixed objective over side states, optimizing over all full-rank states is
the same as first imposing a source-valid cutoff `delta • I ≤ sigma` and then
letting `delta` range over all positive values allowed by the Sion compactness
side condition.  This is the order-theoretic core of the KW `delta downarrow 0`
step before any supremum over the purifying side is considered. -/
theorem fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal
    {b : Type v1} [Fintype b] [DecidableEq b] (f : MState b → EReal) :
    (⨅ σ : {σ : MState b // σ.m.PosDef}, f σ.val) =
      ⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
        ⨅ σ : {σ : MState b // delta.val • (1 : CMatrix b) ≤ σ.m}, f σ.val := by
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro delta
    exact fullRankState_iInf_le_uniformlyPositiveState_iInf_EReal delta.property.1 f
  · refine le_iInf ?_
    intro σ
    rcases exists_uniformlyPositiveDensityMatrixSet_mem_of_posDef σ.val σ.property with
      ⟨delta, hdelta_pos, hdelta_le, hσmem⟩
    have hleft :
        (⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
          ⨅ τ : {τ : MState b // delta.val • (1 : CMatrix b) ≤ τ.m}, f τ.val) ≤
          ⨅ τ : {τ : MState b // delta • (1 : CMatrix b) ≤ τ.m}, f τ.val :=
      iInf_le
        (fun delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹} =>
          ⨅ τ : {τ : MState b // delta.val • (1 : CMatrix b) ≤ τ.m}, f τ.val)
        ⟨delta, hdelta_pos, hdelta_le⟩
    have hright :
        (⨅ τ : {τ : MState b // delta • (1 : CMatrix b) ≤ τ.m}, f τ.val) ≤
          f σ.val :=
      iInf_le
        (fun τ : {τ : MState b // delta • (1 : CMatrix b) ≤ τ.m} => f τ.val)
        ⟨σ.val, hσmem.2⟩
    exact hleft.trans hright

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u1 v1 u2 v2

/-- Fixed-`tau_C` specialization of the pointwise `delta downarrow 0` removal
for the KW Sion bracket.

This is the exact statement obtained by applying
`fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal` to the source
bracket.  It is pointwise in `tau_C`; moving the cutoff removal through the
`tau_C` supremum is a separate step of the reverse alternate-expression
argument. -/
theorem sandwichedMutualInformationSionBracketRe_fullRank_iInf_eq_iInf_uniformlyPositive
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τ : MState c) {alpha : ℝ} :
    (⨅ σ : {σ : MState b // σ.m.PosDef},
        (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) =
      ⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
        ⨅ σ : {σ : MState b // delta.val • (1 : CMatrix b) ≤ σ.m},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  simpa using
    fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal
      (b := b)
      (fun σ : MState b =>
        (sandwichedMutualInformationSionBracketRe rhoA ψ σ τ alpha : EReal))

/-- Logarithmic fixed-`tau_C` form of the pointwise `delta downarrow 0`
removal for the KW Sion bracket. -/
theorem sandwichedMutualInformationSionBracketLog_fullRank_iInf_eq_iInf_uniformlyPositive
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τ : MState c) {alpha : ℝ} :
    (⨅ σ : {σ : MState b // σ.m.PosDef},
        ((alpha / (alpha - 1) *
          log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha) : ℝ) :
          EReal)) =
      ⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
        ⨅ σ : {σ : MState b // delta.val • (1 : CMatrix b) ≤ σ.m},
          ((alpha / (alpha - 1) *
            log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha) : ℝ) :
            EReal) := by
  simpa using
    fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal
      (b := b)
      (fun σ : MState b =>
        ((alpha / (alpha - 1) *
          log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σ τ alpha) : ℝ) :
          EReal))

end

end Ket

namespace QIT
noncomputable section

universe u1 v1 u2 v2

/-- Doubling the two-sided sandwich exponent gives the one-sided exponent in
the trace-bracket expression of KW `eq-sand_rel_mut_inf_alt`. -/
theorem sandwichedSideWeightExponent_two_mul
    {alpha : ℝ} (halpha : 1 < alpha) :
    2 * ((1 - alpha) / (2 * alpha)) = (1 - alpha) / alpha := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  field_simp [ne_of_gt halpha_pos]

/-- In the channel alternate expression, multiplying the polar-decomposition
factor `tau_R^(1/2)` by the source sandwich `tau_R^((1-alpha)/(2alpha))`
leaves the CB-norm input exponent `1/(2alpha)`. -/
theorem sandwichedPolarInputExponent_add
    {alpha : ℝ} (halpha : 1 < alpha) :
    (1 - alpha) / (2 * alpha) + 1 / 2 = 1 / (2 * alpha) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  field_simp [ne_of_gt halpha_pos]
  all_goals ring

/-- The Sion parameter in the source proof is the negative of the high-alpha
side-information exponent. -/
theorem sandwichedAlphaPrime_eq_neg_sideExponent
    {alpha : ℝ} (_halpha : 1 < alpha) :
    (alpha - 1) / alpha = -((1 - alpha) / alpha) := by
  have hnum : alpha - 1 = -(1 - alpha) := by ring
  rw [hnum, neg_div]

/-- The high-alpha side-information exponent belongs to the operator-convexity
interval `[-1,0]`; this is the scalar side condition for
`sigma_B ↦ sigma_B^((1-alpha)/alpha)` in KW `EA_capacity.tex:2032-2039`. -/
theorem sandwichedSideExponent_mem_Icc_neg_one_zero
    {alpha : ℝ} (halpha : 1 < alpha) :
    (1 - alpha) / alpha ∈ Set.Icc (-1 : ℝ) 0 := by
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  have hside : (1 - alpha) / alpha = -((alpha - 1) / alpha) := by
    ring_nf
  rw [hside]
  exact ⟨by linarith [hp.2], by linarith [hp.1]⟩

/-- The Schatten exponent in the state alternate expression,
`alpha / (2 * alpha - 1)`, lies in `(0, 1)` for `alpha > 1`. -/
theorem sandwichedAlternateSchattenExponent_pos_lt_one
    {alpha : ℝ} (halpha : 1 < alpha) :
    0 < alpha / (2 * alpha - 1) ∧ alpha / (2 * alpha - 1) < 1 := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hden_pos : 0 < 2 * alpha - 1 := by linarith
  exact ⟨div_pos halpha_pos hden_pos, by
    rw [div_lt_one hden_pos]
    linarith⟩

/-- Reverse-Holder exponent conversion used at the last line of
`eq-sand_rel_mut_inf_alt`: for
`p = alpha / (2 * alpha - 1)`, the exponent `1 - 1 / p` is
`(1 - alpha) / alpha`. -/
theorem sandwichedAlternate_reverseHolderExponent
    {alpha : ℝ} (halpha : 1 < alpha) :
    1 - 1 / (alpha / (2 * alpha - 1)) = (1 - alpha) / alpha := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hden_ne : 2 * alpha - 1 ≠ 0 := by linarith
  field_simp [ne_of_gt halpha_pos, hden_ne]
  all_goals ring_nf

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u1 v1 u2 v2

/-- Each supported side-information state gives a reverse-Holder objective
value for the KW `AC` trace matrix. -/
theorem sandwichedMutualInformationSionBracketRe_mem_reverseHolderStateValueSet
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c) {alpha : ℝ} (halpha : 1 < alpha)
    (hSupport :
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.m) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ∈
      psdTraceReverseHolderStateValueSet
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (alpha / (2 * alpha - 1)) := by
  refine ⟨σB.m, σB.psd, ?_, hSupport, ?_⟩
  · simp
  · rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
    rw [sandwichedAlternate_reverseHolderExponent halpha]

/-- Reverse-Holder lower-bound direction for a fixed supported `σ_B` in the
KW Sion bracket. -/
theorem psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c) {alpha : ℝ} (halpha : 1 < alpha)
    (hSupport :
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.m) :
    psdSchattenPNorm
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
        (sandwichedAlternateSchattenOrder halpha) ≤
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha
  let hM : M.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha
  have hp := sandwichedAlternateSchattenExponent_pos_lt_one halpha
  have hx :
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ∈
        psdTraceReverseHolderStateValueSet M (alpha / (2 * alpha - 1)) := by
    simpa [M] using
      sandwichedMutualInformationSionBracketRe_mem_reverseHolderStateValueSet
        rhoA ψ σB τC halpha hSupport
  exact
    (psdTraceReverseHolderStateValueSet_lowerBound
      (M := M) hM hp.1 hp.2) hx

/-- Logarithmic form of the reverse-Holder lower-bound direction used after
the Sion exchange in KW `EA_capacity.tex:2030-2035`.

The previous theorem gives the norm inequality.  This lemma performs only the
source scalar step: `log2` monotonicity and multiplication by the positive
coefficient `alpha / (alpha - 1)`. -/
theorem sandwichedACTraceMatrixLog_le_SionBracketLog_of_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c)
    (hrhoA : rhoA.m.PosDef) (hτC : τC.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hSupport :
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.m) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
            (sandwichedAlternateSchattenOrder halpha)) ≤
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha
  let hM : M.PosSemidef := sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha
  have hnorm_le :
      psdSchattenPNorm M hM (sandwichedAlternateSchattenOrder halpha) ≤
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha := by
    simpa [M, hM] using
      psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
        rhoA ψ σB τC halpha hSupport
  have hnorm_pos :
      0 < psdSchattenPNorm M hM (sandwichedAlternateSchattenOrder halpha) := by
    simpa [M, hM] using
      psdSchattenPNorm_ACTraceMatrix_pos_posDef rhoA ψ τC hrhoA hτC halpha
  have hlog :
      log2 (psdSchattenPNorm M hM (sandwichedAlternateSchattenOrder halpha)) ≤
        log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
    unfold log2
    exact div_le_div_of_nonneg_right (Real.log_le_log hnorm_pos hnorm_le)
      (le_of_lt (Real.log_pos one_lt_two))
  exact mul_le_mul_of_nonneg_left hlog (le_of_lt (highAlpha_conjExponent_pos halpha))

/-- Full-rank side-information specialization of
`sandwichedACTraceMatrixLog_le_SionBracketLog_of_support`.

This is the form needed on the full-rank `sigma_B` branch of the KW
alternate-expression proof. -/
theorem sandwichedACTraceMatrixLog_le_SionBracketLog_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (σB : MState b) (τC : MState c)
    (hrhoA : rhoA.m.PosDef) (hσB : σB.m.PosDef)
    (hτC : τC.m.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
            (sandwichedAlternateSchattenOrder halpha)) ≤
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) :=
  sandwichedACTraceMatrixLog_le_SionBracketLog_of_support
    rhoA ψ σB τC hrhoA hτC halpha
    (Matrix.Supports.of_right_posDef _ _ hσB)

/-- Reverse-Holder lower bound after optimizing over full-rank `sigma_B`.

This is the `inf_{sigma_B}` form of
`sandwichedACTraceMatrixLog_le_SionBracketLog_posDef`, matching the order in
KW immediately after the Sion exchange. -/
theorem sandwichedACTraceMatrixLog_le_fullRankSionBracketLog_iInf
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty b] [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) (hrhoA : rhoA.m.PosDef) (hτC : τC.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
            (sandwichedAlternateSchattenOrder halpha)) ≤
      sInf (Set.range fun σB : {σ : MState b // σ.m.PosDef} =>
        alpha / (alpha - 1) *
          log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) := by
  have : Nonempty {σ : MState b // σ.m.PosDef} :=
    ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  refine le_csInf (Set.range_nonempty _) ?_
  rintro y ⟨σB, rfl⟩
  exact sandwichedACTraceMatrixLog_le_SionBracketLog_posDef
    rhoA ψ σB.1 τC hrhoA σB.2 hτC halpha

/-- Reverse-Holder optimizer as a genuine side-information state for a nonzero
KW `AC` trace matrix. -/
theorem exists_state_SionBracketRe_eq_psdSchattenPNorm_of_ACTraceMatrix_ne_zero
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) {alpha : ℝ} (halpha : 1 < alpha)
    (hMne : sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha ≠ 0) :
    ∃ σB : MState b,
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.m ∧
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
          (sandwichedAlternateSchattenOrder halpha) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha
  let hM : M.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha
  have hp := sandwichedAlternateSchattenExponent_pos_lt_one halpha
  have hMne' : M ≠ 0 := by simpa [M] using hMne
  have hpower_pos : 0 < psdTracePower M hM (alpha / (2 * alpha - 1)) :=
    psdTracePower_pos_of_ne_zero M hM hMne'
  rcases exists_psdTraceReverseHolder_sideState_attaining
      (M := M) hM hp.1 hpower_pos with
    ⟨N, hN, hNtr, hSupport, hattain⟩
  have hNtrace : N.trace = 1 := by
    apply Complex.ext
    · simpa using hNtr
    · simpa using (Matrix.PosSemidef.trace_nonneg hN).2.symm
  have hattain' :
      psdSchattenPNorm M hM (sandwichedAlternateSchattenOrder halpha) =
        (M * CFC.rpow N ((1 - alpha) / alpha)).trace.re := by
    rw [sandwichedAlternate_reverseHolderExponent halpha] at hattain
    exact hattain
  let σB : MState b := .ofMatrix (matrix := N) (pos := hN) (trace_eq_one := hNtrace)
  refine ⟨σB, ?_, ?_⟩
  · simpa [σB, M] using hSupport
  · rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
    simpa [σB, M, hM] using hattain'.symm

/-- Exact reverse-Holder `sInf` formula for the KW Sion bracket on the
support-restricted side-state domain.

This is the formal counterpart of the last transition in
`EA_capacity.tex:2030-2035` after the `AC` trace matrix has been identified as
positive semidefinite. -/
theorem sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (ψ : Ket ((a × b) × c))
    (τC : MState c) {alpha : ℝ} (halpha : 1 < alpha)
    (hMne : sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha ≠ 0) :
    sInf (Set.range fun σB :
        {σ : MState b //
          Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            σ.m} =>
      sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
          (sandwichedAlternateSchattenOrder halpha) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha
  let hM : M.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha
  let target : ℝ :=
    psdSchattenPNorm M hM (sandwichedAlternateSchattenOrder halpha)
  let S : Set ℝ := Set.range fun σB :
      {σ : MState b // Matrix.Supports M σ.m} =>
    sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha
  rcases exists_state_SionBracketRe_eq_psdSchattenPNorm_of_ACTraceMatrix_ne_zero
      rhoA ψ τC halpha hMne with
    ⟨σ0, hσ0Support, hσ0⟩
  have hmem : target ∈ S := by
    refine ⟨⟨σ0, ?_⟩, ?_⟩
    · simpa [M] using hσ0Support
    · simpa [S, target, M, hM] using hσ0
  have hLower : target ∈ lowerBounds S := by
    intro y hy
    rcases hy with ⟨σB, rfl⟩
    exact psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
      rhoA ψ σB.1 τC halpha (by simpa [M] using σB.2)
  have hBdd : BddBelow S := ⟨target, hLower⟩
  apply le_antisymm
  · exact csInf_le hBdd hmem
  · exact le_csInf (Set.nonempty_of_mem hmem) hLower

/-- Zero-`AC` branch of the exact reverse-Holder `sInf` formula for the KW
Sion bracket. -/
theorem sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm_zero
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (psi : Ket ((a × b) × c))
    (tauC : MState c) {alpha : ℝ} (halpha : 1 < alpha)
    (hMzero : sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha = 0) :
    sInf (Set.range fun sigmaB :
        {sigma : MState b //
          Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            sigma.m} =>
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
          (sandwichedAlternateSchattenOrder halpha) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha
  let hM : M.PosSemidef := sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha
  let target : ℝ :=
    psdSchattenPNorm M hM (sandwichedAlternateSchattenOrder halpha)
  let S : Set ℝ := Set.range fun sigmaB :
      {sigma : MState b // Matrix.Supports M sigma.m} =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  have hMzero' : M = 0 := by
    simpa [M] using hMzero
  have htarget : target = 0 := by
    have hp := sandwichedAlternateSchattenExponent_pos_lt_one halpha
    have hcongr :
        psdSchattenPNorm M hM (sandwichedAlternateSchattenOrder halpha) =
          psdSchattenPNorm (0 : CMatrix b) Matrix.PosSemidef.zero
            (sandwichedAlternateSchattenOrder halpha) :=
      psdSchattenPNorm_congr hMzero' hM Matrix.PosSemidef.zero
        (sandwichedAlternateSchattenOrder halpha)
    change psdSchattenPNorm M hM (sandwichedAlternateSchattenOrder halpha) = 0
    rw [hcongr]
    exact psdSchattenPNorm_zero (sandwichedAlternateSchattenOrder halpha)
  have hvalue :
      ∀ sigmaB : {sigma : MState b // Matrix.Supports M sigma.m},
        sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha = 0 := by
    intro sigmaB
    rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
    simp [M, hMzero']
  let sigma0 : {sigma : MState b // Matrix.Supports M sigma.m} :=
    ⟨(MState.uniform : MState b), by
      intro v hv
      simp [M, hMzero']⟩
  have hmem : (0 : ℝ) ∈ S := by
    refine ⟨sigma0, ?_⟩
    exact hvalue sigma0
  have hLower : (0 : ℝ) ∈ lowerBounds S := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    change (0 : ℝ) ≤
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
    rw [hvalue sigmaB]
  have hS : sInf S = 0 := by
    apply le_antisymm
    · exact csInf_le ⟨0, hLower⟩ hmem
    · exact le_csInf (Set.nonempty_of_mem hmem) hLower
  change sInf S = target
  rw [hS, htarget]

/-- Exact reverse-Holder `sInf` formula for the KW Sion bracket on the
support-restricted side-state domain, including both the nonzero and zero
`AC` trace-matrix branches. -/
theorem sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm_all
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (psi : Ket ((a × b) × c))
    (tauC : MState c) {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun sigmaB :
        {sigma : MState b //
          Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            sigma.m} =>
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
          (sandwichedAlternateSchattenOrder halpha) := by
  by_cases hMne : sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha ≠ 0
  · exact sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm
      rhoA psi tauC halpha hMne
  · exact sandwichedMutualInformationSionBracketRe_supported_sInf_eq_psdSchattenPNorm_zero
      rhoA psi tauC halpha (not_ne_iff.mp hMne)

/-- Exact reverse-Holder `sInf` formula after closing the full-rank side-state
regularization.

This upgrades `sandwichedMutualInformationSionBracketRe_supported_sInf_eq_...`
from the support-restricted reverse-Holder domain to the full-rank state domain
appearing just before and after the Sion exchange in KW
`EA_capacity.tex:2020-2035`.  The nonzero branch uses the support-aware
identity regularization lemma from `QIT.States.Schatten`; the zero branch is
immediate from the trace form of the bracket. -/
theorem sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (psi : Ket ((a × b) × c))
    (tauC : MState c) {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun sigmaB : {sigma : MState b // sigma.m.PosDef} =>
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
          (sandwichedAlternateSchattenOrder halpha) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha
  let hM : M.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha
  let p : SchattenOrder := sandwichedAlternateSchattenOrder halpha
  let r : ℝ := (1 - alpha) / alpha
  let target : ℝ := psdSchattenPNorm M hM p
  let S := {sigma : MState b // sigma.m.PosDef}
  let f : S → ℝ := fun sigmaB =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have hLower : target ∈ lowerBounds (Set.range f) := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    simpa [target, p, f, M, hM] using
      psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
        rhoA psi sigmaB.1 tauC halpha
        (Matrix.Supports.of_right_posDef M sigmaB.1.m sigmaB.2)
  have hBdd : BddBelow (Set.range f) := ⟨target, hLower⟩
  change sInf (Set.range f) = target
  by_cases hMzero : M = 0
  · have hvalue (sigmaB : S) : f sigmaB = 0 := by
      change sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha = 0
      rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
      simp [M, hMzero]
    have htarget : target = 0 := by
      calc
        target = psdSchattenPNorm (0 : CMatrix b) Matrix.PosSemidef.zero p := by
          exact psdSchattenPNorm_congr hMzero hM Matrix.PosSemidef.zero p
        _ = 0 := psdSchattenPNorm_zero p
    apply le_antisymm
    · rw [htarget]
      exact csInf_le hBdd ⟨Classical.choice inferInstance, hvalue (Classical.choice inferInstance)⟩
    · exact le_csInf (Set.range_nonempty f) hLower
  · have hMne : M ≠ 0 := hMzero
    rcases exists_state_SionBracketRe_eq_psdSchattenPNorm_of_ACTraceMatrix_ne_zero
        rhoA psi tauC halpha (by simpa [M] using hMne) with
      ⟨sigma0, hSupport0, hsigma0⟩
    let N0 : CMatrix b := sigma0.m
    have hN0 : N0.PosSemidef := sigma0.psd
    have hN0trace : N0.trace = 1 := sigma0.tr'
    have hN0trace_re : N0.trace.re = 1 := by
      simp [N0]
    have htrace_target :
        ((M * CFC.rpow N0 r).trace).re = target := by
      have h := hsigma0
      rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma] at h
      simpa [M, N0, r, target, p, hM] using h
    let raw : ℝ → ℝ := fun eps =>
      ((M * CFC.rpow (N0 + eps • (1 : CMatrix b)) r).trace).re
    let scale : ℝ → ℝ := fun eps =>
      ((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹
    let reg : ℝ → CMatrix b := fun eps =>
      scale eps • (N0 + eps • (1 : CMatrix b))
    have hraw :
        Filter.Tendsto raw (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds target) := by
      have h :=
        trace_mul_cMatrix_rpow_add_pos_smul_one_tendsto_of_support
          hN0 (by simpa [M, N0] using hSupport0) r
      have h' :
          Filter.Tendsto raw (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds ((M * CFC.rpow N0 r).trace.re)) := by
        simpa [raw, M, N0] using h
      rw [← htrace_target]
      exact h'
    have htraceScale :
        Filter.Tendsto scale (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
      have htrace :
          Filter.Tendsto (fun eps : ℝ => (N0 + eps • (1 : CMatrix b)).trace.re)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
        have hcont : Continuous fun eps : ℝ =>
            (N0 + eps • (1 : CMatrix b)).trace.re := by
          fun_prop
        have hlim := (hcont.tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
        simpa [N0, hN0trace_re] using hlim
      simpa [scale] using htrace.inv₀ one_ne_zero
    have hscalePow :
        Filter.Tendsto (fun eps : ℝ => scale eps ^ r)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 : ℝ)) := by
      have hpow :=
        (Real.continuousAt_rpow_const (1 : ℝ) r (Or.inl one_ne_zero)).tendsto.comp
          htraceScale
      simpa [Function.comp_def] using hpow
    have hregValue :
        Filter.Tendsto
          (fun eps : ℝ => ((M * CFC.rpow (reg eps) r).trace).re)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds target) := by
      have heq :
          (fun eps : ℝ => ((M * CFC.rpow (reg eps) r).trace).re)
            =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          fun eps : ℝ => scale eps ^ r * raw eps := by
        filter_upwards [self_mem_nhdsWithin] with eps heps
        have hBpos : (N0 + eps • (1 : CMatrix b)).PosDef :=
          MState.cMatrix_posSemidef_add_pos_smul_one_posDef hN0 heps
        have hscale_pos : 0 < scale eps := by
          have htr_pos : 0 < (N0 + eps • (1 : CMatrix b)).trace.re := by
            exact (Matrix.PosDef.trace_pos hBpos).1
          exact inv_pos.mpr htr_pos
        have hpow :
            CFC.rpow (reg eps) r =
              (scale eps ^ r : ℝ) •
                CFC.rpow (N0 + eps • (1 : CMatrix b)) r := by
          simpa [reg] using
            cMatrix_rpow_real_smul_posSemidef_schatten hBpos.posSemidef
              (le_of_lt hscale_pos) (s := r)
        change ((M * CFC.rpow (reg eps) r).trace).re = scale eps ^ r * raw eps
        rw [hpow]
        simp [raw, Matrix.trace_smul, Complex.real_smul]
      have hprod :
          Filter.Tendsto (fun eps : ℝ => scale eps ^ r * raw eps)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds target) := by
        simpa using hscalePow.mul hraw
      exact hprod.congr' heq.symm
    have hupper : sInf (Set.range f) ≤ target := by
      exact ge_of_tendsto hregValue (by
        filter_upwards [self_mem_nhdsWithin] with eps heps
        have hBpos : (N0 + eps • (1 : CMatrix b)).PosDef :=
          MState.cMatrix_posSemidef_add_pos_smul_one_posDef hN0 heps
        have htr_pos : 0 < (N0 + eps • (1 : CMatrix b)).trace.re := by
          exact (Matrix.PosDef.trace_pos hBpos).1
        have hscale_pos : 0 < scale eps := inv_pos.mpr htr_pos
        have hreg_pos : (reg eps).PosDef := by
          simpa [reg] using Matrix.PosDef.smul hBpos hscale_pos
        have hreg_trace : (reg eps).trace = 1 := by
          have htr_real :
              (N0 + eps • (1 : CMatrix b)).trace =
                ((N0 + eps • (1 : CMatrix b)).trace.re : ℂ) := by
            exact posSemidef_trace_eq_re_coe hBpos.posSemidef
          have htr_ne : (N0 + eps • (1 : CMatrix b)).trace.re ≠ 0 :=
            ne_of_gt htr_pos
          calc
            (reg eps).trace =
                (scale eps : ℂ) * (N0 + eps • (1 : CMatrix b)).trace := by
                  change (scale eps • (N0 + eps • (1 : CMatrix b))).trace =
                    (scale eps : ℂ) * (N0 + eps • (1 : CMatrix b)).trace
                  rw [Matrix.trace_smul]
                  simpa using (Complex.real_smul (x := scale eps)
                    (z := (N0 + eps • (1 : CMatrix b)).trace))
            _ = (scale eps : ℂ) *
                ((N0 + eps • (1 : CMatrix b)).trace.re : ℂ) := by
                  exact congrArg (fun z : ℂ => (scale eps : ℂ) * z) htr_real
            _ = 1 := by
                  have htr_ne_complex :
                      ((N0 + eps • (1 : CMatrix b)).trace.re : ℂ) ≠ 0 := by
                    exact_mod_cast htr_ne
                  have hscale_eq :
                      (scale eps : ℂ) =
                        ((((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹ : ℝ) : ℂ) := by
                    change ((((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹ : ℝ) : ℂ) =
                      ((((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹ : ℝ) : ℂ)
                    rfl
                  rw [hscale_eq]
                  simpa using inv_mul_cancel₀ htr_ne_complex
        let sigmaReg : MState b :=
          .ofMatrix (matrix := reg eps) (pos := hreg_pos.posSemidef) (trace_eq_one := hreg_trace)
        have hsigmaReg : sigmaReg.m.PosDef := by
          simp only [sigmaReg, MState.matrix_ofMatrix]
          exact hreg_pos
        have hmem :
            ((M * CFC.rpow (reg eps) r).trace).re ∈ Set.range f := by
          refine ⟨⟨sigmaReg, hsigmaReg⟩, ?_⟩
          change sandwichedMutualInformationSionBracketRe rhoA psi sigmaReg tauC alpha =
            ((M * CFC.rpow (reg eps) r).trace).re
          simpa [sigmaReg, M, r] using
            sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma
              rhoA psi sigmaReg tauC alpha
        exact csInf_le hBdd hmem)
    have hlower : target ≤ sInf (Set.range f) :=
      le_csInf (Set.range_nonempty f) hLower
    exact le_antisymm hupper hlower

/-- Fixed-`tau_C` logarithmic form of the KW reverse-Holder infimum after
closing the full-rank side-state regularization.

This is the post-Sion rewrite target in `EA_capacity.tex:2028-2035`: once the
`sigma_B` infimum has been exchanged past the `tau_C` supremum, the full-rank
infimum of the logarithmic Sion bracket is exactly the logarithmic Schatten
`AC` trace-matrix expression. -/
theorem sandwichedMutualInformationSionBracketLog_fullRank_sInf_eq_ACTraceMatrixLog
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (psi : Ket ((a × b) × c))
    (tauC : MState c) (hrhoA : rhoA.m.PosDef) (htauC : tauC.m.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sInf (Set.range fun sigmaB : {sigma : MState b // sigma.m.PosDef} =>
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha)) =
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
            (sandwichedAlternateSchattenOrder halpha)) := by
  let S := {sigma : MState b // sigma.m.PosDef}
  let raw : S → ℝ := fun sigmaB =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let target : ℝ :=
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
      (sandwichedAlternateSchattenOrder halpha)
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have hraw_sInf : sInf (Set.range raw) = target := by
    simpa [S, raw, target] using
      sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
        rhoA psi tauC halpha
  have htarget_lower : target ∈ lowerBounds (Set.range raw) := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    simpa [raw, target] using
      psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
        rhoA psi sigmaB.1 tauC halpha
        (Matrix.Supports.of_right_posDef
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          sigmaB.1.m sigmaB.2)
  have hraw_bdd : BddBelow (Set.range raw) := ⟨target, htarget_lower⟩
  have htarget_pos : 0 < target := by
    simpa [target] using
      psdSchattenPNorm_ACTraceMatrix_pos_posDef rhoA psi tauC hrhoA htauC halpha
  have hinf_pos : 0 < sInf (Set.range raw) := by
    rw [hraw_sInf]
    exact htarget_pos
  have hlog_sInf :
      sInf (Set.range fun sigmaB : S => log2 (raw sigmaB)) = log2 target := by
    have himage :
        Set.range (fun sigmaB : S => log2 (raw sigmaB)) =
          log2 '' Set.range raw := by
      ext x
      constructor
      · rintro ⟨sigmaB, rfl⟩
        exact ⟨raw sigmaB, ⟨sigmaB, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨sigmaB, rfl⟩, rfl⟩
        exact ⟨sigmaB, rfl⟩
    rw [himage, real_log2_sInf_image_eq (Set.range_nonempty raw) hraw_bdd hinf_pos,
      hraw_sInf]
  have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
    simpa [coeff] using highAlpha_conjExponent_pos halpha)
  have hscaled :
      sInf (Set.range fun sigmaB : S => coeff * log2 (raw sigmaB)) =
        coeff * log2 target := by
    let logs : S → ℝ := fun sigmaB => log2 (raw sigmaB)
    have himage :
        Set.range (fun sigmaB : S => coeff * logs sigmaB) =
          (fun x : ℝ => coeff * x) '' Set.range logs := by
      ext x
      constructor
      · rintro ⟨sigmaB, rfl⟩
        exact ⟨logs sigmaB, ⟨sigmaB, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨sigmaB, rfl⟩, rfl⟩
        exact ⟨sigmaB, rfl⟩
    have hsmul : (fun x : ℝ => coeff * x) '' Set.range logs =
        coeff • Set.range logs := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨y, hy, by rw [smul_eq_mul]⟩
      · intro hx
        rcases Set.mem_smul_set.mp hx with ⟨y, hy, hxy⟩
        exact ⟨y, hy, by simpa [smul_eq_mul] using hxy⟩
    calc
      sInf (Set.range fun sigmaB : S => coeff * log2 (raw sigmaB)) =
          sInf ((fun x : ℝ => coeff * x) '' Set.range logs) := by
            rw [himage]
      _ = sInf (coeff • Set.range logs) := by
            rw [hsmul]
      _ = coeff * sInf (Set.range logs) := by
            rw [Real.sInf_smul_of_nonneg hcoeff_nonneg]
            simp [smul_eq_mul]
      _ = coeff * log2 target := by
            rw [hlog_sInf]
  simpa [S, raw, coeff, target] using hscaled

/-- Fixed-`tau_C` logarithmic reverse-Holder formula when the KW `AC` trace
matrix is nonzero.

This is the same post-Sion reverse-Holder step as
`sandwichedMutualInformationSionBracketLog_fullRank_sInf_eq_ACTraceMatrixLog`,
but it records the actual logarithm side condition: strict positivity of the
Schatten expression follows from a nonzero PSD `AC` trace matrix.  It is the
form needed before the full-rank `tau_C` closure, where singular states are
approximated by full-rank regularizations. -/
theorem sandwichedMutualInformationSionBracketLog_fullRank_sInf_eq_ACTraceMatrixLog_of_ne_zero
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : MState a) (psi : Ket ((a × b) × c))
    (tauC : MState c) {alpha : ℝ} (halpha : 1 < alpha)
    (hMne : sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha ≠ 0) :
    sInf (Set.range fun sigmaB : {sigma : MState b // sigma.m.PosDef} =>
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha)) =
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
            (sandwichedAlternateSchattenOrder halpha)) := by
  let S := {sigma : MState b // sigma.m.PosDef}
  let raw : S → ℝ := fun sigmaB =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let target : ℝ :=
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
      (sandwichedAlternateSchattenOrder halpha)
  have : Nonempty S := ⟨⟨(MState.uniform : MState b), MState.uniform_posDef⟩⟩
  have hraw_sInf : sInf (Set.range raw) = target := by
    simpa [S, raw, target] using
      sandwichedMutualInformationSionBracketRe_fullRank_sInf_eq_psdSchattenPNorm
        rhoA psi tauC halpha
  have htarget_lower : target ∈ lowerBounds (Set.range raw) := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    simpa [raw, target] using
      psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
        rhoA psi sigmaB.1 tauC halpha
        (Matrix.Supports.of_right_posDef
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          sigmaB.1.m sigmaB.2)
  have hraw_bdd : BddBelow (Set.range raw) := ⟨target, htarget_lower⟩
  have htarget_pos : 0 < target := by
    convert
      psdSchattenPNorm_pos_of_ne_zero
        (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
        (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
        (p := sandwichedAlternateSchattenOrder halpha)
        hMne using 1
  have hinf_pos : 0 < sInf (Set.range raw) := by
    rw [hraw_sInf]
    exact htarget_pos
  have hlog_sInf :
      sInf (Set.range fun sigmaB : S => log2 (raw sigmaB)) = log2 target := by
    have himage :
        Set.range (fun sigmaB : S => log2 (raw sigmaB)) =
          log2 '' Set.range raw := by
      ext x
      constructor
      · rintro ⟨sigmaB, rfl⟩
        exact ⟨raw sigmaB, ⟨sigmaB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨sigmaB, rfl⟩, rfl⟩
        exact ⟨sigmaB, rfl⟩
    rw [himage, real_log2_sInf_image_eq (Set.range_nonempty raw) hraw_bdd hinf_pos,
      hraw_sInf]
  have hcoeff_nonneg : 0 ≤ coeff := le_of_lt (by
    simpa [coeff] using highAlpha_conjExponent_pos halpha)
  have hscaled :
      sInf (Set.range fun sigmaB : S => coeff * log2 (raw sigmaB)) =
        coeff * log2 target := by
    let logs : S → ℝ := fun sigmaB => log2 (raw sigmaB)
    have himage :
        Set.range (fun sigmaB : S => coeff * logs sigmaB) =
          (fun x : ℝ => coeff * x) '' Set.range logs := by
      ext x
      constructor
      · rintro ⟨sigmaB, rfl⟩
        exact ⟨logs sigmaB, ⟨sigmaB, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨sigmaB, rfl⟩, rfl⟩
        exact ⟨sigmaB, rfl⟩
    have hsmul : (fun x : ℝ => coeff * x) '' Set.range logs =
        coeff • Set.range logs := by
      ext x
      constructor
      · rintro ⟨_, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨_, hy, by rw [smul_eq_mul]⟩
      · intro hx
        rcases Set.mem_smul_set.mp hx with ⟨_, hy, hxy⟩
        exact ⟨_, hy, by simpa [smul_eq_mul] using hxy⟩
    calc
      sInf (Set.range fun sigmaB : S => coeff * log2 (raw sigmaB)) =
          sInf ((fun x : ℝ => coeff * x) '' Set.range logs) := by
            rw [himage]
      _ = sInf (coeff • Set.range logs) := by
            rw [hsmul]
      _ = coeff * sInf (Set.range logs) := by
            rw [Real.sInf_smul_of_nonneg hcoeff_nonneg]
            simp [smul_eq_mul]
      _ = coeff * log2 target := by
            rw [hlog_sInf]
  simpa [S, raw, coeff, target] using hscaled

end

end Ket

namespace QIT
noncomputable section

universe u1 v1 u2 v2
end

end QIT
