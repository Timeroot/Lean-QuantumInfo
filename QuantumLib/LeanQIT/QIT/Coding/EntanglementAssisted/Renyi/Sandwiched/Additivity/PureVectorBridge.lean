/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.WeightedSion

/-!
# Pure-vector bridge for sandwiched EA additivity

This module is part of the Khatri--Wilde sandwiched-Renyi additivity proof
spine for entanglement-assisted classical communication.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Pointwise

namespace QIT

universe u1 v1 u2 v2

noncomputable section

namespace PureVector

/-- Reindex `(A1B1C1) x (A2B2C2)` into the KW product-purification order
`((A1 x A2) x (B1 x B2)) x (C1 x C2)`. -/
def bipartiteProductPurificationEquiv
    {a1 b1 c1 a2 b2 c2 : Type*} :
    Prod (Prod (Prod a1 b1) c1) (Prod (Prod a2 b2) c2) ≃
      Prod (Prod (Prod a1 a2) (Prod b1 b2)) (Prod c1 c2) where
  toFun x := (((x.1.1.1, x.2.1.1), (x.1.1.2, x.2.1.2)), (x.1.2, x.2.2))
  invFun x := (((x.1.1.1, x.1.2.1), x.2.1), ((x.1.1.2, x.1.2.2), x.2.2))
  left_inv := by
    intro x
    rcases x with ⟨⟨⟨i1, j1⟩, k1⟩, ⟨⟨i2, j2⟩, k2⟩⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨⟨i1, i2⟩, ⟨j1, j2⟩⟩, ⟨k1, k2⟩⟩
    rfl

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
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2)) :
    PureVector (Prod (Prod (Prod a1 a2) (Prod b1 b2)) (Prod c1 c2)) :=
  (psi.prod phi).reindex bipartiteProductPurificationEquiv

@[simp]
theorem bipartiteProductPurification_amp
    {a1 b1 c1 a2 b2 c2 : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
    [Fintype c1] [DecidableEq c1] [Fintype a2] [DecidableEq a2]
    [Fintype b2] [DecidableEq b2] [Fintype c2] [DecidableEq c2]
    (psi : PureVector (Prod (Prod a1 b1) c1))
    (phi : PureVector (Prod (Prod a2 b2) c2))
    (p : Prod (Prod (Prod a1 a2) (Prod b1 b2)) (Prod c1 c2)) :
    (bipartiteProductPurification psi phi).amp p =
      psi.amp ((p.1.1.1, p.1.2.1), p.2.1) *
        phi.amp ((p.1.1.2, p.1.2.2), p.2.2) :=
  rfl

/-- Definition-level bridge from the source common bracket to the raw matrix
trace functional used by the Sion API. -/
theorem upwardRenyiDualityCommonBracket_re_eq_abcSidePowerTraceRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c)) (σB : State b) (τC : State c)
    (alphaPrime : ℝ) :
    (ψ.upwardRenyiDualityCommonBracket σB τC alphaPrime).re =
      State.abcSidePowerTraceRe (a := a) ψ.state.matrix σB.matrix τC.matrix
        alphaPrime := by
  rfl

/-- KW mutual-information Sion bracket with the fixed `rho_A` side weight from
`EA_capacity.tex:2020-2025`. -/
def sandwichedMutualInformationSionBracketRe
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) : ℝ :=
  State.abcWeightedSidePowerTraceRe
    (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
    ψ.state.matrix σB.matrix τC.matrix ((alpha - 1) / alpha)

/-- The KW sandwiched mutual-information Sion bracket is nonnegative. -/
theorem sandwichedMutualInformationSionBracketRe_nonneg
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) :
    0 ≤ sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha := by
  unfold sandwichedMutualInformationSionBracketRe
  exact State.abcWeightedSidePowerTraceRe_nonneg
    (cMatrix_rpow_posSemidef
      (A := rhoA.matrix) (s := (1 - alpha) / alpha) rhoA.pos)
    ψ.state.pos σB.pos τC.pos ((alpha - 1) / alpha)

/-- Definition-level source form of the KW fixed-`rho_A` Sion bracket. -/
theorem sandwichedMutualInformationSionBracketRe_eq_source
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          (CFC.rpow τC.matrix ((alpha - 1) / alpha)) *
        ψ.state.matrix).trace).re := by
  unfold sandwichedMutualInformationSionBracketRe State.abcWeightedSidePowerTraceRe
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) : CMatrix b :=
  fun j j' =>
    ∑ i : a, ∑ k : c,
      ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (1 : CMatrix b))
          (CFC.rpow τC.matrix ((alpha - 1) / alpha)) *
        ψ.state.matrix) ((i, j), k) ((i, j'), k))

/-- The `AC`-side weight from KW `EA_capacity.tex:2028-2035`, after
grouping the traced systems together. -/
def sandwichedMutualInformationACWeight
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c) (alpha : ℝ) : CMatrix (Prod a c) :=
  Matrix.kronecker
    (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
    (CFC.rpow τC.matrix ((alpha - 1) / alpha))

/-- Coordinate form of the KW trace-out-`AC` matrix. -/
theorem sandwichedMutualInformationACTraceMatrix_apply
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) (j j' : b) :
    sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha j j' =
      ∑ i : a, ∑ k : c, ∑ i' : a, ∑ k' : c,
        sandwichedMutualInformationACWeight rhoA τC alpha (i, k) (i', k') *
          ψ.amp ((i', j), k') * star (ψ.amp ((i, j'), k)) := by
  simp [sandwichedMutualInformationACTraceMatrix, sandwichedMutualInformationACWeight,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    PureVector.state_matrix, rankOneMatrix_apply, Fintype.sum_prod_type, mul_assoc]

/-- The `AC`-grouped amplitude obtained by applying the square-root of the
KW `AC` weight and leaving the `B` system untouched.  Its rank-one matrix is
the PSD representative of the trace-cyclic expression in
KW `EA_capacity.tex:2028-2035`. -/
def sandwichedMutualInformationACWeightedAmp
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) : Prod (Prod a c) b → ℂ :=
  Matrix.mulVec
    (Matrix.kronecker
      (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha))
      (1 : CMatrix b))
    (fun p : Prod (Prod a c) b => ψ.amp ((p.1.1, p.2), p.1.2))

/-- The KW `AC` weight is positive semidefinite. -/
theorem sandwichedMutualInformationACWeight_posSemidef
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c) (alpha : ℝ) :
    (sandwichedMutualInformationACWeight rhoA τC alpha).PosSemidef := by
  exact
    (cMatrix_rpow_posSemidef
        (A := rhoA.matrix) (s := (1 - alpha) / alpha) rhoA.pos).kronecker
      (cMatrix_rpow_posSemidef
        (A := τC.matrix) (s := (alpha - 1) / alpha) τC.pos)

/-- The KW `AC` weight is positive definite when both side weights are full
rank. -/
theorem sandwichedMutualInformationACWeight_posDef
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef) (alpha : ℝ) :
    (sandwichedMutualInformationACWeight rhoA τC alpha).PosDef := by
  exact
    (cMatrix_rpow_posDef_of_posDef hrhoA ((1 - alpha) / alpha)).kronecker
      (cMatrix_rpow_posDef_of_posDef hτC ((alpha - 1) / alpha))

/-- The square root of the KW `AC` weight squares back to the weight. -/
theorem sandwichedMutualInformationACWeight_sqrt_mul_self
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c) (alpha : ℝ) :
    CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha) *
        CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha) =
      sandwichedMutualInformationACWeight rhoA τC alpha := by
  exact CFC.sqrt_mul_sqrt_self _
    (sandwichedMutualInformationACWeight_posSemidef rhoA τC alpha).nonneg

/-- The square root of the KW `AC` weight is Hermitian. -/
theorem sandwichedMutualInformationACWeight_sqrt_isHermitian
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c) (alpha : ℝ) :
    (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)).IsHermitian := by
  exact (Matrix.nonneg_iff_posSemidef.mp
    (CFC.sqrt_nonneg (sandwichedMutualInformationACWeight rhoA τC alpha))).isHermitian

/-- The square root of a full-rank KW `AC` weight is invertible. -/
theorem sandwichedMutualInformationACWeight_sqrt_isUnit_posDef
    {a : Type u1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (rhoA : State a) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef) (alpha : ℝ) :
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) :
    (rankOneMatrix
      (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha)).PosSemidef :=
  rankOneMatrix_pos (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha)

/-- A rank-one kernel is zero exactly when its generating vector is zero. -/
private theorem rankOneMatrix_eq_zero_iff
    {d : Type*} (v : d → Complex) :
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

/-- Repartitioning a normalized `ABC` pure vector as an `ACB` amplitude does not
make it zero. -/
private theorem pureVector_acb_amp_ne_zero
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c)) :
    (fun p : Prod (Prod a c) b => ψ.amp ((p.1.1, p.2), p.1.2)) ≠ 0 := by
  intro hzero
  have hamp_zero : ψ.amp = 0 := by
    funext x
    rcases x with ⟨⟨i, j⟩, k⟩
    have hentry := congrFun hzero ((i, k), j)
    simpa using hentry
  have htrace_zero : (rankOneMatrix ψ.amp).trace = 0 := by
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
    (alpha : ℝ) :
    sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha ≠ 0 := by
  let S : CMatrix (Prod a c) := CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)
  let psiACB : Prod (Prod a c) b → Complex := fun p => ψ.amp ((p.1.1, p.2), p.1.2)
  have hpsi : psiACB ≠ 0 := by
    simpa [psiACB] using pureVector_acb_amp_ne_zero ψ
  have hS : IsUnit S := by
    simpa [S] using
      sandwichedMutualInformationACWeight_sqrt_isUnit_posDef rhoA τC hrhoA hτC alpha
  have hK : IsUnit (Matrix.kronecker S (1 : CMatrix b)) := by
    exact Matrix.IsUnit.kronecker hS isUnit_one
  intro hzero
  have hmul :
      Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psiACB = 0 := by
    simpa [sandwichedMutualInformationACWeightedAmp, S, psiACB] using hzero
  have hmul' :
      Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psiACB =
        Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) 0 := by
    simpa using hmul
  exact hpsi ((Matrix.mulVec_injective_of_isUnit hK) hmul')

/-- Coordinate form of the KW `AC` square-root-weighted amplitude. -/
theorem sandwichedMutualInformationACWeightedAmp_apply
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) (i : a) (k : c) (j : b) :
    sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha ((i, k), j) =
      ∑ i' : a, ∑ k' : c,
        (CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)) (i, k) (i', k') *
          ψ.amp ((i', j), k') := by
  unfold sandwichedMutualInformationACWeightedAmp
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  simp [Fintype.sum_prod_type]

/-- Moving a Hermitian square-root weight from a rank-one vector back to the
left-hand weight before tracing out the weighted system. -/
theorem partialTraceA_rankOne_kron_left_mulVec_eq_weight_mul
    {d : Type u1} {b : Type v1} [Fintype d] [DecidableEq d]
    [Fintype b] [DecidableEq b]
    (S : CMatrix d) (hS : S.IsHermitian) (psi : Prod d b → ℂ) :
    partialTraceA (a := d) (b := b)
        (rankOneMatrix (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psi)) =
      partialTraceA (a := d) (b := b)
        (Matrix.kronecker (S * S) (1 : CMatrix b) * rankOneMatrix psi) := by
  ext j j'
  have hstar : ∀ x y : d, star (S x y) = S y x := by
    intro x y
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hS.eq y) x
  have hstar' : ∀ x y : d, (starRingEnd ℂ) (S x y) = S y x := hstar
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

/-- The KW trace-out-`AC` matrix is the partial trace of the square-root
weighted rank-one vector.  This provides the PSD representative needed for the
reverse-Holder variational formula in `EA_capacity.tex:2032-2035`. -/
theorem partialTraceA_rankOne_ACWeightedAmp_eq_ACTraceMatrix
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) :
    partialTraceA (a := Prod a c) (b := b)
        (rankOneMatrix
          (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha)) =
      sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha := by
  let S : CMatrix (Prod a c) :=
    CFC.sqrt (sandwichedMutualInformationACWeight rhoA τC alpha)
  let psiACB : Prod (Prod a c) b → ℂ := fun p => ψ.amp ((p.1.1, p.2), p.1.2)
  have hmove :
      partialTraceA (a := Prod a c) (b := b)
          (rankOneMatrix (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psiACB)) =
        partialTraceA (a := Prod a c) (b := b)
          (Matrix.kronecker (S * S) (1 : CMatrix b) * rankOneMatrix psiACB) := by
    exact partialTraceA_rankOne_kron_left_mulVec_eq_weight_mul S
      (by
        simpa [S] using
          (sandwichedMutualInformationACWeight_sqrt_isHermitian rhoA τC alpha))
      psiACB
  have hsqrt :
      S * S = sandwichedMutualInformationACWeight rhoA τC alpha := by
    simpa [S] using
      (sandwichedMutualInformationACWeight_sqrt_mul_self rhoA τC alpha)
  calc
    partialTraceA (a := Prod a c) (b := b)
        (rankOneMatrix
          (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha))
        =
      partialTraceA (a := Prod a c) (b := b)
          (rankOneMatrix (Matrix.mulVec (Matrix.kronecker S (1 : CMatrix b)) psiACB)) := by
        simp [sandwichedMutualInformationACWeightedAmp, S, psiACB]
    _ =
      partialTraceA (a := Prod a c) (b := b)
        (Matrix.kronecker (S * S) (1 : CMatrix b) * rankOneMatrix psiACB) := hmove
    _ =
      partialTraceA (a := Prod a c) (b := b)
        (Matrix.kronecker (sandwichedMutualInformationACWeight rhoA τC alpha)
          (1 : CMatrix b) * rankOneMatrix psiACB) := by
        rw [hsqrt]
    _ = sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha := by
        ext j j'
        rw [sandwichedMutualInformationACTraceMatrix_apply]
        simp [partialTraceA, rankOneMatrix_apply, Matrix.mul_apply, Matrix.kronecker,
          Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
          mul_assoc, psiACB]

/-- The KW trace-out-`AC` matrix is positive semidefinite, as required by the
positive reverse-Holder variational formula. -/
theorem sandwichedMutualInformationACTraceMatrix_posSemidef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (alpha : ℝ) :
    (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha).PosSemidef := by
  have hpt :
      (partialTraceA (a := Prod a c) (b := b)
        (rankOneMatrix
          (sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha))).PosSemidef :=
    partialTraceA_posSemidef
      (sandwichedMutualInformationACWeightedAmp_rankOne_posSemidef rhoA ψ τC alpha)
  have heq := partialTraceA_rankOne_ACWeightedAmp_eq_ACTraceMatrix rhoA ψ τC alpha
  simpa [heq] using hpt

/-- Full-rank side weights make the KW `AC` trace matrix nonzero. -/
theorem sandwichedMutualInformationACTraceMatrix_ne_zero_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
    (alpha : ℝ) :
    sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha ≠ 0 := by
  let v : Prod (Prod a c) b → Complex :=
    sandwichedMutualInformationACWeightedAmp rhoA ψ τC alpha
  have hvne : v ≠ 0 := by
    simpa [v] using
      sandwichedMutualInformationACWeightedAmp_ne_zero_posDef
        rhoA ψ τC hrhoA hτC alpha
  intro hzero
  have hptzero :
      partialTraceA (a := Prod a c) (b := b) (rankOneMatrix v) = 0 := by
    rw [partialTraceA_rankOne_ACWeightedAmp_eq_ACTraceMatrix]
    simpa [v] using hzero
  have htrace_zero : (rankOneMatrix v).trace = 0 := by
    have htrace := congrArg Matrix.trace hptzero
    simpa [partialTraceA_trace] using htrace
  have hrank_zero : rankOneMatrix v = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (rankOneMatrix_pos v)).mp htrace_zero
  exact hvne ((rankOneMatrix_eq_zero_iff v).mp hrank_zero)

/-- Positive Schatten order `alpha / (2 * alpha - 1)` used by the high-alpha
alternate-expression route. -/
def sandwichedAlternateSchattenOrder {alpha : Real} (halpha : 1 < alpha) :
    SchattenOrder := by
  refine ⟨alpha / (2 * alpha - 1), ?_⟩
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hden_pos : 0 < 2 * alpha - 1 := by linarith
  exact div_pos halpha_pos hden_pos

@[simp]
theorem sandwichedAlternateSchattenOrder_coe {alpha : Real}
    (halpha : 1 < alpha) :
    (sandwichedAlternateSchattenOrder halpha : Real) =
      alpha / (2 * alpha - 1) := rfl

/-- Full-rank side weights make the KW `AC` trace-matrix Schatten norm strictly
positive on the high-alpha branch. -/
theorem psdSchattenPNorm_ACTraceMatrix_pos_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
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
    (f : bb -> aa -> cc -> aa -> bb -> cc -> ℂ) :
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((CFC.rpow σB.matrix ((1 - alpha) / alpha) *
        sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha).trace).re := by
  rw [sandwichedMutualInformationSionBracketRe_eq_source]
  simp only [sandwichedMutualInformationACTraceMatrix, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha *
        CFC.rpow σB.matrix ((1 - alpha) / alpha)).trace).re := by
  rw [sandwichedMutualInformationSionBracketRe_eq_trace_sigma_mul_ACTraceMatrix]
  exact congrArg Complex.re (Matrix.trace_mul_comm
    (CFC.rpow σB.matrix ((1 - alpha) / alpha))
    (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha))

/-- The `AB`-side weight in the proof of KW `eq-sand_rel_mut_inf_alt`. -/
def sandwichedMutualInformationABWeight
    {a : Type u1} {b : Type v1}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoA : State a) (σB : State b) (alpha : ℝ) : CMatrix (Prod a b) :=
  Matrix.kronecker
    (CFC.rpow rhoA.matrix ((1 - alpha) / (2 * alpha)))
    (CFC.rpow σB.matrix ((1 - alpha) / (2 * alpha)))

/-- Coordinate form of a left tensor factor acting on a bipartite vector. -/
theorem kronecker_left_one_mulVec_apply
    {d : Type u1} {c : Type u2} [Fintype d] [DecidableEq d]
    [Fintype c] [DecidableEq c]
    (W : CMatrix d) (psi : Prod d c → ℂ) (i : d) (k : c) :
    (Matrix.kronecker W (1 : CMatrix c)).mulVec psi (i, k) =
      W.mulVec (fun j => psi (j, k)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.one_apply]

/-- Applying `W ⊗ I` to a bipartite rank-one vector and tracing out the
second system sandwiches the original first-system marginal by `W`.

This is the finite-sum kernel of the weighted-purification identity in
KW `EA_capacity.tex:1989-1996`. -/
theorem partialTraceB_rankOne_kron_left_mulVec_eq
    {d : Type u1} {c : Type u2} [Fintype d] [DecidableEq d]
    [Fintype c] [DecidableEq c]
    (W : CMatrix d) (psi : Prod d c → ℂ) :
    partialTraceB (a := d) (b := c)
        (rankOneMatrix (Matrix.mulVec (Matrix.kronecker W (1 : CMatrix c)) psi)) =
      W * partialTraceB (a := d) (b := c) (rankOneMatrix psi) *
        Matrix.conjTranspose W := by
  ext x y
  have hmulVec :
      Matrix.mulVec (Matrix.kronecker W (1 : CMatrix c)) psi =
        fun p : Prod d c => W.mulVec (fun i => psi (i, p.2)) p.1 := by
    ext p
    exact kronecker_left_one_mulVec_apply W psi p.1 p.2
  rw [hmulVec]
  let F : c → d → d → ℂ := fun k i j =>
    W x i * (psi (i, k) * (star (W y j) * star (psi (j, k))))
  calc
    partialTraceB (a := d) (b := c)
        (rankOneMatrix (fun p : Prod d c => W.mulVec (fun i => psi (i, p.2)) p.1)) x y
        =
      ∑ k : c, ∑ j : d, ∑ i : d, F k i j := by
        simp [F, partialTraceB, rankOneMatrix_apply, Matrix.mulVec, dotProduct,
          Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = ∑ j : d, ∑ k : c, ∑ i : d, F k i j := by
        rw [Finset.sum_comm]
    _ = ∑ j : d, ∑ i : d, ∑ k : c, F k i j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
    _ = ∑ j : d, star (W y j) *
          ∑ i : d, W x i * ∑ k : c, psi (i, k) * star (psi (j, k)) := by
        simp [F, Finset.mul_sum, mul_left_comm]
    _ =
      (W * partialTraceB (a := d) (b := c) (rankOneMatrix psi) *
        Matrix.conjTranspose W) x y := by
        simp [partialTraceB, rankOneMatrix_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, mul_comm]

/-- The weighted purification vector used in the proof of KW
`eq-sand_rel_mut_inf_alt`.

It is obtained from the purification `psi_ABC` by applying
`rho_A^((1-alpha)/(2 alpha)) ⊗ sigma_B^((1-alpha)/(2 alpha))` on the `AB`
legs and the identity on the purifying `C` leg. -/
def sandwichedMutualInformationWeightedPurificationAmp
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (σB : State b)
    (ψ : PureVector (Prod (Prod a b) c)) (alpha : ℝ) :
    Prod (Prod a b) c → ℂ :=
  Matrix.mulVec
    (Matrix.kronecker
      (sandwichedMutualInformationABWeight rhoA σB alpha)
      (1 : CMatrix c))
    ψ.amp

/-- Partial tracing the KW weighted purification over the purifying system
produces the sandwich of the original `AB` marginal by the source weight.

This is the matrix identity behind KW `EA_capacity.tex:1989-1996`. -/
theorem partialTraceB_rankOne_weightedPurificationAmp_eq
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (σB : State b)
    (ψ : PureVector (Prod (Prod a b) c)) (alpha : ℝ) :
    partialTraceB (a := Prod a b) (b := c)
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)) =
      sandwichedMutualInformationABWeight rhoA σB alpha *
        partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp) *
        Matrix.conjTranspose (sandwichedMutualInformationABWeight rhoA σB alpha) := by
  exact partialTraceB_rankOne_kron_left_mulVec_eq
    (sandwichedMutualInformationABWeight rhoA σB alpha) ψ.amp

private theorem sandwiched_partialTraceA_mul_trace_eq_trace_mul_rightKroneckerOne
    {d : Type u1} {c : Type u2} [Fintype d] [DecidableEq d] [Fintype c] [DecidableEq c]
    (X : CMatrix (Prod d c)) (T : CMatrix c) :
    ((partialTraceA (a := d) (b := c) X) * T).trace =
      (X * Matrix.kronecker (1 : CMatrix d) T).trace := by
  rw [← partialTraceA_mul_rightKroneckerOne X T]
  exact partialTraceA_trace (a := d) (b := c)
    (X * Matrix.kronecker (1 : CMatrix d) T)

private theorem rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose
    {d : Type u1} [Fintype d] [DecidableEq d] (M : CMatrix d) (v : d → ℂ) :
    rankOneMatrix (M.mulVec v) = M * rankOneMatrix v * Matrix.conjTranspose M := by
  rw [rankOneMatrix, rankOneMatrix]
  rw [Matrix.mul_vecMulVec]
  rw [Matrix.vecMulVec_mul]
  congr
  ext i
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose, mul_comm]

/-- Trace-pairing form of the KW weighted-purification bracket.

This is the cyclic trace/partial-trace bridge in `EA_capacity.tex:2006-2025`:
after applying the `AB` square weights to the purification, pairing the
purifying marginal with `tau_C^((alpha-1)/alpha)` is exactly the Sion trace
bracket on the full-rank side-reference branch. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hσB : σB.matrix.PosDef) (alpha : ℝ) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)) *
        CFC.rpow τC.matrix ((alpha - 1) / alpha)).trace).re := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let T : CMatrix c := CFC.rpow τC.matrix ((alpha - 1) / alpha)
  let Wab : CMatrix (Prod a b) := sandwichedMutualInformationABWeight rhoA σB alpha
  let W : CMatrix (Prod (Prod a b) c) := Matrix.kronecker Wab (1 : CMatrix c)
  let K : CMatrix (Prod (Prod a b) c) := Matrix.kronecker (1 : CMatrix (Prod a b)) T
  have hρpow :
      CFC.rpow rhoA.matrix s * CFC.rpow rhoA.matrix s =
        CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
    calc
      CFC.rpow rhoA.matrix s * CFC.rpow rhoA.matrix s =
          CFC.rpow rhoA.matrix (s + s) := by
            exact (CFC.rpow_add (a := rhoA.matrix) (x := s) (y := s) hrhoA.isUnit).symm
      _ = CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
            congr 1
            simp [s]
            ring
  have hσpow :
      CFC.rpow σB.matrix s * CFC.rpow σB.matrix s =
        CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
    calc
      CFC.rpow σB.matrix s * CFC.rpow σB.matrix s =
          CFC.rpow σB.matrix (s + s) := by
            exact (CFC.rpow_add (a := σB.matrix) (x := s) (y := s) hσB.isUnit).symm
      _ = CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
            congr 1
            simp [s]
            ring
  have hWstar : Matrix.conjTranspose W = W := by
    have hWab : Wab.IsHermitian := by
      unfold Wab sandwichedMutualInformationABWeight
      exact kronecker_isHermitian
        (CFC.rpow rhoA.matrix s)
        (CFC.rpow σB.matrix s)
        (cMatrix_rpow_posSemidef (A := rhoA.matrix) (s := s) rhoA.pos).isHermitian
        (cMatrix_rpow_posSemidef (A := σB.matrix) (s := s) σB.pos).isHermitian
    unfold W
    exact (kronecker_isHermitian Wab (1 : CMatrix c) hWab (by simp)).eq
  have hWKW :
      W * K * W =
        Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T := by
    have hWK : W * K = Matrix.kronecker Wab T := by
      unfold W K
      simpa using
        (Matrix.mul_kronecker_mul Wab (1 : CMatrix (Prod a b)) (1 : CMatrix c) T).symm
    have hWab2 :
        Wab * Wab =
          Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)) := by
      unfold Wab sandwichedMutualInformationABWeight
      let R : CMatrix a := CFC.rpow rhoA.matrix ((1 - alpha) / (2 * alpha))
      let S : CMatrix b := CFC.rpow σB.matrix ((1 - alpha) / (2 * alpha))
      have hR :
          R * R = CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
        simpa [R, s, mul_comm] using hρpow
      have hS :
          S * S = CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
        simpa [S, s, mul_comm] using hσpow
      calc
        Matrix.kronecker R S * Matrix.kronecker R S =
            Matrix.kronecker (R * R) (S * S) := by
              exact (Matrix.mul_kronecker_mul R R S S).symm
        _ = Matrix.kronecker
              (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
              (CFC.rpow σB.matrix ((1 - alpha) / alpha)) := by
              rw [hR, hS]
    calc
      W * K * W = Matrix.kronecker Wab T * W := by rw [hWK]
      _ = Matrix.kronecker Wab T * Matrix.kronecker Wab (1 : CMatrix c) := by
            rfl
      _ = Matrix.kronecker (Wab * Wab) (T * (1 : CMatrix c)) := by
            exact (Matrix.mul_kronecker_mul Wab Wab T (1 : CMatrix c)).symm
      _ = Matrix.kronecker
            (Matrix.kronecker
              (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
              (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
            T := by
            rw [hWab2]
            simp
  have hrank :
      rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) =
        W * rankOneMatrix ψ.amp * W := by
    unfold sandwichedMutualInformationWeightedPurificationAmp W Wab
    rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    rw [hWstar]
  rw [sandwichedMutualInformationSionBracketRe_eq_source]
  rw [sandwiched_partialTraceA_mul_trace_eq_trace_mul_rightKroneckerOne]
  change
    ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T *
        rankOneMatrix ψ.amp).trace).re =
      ((rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) *
        K).trace).re
  rw [hrank]
  calc
    ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T *
        rankOneMatrix ψ.amp).trace).re =
        ((W * K * W * rankOneMatrix ψ.amp).trace).re := by rw [hWKW]
    _ = (((W * rankOneMatrix ψ.amp * W) * K).trace).re := by
          congr 1
          simpa [Matrix.mul_assoc] using
            Matrix.trace_mul_cycle W K (W * rankOneMatrix ψ.amp)

/-- Support-convention trace-pairing form of the KW weighted-purification
bracket.

The older lemma
`sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau`
used `CFC.rpow_add` and therefore required `rho_A` to be full rank.  KW
`EA_capacity.tex:2006-2025` does not impose that hypothesis.  This sibling
keeps the source statement: only the optimized side state `sigma_B` is
full-rank, while the fixed `rho_A` is an arbitrary state.  The `rho_A` square
weight is multiplied using the repository support convention for PSD real
powers. -/
theorem sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hσB : σB.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
      ((partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)) *
        CFC.rpow τC.matrix ((alpha - 1) / alpha)).trace).re := by
  let s : ℝ := (1 - alpha) / (2 * alpha)
  let T : CMatrix c := CFC.rpow τC.matrix ((alpha - 1) / alpha)
  let Wab : CMatrix (Prod a b) := sandwichedMutualInformationABWeight rhoA σB alpha
  let W : CMatrix (Prod (Prod a b) c) := Matrix.kronecker Wab (1 : CMatrix c)
  let K : CMatrix (Prod (Prod a b) c) := Matrix.kronecker (1 : CMatrix (Prod a b)) T
  have hρpow :
      CFC.rpow rhoA.matrix s * CFC.rpow rhoA.matrix s =
        CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
    refine cMatrix_rpow_mul_rpow_of_posSemidef_scalar rhoA.pos ?_
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
      CFC.rpow σB.matrix s * CFC.rpow σB.matrix s =
        CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
    calc
      CFC.rpow σB.matrix s * CFC.rpow σB.matrix s =
          CFC.rpow σB.matrix (s + s) := by
            exact (CFC.rpow_add (a := σB.matrix) (x := s) (y := s) hσB.isUnit).symm
      _ = CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
            congr 1
            simp [s]
            ring
  have hWstar : Matrix.conjTranspose W = W := by
    have hWab : Wab.IsHermitian := by
      unfold Wab sandwichedMutualInformationABWeight
      exact kronecker_isHermitian
        (CFC.rpow rhoA.matrix s)
        (CFC.rpow σB.matrix s)
        (cMatrix_rpow_posSemidef (A := rhoA.matrix) (s := s) rhoA.pos).isHermitian
        (cMatrix_rpow_posSemidef (A := σB.matrix) (s := s) σB.pos).isHermitian
    unfold W
    exact (kronecker_isHermitian Wab (1 : CMatrix c) hWab (by simp)).eq
  have hWKW :
      W * K * W =
        Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T := by
    have hWK : W * K = Matrix.kronecker Wab T := by
      unfold W K
      simpa using
        (Matrix.mul_kronecker_mul Wab (1 : CMatrix (Prod a b)) (1 : CMatrix c) T).symm
    have hWab2 :
        Wab * Wab =
          Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)) := by
      unfold Wab sandwichedMutualInformationABWeight
      let R : CMatrix a := CFC.rpow rhoA.matrix ((1 - alpha) / (2 * alpha))
      let S : CMatrix b := CFC.rpow σB.matrix ((1 - alpha) / (2 * alpha))
      have hR :
          R * R = CFC.rpow rhoA.matrix ((1 - alpha) / alpha) := by
        simpa [R, s, mul_comm] using hρpow
      have hS :
          S * S = CFC.rpow σB.matrix ((1 - alpha) / alpha) := by
        simpa [S, s, mul_comm] using hσpow
      calc
        Matrix.kronecker R S * Matrix.kronecker R S =
            Matrix.kronecker (R * R) (S * S) := by
              exact (Matrix.mul_kronecker_mul R R S S).symm
        _ = Matrix.kronecker
              (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
              (CFC.rpow σB.matrix ((1 - alpha) / alpha)) := by
              rw [hR, hS]
    calc
      W * K * W = Matrix.kronecker Wab T * W := by rw [hWK]
      _ = Matrix.kronecker Wab T * Matrix.kronecker Wab (1 : CMatrix c) := by
            rfl
      _ = Matrix.kronecker (Wab * Wab) (T * (1 : CMatrix c)) := by
            exact (Matrix.mul_kronecker_mul Wab Wab T (1 : CMatrix c)).symm
      _ = Matrix.kronecker
            (Matrix.kronecker
              (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
              (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
            T := by
            rw [hWab2]
            simp
  have hrank :
      rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) =
        W * rankOneMatrix ψ.amp * W := by
    unfold sandwichedMutualInformationWeightedPurificationAmp W Wab
    rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    rw [hWstar]
  rw [sandwichedMutualInformationSionBracketRe_eq_source]
  rw [sandwiched_partialTraceA_mul_trace_eq_trace_mul_rightKroneckerOne]
  change
    ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T *
        rankOneMatrix ψ.amp).trace).re =
      ((rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha) *
        K).trace).re
  rw [hrank]
  calc
    ((Matrix.kronecker
          (Matrix.kronecker
            (CFC.rpow rhoA.matrix ((1 - alpha) / alpha))
            (CFC.rpow σB.matrix ((1 - alpha) / alpha)))
          T *
        rankOneMatrix ψ.amp).trace).re =
        ((W * K * W * rankOneMatrix ψ.amp).trace).re := by rw [hWKW]
    _ = (((W * rankOneMatrix ψ.amp * W) * K).trace).re := by
          congr 1
          simpa [Matrix.mul_assoc] using
            Matrix.trace_mul_cycle W K (W * rankOneMatrix ψ.amp)

/-- Every full-rank side-reference Sion bracket value lies below the Holder
unit-ball supremum of the KW weighted purification marginal.

This is the inequality direction of the variational step in
`EA_capacity.tex:2006-2025`, after the trace-pairing identity has moved the
`tau_C` power onto the purifying marginal. -/
theorem sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hσB : σB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ≤
      sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
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
  have hτtrace : τC.matrix.trace.re = 1 := by
    simpa using congrArg Complex.re τC.trace_eq_one
  have hvar :
      ((M * CFC.rpow τC.matrix r).trace).re ≤
        psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) := by
    exact psd_trace_rpow_holder_variational_upper
      (M := M) (N := τC.matrix) hM τC.pos hτtrace hpq hr
  have htrace :
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
        ((M * CFC.rpow τC.matrix r).trace).re := by
    simpa [M, r] using
      sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) (hσB : σB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ≤
      sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
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
  have hτtrace : τC.matrix.trace.re = 1 := by
    simpa using congrArg Complex.re τC.trace_eq_one
  have hvar :
      ((M * CFC.rpow τC.matrix r).trace).re ≤
        psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha) := by
    exact psd_trace_rpow_holder_variational_upper
      (M := M) (N := τC.matrix) hM τC.pos hτtrace hpq hr
  have htrace :
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
        ((M * CFC.rpow τC.matrix r).trace).re := by
    simpa [M, r] using
      sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau_support
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
Holder witness `B` with `Tr B^q <= 1` is either zero, or its normalized
`q`-power is a state `tau_C` whose `q`-root dominates the original witness. -/
theorem weightedPurification_holderUnitBall_sSup_le_sandwichedMutualInformationSionBracketRe_sSup
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b)
    (hrhoA : rhoA.matrix.PosDef) (hσB : σB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) ≤
      sSup (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
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
      BddAbove (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
    refine ⟨psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha), ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle :=
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup
        rhoA ψ σB τC hrhoA hσB halpha
    rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
      (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)] at hle
    simpa [M, q] using hle
  have hholderNonempty :
      (psdTraceHolderUnitBallValueSet M q).Nonempty :=
    Set.nonempty_of_mem (psdTraceHolderUnitBall_isGreatest hM hpq).1
  change sSup (psdTraceHolderUnitBallValueSet M q) ≤
    sSup (Set.range fun τC : State c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha)
  refine csSup_le hholderNonempty ?_
  intro x hx
  rcases hx with ⟨B, hB, hBq, rfl⟩
  by_cases hBzero : B = 0
  · have hvalue_zero : ((M * B).trace).re = 0 := by
      simp [hBzero]
    rw [hvalue_zero]
    let τ0 : State c := State.maximallyMixed c
    have hτ0_nonneg :
        0 ≤ sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha := by
      have htrace :
          sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha =
            ((M * CFC.rpow τ0.matrix r).trace).re := by
        simpa [M, r] using
          sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau
            rhoA ψ σB τ0 hrhoA hσB alpha
      rw [htrace]
      exact cMatrix_trace_mul_posSemidef_re_nonneg hM
        (cMatrix_rpow_posSemidef (A := τ0.matrix) (s := r) τ0.pos)
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
    let τC : State c := { matrix := T, pos := hT, trace_eq_one := hTtrace }
    have hτpow : CFC.rpow τC.matrix r = N := by
      dsimp [τC, T]
      change (N ^ q) ^ r = N
      rw [CFC.rpow_rpow_of_exponent_nonneg N q r hq_nonneg hr_nonneg
        (Matrix.nonneg_iff_posSemidef.mpr hN)]
      rw [hqr]
      simp [CFC.rpow_one N (ha := Matrix.nonneg_iff_posSemidef.mpr hN)]
    have hbracket :
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
          ((M * N).trace).re := by
      have htrace :=
        sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (hσB : σB.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sSup
        (psdTraceHolderUnitBallValueSet
          (partialTraceA (a := Prod a b) (b := c)
            (rankOneMatrix
              (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
          (Real.conjExponent alpha)) ≤
      sSup (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
  let M : CMatrix c :=
    partialTraceA (a := Prod a b) (b := c)
      (rankOneMatrix
        (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha))
  let hM : M.PosSemidef :=
    partialTraceA_posSemidef
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
      BddAbove (Set.range fun τC : State c =>
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha) := by
    refine ⟨psdSchattenPNorm M hM (SchattenOrder.ofOneLt halpha), ?_⟩
    rintro y ⟨τC, rfl⟩
    have hle :=
      sandwichedMutualInformationSionBracketRe_le_weightedPurification_holderUnitBall_sSup_of_side_posDef
        rhoA ψ σB τC hσB halpha
    rw [psdTraceHolderUnitBall_sSup_eq (M := M) hM (p := alpha)
      (q := Real.conjExponent alpha)
      (Real.HolderConjugate.conjExponent halpha)] at hle
    simpa [M, q] using hle
  have hholderNonempty :
      (psdTraceHolderUnitBallValueSet M q).Nonempty :=
    Set.nonempty_of_mem (psdTraceHolderUnitBall_isGreatest hM hpq).1
  change sSup (psdTraceHolderUnitBallValueSet M q) ≤
    sSup (Set.range fun τC : State c =>
      sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha)
  refine csSup_le hholderNonempty ?_
  intro x hx
  rcases hx with ⟨B, hB, hBq, rfl⟩
  by_cases hBzero : B = 0
  · have hvalue_zero : ((M * B).trace).re = 0 := by
      simp [hBzero]
    rw [hvalue_zero]
    let τ0 : State c := State.maximallyMixed c
    have hτ0_nonneg :
        0 ≤ sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha := by
      have htrace :
          sandwichedMutualInformationSionBracketRe rhoA ψ σB τ0 alpha =
            ((M * CFC.rpow τ0.matrix r).trace).re := by
        simpa [M, r] using
          sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau_support
            rhoA ψ σB τ0 hσB halpha
      rw [htrace]
      exact cMatrix_trace_mul_posSemidef_re_nonneg hM
        (cMatrix_rpow_posSemidef (A := τ0.matrix) (s := r) τ0.pos)
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
    let τC : State c := { matrix := T, pos := hT, trace_eq_one := hTtrace }
    have hτpow : CFC.rpow τC.matrix r = N := by
      dsimp [τC, T]
      change (N ^ q) ^ r = N
      rw [CFC.rpow_rpow_of_exponent_nonneg N q r hq_nonneg hr_nonneg
        (Matrix.nonneg_iff_posSemidef.mpr hN)]
      rw [hqr]
      simp [CFC.rpow_one N (ha := Matrix.nonneg_iff_posSemidef.mpr hN)]
    have hbracket :
        sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha =
          ((M * N).trace).re := by
      have htrace :=
        sandwichedMutualInformationSionBracketRe_eq_trace_weightedPurification_partialTraceA_mul_tau_support
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
theorem partialTraceB_rankOne_weightedPurificationAmp_eq_referenceInner
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hσ : σB.matrix.PosDef) (alpha : ℝ) :
    partialTraceB (a := Prod a b) (b := c)
        (rankOneMatrix
          (sandwichedMutualInformationWeightedPurificationAmp
            ψ.state.marginalAB.marginalA σB ψ alpha)) =
      State.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.marginalA.prod σB).matrix alpha := by
  let W : CMatrix (Prod a b) :=
    sandwichedMutualInformationABWeight ψ.state.marginalAB.marginalA σB alpha
  have hW :
      Matrix.conjTranspose W = W := by
    unfold W sandwichedMutualInformationABWeight
    exact (kronecker_isHermitian
      (CFC.rpow ψ.state.marginalAB.marginalA.matrix ((1 - alpha) / (2 * alpha)))
      (CFC.rpow σB.matrix ((1 - alpha) / (2 * alpha)))
      (cMatrix_rpow_posSemidef
        (A := ψ.state.marginalAB.marginalA.matrix)
        (s := (1 - alpha) / (2 * alpha))
        ψ.state.marginalAB.marginalA.pos).isHermitian
      (cMatrix_rpow_posSemidef
        (A := σB.matrix)
        (s := (1 - alpha) / (2 * alpha))
        σB.pos).isHermitian).eq
  rw [partialTraceB_rankOne_weightedPurificationAmp_eq]
  unfold State.sandwichedRenyiReferenceInner
  rw [show (ψ.state.marginalAB.marginalA.prod σB).matrix =
      Matrix.kronecker ψ.state.marginalAB.marginalA.matrix σB.matrix from rfl]
  change sandwichedMutualInformationABWeight ψ.state.marginalAB.marginalA σB alpha *
      partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp) *
        Matrix.conjTranspose
          (sandwichedMutualInformationABWeight ψ.state.marginalAB.marginalA σB alpha) =
    CFC.rpow (Matrix.kronecker ψ.state.marginalAB.marginalA.matrix σB.matrix)
        ((1 - alpha) / (2 * alpha)) *
      ψ.state.marginalAB.matrix *
      CFC.rpow (Matrix.kronecker ψ.state.marginalAB.marginalA.matrix σB.matrix)
        ((1 - alpha) / (2 * alpha))
  rw [cMatrix_rpow_kronecker_posDef hA hσ ((1 - alpha) / (2 * alpha))]
  change W * partialTraceB (a := Prod a b) (b := c) (rankOneMatrix ψ.amp) *
      Matrix.conjTranspose W =
    W * ψ.state.marginalAB.matrix * W
  rw [hW]
  rfl

/-- The two partial traces of the KW weighted purification rank-one operator
have equal Schatten `p` norms.

This is the Lean form of the same-nonzero-eigenvalues step in
KW `EA_capacity.tex:1990-2004`, before the reverse-Holder variational formula
is applied. -/
theorem psdSchattenPNorm_weightedPurification_partialTraceC_eq_partialTraceAB
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (σB : State b)
    (ψ : PureVector (Prod (Prod a b) c)) (alpha : ℝ)
    {p : ℝ} (hp : 0 < p) :
    psdSchattenPNorm
        (partialTraceB (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (partialTraceB_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (SchattenOrder.ofPositive hp) =
      psdSchattenPNorm
        (partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (partialTraceA_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)))
        (SchattenOrder.ofPositive hp) := by
  exact psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
    (sandwichedMutualInformationWeightedPurificationAmp rhoA σB ψ alpha)
    (SchattenOrder.ofPositive hp)

/-- Schatten-norm form of the KW weighted-purification bridge.

The reference-inner Schatten expression on the `AB` system equals the Schatten
expression of the complementary `C` marginal of the weighted purification,
matching KW `EA_capacity.tex:1990-2004`. -/
theorem psdSchattenPNorm_referenceInner_eq_weightedPurification_partialTraceA
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (σB : State b) (ψ : PureVector (Prod (Prod a b) c))
    (hA : ψ.state.marginalAB.marginalA.matrix.PosDef)
    (hσ : σB.matrix.PosDef) (alpha : ℝ) {p : ℝ} (hp : 0 < p) :
    psdSchattenPNorm
        (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.marginalA.prod σB).matrix alpha)
        (State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
          (State.prod_posDef hA hσ).posSemidef alpha)
        (SchattenOrder.ofPositive hp) =
      psdSchattenPNorm
        (partialTraceA (a := Prod a b) (b := c)
          (rankOneMatrix
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.marginalA σB ψ alpha)))
        (partialTraceA_posSemidef
          (rankOneMatrix_pos
            (sandwichedMutualInformationWeightedPurificationAmp
              ψ.state.marginalAB.marginalA σB ψ alpha)))
        (SchattenOrder.ofPositive hp) := by
  let amp :=
    sandwichedMutualInformationWeightedPurificationAmp
      ψ.state.marginalAB.marginalA σB ψ alpha
  let hB : (partialTraceB (a := Prod a b) (b := c)
      (rankOneMatrix amp)).PosSemidef :=
    partialTraceB_posSemidef (rankOneMatrix_pos amp)
  let hRef :
      (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
        (ψ.state.marginalAB.marginalA.prod σB).matrix alpha).PosSemidef :=
    State.sandwichedRenyiReferenceInner_posSemidef ψ.state.marginalAB
      (State.prod_posDef hA hσ).posSemidef alpha
  have hmatrix :
      partialTraceB (a := Prod a b) (b := c) (rankOneMatrix amp) =
        State.sandwichedRenyiReferenceInner ψ.state.marginalAB
          (ψ.state.marginalAB.marginalA.prod σB).matrix alpha := by
    simpa [amp] using
      partialTraceB_rankOne_weightedPurificationAmp_eq_referenceInner
        σB ψ hA hσ alpha
  have hnormB :
      psdSchattenPNorm (partialTraceB (a := Prod a b) (b := c)
          (rankOneMatrix amp)) hB (SchattenOrder.ofPositive hp) =
        psdSchattenPNorm
          (State.sandwichedRenyiReferenceInner ψ.state.marginalAB
            (ψ.state.marginalAB.marginalA.prod σB).matrix alpha)
          hRef (SchattenOrder.ofPositive hp) :=
    psdSchattenPNorm_congr hmatrix hB hRef (SchattenOrder.ofPositive hp)
  have hBA :
      psdSchattenPNorm (partialTraceB (a := Prod a b) (b := c)
          (rankOneMatrix amp)) hB (SchattenOrder.ofPositive hp) =
        psdSchattenPNorm
          (partialTraceA (a := Prod a b) (b := c) (rankOneMatrix amp))
          (partialTraceA_posSemidef (rankOneMatrix_pos amp))
          (SchattenOrder.ofPositive hp) := by
    simpa [amp, hB] using
      psdSchattenPNorm_weightedPurification_partialTraceC_eq_partialTraceAB
        ψ.state.marginalAB.marginalA σB ψ alpha hp
  exact hnormB.symm.trans hBA

/-- Pure-state specialization of the KW high-`alpha` Sion exchange. -/
theorem sandwichedAlpha_sion_abcSidePowerTraceRe_state_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
        ⨆ τ ∈ State.densityMatrixSet c,
          (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ τ
              ((alpha - 1) / alpha) : EReal)) =
      ⨆ τ ∈ State.densityMatrixSet c,
        ⨅ σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ τ
              ((alpha - 1) / alpha) : EReal) := by
  exact sandwichedAlpha_sion_abcSidePowerTraceRe_EReal
    (a := a) (b := b) (c := c)
    hdelta_pos hdelta_le ψ.state.pos halpha

/-- State-domain form of the KW high-`alpha` Sion exchange.

The sigma side remains restricted to the compact full-support lower-bound
domain used by the already proved Sion theorem; the tau side is the ordinary
state domain. -/
theorem sandwichedAlpha_sion_uniformlyPositiveState_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ.val.matrix τ.matrix
              ((alpha - 1) / alpha) : EReal)) =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ.val.matrix τ.matrix
              ((alpha - 1) / alpha) : EReal) := by
  let F : CMatrix b → CMatrix c → EReal := fun σ τ =>
    (State.abcSidePowerTraceRe (a := a) ψ.state.matrix σ τ ((alpha - 1) / alpha) :
      EReal)
  calc
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c, F σ.val.matrix τ.matrix)
        =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : State c, F σ τ.matrix := by
        exact uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf
          (fun σ => ⨆ τ : State c, F σ τ.matrix)
    _ =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : CMatrix c, ⨆ hτ : τ ∈ State.densityMatrixSet c, F σ τ := by
        simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ State.densityMatrixSet c,
          ⨅ σ : CMatrix b,
            ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b, F σ τ := by
        exact sandwichedAlpha_sion_abcSidePowerTraceRe_state_EReal
          (a := a) (b := b) (c := c) ψ hdelta_pos hdelta_le halpha
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ State.densityMatrixSet c,
          ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
            F σ.val.matrix τ := by
        simp_rw [
          ← uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf]
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          F σ.val.matrix τ.matrix := by
        exact (state_iSup_matrix_eq_densityMatrixSet_iSup
          (fun τ => ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
            F σ.val.matrix τ)).symm

/-- Source-bracket form of the compact-domain Sion exchange in KW
`EA_capacity.tex:2020-2025`. -/
theorem sandwichedAlpha_sion_commonBracket_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          ((ψ.upwardRenyiDualityCommonBracket σ.val τ ((alpha - 1) / alpha)).re :
            EReal)) =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  let A : CMatrix a := CFC.rpow rhoA.matrix ((1 - alpha) / alpha)
  let F : CMatrix b -> CMatrix c -> EReal := fun σ τ =>
    (State.abcWeightedSidePowerTraceRe (a := a) A ψ.state.matrix σ τ
      ((alpha - 1) / alpha) : EReal)
  have hA : A.PosSemidef :=
    cMatrix_rpow_posSemidef (A := rhoA.matrix) (s := (1 - alpha) / alpha) rhoA.pos
  calc
    (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal))
        =
      ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c, F σ.val.matrix τ.matrix := by
        simp [sandwichedMutualInformationSionBracketRe, F, A]
    _ =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : State c, F σ τ.matrix := by
        exact uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf
          (fun σ => ⨆ τ : State c, F σ τ.matrix)
    _ =
      ⨅ σ : CMatrix b,
        ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b,
          ⨆ τ : CMatrix c, ⨆ hτ : τ ∈ State.densityMatrixSet c, F σ τ := by
        simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ State.densityMatrixSet c,
          ⨅ σ : CMatrix b,
            ⨅ hσ : σ ∈ State.uniformlyPositiveDensityMatrixSet delta b, F σ τ := by
        exact sandwichedAlpha_sion_abcWeightedSidePowerTraceRe_EReal
          (a := a) (b := b) (c := c) hdelta_pos hdelta_le hA ψ.state.pos halpha
    _ =
      ⨆ τ : CMatrix c,
        ⨆ hτ : τ ∈ State.densityMatrixSet c,
          ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
            F σ.val.matrix τ := by
        simp_rw [
          ← uniformlyPositiveState_iInf_matrix_eq_uniformlyPositiveDensityMatrixSet_iInf]
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          F σ.val.matrix τ.matrix := by
        exact (state_iSup_matrix_eq_densityMatrixSet_iSup
          (fun τ => ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
            F σ.val.matrix τ)).symm
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
        simp [sandwichedMutualInformationSionBracketRe, F, A]

/-- Full-rank state-domain Sion exchange for the KW sandwiched mutual
information bracket.

This is the state-language form of
`State.fullRankDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal` and
matches the no-cutoff route in KW `EA_capacity.tex:2018-2035`. -/
theorem sandwichedAlpha_fullRank_sion_mutualInformationBracket_EReal
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    {alpha : ℝ} (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // σ.matrix.PosDef},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  let A : CMatrix a := CFC.rpow rhoA.matrix ((1 - alpha) / alpha)
  let F : CMatrix b → CMatrix c → EReal := fun sigma tau =>
    (State.abcWeightedSidePowerTraceRe (a := a) A ψ.state.matrix sigma tau
      ((alpha - 1) / alpha) : EReal)
  have hA : A.PosSemidef :=
    cMatrix_rpow_posSemidef (A := rhoA.matrix) (s := (1 - alpha) / alpha) rhoA.pos
  have hp := sandwichedAlphaPrime_pos_lt_one halpha
  calc
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal))
        =
      ⨅ sigma : CMatrix b,
        ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma,
          ⨆ τ : State c, F sigma τ.matrix := by
        exact fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
          (fun sigma => ⨆ τ : State c, F sigma τ.matrix)
    _ =
      ⨅ sigma : CMatrix b,
        ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma,
          ⨆ tau : CMatrix c,
            ⨆ _hTau : (State.densityMatrixSet c) tau, F sigma tau := by
        simp_rw [state_iSup_matrix_eq_densityMatrixSet_iSup]
        rfl
    _ =
      ⨆ tau : CMatrix c,
        ⨆ _hTau : (State.densityMatrixSet c) tau,
          ⨅ sigma : CMatrix b,
            ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma, F sigma tau := by
        exact State.fullRankDensityMatrixSet_sion_abcWeightedSidePowerTraceRe_EReal
          (a := a) (b := b) (c := c) hA ψ.state.pos hp.1 (le_of_lt hp.2)
    _ =
      ⨆ τ : State c,
        ⨅ sigma : CMatrix b,
          ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma, F sigma τ.matrix := by
        exact (state_iSup_matrix_eq_densityMatrixSet_iSup
          (fun tau => ⨅ sigma : CMatrix b,
            ⨅ _hSigma : (State.fullRankDensityMatrixSet b) sigma, F sigma tau)).symm
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // σ.matrix.PosDef}, F σ.val.matrix τ.matrix := by
        apply iSup_congr
        intro τ
        exact (fullRankState_iInf_matrix_eq_fullRankDensityMatrixSet_iInf
          (fun sigma => F sigma τ.matrix)).symm
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // σ.matrix.PosDef},
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    {delta alpha : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ (Fintype.card b : ℝ)⁻¹)
    (halpha : 1 < alpha) :
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) ≤
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  calc
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal))
        ≤
      (⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
        ⨆ τ : State c,
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) := by
        exact fullRankState_iInf_le_uniformlyPositiveState_iInf_EReal hdelta_pos
          (fun σ : State b =>
            ⨆ τ : State c,
              (sandwichedMutualInformationSionBracketRe rhoA ψ σ τ alpha : EReal))
    _ =
      ⨆ τ : State c,
        ⨅ σ : {σ : State b // delta • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) :=
        sandwichedAlpha_sion_mutualInformationBracket_EReal
          rhoA ψ hdelta_pos hdelta_le halpha

end PureVector

/-- Every full-rank state belongs to some uniformly-positive compact Sion
domain with the source normalization bound `delta <= 1 / |B|`.

This is the local regularization bookkeeping used when the KW proof removes
the compact full-support cutoff after applying Sion: positive definiteness gives
a scalar lower spectral bound, and we shrink it if needed to meet the
`uniformlyPositiveDensityMatrixSet_nonempty` side condition. -/
theorem exists_uniformlyPositiveDensityMatrixSet_mem_of_posDef
    {b : Type v1} [Fintype b] [DecidableEq b]
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹ ∧
      σ.matrix ∈ State.uniformlyPositiveDensityMatrixSet delta b := by
  classical
  haveI : Nonempty b := σ.nonempty
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
  exact ⟨State.state_matrix_mem_densityMatrixSet σ, hdelta_one_le_c_one.trans hc_le⟩

/-- Pointwise removal of the compact uniformly-positive cutoff.

For a fixed objective over side states, optimizing over all full-rank states is
the same as first imposing a source-valid cutoff `delta • I <= sigma` and then
letting `delta` range over all positive values allowed by the Sion compactness
side condition.  This is the order-theoretic core of the KW `delta downarrow 0`
step before any supremum over the purifying side is considered. -/
theorem fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal
    {b : Type v1} [Fintype b] [DecidableEq b] (f : State b → EReal) :
    (⨅ σ : {σ : State b // σ.matrix.PosDef}, f σ.val) =
      ⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
        ⨅ σ : {σ : State b // delta.val • (1 : CMatrix b) ≤ σ.matrix}, f σ.val := by
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
          ⨅ τ : {τ : State b // delta.val • (1 : CMatrix b) ≤ τ.matrix}, f τ.val) ≤
          ⨅ τ : {τ : State b // delta • (1 : CMatrix b) ≤ τ.matrix}, f τ.val :=
      iInf_le
        (fun delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹} =>
          ⨅ τ : {τ : State b // delta.val • (1 : CMatrix b) ≤ τ.matrix}, f τ.val)
        ⟨delta, hdelta_pos, hdelta_le⟩
    have hright :
        (⨅ τ : {τ : State b // delta • (1 : CMatrix b) ≤ τ.matrix}, f τ.val) ≤
          f σ.val :=
      iInf_le
        (fun τ : {τ : State b // delta • (1 : CMatrix b) ≤ τ.matrix} => f τ.val)
        ⟨σ.val, hσmem.2⟩
    exact hleft.trans hright

namespace PureVector

/-- Fixed-`tau_C` specialization of the pointwise `delta downarrow 0` removal
for the KW Sion bracket.

This is the exact statement obtained by applying
`fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal` to the source
bracket.  It is intentionally pointwise in `tau_C`; the remaining reverse
alternate-expression step must still justify moving this cutoff removal through
the `tau_C` supremum. -/
theorem sandwichedMutualInformationSionBracketRe_fullRank_iInf_eq_iInf_uniformlyPositive
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τ : State c) {alpha : ℝ} :
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal)) =
      ⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
        ⨅ σ : {σ : State b // delta.val • (1 : CMatrix b) ≤ σ.matrix},
          (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha : EReal) := by
  simpa using
    fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal
      (b := b)
      (fun σ : State b =>
        (sandwichedMutualInformationSionBracketRe rhoA ψ σ τ alpha : EReal))

/-- Logarithmic fixed-`tau_C` form of the pointwise `delta downarrow 0`
removal for the KW Sion bracket. -/
theorem sandwichedMutualInformationSionBracketLog_fullRank_iInf_eq_iInf_uniformlyPositive
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τ : State c) {alpha : ℝ} :
    (⨅ σ : {σ : State b // σ.matrix.PosDef},
        ((alpha / (alpha - 1) *
          log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha) : ℝ) :
          EReal)) =
      ⨅ delta : {delta : ℝ // 0 < delta ∧ delta ≤ (Fintype.card b : ℝ)⁻¹},
        ⨅ σ : {σ : State b // delta.val • (1 : CMatrix b) ≤ σ.matrix},
          ((alpha / (alpha - 1) *
            log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σ.val τ alpha) : ℝ) :
            EReal) := by
  simpa using
    fullRankState_iInf_eq_iInf_uniformlyPositiveState_iInf_EReal
      (b := b)
      (fun σ : State b =>
        ((alpha / (alpha - 1) *
          log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σ τ alpha) : ℝ) :
          EReal))

end PureVector

/-- The positive prefactor `alpha / (alpha - 1)` appearing in every
sandwiched-Renyi alternate expression for `alpha > 1`. -/
theorem sandwichedCoeff_pos {alpha : ℝ} (halpha : 1 < alpha) :
    0 < alpha / (alpha - 1) := by
  exact div_pos (lt_trans zero_lt_one halpha) (sub_pos.mpr halpha)

/-- The output-side weighting exponent used in
`S_sigma^(alpha)` is negative on the high-alpha branch. -/
theorem sandwichedSideWeightExponent_neg {alpha : ℝ} (halpha : 1 < alpha) :
    (1 - alpha) / (2 * alpha) < 0 := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have hden_pos : 0 < 2 * alpha := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hden_pos

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

namespace PureVector

/-- Each supported side-information state gives a reverse-Holder objective
value for the KW `AC` trace matrix. -/
theorem sandwichedMutualInformationSionBracketRe_mem_reverseHolderStateValueSet
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) {alpha : ℝ} (halpha : 1 < alpha)
    (hSupport :
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.matrix) :
    sandwichedMutualInformationSionBracketRe rhoA ψ σB τC alpha ∈
      psdTraceReverseHolderStateValueSet
        (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        (alpha / (2 * alpha - 1)) := by
  refine ⟨σB.matrix, σB.pos, ?_, hSupport, ?_⟩
  · simpa using congrArg Complex.re σB.trace_eq_one
  · rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
    rw [sandwichedAlternate_reverseHolderExponent halpha]

/-- Reverse-Holder lower-bound direction for a fixed supported `σ_B` in the
KW Sion bracket. -/
theorem psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c) {alpha : ℝ} (halpha : 1 < alpha)
    (hSupport :
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.matrix) :
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hSupport :
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.matrix) :
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
  exact mul_le_mul_of_nonneg_left hlog (le_of_lt (sandwichedCoeff_pos halpha))

/-- Full-rank side-information specialization of
`sandwichedACTraceMatrixLog_le_SionBracketLog_of_support`.

This is the form needed on the full-rank `sigma_B` branch of the KW
alternate-expression proof. -/
theorem sandwichedACTraceMatrixLog_le_SionBracketLog_posDef
    {a : Type u1} {b : Type v1} {c : Type u2}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (σB : State b) (τC : State c)
    (hrhoA : rhoA.matrix.PosDef) (hσB : σB.matrix.PosDef)
    (hτC : τC.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) (hrhoA : rhoA.matrix.PosDef) (hτC : τC.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA ψ τC alpha)
            (sandwichedAlternateSchattenOrder halpha)) ≤
      sInf (Set.range fun σB : {σ : State b // σ.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (sandwichedMutualInformationSionBracketRe rhoA ψ σB.1 τC alpha)) := by
  haveI : Nonempty {σ : State b // σ.matrix.PosDef} :=
    ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) {alpha : ℝ} (halpha : 1 < alpha)
    (hMne : sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha ≠ 0) :
    ∃ σB : State b,
      Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
        σB.matrix ∧
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
  let σB : State b := { matrix := N, pos := hN, trace_eq_one := hNtrace }
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
    (rhoA : State a) (ψ : PureVector (Prod (Prod a b) c))
    (τC : State c) {alpha : ℝ} (halpha : 1 < alpha)
    (hMne : sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha ≠ 0) :
    sInf (Set.range fun σB :
        {σ : State b //
          Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA ψ τC alpha)
            σ.matrix} =>
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
      {σ : State b // Matrix.Supports M σ.matrix} =>
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
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) {alpha : Real} (halpha : 1 < alpha)
    (hMzero : sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha = 0) :
    sInf (Set.range fun sigmaB :
        {sigma : State b //
          Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            sigma.matrix} =>
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
          (sandwichedAlternateSchattenOrder halpha) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha
  let hM : M.PosSemidef := sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha
  let target : Real :=
    psdSchattenPNorm M hM (sandwichedAlternateSchattenOrder halpha)
  let S : Set Real := Set.range fun sigmaB :
      {sigma : State b // Matrix.Supports M sigma.matrix} =>
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
      forall sigmaB : {sigma : State b // Matrix.Supports M sigma.matrix},
        sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha = 0 := by
    intro sigmaB
    rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma]
    simp [M, hMzero']
  let sigma0 : {sigma : State b // Matrix.Supports M sigma.matrix} :=
    ⟨State.maximallyMixed b, by
      intro v hv
      simp [M, hMzero']⟩
  have hmem : (0 : Real) ∈ S := by
    refine ⟨sigma0, ?_⟩
    exact hvalue sigma0
  have hLower : (0 : Real) ∈ lowerBounds S := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    change (0 : Real) <=
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
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) {alpha : Real} (halpha : 1 < alpha) :
    sInf (Set.range fun sigmaB :
        {sigma : State b //
          Matrix.Supports (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            sigma.matrix} =>
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
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) {alpha : Real} (halpha : 1 < alpha) :
    sInf (Set.range fun sigmaB : {sigma : State b // sigma.matrix.PosDef} =>
      sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha) =
        psdSchattenPNorm
          (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
          (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
          (sandwichedAlternateSchattenOrder halpha) := by
  let M : CMatrix b := sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha
  let hM : M.PosSemidef :=
    sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha
  let p : SchattenOrder := sandwichedAlternateSchattenOrder halpha
  let r : Real := (1 - alpha) / alpha
  let target : Real := psdSchattenPNorm M hM p
  let S := {sigma : State b // sigma.matrix.PosDef}
  let f : S -> Real := fun sigmaB =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
  have hLower : target ∈ lowerBounds (Set.range f) := by
    intro y hy
    rcases hy with ⟨sigmaB, rfl⟩
    simpa [target, p, f, M, hM] using
      psdSchattenPNorm_ACTraceMatrix_le_SionBracketRe_of_support
        rhoA psi sigmaB.1 tauC halpha
        (Matrix.Supports.of_right_posDef M sigmaB.1.matrix sigmaB.2)
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
    let N0 : CMatrix b := sigma0.matrix
    have hN0 : N0.PosSemidef := sigma0.pos
    have hN0trace : N0.trace = 1 := sigma0.trace_eq_one
    have hN0trace_re : N0.trace.re = 1 := by
      simpa [N0] using congrArg Complex.re hN0trace
    have htrace_target :
        ((M * CFC.rpow N0 r).trace).re = target := by
      have h := hsigma0
      rw [sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma] at h
      simpa [M, N0, r, target, p, hM] using h
    let raw : Real -> Real := fun eps =>
      ((M * CFC.rpow (N0 + eps • (1 : CMatrix b)) r).trace).re
    let scale : Real -> Real := fun eps =>
      ((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹
    let reg : Real -> CMatrix b := fun eps =>
      scale eps • (N0 + eps • (1 : CMatrix b))
    have hraw :
        Filter.Tendsto raw (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds target) := by
      have h :=
        trace_mul_cMatrix_rpow_add_pos_smul_one_tendsto_of_support
          hN0 (by simpa [M, N0] using hSupport0) r
      have h' :
          Filter.Tendsto raw (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhds ((M * CFC.rpow N0 r).trace.re)) := by
        simpa [raw, M, N0] using h
      rw [← htrace_target]
      exact h'
    have htraceScale :
        Filter.Tendsto scale (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) := by
      have htrace :
          Filter.Tendsto (fun eps : Real => (N0 + eps • (1 : CMatrix b)).trace.re)
            (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) := by
        have hcont : Continuous fun eps : Real =>
            (N0 + eps • (1 : CMatrix b)).trace.re := by
          fun_prop
        have hlim := (hcont.tendsto (0 : Real)).mono_left
          (nhdsWithin_le_nhds (a := (0 : Real)) (s := Set.Ioi (0 : Real)))
        simpa [N0, hN0trace_re] using hlim
      simpa [scale] using htrace.inv₀ one_ne_zero
    have hscalePow :
        Filter.Tendsto (fun eps : Real => scale eps ^ r)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (1 : Real)) := by
      have hpow :=
        (Real.continuousAt_rpow_const (1 : Real) r (Or.inl one_ne_zero)).tendsto.comp
          htraceScale
      simpa using hpow
    have hregValue :
        Filter.Tendsto
          (fun eps : Real => ((M * CFC.rpow (reg eps) r).trace).re)
          (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds target) := by
      have heq :
          (fun eps : Real => ((M * CFC.rpow (reg eps) r).trace).re)
            =ᶠ[nhdsWithin (0 : Real) (Set.Ioi 0)]
          fun eps : Real => scale eps ^ r * raw eps := by
        filter_upwards [self_mem_nhdsWithin] with eps heps
        have hBpos : (N0 + eps • (1 : CMatrix b)).PosDef :=
          State.cMatrix_posSemidef_add_pos_smul_one_posDef hN0 heps
        have hscale_pos : 0 < scale eps := by
          have htr_pos : 0 < (N0 + eps • (1 : CMatrix b)).trace.re := by
            exact (Matrix.PosDef.trace_pos hBpos).1
          exact inv_pos.mpr htr_pos
        have hpow :
            CFC.rpow (reg eps) r =
              (scale eps ^ r : Real) •
                CFC.rpow (N0 + eps • (1 : CMatrix b)) r := by
          simpa [reg] using
            cMatrix_rpow_real_smul_posSemidef_schatten hBpos.posSemidef
              (le_of_lt hscale_pos) (s := r)
        change ((M * CFC.rpow (reg eps) r).trace).re = scale eps ^ r * raw eps
        rw [hpow]
        simp [raw, Matrix.trace_smul, Complex.real_smul]
      have hprod :
          Filter.Tendsto (fun eps : Real => scale eps ^ r * raw eps)
            (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds target) := by
        simpa using hscalePow.mul hraw
      exact hprod.congr' heq.symm
    have hupper : sInf (Set.range f) <= target := by
      exact ge_of_tendsto hregValue (by
        filter_upwards [self_mem_nhdsWithin] with eps heps
        have hBpos : (N0 + eps • (1 : CMatrix b)).PosDef :=
          State.cMatrix_posSemidef_add_pos_smul_one_posDef hN0 heps
        have htr_pos : 0 < (N0 + eps • (1 : CMatrix b)).trace.re := by
          exact (Matrix.PosDef.trace_pos hBpos).1
        have hscale_pos : 0 < scale eps := inv_pos.mpr htr_pos
        have hreg_pos : (reg eps).PosDef := by
          simpa [reg] using Matrix.PosDef.smul hBpos hscale_pos
        have hreg_trace : (reg eps).trace = 1 := by
          have htr_real :
              (N0 + eps • (1 : CMatrix b)).trace =
                ((N0 + eps • (1 : CMatrix b)).trace.re : Complex) := by
            exact posSemidef_trace_eq_re_coe hBpos.posSemidef
          have htr_ne : (N0 + eps • (1 : CMatrix b)).trace.re ≠ 0 :=
            ne_of_gt htr_pos
          calc
            (reg eps).trace =
                (scale eps : Complex) * (N0 + eps • (1 : CMatrix b)).trace := by
                  change (scale eps • (N0 + eps • (1 : CMatrix b))).trace =
                    (scale eps : Complex) * (N0 + eps • (1 : CMatrix b)).trace
                  rw [Matrix.trace_smul]
                  simpa using (Complex.real_smul (x := scale eps)
                    (z := (N0 + eps • (1 : CMatrix b)).trace))
            _ = (scale eps : Complex) *
                ((N0 + eps • (1 : CMatrix b)).trace.re : Complex) := by
                  exact congrArg (fun z : Complex => (scale eps : Complex) * z) htr_real
            _ = 1 := by
                  have htr_ne_complex :
                      ((N0 + eps • (1 : CMatrix b)).trace.re : Complex) ≠ 0 := by
                    exact_mod_cast htr_ne
                  have hscale_eq :
                      (scale eps : Complex) =
                        ((((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹ : Real) : Complex) := by
                    change ((((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹ : Real) : Complex) =
                      ((((N0 + eps • (1 : CMatrix b)).trace.re)⁻¹ : Real) : Complex)
                    rfl
                  rw [hscale_eq]
                  simpa using inv_mul_cancel₀ htr_ne_complex
        let sigmaReg : State b :=
          { matrix := reg eps, pos := hreg_pos.posSemidef, trace_eq_one := hreg_trace }
        have hsigmaReg : sigmaReg.matrix.PosDef := hreg_pos
        have hmem :
            ((M * CFC.rpow (reg eps) r).trace).re ∈ Set.range f := by
          refine ⟨⟨sigmaReg, hsigmaReg⟩, ?_⟩
          change sandwichedMutualInformationSionBracketRe rhoA psi sigmaReg tauC alpha =
            ((M * CFC.rpow (reg eps) r).trace).re
          simpa [sigmaReg, M, r] using
            sandwichedMutualInformationSionBracketRe_eq_trace_ACTraceMatrix_mul_sigma
              rhoA psi sigmaReg tauC alpha
        exact csInf_le hBdd hmem)
    have hlower : target <= sInf (Set.range f) :=
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
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) (hrhoA : rhoA.matrix.PosDef) (htauC : tauC.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    sInf (Set.range fun sigmaB : {sigma : State b // sigma.matrix.PosDef} =>
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha)) =
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
            (sandwichedAlternateSchattenOrder halpha)) := by
  let S := {sigma : State b // sigma.matrix.PosDef}
  let raw : S → ℝ := fun sigmaB =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let target : ℝ :=
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
      (sandwichedAlternateSchattenOrder halpha)
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
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
          sigmaB.1.matrix sigmaB.2)
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
    simpa [coeff] using sandwichedCoeff_pos halpha)
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
    (rhoA : State a) (psi : PureVector (Prod (Prod a b) c))
    (tauC : State c) {alpha : Real} (halpha : 1 < alpha)
    (hMne : sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha ≠ 0) :
    sInf (Set.range fun sigmaB : {sigma : State b // sigma.matrix.PosDef} =>
      alpha / (alpha - 1) *
        log2 (sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha)) =
      alpha / (alpha - 1) *
        log2
          (psdSchattenPNorm
            (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
            (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
            (sandwichedAlternateSchattenOrder halpha)) := by
  let S := {sigma : State b // sigma.matrix.PosDef}
  let raw : S → ℝ := fun sigmaB =>
    sandwichedMutualInformationSionBracketRe rhoA psi sigmaB.1 tauC alpha
  let coeff : ℝ := alpha / (alpha - 1)
  let target : ℝ :=
    psdSchattenPNorm
      (sandwichedMutualInformationACTraceMatrix rhoA psi tauC alpha)
      (sandwichedMutualInformationACTraceMatrix_posSemidef rhoA psi tauC alpha)
      (sandwichedAlternateSchattenOrder halpha)
  haveI : Nonempty S := ⟨⟨State.maximallyMixed b, State.maximallyMixed_posDef⟩⟩
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
          sigmaB.1.matrix sigmaB.2)
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
    simpa [coeff] using sandwichedCoeff_pos halpha)
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

end PureVector
end

end QIT
