/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Additivity.ChannelAlternate

/-!
# Channel product branch for sandwiched EA additivity

This module is part of the Khatri--Wilde sandwiched-Renyi additivity proof
spine for entanglement-assisted classical communication.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Pointwise

namespace QIT

universe u1 v1 u2 v2

noncomputable section

namespace Channel

variable {a1 : Type u1} {b1 : Type v1} {a2 : Type u2} {b2 : Type v2}
variable [Fintype a1] [DecidableEq a1] [Fintype b1] [DecidableEq b1]
variable [Fintype a2] [DecidableEq a2] [Fintype b2] [DecidableEq b2]

/-- Product-reference version of the KW channel alternate-expression
upper bound.

This is the order step used by the channel subadditivity proof after
restricting the side-reference infimum to product states, matching
`EA_capacity.tex:1247-1252`. -/
theorem sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hBelow :
      BddBelow (Set.range fun
          p : {sigma : State b1 // sigma.matrix.PosDef} ×
              {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
          (SchattenOrder.ofOneLt halpha))) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun
          p : {sigma : State b1 // sigma.matrix.PosDef} ×
              {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
          (SchattenOrder.ofOneLt halpha)) :
          ℝ) : EReal) := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  haveI : Nonempty S1 := ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty S2 := ⟨⟨State.maximallyMixed b2, State.maximallyMixed_posDef⟩⟩
  let f : S1 × S2 → ℝ := fun p =>
    sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
      (SchattenOrder.ofOneLt halpha)
  have hInf :
      sInf (Set.range fun p : S1 × S2 => ((f p : ℝ) : EReal)) =
        ((sInf (Set.range f) : ℝ) : EReal) :=
    ereal_sInf_range_coe_eq_coe_real_sInf f (by simpa [S1, S2, f] using hBelow)
  rw [(N1.prod N2).sandwichedRenyiMutualInformationE_eq_sSup]
  refine csSup_le ((N1.prod N2).sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  rintro y ⟨psi, rfl⟩
  have hleInf :
      (N1.prod N2).inputSandwichedRenyiMutualInformationE psi alpha ≤
        sInf (Set.range fun p : S1 × S2 => ((f p : ℝ) : EReal)) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro z ⟨p, rfl⟩
    have hsigma : (p.1.1.prod p.2.1).matrix.PosDef :=
      State.prod_posDef p.1.2 p.2.2
    simpa [S1, S2, f] using
      inputSandwichedRenyiMutualInformationE_le_CBNormExpression
        (N1.prod N2) (p.1.1.prod p.2.1) psi hsigma halpha
  simpa [S1, S2, f, hInf] using hleInf

/-- Product-reference KW upper bound in extended-real `inf` form.

This is the product-channel analogue of
`sandwichedRenyiMutualInformationE_le_fullRankCB_sInf_EReal`.  It proves the
source order step after restricting the product channel side reference to
full-rank product states, without importing the real bounded-below hypotheses
used by the scalar split theorem. -/
theorem sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf_EReal
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      sInf (Set.range fun
          p : Prod {sigma : State b1 // sigma.matrix.PosDef}
              {sigma : State b2 // sigma.matrix.PosDef} =>
        ((sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
          (SchattenOrder.ofOneLt halpha) : ℝ) : EReal)) := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  haveI : Nonempty S1 := ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty S2 := ⟨⟨State.maximallyMixed b2, State.maximallyMixed_posDef⟩⟩
  let f : Prod S1 S2 → ℝ := fun p =>
    sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
      (SchattenOrder.ofOneLt halpha)
  rw [(N1.prod N2).sandwichedRenyiMutualInformationE_eq_sSup]
  refine csSup_le ((N1.prod N2).sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  rintro y ⟨psi, rfl⟩
  refine le_csInf (Set.range_nonempty _) ?_
  rintro z ⟨p, rfl⟩
  have hsigma : (p.1.1.prod p.2.1).matrix.PosDef :=
    State.prod_posDef p.1.2 p.2.2
  simpa [S1, S2, f] using
    inputSandwichedRenyiMutualInformationE_le_CBNormExpression
      (N1.prod N2) (p.1.1.prod p.2.1) psi hsigma halpha

/-- For full-rank side information, the maximally mixed source-side CB
candidate has strictly positive value under the KW weighted channel map. -/
theorem cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_maximallyMixed_pos_of_posDef
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 0 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaOriginalValue
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        { matrix := (State.maximallyMixed a1).matrix,
          pos := (State.maximallyMixed a1).pos,
          trace_le_one := by
            rw [(State.maximallyMixed a1).trace_eq_one]
            norm_num }
        (SchattenOrder.ofPositive halpha) := by
  let Y0 : MatrixMap.CBOneToAlphaOriginalDomain a1 :=
    { matrix := (State.maximallyMixed a1).matrix,
      pos := (State.maximallyMixed a1).pos,
      trace_le_one := by
        rw [(State.maximallyMixed a1).trace_eq_one]
        norm_num }
  let X : CMatrix (Prod a1 a1) := MatrixMap.cbOneToAlphaOriginalInput Y0.matrix alpha
  let hX : X.PosSemidef := MatrixMap.cbOneToAlphaOriginalInput_posSemidef Y0.pos alpha
  have hXne : X ≠ 0 := by
    simpa [X, Y0] using MatrixMap.cbOneToAlphaOriginalInput_maximallyMixed_ne_zero
      (a1 := a1) halpha
  have hPhiXne :
      MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X ≠ 0 :=
    sandwichedSideWeightedMap_referenceLift_apply_ne_zero_of_posDef
      N sigma hsigma alpha hX hXne
  unfold MatrixMap.cbOneToAlphaOriginalValue
  change 0 <
    psdSchattenPNorm
      (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _
      (SchattenOrder.ofPositive halpha)
  exact psdSchattenPNorm_pos_of_ne_zero
    (MatrixMap.referenceLift (sandwichedSideWeightedMap N sigma alpha) X) _ hPhiXne

/-- Full-rank side information makes the KW weighted-channel CB norm strictly
positive, so the source logarithm is on the nonzero branch. -/
theorem cbOneToAlphaNorm_sandwichedSideWeightedMap_pos_of_posDef
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaNorm
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        (SchattenOrder.ofOneLt halpha) := by
  let Y0 : MatrixMap.CBOneToAlphaOriginalDomain a1 :=
    { matrix := (State.maximallyMixed a1).matrix,
      pos := (State.maximallyMixed a1).pos,
      trace_le_one := by
        rw [(State.maximallyMixed a1).trace_eq_one]
        norm_num }
  have hval_pos :
      0 <
        MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y0
          (SchattenOrder.ofOneLt halpha) := by
    simpa [Y0] using
      cbOneToAlphaOriginalValue_sandwichedSideWeightedMap_maximallyMixed_pos_of_posDef
        N sigma hsigma (lt_trans zero_lt_one halpha)
  have hval_le :
      MatrixMap.cbOneToAlphaOriginalValue
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          Y0
          (SchattenOrder.ofOneLt halpha) ≤
        MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N sigma alpha)
          (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
          (SchattenOrder.ofOneLt halpha) := by
    exact MatrixMap.cbOneToAlphaOriginalValue_le_cbOneToAlphaNorm_of_one_lt
      (sandwichedSideWeightedMap N sigma alpha)
      (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
      halpha
      Y0
  exact lt_of_lt_of_le hval_pos hval_le

/-- Full-rank side information also makes the KW alternate CB expression
strictly positive after substituting the proved CB alternate-expression theorem. -/
theorem cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_pos_of_posDef
    [Nonempty a1] (N : Channel a1 b1) (sigma : State b1)
    (hsigma : sigma.matrix.PosDef) {alpha : ℝ} (halpha : 1 < alpha) :
    0 <
      MatrixMap.cbOneToAlphaAlternateExpression
        (sandwichedSideWeightedMap N sigma alpha)
        (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
        (SchattenOrder.ofOneLt halpha) := by
  rw [← MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap N sigma alpha)
    (sandwichedSideWeightedMap_completelyPositive N sigma alpha)
    halpha]
  exact cbOneToAlphaNorm_sandwichedSideWeightedMap_pos_of_posDef
    N sigma hsigma halpha

/-- Product pure input for the sandwiched entanglement-assisted objective of a
product channel, repartitioned from `(A1 x A1) x (A2 x A2)` to
`(A1 x A2) x (A1 x A2)`. -/
def sandwichedRenyiProductInput
    (psi : PureVector (Prod a1 a1)) (phi : PureVector (Prod a2 a2)) :
    PureVector (Prod (Prod a1 a2) (Prod a1 a2)) :=
  (psi.prod phi).reindex
    (State.bipartiteProductEquiv (a1 := a1) (b1 := a1) (a2 := a2) (b2 := a2))

/-- Applying a product channel to a repartitioned product input yields the
repartitioned product of the two individual output states. -/
private theorem applyState_prod_reindex_sandwichedRenyiProductInput
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (rho : State (Prod a1 a1)) (sigma : State (Prod a2 a2)) :
    (((Channel.idChannel (Prod a1 a2)).prod (N1.prod N2)).applyState
        ((rho.prod sigma).reindex
          (State.bipartiteProductEquiv
            (a1 := a1) (b1 := a1) (a2 := a2) (b2 := a2)))) =
      ((((Channel.idChannel a1).prod N1).applyState rho).prod
          (((Channel.idChannel a2).prod N2).applyState sigma)).reindex
        (State.bipartiteProductEquiv
          (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2)) := by
  apply State.ext
  ext x y
  rcases x with ⟨xR, xB⟩
  rcases y with ⟨yR, yB⟩
  rcases xR with ⟨xR1, xR2⟩
  rcases xB with ⟨xB1, xB2⟩
  rcases yR with ⟨yR1, yR2⟩
  rcases yB with ⟨yB1, yB2⟩
  simp only [Channel.applyState, Channel.prod, State.reindex_matrix,
    State.prod_matrix_kronecker, Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hslice :
      (fun j j' =>
          (Matrix.kronecker rho.matrix sigma.matrix).submatrix
            (State.bipartiteProductEquiv
              (a1 := a1) (b1 := a1) (a2 := a2) (b2 := a2)).symm
            (State.bipartiteProductEquiv
              (a1 := a1) (b1 := a1) (a2 := a2) (b2 := a2)).symm
            (((xR1, xR2), (xB1, xB2)).1, j)
            (((yR1, yR2), (yB1, yB2)).1, j')) =
        Matrix.kronecker
          (fun i i' => rho.matrix (xR1, i) (yR1, i'))
          (fun k k' => sigma.matrix (xR2, k) (yR2, k')) := by
    ext z z'
    rcases z with ⟨z1, z2⟩
    rcases z' with ⟨z1', z2'⟩
    simp [State.bipartiteProductEquiv, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
  rw [hslice]
  change MatrixMap.kron N1.map N2.map
      (Matrix.kronecker
        (fun i i' => rho.matrix (xR1, i) (yR1, i'))
        (fun k k' => sigma.matrix (xR2, k) (yR2, k')))
      (xB1, xB2) (yB1, yB2) = _
  rw [MatrixMap.kron_apply_kronecker]
  simp [State.bipartiteProductEquiv, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rw [MatrixMap.kron_idChannel_left_apply_slice]

/-- Product-channel output states factor on the product pure inputs used by the
sandwiched entanglement-assisted objective. -/
theorem hypothesisTestingOutputState_prod
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (psi : PureVector (Prod a1 a1)) (phi : PureVector (Prod a2 a2)) :
    (N1.prod N2).hypothesisTestingOutputState
        (sandwichedRenyiProductInput psi phi) =
      (N1.hypothesisTestingOutputState psi).bipartiteProduct
        (N2.hypothesisTestingOutputState phi) := by
  unfold Channel.hypothesisTestingOutputState sandwichedRenyiProductInput
  rw [PureVector.reindex_state, PureVector.prod_state]
  exact applyState_prod_reindex_sandwichedRenyiProductInput
    N1 N2 psi.state phi.state

/-- Product pure inputs reduce the channel sandwiched-Renyi objective to the
bipartite product output state.  This is the first source step in the
superadditivity half of Khatri--Wilde, `EA_capacity.tex:1224-1234`. -/
theorem inputSandwichedRenyiMutualInformationE_prodProductInput
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (psi : PureVector (Prod a1 a1)) (phi : PureVector (Prod a2 a2))
    (alpha : ℝ) :
    (N1.prod N2).inputSandwichedRenyiMutualInformationE
        (sandwichedRenyiProductInput psi phi) alpha =
      ((N1.hypothesisTestingOutputState psi).bipartiteProduct
        (N2.hypothesisTestingOutputState phi)).sandwichedRenyiMutualInformationE alpha := by
  unfold Channel.inputSandwichedRenyiMutualInformationE
  rw [hypothesisTestingOutputState_prod]

/-- The product-output state value obtained from product pure inputs is below
the optimized product-channel sandwiched-Renyi mutual information.  This is the
order-theoretic supremum step in the superadditivity half of
Khatri--Wilde, `EA_capacity.tex:1224-1234`. -/
theorem bipartiteProduct_output_sandwichedRenyiMutualInformationE_le_prodChannel
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (psi : PureVector (Prod a1 a1)) (phi : PureVector (Prod a2 a2))
    (alpha : ℝ) :
    ((N1.hypothesisTestingOutputState psi).bipartiteProduct
        (N2.hypothesisTestingOutputState phi)).sandwichedRenyiMutualInformationE alpha ≤
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha := by
  rw [← inputSandwichedRenyiMutualInformationE_prodProductInput N1 N2 psi phi alpha]
  exact (N1.prod N2).inputSandwichedRenyiMutualInformationE_le_channel
    (sandwichedRenyiProductInput psi phi) alpha

/-- KW superadditivity order bridge for product channels.

This is the supremum step in `EA_capacity.tex:1229-1238`: once the product
output states satisfy the state-level product lower bound, restricting the
channel optimization to product pure inputs gives the corresponding
channel-level lower bound. -/
theorem sandwichedRenyiMutualInformationE_prod_ge_add_of_state_product_ge
    [Nonempty a1] [Nonempty a2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) (alpha : ℝ)
    (hstate :
      ∀ psi : PureVector (Prod a1 a1), ∀ phi : PureVector (Prod a2 a2),
        N1.inputSandwichedRenyiMutualInformationE psi alpha +
            N2.inputSandwichedRenyiMutualInformationE phi alpha ≤
          ((N1.hypothesisTestingOutputState psi).bipartiteProduct
            (N2.hypothesisTestingOutputState phi)).sandwichedRenyiMutualInformationE alpha) :
    N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha ≤
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha := by
  haveI : Nonempty (PureVector (Prod a1 a1)) := ⟨PureVector.basisPureVector⟩
  haveI : Nonempty (PureVector (Prod a2 a2)) := ⟨PureVector.basisPureVector⟩
  rw [N1.sandwichedRenyiMutualInformationE_eq_sSup,
    N2.sandwichedRenyiMutualInformationE_eq_sSup]
  refine EReal.add_le_of_forall_lt ?_
  intro x hx y hy
  obtain ⟨value1, hvalue1, hxvalue1⟩ :=
    exists_lt_of_lt_csSup
      (Set.range_nonempty
        (fun psi : PureVector (Prod a1 a1) =>
          N1.inputSandwichedRenyiMutualInformationE psi alpha))
      hx
  obtain ⟨value2, hvalue2, hyvalue2⟩ :=
    exists_lt_of_lt_csSup
      (Set.range_nonempty
        (fun phi : PureVector (Prod a2 a2) =>
          N2.inputSandwichedRenyiMutualInformationE phi alpha))
      hy
  rcases hvalue1 with ⟨psi, rfl⟩
  rcases hvalue2 with ⟨phi, rfl⟩
  exact (EReal.add_lt_add hxvalue1 hyvalue2).le.trans
    ((hstate psi phi).trans
      (bipartiteProduct_output_sandwichedRenyiMutualInformationE_le_prodChannel
        N1 N2 psi phi alpha))

/-- KW superadditivity bridge stated with the eventual state product theorem.

The hypothesis is exactly the state-level lower-bound half of
`EA_capacity.tex:1193-1214`; the conclusion is the channel superadditivity
step used in `EA_capacity.tex:1229-1238`. -/
theorem sandwichedRenyiMutualInformationE_prod_ge_add_of_bipartiteProduct_ge
    [Nonempty a1] [Nonempty a2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) (alpha : ℝ)
    (hstate :
      ∀ xi : State (Prod a1 b1), ∀ omega : State (Prod a2 b2),
        xi.sandwichedRenyiMutualInformationE alpha +
            omega.sandwichedRenyiMutualInformationE alpha ≤
          (xi.bipartiteProduct omega).sandwichedRenyiMutualInformationE alpha) :
    N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha ≤
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha := by
  refine sandwichedRenyiMutualInformationE_prod_ge_add_of_state_product_ge
    N1 N2 alpha ?_
  intro psi phi
  exact hstate (N1.hypothesisTestingOutputState psi) (N2.hypothesisTestingOutputState phi)

/-- KW channel superadditivity from the completed state-product lower branch.

This is the unconditional version of the `>=` half in
`EA_capacity.tex:1224-1238`: restrict the product-channel optimization to
product pure inputs, then apply state-level product additivity to the two
output states. -/
theorem sandwichedRenyiMutualInformationE_prod_ge_add
    [Nonempty a1] [Nonempty a2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha) :
    N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha ≤
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha := by
  refine sandwichedRenyiMutualInformationE_prod_ge_add_of_bipartiteProduct_ge
    N1 N2 alpha ?_
  intro xi omega
  exact State.sandwichedRenyiMutualInformationE_bipartiteProduct_ge_add
    xi omega halpha

/-- The CB `1 -> alpha` norm is multiplicative on the maps underlying product
channels.  This is the channel-level instance of the Khatri--Wilde
subadditivity step, `EA_capacity.tex:1242-1254`, using the source-backed
MatrixMap theorem from the CB-norm module. -/
theorem cbOneToAlphaNorm_prod_map_eq_mul
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaNorm (N1.prod N2).map (N1.prod N2).completelyPositive (SchattenOrder.ofOneLt halpha) =
      MatrixMap.cbOneToAlphaNorm N1.map N1.completelyPositive (SchattenOrder.ofOneLt halpha) *
        MatrixMap.cbOneToAlphaNorm N2.map N2.completelyPositive (SchattenOrder.ofOneLt halpha) := by
  simpa [Channel.prod] using
    (MatrixMap.cbOneToAlphaNorm_kron_eq_mul
      N1.map N1.completelyPositive N2.map N2.completelyPositive halpha)

/-- Channel-level form of the KW weighting-map product identity. -/
theorem sandwichedSideWeightMap_prod_comp_prod_map_posDef
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    (alpha : ℝ) :
    (MatrixMap.sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
        (N1.prod N2).map =
      MatrixMap.kron
        ((MatrixMap.sandwichedSideWeightMap sigma1 alpha).comp N1.map)
        ((MatrixMap.sandwichedSideWeightMap sigma2 alpha).comp N2.map) := by
  simpa [Channel.prod] using
    MatrixMap.sandwichedSideWeightMap_prod_comp_kron_posDef
      sigma1 sigma2 N1.map N2.map hsigma1 hsigma2 alpha

/-- Weighted product-channel maps factor as products of the weighted component
maps on full-rank product references. -/
theorem sandwichedSideWeightedMap_prod_posDef
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    (alpha : ℝ) :
    sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha =
      MatrixMap.kron (sandwichedSideWeightedMap N1 sigma1 alpha)
        (sandwichedSideWeightedMap N2 sigma2 alpha) := by
  simpa [sandwichedSideWeightedMap] using
    sandwichedSideWeightMap_prod_comp_prod_map_posDef
      N1 N2 sigma1 sigma2 hsigma1 hsigma2 alpha

/-- Channel-level weighted-map CB-norm multiplicativity for full-rank product
references, the map-norm step in KW `EA_capacity.tex:1242-1254`. -/
theorem cbOneToAlphaNorm_sandwichedSideWeightMap_prod_map_eq_mul_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaNorm
        ((MatrixMap.sandwichedSideWeightMap (sigma1.prod sigma2) alpha).comp
          (N1.prod N2).map)
        (MatrixMap.isCompletelyPositive_comp _ _
          (MatrixMap.sandwichedSideWeightMap_completelyPositive
            (sigma1.prod sigma2) alpha)
          (N1.prod N2).completelyPositive)
        (SchattenOrder.ofOneLt halpha) =
      MatrixMap.cbOneToAlphaNorm
          ((MatrixMap.sandwichedSideWeightMap sigma1 alpha).comp N1.map)
          (MatrixMap.isCompletelyPositive_comp _ _
            (MatrixMap.sandwichedSideWeightMap_completelyPositive sigma1 alpha)
            N1.completelyPositive)
          (SchattenOrder.ofOneLt halpha) *
        MatrixMap.cbOneToAlphaNorm
          ((MatrixMap.sandwichedSideWeightMap sigma2 alpha).comp N2.map)
          (MatrixMap.isCompletelyPositive_comp _ _
            (MatrixMap.sandwichedSideWeightMap_completelyPositive sigma2 alpha)
            N2.completelyPositive)
          (SchattenOrder.ofOneLt halpha) := by
  simpa [Channel.prod] using
    MatrixMap.cbOneToAlphaNorm_sandwichedSideWeightMap_prod_comp_kron_eq_mul_posDef
      sigma1 sigma2 N1.map N1.completelyPositive N2.map N2.completelyPositive
      hsigma1 hsigma2 halpha

/-- Weighted-map CB-norm multiplicativity, stated using the local weighted-map
abbreviation. -/
theorem cbOneToAlphaNorm_sandwichedSideWeightedMap_prod_eq_mul_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaNorm
        (sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha)
        (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
          (sigma1.prod sigma2) alpha)
        (SchattenOrder.ofOneLt halpha) =
      MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N1 sigma1 alpha)
          (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
          (SchattenOrder.ofOneLt halpha) *
        MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N2 sigma2 alpha)
          (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
          (SchattenOrder.ofOneLt halpha) := by
  simpa [sandwichedSideWeightedMap, sandwichedSideWeightedMap_completelyPositive] using
    cbOneToAlphaNorm_sandwichedSideWeightMap_prod_map_eq_mul_posDef
      N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha

/-- Multiplicativity of the KW alternate CB expression for full-rank product
side references, obtained by substituting the proved CB alternate-expression
theorem into the CB-norm multiplicativity step. -/
theorem cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_prod_eq_mul_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    MatrixMap.cbOneToAlphaAlternateExpression
        (sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha)
        (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
          (sigma1.prod sigma2) alpha)
        (SchattenOrder.ofOneLt halpha) =
      MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap N1 sigma1 alpha)
          (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
          (SchattenOrder.ofOneLt halpha) *
        MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap N2 sigma2 alpha)
          (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
          (SchattenOrder.ofOneLt halpha) := by
  rw [← MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha)
    (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
      (sigma1.prod sigma2) alpha)
    halpha]
  rw [← MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap N1 sigma1 alpha)
    (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
    halpha]
  rw [← MatrixMap.cbOneToAlphaNorm_eq_cbOneToAlphaAlternateExpression
    (sandwichedSideWeightedMap N2 sigma2 alpha)
    (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
    halpha]
  exact cbOneToAlphaNorm_sandwichedSideWeightedMap_prod_eq_mul_posDef
    N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha

/-- Log-additivity of the KW alternate CB expression on full-rank product
references.  This is the alternate-expression version of the scalar step used
in KW `EA_capacity.tex:1265-1267`. -/
theorem sandwichedRenyiCBAlternateExpression_prod_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    alpha / (alpha - 1) *
        log2 (MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap (N1.prod N2) (sigma1.prod sigma2) alpha)
          (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
            (sigma1.prod sigma2) alpha)
          (SchattenOrder.ofOneLt halpha)) =
      alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N1 sigma1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
            (SchattenOrder.ofOneLt halpha)) +
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N2 sigma2 alpha)
            (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
            (SchattenOrder.ofOneLt halpha)) := by
  rw [cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_prod_eq_mul_posDef
    N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha]
  rw [log2_mul
    (ne_of_gt (cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_pos_of_posDef
      N1 sigma1 hsigma1 halpha))
    (ne_of_gt (cbOneToAlphaAlternateExpression_sandwichedSideWeightedMap_pos_of_posDef
      N2 sigma2 hsigma2 halpha))]
  ring

/-- Full-rank product-reference infimum split written directly in the KW
alternate CB expression.

This is the source scalar optimization step after the CB alternate-expression
substitution.  The theorem is intentionally restricted to the full-rank domain;
the later channel alternate-expression theorem must still prove the singular
reference closure before this can close the optimized additivity theorem. -/
theorem sandwichedRenyiCBAlternateExpression_fullRankProduct_sInf_eq_add
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1 :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N1 sigma1.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N1 sigma1.1 alpha)
            (SchattenOrder.ofOneLt halpha))))
    (hN2 :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N2 sigma2.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N2 sigma2.1 alpha)
            (SchattenOrder.ofOneLt halpha)))) :
    sInf (Set.range fun
        p : {sigma : State b1 // sigma.matrix.PosDef} ×
            {sigma : State b2 // sigma.matrix.PosDef} =>
      alpha / (alpha - 1) *
        log2 (MatrixMap.cbOneToAlphaAlternateExpression
          (sandwichedSideWeightedMap (N1.prod N2) (p.1.1.prod p.2.1) alpha)
          (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
            (p.1.1.prod p.2.1) alpha)
          (SchattenOrder.ofOneLt halpha))) =
      sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N1 sigma1.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N1 sigma1.1 alpha)
            (SchattenOrder.ofOneLt halpha))) +
      sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap N2 sigma2.1 alpha)
            (sandwichedSideWeightedMap_completelyPositive N2 sigma2.1 alpha)
            (SchattenOrder.ofOneLt halpha))) := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  haveI : Nonempty S1 := ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty S2 := ⟨⟨State.maximallyMixed b2, State.maximallyMixed_posDef⟩⟩
  let f : S1 → ℝ := fun sigma1 =>
    alpha / (alpha - 1) *
      log2 (MatrixMap.cbOneToAlphaAlternateExpression
        (sandwichedSideWeightedMap N1 sigma1.1 alpha)
        (sandwichedSideWeightedMap_completelyPositive N1 sigma1.1 alpha)
        (SchattenOrder.ofOneLt halpha))
  let g : S2 → ℝ := fun sigma2 =>
    alpha / (alpha - 1) *
      log2 (MatrixMap.cbOneToAlphaAlternateExpression
        (sandwichedSideWeightedMap N2 sigma2.1 alpha)
        (sandwichedSideWeightedMap_completelyPositive N2 sigma2.1 alpha)
        (SchattenOrder.ofOneLt halpha))
  have hpoint :
      (fun p : S1 × S2 =>
        alpha / (alpha - 1) *
          log2 (MatrixMap.cbOneToAlphaAlternateExpression
            (sandwichedSideWeightedMap (N1.prod N2) (p.1.1.prod p.2.1) alpha)
            (sandwichedSideWeightedMap_completelyPositive (N1.prod N2)
              (p.1.1.prod p.2.1) alpha)
            (SchattenOrder.ofOneLt halpha))) =
        (fun p : S1 × S2 => f p.1 + g p.2) := by
    funext p
    exact sandwichedRenyiCBAlternateExpression_prod_posDef
      N1 N2 p.1.1 p.2.1 p.1.2 p.2.2 halpha
  rw [hpoint]
  exact real_sInf_range_prod_add_eq_add_sInf_range f g hN1 hN2

/-- Log-additivity of the KW CB-norm expression on full-rank product
references.  The nonzero hypotheses are only the scalar side conditions needed
for `log2_mul`; they are not a replacement for the missing source alternate
expression equating this candidate with optimized channel mutual information. -/
theorem sandwichedRenyiCBNormExpression_prod_posDef_of_ne
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha)
    (hN1 :
      MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N1 sigma1 alpha)
          (sandwichedSideWeightedMap_completelyPositive N1 sigma1 alpha)
          (SchattenOrder.ofOneLt halpha) ≠ 0)
    (hN2 :
      MatrixMap.cbOneToAlphaNorm
          (sandwichedSideWeightedMap N2 sigma2 alpha)
          (sandwichedSideWeightedMap_completelyPositive N2 sigma2 alpha)
          (SchattenOrder.ofOneLt halpha) ≠ 0) :
    sandwichedRenyiCBNormExpression (N1.prod N2) (sigma1.prod sigma2) (SchattenOrder.ofOneLt halpha) =
      sandwichedRenyiCBNormExpression N1 sigma1 (SchattenOrder.ofOneLt halpha) +
        sandwichedRenyiCBNormExpression N2 sigma2 (SchattenOrder.ofOneLt halpha) := by
  unfold sandwichedRenyiCBNormExpression
  simp only [SchattenOrder.coe_ofOneLt]
  rw [cbOneToAlphaNorm_sandwichedSideWeightedMap_prod_eq_mul_posDef
    N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha]
  rw [log2_mul hN1 hN2]
  ring

/-- Log-additivity of the KW CB-norm expression on full-rank product
references, with the logarithm side conditions discharged from positivity of
the weighted-channel CB norms. -/
theorem sandwichedRenyiCBNormExpression_prod_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    (sigma1 : State b1) (sigma2 : State b2)
    (hsigma1 : sigma1.matrix.PosDef) (hsigma2 : sigma2.matrix.PosDef)
    {alpha : ℝ} (halpha : 1 < alpha) :
    sandwichedRenyiCBNormExpression (N1.prod N2) (sigma1.prod sigma2) (SchattenOrder.ofOneLt halpha) =
      sandwichedRenyiCBNormExpression N1 sigma1 (SchattenOrder.ofOneLt halpha) +
        sandwichedRenyiCBNormExpression N2 sigma2 (SchattenOrder.ofOneLt halpha) := by
  exact sandwichedRenyiCBNormExpression_prod_posDef_of_ne
    N1 N2 sigma1 sigma2 hsigma1 hsigma2 halpha
    (ne_of_gt (cbOneToAlphaNorm_sandwichedSideWeightedMap_pos_of_posDef
      N1 sigma1 hsigma1 halpha))
    (ne_of_gt (cbOneToAlphaNorm_sandwichedSideWeightedMap_pos_of_posDef
      N2 sigma2 hsigma2 halpha))

/-- Full-rank product-reference infimum split for the KW CB expression.

This is the source scalar optimization step in `EA_capacity.tex:1265-1267`,
after the weighted-map product identity and CB-norm multiplicativity have
turned the product-channel integrand into a sum of two independent integrands.
It is deliberately stated on the full-rank reference domain used by the
currently proved logarithmic CB-expression lemmas; the singular-reference
closure still belongs to the missing channel alternate-expression layer. -/
theorem sandwichedRenyiCBNormExpression_fullRankProduct_sInf_eq_add
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1 :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)))
    (hN2 :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha))) :
    sInf (Set.range fun
        p : {sigma : State b1 // sigma.matrix.PosDef} ×
            {sigma : State b2 // sigma.matrix.PosDef} =>
      sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) (SchattenOrder.ofOneLt halpha)) =
      sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) +
      sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  haveI : Nonempty S1 := ⟨⟨State.maximallyMixed b1, State.maximallyMixed_posDef⟩⟩
  haveI : Nonempty S2 := ⟨⟨State.maximallyMixed b2, State.maximallyMixed_posDef⟩⟩
  let f : S1 → ℝ := fun sigma1 => sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)
  let g : S2 → ℝ := fun sigma2 => sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)
  have hpoint :
      (fun p : S1 × S2 =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) (SchattenOrder.ofOneLt halpha)) =
        (fun p : S1 × S2 => f p.1 + g p.2) := by
    funext p
    exact sandwichedRenyiCBNormExpression_prod_posDef
      N1 N2 p.1.1 p.2.1 p.1.2 p.2.2 halpha
  rw [hpoint]
  exact real_sInf_range_prod_add_eq_add_sInf_range f g hN1 hN2

/-- Boundedness of the full-rank product-reference CB expression follows from
the two one-channel boundedness hypotheses.

This is the order side condition needed before converting the product
full-rank `inf` into the real-valued expression used in the KW
`EA_capacity.tex:1247-1267` subadditivity chain. -/
theorem sandwichedRenyiCBNormExpression_fullRankProduct_bddBelow
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1 :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)))
    (hN2 :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha))) :
    BddBelow (Set.range fun
        p : Prod {sigma : State b1 // sigma.matrix.PosDef}
            {sigma : State b2 // sigma.matrix.PosDef} =>
      sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) (SchattenOrder.ofOneLt halpha)) := by
  rcases hN1 with ⟨l1, hl1⟩
  rcases hN2 with ⟨l2, hl2⟩
  refine ⟨l1 + l2, ?_⟩
  rintro y ⟨p, rfl⟩
  change l1 + l2 ≤
    sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) (SchattenOrder.ofOneLt halpha)
  rw [sandwichedRenyiCBNormExpression_prod_posDef N1 N2
    p.1.1 p.2.1 p.1.2 p.2.2 halpha]
  exact add_le_add (hl1 ⟨p.1, rfl⟩) (hl2 ⟨p.2, rfl⟩)

/-- Component full-support output hypotheses supply the boundedness side
condition for the product-reference KW channel alternate-expression upper
bound. -/
theorem sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf_of_outputs_posDef
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      ((sInf (Set.range fun
          p : {sigma : State b1 // sigma.matrix.PosDef} ×
              {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) (SchattenOrder.ofOneLt halpha)) :
          ℝ) : EReal) := by
  have hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N1 halpha hOut1
  have hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N2 halpha hOut2
  exact sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf
    N1 N2 halpha
    (sandwichedRenyiCBNormExpression_fullRankProduct_bddBelow
      N1 N2 halpha hN1Below hN2Below)

/-- KW subadditivity assembly bridge for product channels.

This is the order/scalar part of `EA_capacity.tex:1247-1267`: if the pending
channel alternate-expression theorem identifies each optimized channel
quantity with the full-rank CB expression, then restricting the product
channel's side-state infimum to product references and applying CB-norm
multiplicativity gives the `≤` half of channel additivity.

The hypotheses are intentionally explicit: this theorem is not the missing
alternate-expression theorem itself, and it is not a completion claim for
the unconditional channel additivity result. -/
theorem sandwichedRenyiMutualInformationE_prod_le_add_of_cb_fullRankAlternate
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)))
    (hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)))
    (hprodAltLe :
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
        ((sInf (Set.range fun
            p : Prod {sigma : State b1 // sigma.matrix.PosDef}
                {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
            (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))
    (hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))
    (hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal)) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  let S1 := {sigma : State b1 // sigma.matrix.PosDef}
  let S2 := {sigma : State b2 // sigma.matrix.PosDef}
  let f : S1 → ℝ := fun sigma1 =>
    sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)
  let g : S2 → ℝ := fun sigma2 =>
    sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)
  let prodF : Prod S1 S2 → ℝ := fun p =>
    sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1) (SchattenOrder.ofOneLt halpha)
  have hsplit :
      sInf (Set.range prodF) = sInf (Set.range f) + sInf (Set.range g) := by
    simpa [S1, S2, f, g, prodF] using
      sandwichedRenyiCBNormExpression_fullRankProduct_sInf_eq_add
        N1 N2 halpha hN1Below hN2Below
  have hprodAltLe' :
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
        ((sInf (Set.range prodF) : ℝ) : EReal) := by
    simpa [S1, S2, prodF] using hprodAltLe
  have hN1Alt' :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range f) : ℝ) : EReal) := by
    simpa [S1, f] using hN1Alt
  have hN2Alt' :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range g) : ℝ) : EReal) := by
    simpa [S2, g] using hN2Alt
  calc
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha
        ≤ ((sInf (Set.range prodF) : ℝ) : EReal) := hprodAltLe'
    _ = (((sInf (Set.range f) + sInf (Set.range g) : ℝ)) : EReal) := by
      rw [hsplit]
    _ = ((sInf (Set.range f) : ℝ) : EReal) +
          ((sInf (Set.range g) : ℝ) : EReal) := by
      rw [EReal.coe_add]
    _ = N1.sandwichedRenyiMutualInformationE alpha +
          N2.sandwichedRenyiMutualInformationE alpha := by
      rw [← hN1Alt', ← hN2Alt']

/-- KW subadditivity assembly bridge with the product-channel CB upper bound
generated internally from the two single-channel CB alternate expressions.

Compared with `sandwichedRenyiMutualInformationE_prod_le_add_of_cb_fullRankAlternate`,
this removes the separate product boundedness/upper-bound input: it follows
from the weighted-map product identity and the pointwise CB expression
additivity already proved above.  The remaining hypotheses are the genuinely
missing one-channel alternate-expression equalities. -/
theorem sandwichedRenyiMutualInformationE_prod_le_add_of_single_cb_fullRankAlternate
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)))
    (hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)))
    (hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))
    (hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal)) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hProdBelow :
      BddBelow (Set.range fun
          p : Prod {sigma : State b1 // sigma.matrix.PosDef}
              {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
          (SchattenOrder.ofOneLt halpha)) :=
    sandwichedRenyiCBNormExpression_fullRankProduct_bddBelow
      N1 N2 halpha hN1Below hN2Below
  have hprodAltLe :
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
        ((sInf (Set.range fun
            p : Prod {sigma : State b1 // sigma.matrix.PosDef}
                {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
            (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) :=
    sandwichedRenyiMutualInformationE_prod_le_fullRankProductCB_sInf
      N1 N2 halpha hProdBelow
  exact sandwichedRenyiMutualInformationE_prod_le_add_of_cb_fullRankAlternate
    N1 N2 halpha hN1Below hN2Below hprodAltLe hN1Alt hN2Alt

/-- KW channel subadditivity after the channel alternate expression has been
proved in real `sInf` form.

This is the unconditional `<=` half of `EA_capacity.tex:1242-1267`: restrict
the product side-reference optimization to full-rank product references, use
CB-norm multiplicativity, and split the independent real infima. -/
theorem sandwichedRenyiMutualInformationE_prod_le_add
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) := by
    simpa using sandwichedRenyiCBNormExpression_fullRank_bddBelow N1 halpha
  have hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) := by
    simpa using sandwichedRenyiCBNormExpression_fullRank_bddBelow N2 halpha
  exact sandwichedRenyiMutualInformationE_prod_le_add_of_single_cb_fullRankAlternate
    N1 N2 halpha hN1Below hN2Below
    (sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf N1 halpha)
    (sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf N2 halpha)

/-- Full-support assembly theorem for the KW channel-additivity route.

This combines the already proved product-input superadditivity branch with the
CB alternate-expression subadditivity bridge above.  It is deliberately not the
unconditional channel additivity theorem: the explicit hypotheses record the
real-valued full-rank CB bookkeeping used by this auxiliary assembly and the
channel alternate-expression equality.  The state-product lower branch is
already support-convention/unconditional. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add_of_output_posDef_cb_fullRankAlternate
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef)
    (hprodAltLe :
      (N1.prod N2).sandwichedRenyiMutualInformationE alpha ≤
        ((sInf (Set.range fun
            p : Prod {sigma : State b1 // sigma.matrix.PosDef}
                {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression (N1.prod N2) (p.1.1.prod p.2.1)
            (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))
    (hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))
    (hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal)) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N1 halpha hOut1
  have hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N2 halpha hOut2
  exact le_antisymm
    (sandwichedRenyiMutualInformationE_prod_le_add_of_cb_fullRankAlternate
      N1 N2 halpha hN1Below hN2Below hprodAltLe hN1Alt hN2Alt)
    (sandwichedRenyiMutualInformationE_prod_ge_add N1 N2 halpha)

/-- Full-support assembly with the product-channel CB upper bound generated
from the source weighted-rank-one route.

Compared with
`sandwichedRenyiMutualInformationE_prod_eq_add_of_output_posDef_cb_fullRankAlternate`,
this removes the bare `hprodAltLe` parameter by proving it from the
product-channel alternate-expression upper-bound branch.  The remaining
hypotheses are exactly the still-missing KW closure/equality pieces for this
auxiliary real-valued full-rank CB assembly: component boundedness supplied by
full-support outputs and the one-channel CB alternate expression identities. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_cb_fullRankAlternate
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef)
    (hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal))
    (hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal)) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hN1Below :
      BddBelow (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N1 halpha hOut1
  have hN2Below :
      BddBelow (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
        sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) :=
    sandwichedRenyiCBNormExpression_fullRank_bddBelow_of_outputs_posDef
      N2 halpha hOut2
  exact le_antisymm
      (sandwichedRenyiMutualInformationE_prod_le_add_of_single_cb_fullRankAlternate
        N1 N2 halpha hN1Below hN2Below hN1Alt hN2Alt)
      (sandwichedRenyiMutualInformationE_prod_ge_add N1 N2 halpha)

/-- Full-support channel-additivity assembly after the KW Sion exchange.

This replaces the abstract one-channel alternate-expression hypotheses in
`sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_cb_fullRankAlternate`
by the exact Sion exchange from KW `EA_capacity.tex:2080-2084`, combined with
the already formalized full-support scalar closure from `EReal` to real `sInf`.

This remains a full-support auxiliary theorem; the unconditional theorem below
uses the proved Sion exchange and the support-convention product and CB-norm
branches, so the final product-channel theorem carries no full-support output
assumptions. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_sionExchange
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef)
    (hSion1 : N1.sandwichedChannelAlternateSionExchange alpha halpha)
    (hSion2 : N2.sandwichedChannelAlternateSionExchange alpha halpha) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  have hN1Alt :
      N1.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma1 : {sigma : State b1 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N1 sigma1.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) :=
    sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sionExchange
      N1 halpha hOut1 hSion1
  have hN2Alt :
      N2.sandwichedRenyiMutualInformationE alpha =
        ((sInf (Set.range fun sigma2 : {sigma : State b2 // sigma.matrix.PosDef} =>
          sandwichedRenyiCBNormExpression N2 sigma2.1 (SchattenOrder.ofOneLt halpha)) : ℝ) : EReal) :=
    sandwichedRenyiMutualInformationE_eq_fullRankCB_sInf_of_outputs_posDef_sionExchange
      N2 halpha hOut2 hSion2
  exact sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_cb_fullRankAlternate
    N1 N2 halpha hOut1 hOut2 hN1Alt hN2Alt

/-- Full-support channel-additivity assembly with the KW Sion exchange proved. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2) {alpha : ℝ} (halpha : 1 < alpha)
    (hOut1 : ∀ psi : PureVector (Prod a1 a1),
      (N1.hypothesisTestingOutputState psi).matrix.PosDef)
    (hOut2 : ∀ phi : PureVector (Prod a2 a2),
      (N2.hypothesisTestingOutputState phi).matrix.PosDef) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  exact sandwichedRenyiMutualInformationE_prod_eq_add_of_fullSupport_sionExchange
    N1 N2 halpha hOut1 hOut2
    (sandwichedChannelAlternateSionExchange_proved N1 halpha)
    (sandwichedChannelAlternateSionExchange_proved N2 halpha)

/-- Khatri--Wilde sandwiched entanglement-assisted mutual information is
additive under product channels for `alpha > 1`.

This corresponds to KhatriWilde2024Principles, `EA_capacity.tex:1220-1277`:
the lower bound comes from the state-product theorem over product pure inputs,
and the upper bound comes from the channel CB-norm alternate expression and
multiplicativity. -/
theorem sandwichedRenyiMutualInformationE_prod_eq_add
    [Nonempty a1] [Nonempty a2] [Nonempty b1] [Nonempty b2]
    (N1 : Channel a1 b1) (N2 : Channel a2 b2)
    {alpha : Real} (halpha : 1 < alpha) :
    (N1.prod N2).sandwichedRenyiMutualInformationE alpha =
      N1.sandwichedRenyiMutualInformationE alpha +
        N2.sandwichedRenyiMutualInformationE alpha := by
  exact le_antisymm
    (sandwichedRenyiMutualInformationE_prod_le_add N1 N2 halpha)
    (sandwichedRenyiMutualInformationE_prod_ge_add N1 N2 halpha)

end Channel

end

end QIT
