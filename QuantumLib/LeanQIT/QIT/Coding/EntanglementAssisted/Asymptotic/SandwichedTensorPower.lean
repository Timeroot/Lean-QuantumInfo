/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.Asymptotic.MutualInformationAdditivity

/-!
# Sandwiched Renyi tensor-power scaling

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.  It was split out mechanically from the historical
`EntanglementAssistedAsymptotic` files; theorem statements and proof routes are
unchanged.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

namespace QIT

universe u v w x y

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace Channel

variable (N : Channel a b)

/-- On a one-dimensional system, the density matrix of any state is the scalar
identity `1`. -/
private theorem punit_state_matrix_eq_one
    (ρ : State PUnit.{u + 1}) : ρ.matrix = 1 := by
  ext i j
  rcases i with ⟨⟩
  rcases j with ⟨⟩
  show ρ.matrix PUnit.unit PUnit.unit = (1 : CMatrix PUnit.{u + 1}) PUnit.unit PUnit.unit
  rw [Matrix.one_apply, if_pos rfl]
  -- Use that the trace equals the single matrix entry for a 1-dim system.
  have htrace : ∑ k : PUnit.{u + 1}, ρ.matrix k k = 1 := ρ.trace_eq_one
  simpa using htrace

/-- On a one-dimensional bipartite system, the density matrix of any state is
the scalar identity `1`. -/
private theorem punit_punit_state_matrix_eq_one
    (ρ : State (Prod PUnit.{u + 1} PUnit.{v + 1})) : ρ.matrix = 1 := by
  ext i j
  rcases i with ⟨⟨⟩, ⟨⟩⟩
  rcases j with ⟨⟨⟩, ⟨⟩⟩
  show ρ.matrix (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) =
      (1 : CMatrix (Prod PUnit.{u + 1} PUnit.{v + 1})) (PUnit.unit, PUnit.unit) (PUnit.unit,
        PUnit.unit)
  rw [Matrix.one_apply, if_pos rfl]
  have htrace :
      ∑ k : Prod PUnit.{u + 1} PUnit.{v + 1}, ρ.matrix k k = 1 := ρ.trace_eq_one
  have hsum :
      (∑ k : Prod PUnit.{u + 1} PUnit.{v + 1}, ρ.matrix k k) =
        ρ.matrix (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) := by
    rw [Finset.sum_eq_single (PUnit.unit, PUnit.unit)]
    · simp
    · intro hnot
      simp at hnot
  rw [hsum] at htrace
  exact htrace

/-- On a one-dimensional bipartite system, the high-`alpha` finite
sandwiched-Renyi PSD-reference divergence of any state from the identity
matrix reference is zero, since both arguments reduce to the scalar matrix
`1` and the trace-power collapses to `Tr[1] = 1`. -/
private theorem sandwichedRenyiPSDReferenceHighAlphaFinite_unit_eq_zero_punit_punit
    (ρ : State (Prod PUnit.{u + 1} PUnit.{v + 1})) (alpha : ℝ) (_halpha : 1 < alpha) :
    State.sandwichedRenyiPSDReferenceHighAlphaFinite ρ
      (1 : CMatrix (Prod PUnit.{u + 1} PUnit.{v + 1})) Matrix.PosSemidef.one alpha = 0 := by
  have hcard :
      Fintype.card (Prod PUnit.{u + 1} PUnit.{v + 1}) = 1 := by simp
  have hρmatrix : ρ.matrix = 1 := punit_punit_state_matrix_eq_one ρ
  have htrace :
      ((Matrix.trace ((ρ.matrix : CMatrix _) ^ alpha)).re) = 1 := by
    rw [hρmatrix, CFC.one_rpow, Matrix.trace_one]
    simp [hcard]
  simp [State.sandwichedRenyiPSDReferenceHighAlphaFinite,
    State.sandwichedRenyiReferenceInner, psdTracePower, log2, CFC.one_rpow, hρmatrix]

/-- On a one-dimensional bipartite system, every state has zero sandwiched-Renyi
mutual information for `alpha > 1`: the infimum over side-information states is
squeezed below by candidate nonnegativity and above by the self-product
candidate `D~_alpha(rho || rho_A tensor rho_B) = D~_alpha(1 || 1) = 0`. -/
private theorem sandwichedRenyiMutualInformationE_punit_punit_eq_zero
    (ρ : State (Prod PUnit.{u + 1} PUnit.{v + 1})) {alpha : ℝ} (halpha : 1 < alpha) :
    ρ.sandwichedRenyiMutualInformationE alpha = 0 := by
  refine le_antisymm ?_ ?_
  · -- Upper bound: Ĩ_α(ρ) ≤ D̃_α(ρ ∥ ρ_A ⊗ ρ_B) = 0.
    have hA_matrix : ρ.marginalA.matrix = 1 := punit_state_matrix_eq_one ρ.marginalA
    have hσB_matrix : ρ.marginalB.matrix = 1 := punit_state_matrix_eq_one ρ.marginalB
    have hRef_matrix :
        (ρ.marginalA.prod ρ.marginalB).matrix =
          (1 : CMatrix (Prod PUnit.{u + 1} PUnit.{v + 1})) := by
      rw [State.prod]
      simp only [hA_matrix, hσB_matrix]
      simp [Matrix.kronecker]
    have hSupports :
        Matrix.Supports ρ.matrix (ρ.marginalA.prod ρ.marginalB).matrix := by
      rw [hRef_matrix]
      exact Matrix.Supports.of_right_posDef ρ.matrix _ Matrix.PosDef.one
    have hfinite :
        State.sandwichedRenyiPSDReferenceHighAlphaFinite ρ
          (ρ.marginalA.prod ρ.marginalB).matrix
          (ρ.marginalA.prod ρ.marginalB).pos alpha = 0 := by
      simpa [hRef_matrix] using
        sandwichedRenyiPSDReferenceHighAlphaFinite_unit_eq_zero_punit_punit
          ρ alpha halpha
    have hcandidate :
        ρ.sandwichedRenyiMutualInformationCandidateE ρ.marginalB alpha = 0 := by
      rw [State.sandwichedRenyiMutualInformationCandidateE_eq,
        State.sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha,
        State.sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports ρ
          (ρ.marginalA.prod ρ.marginalB).pos alpha hSupports]
      rw [hfinite]
      simp
    calc ρ.sandwichedRenyiMutualInformationE alpha
          ≤ ρ.sandwichedRenyiMutualInformationCandidateE ρ.marginalB alpha :=
        State.sandwichedRenyiMutualInformationE_le_candidate ρ ρ.marginalB alpha
      _ = 0 := hcandidate
  · -- Lower bound: Ĩ_α(ρ) ≥ 0 since every candidate is nonneg.
    rw [State.sandwichedRenyiMutualInformationE_eq_sInf]
    have hnonempty :
        (ρ.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
      haveI : Nonempty PUnit.{v + 1} := ⟨PUnit.unit⟩
      exact State.sandwichedRenyiMutualInformationEValueSet_nonempty ρ alpha
    refine le_csInf hnonempty ?_
    intro _ ⟨σB, hσB⟩
    rw [← hσB]
    exact State.sandwichedRenyiMutualInformationCandidateE_nonneg ρ σB halpha

/-- The sandwiched-Renyi mutual information of the unit channel is zero.

Mirrors the Petz (von Neumann) base `entanglementAssistedInformation_unit`,
using `sandwichedRenyiMutualInformationE_punit_punit_eq_zero` in place of
`State.mutualInformation_punit_punit_eq_zero`. -/
private theorem sandwichedRenyiMutualInformationE_unit
    {alpha : ℝ} (halpha : 1 < alpha) :
    (Channel.unit : Channel PUnit.{u + 1} PUnit.{v + 1}).sandwichedRenyiMutualInformationE
      alpha = 0 := by
  let unitChan := (Channel.unit : Channel PUnit.{u + 1} PUnit.{v + 1})
  have hvalue :
      ∀ psi : PureVector (Prod PUnit.{u + 1} PUnit.{u + 1}),
        unitChan.inputSandwichedRenyiMutualInformationE psi alpha = 0 := by
    intro psi
    rw [Channel.inputSandwichedRenyiMutualInformationE_eq]
    exact sandwichedRenyiMutualInformationE_punit_punit_eq_zero _ halpha
  have hnonempty : (unitChan.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
    haveI : Nonempty PUnit.{u + 1} := ⟨PUnit.unit⟩
    exact unitChan.sandwichedRenyiMutualInformationEValueSet_nonempty alpha
  have hbddAbove :
      BddAbove (unitChan.sandwichedRenyiMutualInformationEValueSet alpha) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨psi, rfl⟩
    show unitChan.inputSandwichedRenyiMutualInformationE psi alpha ≤ 0
    rw [hvalue psi]
  rw [Channel.sandwichedRenyiMutualInformationE_eq_sSup]
  refine le_antisymm ?_ ?_
  · apply csSup_le hnonempty
    rintro _ ⟨psi, rfl⟩
    show unitChan.inputSandwichedRenyiMutualInformationE psi alpha ≤ 0
    rw [hvalue psi]
  · have hbasis : unitChan.inputSandwichedRenyiMutualInformationE
        PureVector.basisPureVector alpha = 0 := hvalue _
    exact le_csSup hbddAbove ⟨PureVector.basisPureVector, hbasis⟩

/-- Tensor-power scaling of the channel sandwiched-Renyi mutual information:
`Ĩ_α(N^{⊗n}) = n · Ĩ_α(N)`.

This mirrors the Petz (von Neumann) tensor-power additivity
`Channel.entanglementAssistedInformation_tensorPower_eq_mul`, with the
unconditional two-channel sandwiched additivity
`Channel.sandwichedRenyiMutualInformationE_prod_eq_add` substituted for
`Channel.entanglementAssistedInformation_prod`.  Source:
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1220-1277]. -/
theorem sandwichedRenyiMutualInformationE_tensorPower_eq_n_mul
    [Nonempty a] [Nonempty b] {alpha : ℝ} (halpha : 1 < alpha) (n : ℕ) :
    (N.tensorPower n).sandwichedRenyiMutualInformationE alpha =
      (n : ℝ) * N.sandwichedRenyiMutualInformationE alpha := by
  induction n with
  | zero =>
      rw [Channel.tensorPower_zero]
      trans 0
      · exact sandwichedRenyiMutualInformationE_unit halpha
      · simp
  | succ n ih =>
      haveI : Nonempty (QIT.TensorPower a n) :=
        tensorPower_nonempty_of_nonempty (α := a) n
      haveI : Nonempty (QIT.TensorPower b n) :=
        tensorPower_nonempty_of_nonempty (α := b) n
      have hsplit : N.tensorPower (n + 1) = N.prod (N.tensorPower n) := by
        rw [Channel.tensorPower_succ]
      have hprod : (N.prod (N.tensorPower n)).sandwichedRenyiMutualInformationE alpha =
          N.sandwichedRenyiMutualInformationE alpha +
            (N.tensorPower n).sandwichedRenyiMutualInformationE alpha :=
        Channel.sandwichedRenyiMutualInformationE_prod_eq_add N (N.tensorPower n) halpha
      rw [hsplit]
      calc
        (N.prod (N.tensorPower n)).sandwichedRenyiMutualInformationE alpha =
            N.sandwichedRenyiMutualInformationE alpha +
              (N.tensorPower n).sandwichedRenyiMutualInformationE alpha := hprod
        _ = ((n + 1 : ℕ) : ℝ) * N.sandwichedRenyiMutualInformationE alpha := by
            rw [ih]
            -- The EReal arithmetic is most robustly expressed as natural
            -- repeated addition; `EReal.nsmul_eq_mul` bridges it to finite
            -- scalar multiplication by the blocklength.
            let X := N.sandwichedRenyiMutualInformationE alpha
            change X + (((n : ℝ) : EReal) * X) =
              ((((n + 1 : ℕ) : ℝ) : EReal) * X)
            rw [EReal.coe_coe_eq_natCast n, EReal.coe_coe_eq_natCast (n + 1)]
            rw [← EReal.nsmul_eq_mul n X, ← EReal.nsmul_eq_mul (n + 1) X]
            rw [succ_nsmul]
            rw [add_comm]

end Channel

end

end QIT
