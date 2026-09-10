/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.Asymptotic.MutualInformationAdditivity

/-!
# Sandwiched Renyi tensor-power scaling

This module is part of the entanglement-assisted classical communication
asymptotic proof spine.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal Topology
open Filter

universe u v w x y

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

variable (N : CPTPMap a b)

/-- On a one-dimensional system, the density matrix of any state is the scalar
identity `1`. -/
private theorem punit_state_matrix_eq_one
    (ρ : MState PUnit.{u + 1}) : ρ.m = 1 := by
  ext i j
  rcases i with ⟨⟩
  rcases j with ⟨⟩
  show ρ.m PUnit.unit PUnit.unit = (1 : CMatrix PUnit.{u + 1}) PUnit.unit PUnit.unit
  rw [Matrix.one_apply, if_pos rfl]
  -- Use that the trace equals the single matrix entry for a 1-dim system.
  have htrace : ∑ k : PUnit.{u + 1}, ρ.m k k = 1 := ρ.tr'
  simpa using htrace

/-- On a one-dimensional bipartite system, the density matrix of any state is
the scalar identity `1`. -/
private theorem punit_punit_state_matrix_eq_one
    (ρ : MState (PUnit.{u + 1} × PUnit.{v + 1})) : ρ.m = 1 := by
  ext i j
  rcases i with ⟨⟨⟩, ⟨⟩⟩
  rcases j with ⟨⟨⟩, ⟨⟩⟩
  show ρ.m (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) =
      (1 : CMatrix (PUnit.{u + 1} × PUnit.{v + 1})) (PUnit.unit, PUnit.unit) (PUnit.unit,
        PUnit.unit)
  rw [Matrix.one_apply, if_pos rfl]
  have htrace :
      ∑ k : PUnit.{u + 1} × PUnit.{v + 1}, ρ.m k k = 1 := ρ.tr'
  have hsum :
      (∑ k : PUnit.{u + 1} × PUnit.{v + 1}, ρ.m k k) =
        ρ.m (PUnit.unit, PUnit.unit) (PUnit.unit, PUnit.unit) := by
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
    (ρ : MState (PUnit.{u + 1} × PUnit.{v + 1})) (alpha : ℝ) (_halpha : 1 < alpha) :
    MState.sandwichedRenyiPSDReferenceHighAlphaFinite ρ
      (1 : CMatrix (PUnit.{u + 1} × PUnit.{v + 1})) Matrix.PosSemidef.one alpha = 0 := by
  have hcard :
      Fintype.card (PUnit.{u + 1} × PUnit.{v + 1}) = 1 := by simp
  have hρmatrix : ρ.m = 1 := punit_punit_state_matrix_eq_one ρ
  have htrace :
      ((Matrix.trace ((ρ.m : CMatrix _) ^ alpha)).re) = 1 := by
    rw [hρmatrix, CFC.one_rpow, Matrix.trace_one]
    simp [hcard]
  simp [MState.sandwichedRenyiPSDReferenceHighAlphaFinite,
    MState.sandwichedRenyiReferenceInner, psdTracePower, log2, CFC.one_rpow, hρmatrix]

/-- On a one-dimensional bipartite system, every state has zero sandwiched-Renyi
mutual information for `alpha > 1`: the infimum over side-information states is
squeezed below by candidate nonnegativity and above by the self-product
candidate `D~_alpha(rho || rho_A tensor rho_B) = D~_alpha(1 || 1) = 0`. -/
private theorem sandwichedRenyiMutualInformationE_punit_punit_eq_zero
    (ρ : MState (PUnit.{u + 1} × PUnit.{v + 1})) {alpha : ℝ} (halpha : 1 < alpha) :
    ρ.sandwichedRenyiMutualInformationE alpha = 0 := by
  refine le_antisymm ?_ ?_
  · -- Upper bound: Ĩ_α(ρ) ≤ D̃_α(ρ ∥ ρ_A ⊗ ρ_B) = 0.
    have hA_matrix : ρ.traceRight.m = 1 := punit_state_matrix_eq_one ρ.traceRight
    have hσB_matrix : ρ.traceLeft.m = 1 := punit_state_matrix_eq_one ρ.traceLeft
    have hRef_matrix :
        (ρ.traceRight.prod ρ.traceLeft).m =
          (1 : CMatrix (PUnit.{u + 1} × PUnit.{v + 1})) := by
      rw [MState.prod_m]
      simp only [hA_matrix, hσB_matrix]
      simp
    have hSupports :
        Matrix.Supports ρ.m (ρ.traceRight.prod ρ.traceLeft).m := by
      rw [hRef_matrix]
      exact Matrix.Supports.of_right_posDef ρ.m _ Matrix.PosDef.one
    have hfinite :
        MState.sandwichedRenyiPSDReferenceHighAlphaFinite ρ
          (ρ.traceRight.prod ρ.traceLeft).m
          (ρ.traceRight.prod ρ.traceLeft).psd alpha = 0 := by
      simpa [hRef_matrix] using
        sandwichedRenyiPSDReferenceHighAlphaFinite_unit_eq_zero_punit_punit
          ρ alpha halpha
    have hcandidate :
        ρ.sandwichedRenyiMutualInformationCandidateE ρ.traceLeft alpha = 0 := by
      rw [MState.sandwichedRenyiMutualInformationCandidateE_eq,
        MState.sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha,
        MState.sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports ρ
          (ρ.traceRight.prod ρ.traceLeft).psd alpha hSupports]
      rw [hfinite]
      simp
    calc ρ.sandwichedRenyiMutualInformationE alpha
          ≤ ρ.sandwichedRenyiMutualInformationCandidateE ρ.traceLeft alpha :=
        MState.sandwichedRenyiMutualInformationE_le_candidate ρ ρ.traceLeft alpha
      _ = 0 := hcandidate
  · -- Lower bound: Ĩ_α(ρ) ≥ 0 since every candidate is nonneg.
    rw [MState.sandwichedRenyiMutualInformationE_eq_sInf]
    have hnonempty :
        (ρ.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
      have : Nonempty PUnit.{v + 1} := ⟨PUnit.unit⟩
      exact MState.sandwichedRenyiMutualInformationEValueSet_nonempty ρ alpha
    refine le_csInf hnonempty ?_
    intro _ ⟨σB, hσB⟩
    rw [← hσB]
    exact MState.sandwichedRenyiMutualInformationCandidateE_nonneg ρ σB halpha

/-- The sandwiched-Renyi mutual information of the unit channel is zero.

Mirrors the Petz (von Neumann) base `entanglementAssistedInformation_unit`,
using `sandwichedRenyiMutualInformationE_punit_punit_eq_zero` in place of
`MState.mutualInformation_punit_punit_eq_zero`. -/
private theorem sandwichedRenyiMutualInformationE_unit
    {alpha : ℝ} (halpha : 1 < alpha) :
    (CPTPOp.unit : CPTPMap PUnit.{u + 1} PUnit.{v + 1}).sandwichedRenyiMutualInformationE
      alpha = 0 := by
  let unitChan := (CPTPOp.unit : CPTPMap PUnit.{u + 1} PUnit.{v + 1})
  have hvalue :
      ∀ psi : Ket (PUnit.{u + 1} × PUnit.{u + 1}),
        unitChan.inputSandwichedRenyiMutualInformationE psi alpha = 0 := by
    intro psi
    rw [CPTPOp.inputSandwichedRenyiMutualInformationE_eq]
    exact sandwichedRenyiMutualInformationE_punit_punit_eq_zero _ halpha
  have hnonempty : (unitChan.sandwichedRenyiMutualInformationEValueSet alpha).Nonempty := by
    have : Nonempty PUnit.{u + 1} := ⟨PUnit.unit⟩
    exact unitChan.sandwichedRenyiMutualInformationEValueSet_nonempty alpha
  have hbddAbove :
      BddAbove (unitChan.sandwichedRenyiMutualInformationEValueSet alpha) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨psi, rfl⟩
    show unitChan.inputSandwichedRenyiMutualInformationE psi alpha ≤ 0
    rw [hvalue psi]
  rw [CPTPOp.sandwichedRenyiMutualInformationE_eq_sSup]
  refine le_antisymm ?_ ?_
  · apply csSup_le hnonempty
    rintro _ ⟨psi, rfl⟩
    show unitChan.inputSandwichedRenyiMutualInformationE psi alpha ≤ 0
    rw [hvalue psi]
  · have hbasis : unitChan.inputSandwichedRenyiMutualInformationE
        default alpha = 0 := hvalue _
    exact le_csSup hbddAbove ⟨default, hbasis⟩

/-- Tensor-power scaling of the channel sandwiched-Renyi mutual information:
`Ĩ_α(N^{⊗n}) = n · Ĩ_α(N)`.

This mirrors the Petz (von Neumann) tensor-power additivity
`CPTPOp.entanglementAssistedInformation_tensorPower_eq_mul`, with the
unconditional two-channel sandwiched additivity
`CPTPOp.sandwichedRenyiMutualInformationE_prod_eq_add` substituted for
`CPTPOp.entanglementAssistedInformation_prod`.  Source:
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:1220-1277]. -/
theorem sandwichedRenyiMutualInformationE_tensorPower_eq_n_mul
    [Nonempty a] [Nonempty b] {alpha : ℝ} (halpha : 1 < alpha) (n : ℕ) :
    (N.tensorPower n).sandwichedRenyiMutualInformationE alpha =
      (n : ℝ) * N.sandwichedRenyiMutualInformationE alpha := by
  induction n with
  | zero =>
      rw [CPTPOp.tensorPower_zero]
      trans 0
      · exact sandwichedRenyiMutualInformationE_unit halpha
      · simp
  | succ n ih =>
      have : Nonempty (QIT.TensorPower a n) :=
        tensorPower_nonempty_of_nonempty (α := a) n
      have : Nonempty (QIT.TensorPower b n) :=
        tensorPower_nonempty_of_nonempty (α := b) n
      have hsplit : N.tensorPower (n + 1) = N.prod (N.tensorPower n) := by
        rw [CPTPOp.tensorPower_succ]
      have hprod : (N.prod (N.tensorPower n)).sandwichedRenyiMutualInformationE alpha =
          N.sandwichedRenyiMutualInformationE alpha +
            (N.tensorPower n).sandwichedRenyiMutualInformationE alpha :=
        CPTPOp.sandwichedRenyiMutualInformationE_prod_eq_add N (N.tensorPower n) halpha
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

end CPTPOp

end
