/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.OneShot.SmoothEndpoint.Order
public import QuantumLib.QIT.OneShot.SmoothEndpoint.MaximallyEntangledProjector
public import QuantumLib.QIT.States.MaximallyMixed
public import QuantumLib.QIT.States.TraceNorm.Spectral
public import QuantumLib.QIT.Util.CMatrixCLM
public import QuantumLib.QIT.Util.MatrixInstances

/-!
# The conditional endpoint entropies of a normalized state, as convex programs

For a normalized `ρ : MState (A ⊗ B)`, this module recasts the conditional min- and max-entropies
in the convex-programming form the endpoint duality needs, and proves each form nonempty, bounded,
and equal to the definition it replaces.

The max-entropy side starts from the raw exponent `sup_σ ‖√ρ_AB √(I_A ⊗ σ_B)‖₁²`, whose `log₂` is
`conditionalMaxEntropyCandidate`.  It is re-presented as a block SDP:
`ConditionalMaxFidelityBlockFeasible ρ σ X` asks that `[[ρ_AB, X], [X†, π_A ⊗ σ_B]]` be positive
semidefinite, with objective `card a * (Re tr X)²`.  Feasible points are fidelity bounded — the two
rows of a square root of the block matrix are amplitude matrices whose Gram matrices are the
diagonal blocks and whose cross-Gram is `X`, so `|tr X|` is an overlap of purifications and hence
at most `F(ρ, π_A ⊗ σ)`; `maxEntangledSideKet` supplies the purification on the side state.  The
bound is attained (`of_unitary_sqrt`, `smul_phase`), so the block program has the same value:
`conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet`.

The min-entropy side is the scale `inf {Re tr T | T ≥ 0, ρ_AB ≤ I_A ⊗ T}`, equivalently the
normalized form `inf {2^(-λ) | ...}`.  Its dual ranges over effects `M_AB ≥ 0` with `Tr_A M ≤ I_B`,
objective `Re tr (ρ M)`; `conditionalMinEntropyDualEffectChoiMatrix` and its transposed variant read
such an effect as the Choi matrix of a map `B → A`, in the two orientations the `Duality` link map
needs, and `conditionalMinEntropyDualEffectProgram` packages the dual as an
`SDP.ContinuousConeProgram` whose primal value set is exactly the dual-effect value set.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator NNReal Pointwise QIT.MatrixL2
open scoped Topology
open Matrix hiding traceNorm traceNorm_conjTranspose traceNorm_nonneg
open Set Filter

noncomputable section
universe u v w x

open QIT

namespace MState

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable {c : Type*} [Fintype c] [DecidableEq c]

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid NormedSpace.toModule
attribute [local instance 1001] PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-! ## Elementary state bounds and maximally mixed side states -/

theorem sqrtMatrix_trace_re_pos [Nonempty a] (ρ : MState a) :
    0 < ρ.sqrtMatrix.trace.re := by
  have hnon : 0 ≤ ρ.sqrtMatrix.trace.re :=
    (Matrix.PosSemidef.trace_nonneg ρ.sqrtMatrix_pos).1
  by_contra hnot
  have hle : ρ.sqrtMatrix.trace.re ≤ 0 := le_of_not_gt hnot
  have hre : ρ.sqrtMatrix.trace.re = 0 := le_antisymm hle hnon
  have htr : ρ.sqrtMatrix.trace = 0 := by
    apply Complex.ext
    · exact hre
    · exact (Matrix.PosSemidef.trace_nonneg ρ.sqrtMatrix_pos).2.symm
  have hsqrt_zero : ρ.sqrtMatrix = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff ρ.sqrtMatrix_pos).mp htr
  have hrho_zero : ρ.m = 0 := by
    rw [← ρ.sqrtMatrix_mul_self, hsqrt_zero]
    simp
  have htrace : (ρ.m.trace : ℂ) = 0 := by simp [hrho_zero]
  rw [ρ.tr'] at htrace
  norm_num at htrace

/-- The maximally mixed state on a nonempty finite system. -/
theorem identityTensorStateMatrix_trace_re (σ : MState b) :
    (identityTensorStateMatrix (a := a) σ).trace.re = (Fintype.card a : ℝ) := by
  change ((1 : CMatrix a) ⊗ₖ σ.m).trace.re =
    (Fintype.card a : ℝ)
  rw [Matrix.trace_kronecker, σ.tr', Matrix.trace_one]
  norm_num

omit [DecidableEq b] in theorem rpow_two_log2_card [Nonempty b] :
    Real.rpow 2 (log2 (Fintype.card b : ℝ)) = (Fintype.card b : ℝ) := by
  have hcard_pos : 0 < (Fintype.card b : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  unfold log2
  have harg : Real.log 2 * (Real.log (Fintype.card b : ℝ) / Real.log 2) =
      Real.log (Fintype.card b : ℝ) := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    field_simp [hlog2]
  calc
    Real.rpow 2 (Real.log (Fintype.card b : ℝ) / Real.log 2)
        = Real.exp (Real.log 2 * (Real.log (Fintype.card b : ℝ) / Real.log 2)) := by
          exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _
    _ = Real.exp (Real.log (Fintype.card b : ℝ)) := by rw [harg]
    _ = (Fintype.card b : ℝ) := Real.exp_log hcard_pos

/-! ## Conditional max-entropy exponent -/

/-- The raw squared-fidelity expression optimized by conditional max-entropy,
before applying `log₂`. -/
def conditionalMaxEntropyExponentCandidate (ρ : MState (a × b)) (σ : MState b) :
    ℝ :=
  (traceNorm (ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2

@[simp]
theorem conditionalMaxEntropyExponentCandidate_eq
    (ρ : MState (a × b)) (σ : MState b) :
    ρ.conditionalMaxEntropyExponentCandidate σ =
      (traceNorm (ρ.sqrtMatrix *
        psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2 :=
  rfl

/-- The raw endpoint exponent
`sup_σ ‖√ρ_AB √(I_A ⊗ σ_B)‖₁²`. -/
def conditionalMaxEntropyExponentValueSet (ρ : MState (a × b)) : Set ℝ :=
  {x : ℝ | ∃ σ : MState b,
    x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

/-- The raw endpoint exponent
`sup_σ ‖√ρ_AB √(I_A ⊗ σ_B)‖₁²`. -/
def conditionalMaxEntropyExponent (ρ : MState (a × b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyExponentValueSet (a := a))

@[simp]
theorem conditionalMaxEntropyExponent_eq (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyExponent =
      sSup (ρ.conditionalMaxEntropyExponentValueSet (a := a)) :=
  rfl

/-- The existing conditional max-entropy candidate is the logarithm of the raw
endpoint candidate. -/
theorem conditionalMaxEntropyCandidate_eq_log2_exponentCandidate
    (ρ : MState (a × b)) (σ : MState b) :
    ρ.conditionalMaxEntropyCandidate σ =
      log2 (ρ.conditionalMaxEntropyExponentCandidate (a := a) σ) :=
  rfl

theorem conditionalMaxEntropyExponentCandidate_nonneg
    (ρ : MState (a × b)) (σ : MState b) :
    0 ≤ ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  exact sq_nonneg _

theorem conditionalMaxEntropyExponentCandidate_uniform_pos
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) (MState.uniform : MState b) := by
  let c : ℝ := (Fintype.card b : ℝ)⁻¹
  have hc_nonneg : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hc_pos : 0 < Real.sqrt c := by
    have hcard_pos : 0 < (Fintype.card b : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    exact Real.sqrt_pos.mpr (inv_pos.mpr hcard_pos)
  have hsqrt_id :
      psdSqrt (identityTensorStateMatrix (a := a) (MState.uniform : MState b)) =
        (((Real.sqrt c : ℝ) : ℂ) • (1 : CMatrix (a × b))) := by
    rw [identityTensorStateMatrix_uniform (a := a) (b := b)]
    exact psdSqrt_real_smul_one (a := a × b) hc_nonneg
  have htrace_eq :
      (ρ.sqrtMatrix *
          psdSqrt (identityTensorStateMatrix (a := a) (MState.uniform : MState b))).trace =
        ((Real.sqrt c : ℝ) : ℂ) * ρ.sqrtMatrix.trace := by
    rw [hsqrt_id]
    simp [Matrix.trace_smul]
  have htrace_abs_pos :
      0 < ‖(ρ.sqrtMatrix *
          psdSqrt (identityTensorStateMatrix (a := a) (MState.uniform : MState b))).trace‖ := by
    rw [htrace_eq, norm_mul]
    have htr_ne : ρ.sqrtMatrix.trace ≠ 0 := by
      intro hzero
      have hre : ρ.sqrtMatrix.trace.re = 0 := by rw [hzero]; rfl
      have hpos : 0 < ρ.sqrtMatrix.trace.re := ρ.sqrtMatrix_trace_re_pos
      linarith
    have hc_ne : (((Real.sqrt c : ℝ) : ℂ) : ℂ) ≠ 0 := by
      exact_mod_cast hc_pos.ne'
    exact mul_pos (norm_pos_iff.mpr hc_ne) (norm_pos_iff.mpr htr_ne)
  have htn_pos :
      0 < traceNorm (ρ.sqrtMatrix *
        psdSqrt (identityTensorStateMatrix (a := a) (MState.uniform : MState b))) :=
    lt_of_lt_of_le htrace_abs_pos (trace_abs_le_traceNorm _)
  unfold conditionalMaxEntropyExponentCandidate
  exact sq_pos_of_pos htn_pos

theorem psdSqrt_identityTensorStateMatrix (σ : MState b) :
    psdSqrt (identityTensorStateMatrix (a := a) σ) =
      (1 : CMatrix a) ⊗ₖ σ.sqrtMatrix := by
  change psdSqrt ((1 : CMatrix a) ⊗ₖ σ.m) =
    (1 : CMatrix a) ⊗ₖ σ.sqrtMatrix
  rw [psdSqrt_kronecker Matrix.PosSemidef.one σ.psd]
  have hone : psdSqrt (1 : CMatrix a) = (1 : CMatrix a) := by
    simpa using (psdSqrt_real_smul_one (a := a) (r := 1) (by norm_num))
  rw [hone]
  simp [MState.sqrtMatrix]

theorem conditionalMaxEntropyExponentCandidate_eq_sqrt_identity
    (ρ : MState (a × b)) (σ : MState b) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ =
      (traceNorm (ρ.sqrtMatrix *
        ((1 : CMatrix a) ⊗ₖ σ.sqrtMatrix))) ^ 2 := by
  rw [conditionalMaxEntropyExponentCandidate_eq,
    psdSqrt_identityTensorStateMatrix (a := a) σ]

theorem conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
    [Nonempty a] (ρ : MState (a × b)) (σ : MState b) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ =
      (Fintype.card a : ℝ) *
        ρ.squaredFidelity ((MState.uniform : MState a).prod σ) := by
  let d : ℝ := Fintype.card a
  let M : CMatrix (a × b) :=
    ρ.sqrtMatrix * ((MState.uniform : MState a).prod σ).sqrtMatrix
  have hd_nonneg : 0 ≤ d := Nat.cast_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsqrt_sq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd_nonneg
  have hrewrite :
      ρ.sqrtMatrix * ((1 : CMatrix a) ⊗ₖ σ.sqrtMatrix) =
        (((Real.sqrt d : ℝ) : ℂ) • M) := by
    have hsqrt :
        (1 : CMatrix a) ⊗ₖ σ.sqrtMatrix =
          (((Real.sqrt d : ℝ) : ℂ) • ((MState.uniform : MState a).prod σ).sqrtMatrix) := by
      dsimp [d]
      exact sqrt_identityTensorStateMatrix_eq_sqrt_card_smul_uniform_prod_sqrtMatrix
        (a := a) σ
    calc
      ρ.sqrtMatrix * ((1 : CMatrix a) ⊗ₖ σ.sqrtMatrix) =
          ρ.sqrtMatrix *
            (((Real.sqrt d : ℝ) : ℂ) • ((MState.uniform : MState a).prod σ).sqrtMatrix) := by
            rw [hsqrt]
      _ = (((Real.sqrt d : ℝ) : ℂ) • M) := by
            dsimp [M]
            rw [Matrix.mul_smul]
  rw [conditionalMaxEntropyExponentCandidate_eq_sqrt_identity]
  rw [hrewrite]
  rw [traceNorm_real_smul_eq hsqrt_nonneg M]
  rw [MState.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  dsimp [M, d]
  let t : ℝ := traceNorm (ρ.sqrtMatrix * ((MState.uniform : MState a).prod σ).sqrtMatrix)
  change (Real.sqrt (Fintype.card a : ℝ) * t) ^ 2 =
    (Fintype.card a : ℝ) * t ^ 2
  nlinarith [hsqrt_sq]

theorem conditionalMaxEntropy_hilbertSchmidt_trace_le
    (ρ : MState (a × b)) (σ : MState b) :
    ((star (ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ)) *
        (ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ))).trace).re ≤
      (Fintype.card a : ℝ) := by
  let S : CMatrix (a × b) := identityTensorStateMatrix (a := a) σ
  let T : CMatrix (a × b) := psdSqrt S
  have hSpos : S.PosSemidef := identityTensorStateMatrix_posSemidef (a := a) σ
  have hTstar : star T = T := (psdSqrt_isHermitian S).eq
  have hle : star T * ρ.m * T ≤ star T * (1 : CMatrix (a × b)) * T :=
    star_left_conjugate_le_conjugate (ρ.matrix_le_one) T
  have hleft_eq :
      star (ρ.sqrtMatrix * T) * (ρ.sqrtMatrix * T) = star T * ρ.m * T := by
    calc
      star (ρ.sqrtMatrix * T) * (ρ.sqrtMatrix * T)
          = Tᴴ * (ρ.sqrtMatrix * (ρ.sqrtMatrix * T)) := by
              simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
                ρ.sqrtMatrix_isHermitian.eq, Matrix.mul_assoc]
      _ = Tᴴ * ((ρ.sqrtMatrix * ρ.sqrtMatrix) * T) := by rw [Matrix.mul_assoc]
      _ = Tᴴ * (ρ.m * T) := by rw [ρ.sqrtMatrix_mul_self]
      _ = star T * ρ.m * T := by
          simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hright_eq : star T * (1 : CMatrix (a × b)) * T = S := by
    rw [hTstar]
    simp [T, psdSqrt_mul_self_of_posSemidef hSpos]
  have htrace_le := cMatrix_trace_re_le_of_le hle
  rw [hright_eq] at htrace_le
  change (star (ρ.sqrtMatrix * T) * (ρ.sqrtMatrix * T)).trace.re ≤
    (Fintype.card a : ℝ)
  rw [hleft_eq]
  exact htrace_le.trans_eq (identityTensorStateMatrix_trace_re (a := a) σ)

theorem conditionalMaxEntropyExponentCandidate_le_card
    (ρ : MState (a × b)) (σ : MState b) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ≤
      (Fintype.card (a × b) : ℝ) * (Fintype.card a : ℝ) := by
  let M : CMatrix (a × b) :=
    ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ)
  have hhs : ((star M * M).trace).re ≤ (Fintype.card a : ℝ) :=
    conditionalMaxEntropy_hilbertSchmidt_trace_le (a := a) ρ σ
  have htn := traceNorm_sq_le_card_mul_hilbertSchmidt M
  unfold conditionalMaxEntropyExponentCandidate
  change traceNorm M ^ 2 ≤ (Fintype.card (a × b) : ℝ) * (Fintype.card a : ℝ)
  exact htn.trans (mul_le_mul_of_nonneg_left hhs (Nat.cast_nonneg _))

/-- The definition-level conditional max-entropy candidate set.

It filters out zero endpoint exponents before applying `log₂`, matching the
finite-real-valued convention used by `MState.conditionalMaxEntropy`: this is the
real-valued replacement for the usual extended-real convention `log 0 = -∞`. -/
def conditionalMaxEntropyValueSet (ρ : MState (a × b)) : Set ℝ :=
  {h : ℝ | ∃ σ : MState b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      h = conditionalMaxEntropyCandidate (a := a) ρ σ}

@[simp]
theorem conditionalMaxEntropyValueSet_eq (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyValueSet (a := a) =
      {h : ℝ | ∃ σ : MState b,
        0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
          h = conditionalMaxEntropyCandidate (a := a) ρ σ} :=
  rfl

theorem conditionalMaxEntropy_eq_sSup_valueSet (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropy =
      sSup (ρ.conditionalMaxEntropyValueSet (a := a)) := by
  rfl

theorem conditionalMaxEntropyValueSet_nonempty [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    (ρ.conditionalMaxEntropyValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyCandidate (a := a) (MState.uniform : MState b),
    (MState.uniform : MState b), ρ.conditionalMaxEntropyExponentCandidate_uniform_pos
      (a := a), rfl⟩

theorem conditionalMaxEntropyCandidate_le_log2_card_bound
    [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) (σ : MState b) :
    ρ.conditionalMaxEntropyCandidate (a := a) σ ≤
      max 0 (log2 ((Fintype.card (a × b) : ℝ) * (Fintype.card a : ℝ))) := by
  by_cases hpos : 0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ
  · have hle := ρ.conditionalMaxEntropyExponentCandidate_le_card (a := a) σ
    have hbound_pos :
        0 < (Fintype.card (a × b) : ℝ) * (Fintype.card a : ℝ) := by
      have hprod : 0 < (Fintype.card (a × b) : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨Classical.arbitrary (a × b)⟩
      have ha : 0 < (Fintype.card a : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨Classical.arbitrary a⟩
      exact mul_pos hprod ha
    have hlog :
        log2 (ρ.conditionalMaxEntropyExponentCandidate (a := a) σ) ≤
          log2 ((Fintype.card (a × b) : ℝ) * (Fintype.card a : ℝ)) := by
      unfold log2
      exact div_le_div_of_nonneg_right (Real.log_le_log hpos hle)
        (le_of_lt (Real.log_pos one_lt_two))
    rw [conditionalMaxEntropyCandidate_eq_log2_exponentCandidate]
    exact hlog.trans (le_max_right _ _)
  · have hzero : ρ.conditionalMaxEntropyExponentCandidate (a := a) σ = 0 := by
      exact le_antisymm (le_of_not_gt hpos)
        (ρ.conditionalMaxEntropyExponentCandidate_nonneg (a := a) σ)
    rw [conditionalMaxEntropyCandidate_eq_log2_exponentCandidate, hzero]
    simp [log2]

theorem conditionalMaxEntropyValueSet_bddAbove [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    BddAbove (ρ.conditionalMaxEntropyValueSet (a := a)) := by
  refine ⟨max 0 (log2 ((Fintype.card (a × b) : ℝ) *
    (Fintype.card a : ℝ))), ?_⟩
  intro h hh
  rcases hh with ⟨σ, _hpos, rfl⟩
  exact ρ.conditionalMaxEntropyCandidate_le_log2_card_bound (a := a) σ

/-- The normalized fidelity form of the conditional max-entropy endpoint
optimization:
`{F(ρ_AB, π_A ⊗ σ_B)^2 | σ_B}`. -/
def conditionalMaxEntropyFidelityValueSet [Nonempty a]
    (ρ : MState (a × b)) : Set ℝ :=
  {x : ℝ | ∃ σ : MState b,
    x = ρ.squaredFidelity ((MState.uniform : MState a).prod σ)}

theorem conditionalMaxEntropyFidelityValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    (ρ.conditionalMaxEntropyFidelityValueSet (a := a)).Nonempty :=
  ⟨ρ.squaredFidelity ((MState.uniform : MState a).prod (MState.uniform : MState b)),
    (MState.uniform : MState b), rfl⟩

theorem conditionalMaxEntropyFidelityValueSet_bddAbove
    [Nonempty a] (ρ : MState (a × b)) :
    BddAbove (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  refine ⟨(Fintype.card (a × b) : ℝ), ?_⟩
  intro x hx
  rcases hx with ⟨σ, rfl⟩
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hle := conditionalMaxEntropyExponentCandidate_le_card
    (a := a) ρ σ
  rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
    (a := a) ρ σ] at hle
  nlinarith

/-! ### Block-SDP surface for the fidelity endpoint -/

/-- Block-matrix feasibility for the finite-dimensional fidelity SDP:
`[[ρ_AB, X], [X†, π_A ⊗ σ_B]] ≥ 0`.

This is the primal block-cone side that will later be dualized against the
conditional-min scale. -/
def ConditionalMaxFidelityBlockFeasible [Nonempty a]
    (ρ : MState (a × b)) (σ : MState b) (X : CMatrix (a × b)) : Prop :=
  (Matrix.fromBlocks ρ.m X (star X) ((MState.uniform : MState a).prod σ).m :
      CMatrix ((a × b) ⊕ (a × b))).PosSemidef

@[simp]
theorem ConditionalMaxFidelityBlockFeasible_eq [Nonempty a]
    (ρ : MState (a × b)) (σ : MState b) (X : CMatrix (a × b)) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ↔
      (Matrix.fromBlocks ρ.m X (star X) ((MState.uniform : MState a).prod σ).m :
        CMatrix ((a × b) ⊕ (a × b))).PosSemidef :=
  Iff.rfl

/-- The linear objective in the fidelity block SDP.  The squared endpoint value
uses this quantity squared. -/
def conditionalMaxFidelityBlockValue (X : CMatrix (a × b)) : ℝ :=
  X.trace.re

omit [DecidableEq a] [DecidableEq b] in
@[simp]
theorem conditionalMaxFidelityBlockValue_eq (X : CMatrix (a × b)) :
    conditionalMaxFidelityBlockValue X = X.trace.re :=
  rfl

/-- The max-entropy endpoint value represented through a feasible block SDP
candidate. -/
def conditionalMaxFidelityBlockExponentValue [Nonempty a]
    (X : CMatrix (a × b)) : ℝ :=
  (Fintype.card a : ℝ) * (conditionalMaxFidelityBlockValue X) ^ 2

omit [DecidableEq a] [DecidableEq b] in
@[simp]
theorem conditionalMaxFidelityBlockExponentValue_eq [Nonempty a]
    (X : CMatrix (a × b)) :
    conditionalMaxFidelityBlockExponentValue (a := a) X =
      (Fintype.card a : ℝ) * X.trace.re ^ 2 :=
  rfl

/-- Zero off-diagonal block feasibility.  This proves the block SDP surface is
nonempty without using any fidelity or duality theorem. -/
theorem ConditionalMaxFidelityBlockFeasible_zero [Nonempty a]
    (ρ : MState (a × b)) (σ : MState b) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ 0 := by
  simpa [ConditionalMaxFidelityBlockFeasible] using
    cMatrix_fromBlocks_diagonal_posSemidef (a := a × b) ρ.psd
      (((MState.uniform : MState a).prod σ).psd)

private def scaledBlockEmbeddingMatrix {α : Type*} [Fintype α] [DecidableEq α]
    (t : ℝ) : Matrix (α ⊕ α) α ℂ :=
  fun x y =>
    match x with
    | Sum.inl i => if i = y then (Real.sqrt t : ℂ) else 0
    | Sum.inr i => if i = y then 1 else 0

private theorem scaledBlockEmbeddingMatrix_mul_pos_mul_conjTranspose
    {α : Type*} [Fintype α] [DecidableEq α]
    {τ : CMatrix α} (hτ : τ.PosSemidef) (t : ℝ) :
    (scaledBlockEmbeddingMatrix (α := α) t * τ *
      (scaledBlockEmbeddingMatrix (α := α) t)ᴴ).PosSemidef := by
  exact hτ.mul_mul_conjTranspose_same (scaledBlockEmbeddingMatrix (α := α) t)

private theorem scaledBlockEmbeddingMatrix_block_eq {α : Type*}
    [Fintype α] [DecidableEq α] {τ : CMatrix α} {t : ℝ} (ht : 0 ≤ t) :
    scaledBlockEmbeddingMatrix (α := α) t * τ *
      (scaledBlockEmbeddingMatrix (α := α) t)ᴴ =
        (Matrix.fromBlocks (((t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ) τ : CMatrix (α ⊕ α)) := by
  classical
  ext x y
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          simp [scaledBlockEmbeddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.fromBlocks, Matrix.of_apply]
          rw [Finset.sum_eq_single j]
          · simp
            ring_nf
            rw [← Complex.ofReal_pow]
            rw [Real.sq_sqrt ht]
            ring
          · intro x _ hx
            have hx' : ¬ j = x := by intro h; exact hx h.symm
            simp [hx']
          · intro hnot
            simp at hnot
      | inr j =>
          simp [scaledBlockEmbeddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.fromBlocks, Matrix.of_apply]
  | inr i =>
      cases y with
      | inl j =>
          simp [scaledBlockEmbeddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.fromBlocks, Matrix.of_apply]
          rw [Finset.sum_eq_single j]
          · simp
            ring
          · intro x _ hx
            have hx' : ¬ j = x := by intro h; exact hx h.symm
            simp [hx']
          · intro hnot
            simp at hnot
      | inr j =>
          simp [scaledBlockEmbeddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.fromBlocks, Matrix.of_apply]

theorem ConditionalMaxFidelityBlockFeasible.of_scaled_le [Nonempty a]
    {ρ : MState (a × b)} {σ : MState b} {t : ℝ} (ht : 0 ≤ t)
    (hle : (((t : ℝ) : ℂ) • ((MState.uniform : MState a).prod σ).m) ≤ ρ.m) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ
      ((((Real.sqrt t : ℝ) : ℂ) • ((MState.uniform : MState a).prod σ).m)) := by
  classical
  let τ : CMatrix (a × b) := ((MState.uniform : MState a).prod σ).m
  have hdiff : (ρ.m - (((t : ℝ) : ℂ) • τ)).PosSemidef := by
    simpa [τ, Matrix.le_iff] using hle
  have hdiag :
      (Matrix.fromBlocks (ρ.m - (((t : ℝ) : ℂ) • τ)) 0 0
        (0 : CMatrix (a × b)) :
        CMatrix ((a × b) ⊕ (a × b))).PosSemidef := by
    exact cMatrix_fromBlocks_diagonal_posSemidef hdiff Matrix.PosSemidef.zero
  have hrank :
      (Matrix.fromBlocks (((t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ) τ :
          CMatrix ((a × b) ⊕ (a × b))).PosSemidef := by
    rw [← scaledBlockEmbeddingMatrix_block_eq (α := a × b) (τ := τ) ht]
    exact scaledBlockEmbeddingMatrix_mul_pos_mul_conjTranspose
      ((MState.uniform : MState a).prod σ).psd t
  have hsum :
      (Matrix.fromBlocks ρ.m
          ((((Real.sqrt t : ℝ) : ℂ) • τ))
          (Matrix.conjTranspose ((((Real.sqrt t : ℝ) : ℂ) • τ)))
          τ :
          CMatrix ((a × b) ⊕ (a × b))) =
        (Matrix.fromBlocks (ρ.m - (((t : ℝ) : ℂ) • τ)) 0 0
          (0 : CMatrix (a × b)) :
          CMatrix ((a × b) ⊕ (a × b))) +
        (Matrix.fromBlocks (((t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ) τ :
          CMatrix ((a × b) ⊕ (a × b))) := by
    have hτH : Matrix.conjTranspose τ = τ := ((MState.uniform : MState a).prod σ).psd.isHermitian.eq
    ext x y
    cases x <;> cases y <;>
      simp [Matrix.fromBlocks, Matrix.of_apply, Matrix.conjTranspose_smul, hτH]
  rw [ConditionalMaxFidelityBlockFeasible]
  change (Matrix.fromBlocks ρ.m
    ((((Real.sqrt t : ℝ) : ℂ) • τ))
    (Matrix.conjTranspose ((((Real.sqrt t : ℝ) : ℂ) • τ)))
    τ : CMatrix ((a × b) ⊕ (a × b))).PosSemidef
  rw [hsum]
  exact hdiag.add hrank

theorem ConditionalMaxFidelityBlockFeasible.of_scaled_le_blockExponentValue [Nonempty a]
    {σ : MState b} {t : ℝ} (ht : 0 ≤ t) :
    conditionalMaxFidelityBlockExponentValue (a := a)
        ((((Real.sqrt t : ℝ) : ℂ) • ((MState.uniform : MState a).prod σ).m)) =
      (Fintype.card a : ℝ) * t := by
  have htrace :
      (((((Real.sqrt t : ℝ) : ℂ) • ((MState.uniform : MState a).prod σ).m)).trace).re =
        Real.sqrt t := by
    rw [Matrix.trace_smul, ((MState.uniform : MState a).prod σ).tr']
    simp
  rw [conditionalMaxFidelityBlockExponentValue_eq, htrace]
  rw [Real.sq_sqrt ht]

/-! ### Block-SDP feasible points are fidelity-bounded -/

/-- The ket on `r × α` whose amplitude matrix is `A`, which is a unit vector exactly because
`tr (A Aᴴ) = 1`.  By `ketOfAmplitudeMatrix_purifies` it purifies any `ρ` with `A Aᴴ = ρ.m`. -/
def ketOfAmplitudeMatrix {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (A : Matrix α r ℂ) (htrace : (A * Aᴴ).trace = 1) :
    Ket (r × α) :=
  Ket.ofRankOne (fun x => A x.2 x.1) <| by
    classical
    calc
      (rankOneMatrix (fun x : r × α => A x.2 x.1)).trace =
          ∑ x : r × α, A x.2 x.1 * star (A x.2 x.1) := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = ∑ i : α, ∑ j : r, A i j * star (A i j) := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
      _ = (A * Aᴴ).trace := by
            simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = 1 := htrace

theorem ketOfAmplitudeMatrix_amplitudeMatrix {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (A : Matrix α r ℂ) (htrace : (A * Aᴴ).trace = 1) :
    (ketOfAmplitudeMatrix A htrace).amplitudeMatrix = A := by
  rfl

theorem ketOfAmplitudeMatrix_purifies {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    {A : Matrix α r ℂ} {ρ : MState α}
    (hgram : A * Aᴴ = ρ.m) (htrace : (A * Aᴴ).trace = 1) :
    (ketOfAmplitudeMatrix A htrace).Purifies ρ := by
  rw [Ket.purifies_iff]
  rw [Ket.state_matrix]
  rw [Ket.traceLeft_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
  simpa [ketOfAmplitudeMatrix_amplitudeMatrix] using hgram

/-- Given a purification `η` of a `B`-side state on `r × b`, the amplitude matrix obtained by
gluing a maximally entangled pair across the two `A` copies onto `η`.  Its Gram matrix is
`π_A ⊗ Tr_r η`, by `maxEntangledSideAmplitude_gram`. -/
def maxEntangledSideAmplitude {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a]
    (η : Ket (r × b)) : Matrix (a × b) (r × a) ℂ :=
  fun x y =>
    (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
      (if y.2 = x.1 then η.vec (y.1, x.2) else 0)

theorem maxEntangledSideAmplitude_gram {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (η : Ket (r × b)) :
    maxEntangledSideAmplitude (a := a) η *
        (maxEntangledSideAmplitude (a := a) η)ᴴ =
      ((MState.uniform : MState a).prod η.state.traceLeft).m := by
  classical
  ext x y
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  let s : ℂ := ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ)
  have hcoeff : s * s = (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← sq, Real.sq_sqrt]
    exact inv_nonneg.mpr (le_of_lt hcard_pos)
  have hcoeff' :
      (((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ) *
          ((Real.sqrt ((Fintype.card a : ℝ)⁻¹) : ℝ) : ℂ)) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa [s] using hcoeff
  have hcoeff_inv_sqrt :
      (((Real.sqrt (Fintype.card a : ℝ))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (Fintype.card a : ℝ))⁻¹ : ℝ) : ℂ) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hcard_pos)]
    rw [Real.sq_sqrt (le_of_lt hcard_pos)]
  have hcoeff_complex_inv :
      (((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹) *
          ((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹)) =
        (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa [Complex.ofReal_inv] using hcoeff_inv_sqrt
  by_cases hxy : xa = ya
  · subst ya
    simp [maxEntangledSideAmplitude, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.traceLeft,
      Matrix.kroneckerMap_apply, Finset.mul_sum,
      Fintype.sum_prod_type,
      mul_assoc, mul_left_comm, mul_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, hcoeff_complex_inv]
    rw [Complex.ofReal_inv]
    norm_num
  · simp [maxEntangledSideAmplitude, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, hxy]

/-- The ket of `maxEntangledSideAmplitude`: a purification of `π_A ⊗ Tr_r η` on `(r × a) × (a × b)`,
which is the side state the fidelity endpoint is measured against. -/
def maxEntangledSideKet {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (η : Ket (r × b)) :
    Ket ((r × a) × (a × b)) :=
  ketOfAmplitudeMatrix (maxEntangledSideAmplitude (a := a) η) (by
    rw [maxEntangledSideAmplitude_gram]
    exact ((MState.uniform : MState a).prod η.state.traceLeft).tr')

theorem maxEntangledSideKet_purifies {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (η : Ket (r × b)) :
    (maxEntangledSideKet (a := a) η).Purifies
      ((MState.uniform : MState a).prod η.state.traceLeft) := by
  exact ketOfAmplitudeMatrix_purifies
    (maxEntangledSideAmplitude_gram (a := a) η)
    (by
      rw [maxEntangledSideAmplitude_gram]
      exact ((MState.uniform : MState a).prod η.state.traceLeft).tr')

private def blockSqrtTopRow {α : Type*} [Fintype α] [DecidableEq α]
    (S : CMatrix (α ⊕ α)) : Matrix α (α ⊕ α) ℂ :=
  fun i j => S (Sum.inl i) j

private def blockSqrtBottomRow {α : Type*} [Fintype α] [DecidableEq α]
    (S : CMatrix (α ⊕ α)) : Matrix α (α ⊕ α) ℂ :=
  fun i j => S (Sum.inr i) j

private theorem blockSqrtTopRow_mul_conjTranspose {α : Type*}
    [Fintype α] [DecidableEq α] (S : CMatrix (α ⊕ α)) (hS : S.IsHermitian) :
    blockSqrtTopRow S * (blockSqrtTopRow S)ᴴ = Matrix.sumBlock11 (S * S) := by
  classical
  ext i j
  simp only [blockSqrtTopRow, Matrix.sumBlock11_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk : star (S (Sum.inl j) k) = S k (Sum.inl j) := by
    have h := congrFun (congrFun hS.eq k) (Sum.inl j)
    simpa [Matrix.conjTranspose_apply] using h
  rw [hk]

private theorem blockSqrtBottomRow_mul_conjTranspose {α : Type*}
    [Fintype α] [DecidableEq α] (S : CMatrix (α ⊕ α)) (hS : S.IsHermitian) :
    blockSqrtBottomRow S * (blockSqrtBottomRow S)ᴴ = Matrix.sumBlock22 (S * S) := by
  classical
  ext i j
  simp only [blockSqrtBottomRow, Matrix.sumBlock22_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk : star (S (Sum.inr j) k) = S k (Sum.inr j) := by
    have h := congrFun (congrFun hS.eq k) (Sum.inr j)
    simpa [Matrix.conjTranspose_apply] using h
  rw [hk]

private theorem blockSqrtTopRow_mul_bottomRow_conjTranspose {α : Type*}
    [Fintype α] [DecidableEq α] (S : CMatrix (α ⊕ α)) (hS : S.IsHermitian) :
    blockSqrtTopRow S * (blockSqrtBottomRow S)ᴴ = Matrix.sumBlock12 (S * S) := by
  classical
  ext i j
  simp only [blockSqrtTopRow, blockSqrtBottomRow, Matrix.sumBlock12_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk : star (S (Sum.inr j) k) = S k (Sum.inr j) := by
    have h := congrFun (congrFun hS.eq k) (Sum.inr j)
    simpa [Matrix.conjTranspose_apply] using h
  rw [hk]

private theorem abs_trace_eq_abs_overlap_of_amplitude_gram {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    {A B : Matrix α r ℂ} {X : CMatrix α}
    (hX : A * Bᴴ = X) {hAtrace : (A * Aᴴ).trace = 1}
    {hBtrace : (B * Bᴴ).trace = 1} :
     ‖X.trace‖ =
       ‖(ketOfAmplitudeMatrix A hAtrace).overlap
        (ketOfAmplitudeMatrix B hBtrace)‖ := by
  let Ψ := ketOfAmplitudeMatrix A hAtrace
  let Φ := ketOfAmplitudeMatrix B hBtrace
  have hoverlap :
      Ψ.overlap Φ = (Aᴴ * B).trace := by
    rw [Ket.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
    rfl
  have htrace_conj :
      X.trace = star ((Aᴴ * B).trace) := by
    calc
      X.trace = (A * Bᴴ).trace := by rw [← hX]
      _ = (Bᴴ * A).trace := by rw [Matrix.trace_mul_comm]
      _ = (Matrix.conjTranspose (Aᴴ * B)).trace := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = star ((Aᴴ * B).trace) := Matrix.trace_conjTranspose _
  rw [htrace_conj, hoverlap]
  simp

theorem ConditionalMaxFidelityBlockFeasible.abs_trace_le_fidelity [Nonempty a]
    {ρ : MState (a × b)} {σ : MState b} {X : CMatrix (a × b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
     ‖X.trace‖ ≤ ρ.fidelity ((MState.uniform : MState a).prod σ) := by
  classical
  let α := (a × b)
  let τ : MState α := (MState.uniform : MState a).prod σ
  let H : CMatrix (α ⊕ α) := Matrix.fromBlocks ρ.m X (star X) τ.m
  let S : CMatrix (α ⊕ α) := psdSqrt H
  let A : Matrix α (α ⊕ α) ℂ := blockSqrtTopRow S
  let B : Matrix α (α ⊕ α) ℂ := blockSqrtBottomRow S
  have hH : H.PosSemidef := hX
  have hS : S.IsHermitian := psdSqrt_isHermitian H
  have hSsq : S * S = H := psdSqrt_mul_self_of_posSemidef hH
  have hAgram : A * Aᴴ = ρ.m := by
    calc
      A * Aᴴ = Matrix.sumBlock11 (S * S) :=
        blockSqrtTopRow_mul_conjTranspose S hS
      _ = Matrix.sumBlock11 H := by rw [hSsq]
      _ = ρ.m := by rfl
  have hBgram : B * Bᴴ = τ.m := by
    calc
      B * Bᴴ = Matrix.sumBlock22 (S * S) :=
        blockSqrtBottomRow_mul_conjTranspose S hS
      _ = Matrix.sumBlock22 H := by rw [hSsq]
      _ = τ.m := by rfl
  have hAB : A * Bᴴ = X := by
    calc
      A * Bᴴ = Matrix.sumBlock12 (S * S) :=
        blockSqrtTopRow_mul_bottomRow_conjTranspose S hS
      _ = Matrix.sumBlock12 H := by rw [hSsq]
      _ = X := by rfl
  have hAtrace : (A * Aᴴ).trace = 1 := by
    rw [hAgram, ρ.tr']
  have hBtrace : (B * Bᴴ).trace = 1 := by
    rw [hBgram, τ.tr']
  let Ψ : Ket ((α ⊕ α) × α) := ketOfAmplitudeMatrix A hAtrace
  let Φ : Ket ((α ⊕ α) × α) := ketOfAmplitudeMatrix B hBtrace
  have hΨ : Ψ.Purifies ρ := ketOfAmplitudeMatrix_purifies hAgram hAtrace
  have hΦ : Φ.Purifies τ := ketOfAmplitudeMatrix_purifies hBgram hBtrace
  have habs :
       ‖X.trace‖ = ‖Ψ.overlap Φ‖ :=
    abs_trace_eq_abs_overlap_of_amplitude_gram hAB
  rw [habs]
  exact Ket.abs_overlap_le_fidelity hΨ hΦ

theorem ConditionalMaxFidelityBlockFeasible.trace_re_le_fidelity [Nonempty a]
    {ρ : MState (a × b)} {σ : MState b} {X : CMatrix (a × b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    X.trace.re ≤ ρ.fidelity ((MState.uniform : MState a).prod σ) :=
  (Complex.re_le_norm X.trace).trans hX.abs_trace_le_fidelity

theorem ConditionalMaxFidelityBlockFeasible.blockValue_le_fidelity [Nonempty a]
    {ρ : MState (a × b)} {σ : MState b} {X : CMatrix (a × b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    conditionalMaxFidelityBlockValue X ≤
      ρ.fidelity ((MState.uniform : MState a).prod σ) := by
  simpa [conditionalMaxFidelityBlockValue] using hX.trace_re_le_fidelity

theorem ConditionalMaxFidelityBlockFeasible.blockExponentValue_le_exponentCandidate
    [Nonempty a] {ρ : MState (a × b)} {σ : MState b} {X : CMatrix (a × b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    conditionalMaxFidelityBlockExponentValue (a := a) X ≤
      ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  rw [conditionalMaxFidelityBlockExponentValue_eq,
    conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
    MState.squaredFidelity_eq_fidelity_sq]
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by exact_mod_cast Nat.zero_le _
  have habs_sq :
      X.trace.re ^ 2 ≤ ρ.fidelity ((MState.uniform : MState a).prod σ) ^ 2 := by
    have hre_abs : |X.trace.re| ≤ ‖X.trace‖ :=
      Complex.abs_re_le_norm X.trace
    have hle_abs : |X.trace.re| ≤ ρ.fidelity ((MState.uniform : MState a).prod σ) :=
      hre_abs.trans hX.abs_trace_le_fidelity
    have hleft : 0 ≤ |X.trace.re| := abs_nonneg _
    have hright : 0 ≤ ρ.fidelity ((MState.uniform : MState a).prod σ) :=
      traceNorm_nonneg _
    have hsquare := (sq_le_sq₀ hleft hright).mpr hle_abs
    simpa [sq_abs] using hsquare
  exact mul_le_mul_of_nonneg_left habs_sq hcard_nonneg

/-- Unitary polar factors produce feasible points of the fidelity block SDP:
`X = √ρ U √(π_A ⊗ σ_B)`. -/
theorem ConditionalMaxFidelityBlockFeasible.of_unitary_sqrt [Nonempty a]
    (ρ : MState (a × b)) (σ : MState b)
    (U : Matrix.unitaryGroup (a × b) ℂ) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ
      (ρ.sqrtMatrix * (U : CMatrix (a × b)) *
        ((MState.uniform : MState a).prod σ).sqrtMatrix) := by
  let τ : MState (a × b) := (MState.uniform : MState a).prod σ
  let H : CMatrix ((a × b) ⊕ (a × b)) :=
    Matrix.fromBlocks (1 : CMatrix (a × b)) (U : CMatrix (a × b))
      (star (U : CMatrix (a × b))) 1
  let S : CMatrix ((a × b) ⊕ (a × b)) :=
    Matrix.fromBlocks ρ.sqrtMatrix 0 0 τ.sqrtMatrix
  have hH : H.PosSemidef := by
    simpa [H] using cMatrix_fromBlocks_unitary_posSemidef U
  have hconj : (S * H * star S).PosSemidef := by
    simpa [Matrix.mul_assoc, Matrix.star_eq_conjTranspose] using
      hH.mul_mul_conjTranspose_same S
  have hEq :
      S * H * star S =
        (Matrix.fromBlocks ρ.m
          (ρ.sqrtMatrix * (U : CMatrix (a × b)) * τ.sqrtMatrix)
          (star (ρ.sqrtMatrix * (U : CMatrix (a × b)) * τ.sqrtMatrix))
          τ.m : CMatrix ((a × b) ⊕ (a × b))) := by
    have hρH : ρ.sqrtMatrixᴴ = ρ.sqrtMatrix := ρ.sqrtMatrix_isHermitian.eq
    have hτH : τ.sqrtMatrixᴴ = τ.sqrtMatrix := τ.sqrtMatrix_isHermitian.eq
    have hρsq : ρ.sqrtMatrix * ρ.sqrtMatrix = ρ.m := ρ.sqrtMatrix_mul_self
    have hτsq : τ.sqrtMatrix * τ.sqrtMatrix = τ.m := τ.sqrtMatrix_mul_self
    dsimp [S, H]
    change
      Matrix.fromBlocks ρ.sqrtMatrix 0 0 τ.sqrtMatrix *
          Matrix.fromBlocks (1 : CMatrix (a × b)) (U : CMatrix (a × b))
            (star (U : CMatrix (a × b))) 1 *
            (Matrix.fromBlocks ρ.sqrtMatrix 0 0 τ.sqrtMatrix)ᴴ =
        (Matrix.fromBlocks ρ.m
          (ρ.sqrtMatrix * (U : CMatrix (a × b)) * τ.sqrtMatrix)
          (star (ρ.sqrtMatrix * (U : CMatrix (a × b)) * τ.sqrtMatrix))
          τ.m :
          CMatrix ((a × b) ⊕ (a × b)))
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;>
      simp [hρH, hτH, hρsq, hτsq, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simpa [ConditionalMaxFidelityBlockFeasible, τ, hEq] using hconj

/-- The fidelity block constraint is invariant under a scalar phase rotation of
the off-diagonal block. -/
theorem ConditionalMaxFidelityBlockFeasible.smul_phase [Nonempty a]
    {ρ : MState (a × b)} {σ : MState b} {X : CMatrix (a × b)}
    {c : ℂ} (hc : c * star c = 1)
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ (c • X) := by
  let D : CMatrix ((a × b) ⊕ (a × b)) :=
    Matrix.fromBlocks (1 : CMatrix (a × b)) 0 0
      ((star c) • (1 : CMatrix (a × b)))
  have hc'' : c * (starRingEnd ℂ) c = 1 := by
    simpa using hc
  have hconj :
      (D *
          (Matrix.fromBlocks ρ.m X (star X) ((MState.uniform : MState a).prod σ).m :
            CMatrix ((a × b) ⊕ (a × b))) *
            star D).PosSemidef :=
    hX.mul_mul_conjTranspose_same D
  have hEq :
      D *
          (Matrix.fromBlocks ρ.m X (star X) ((MState.uniform : MState a).prod σ).m :
            CMatrix ((a × b) ⊕ (a × b))) *
            star D =
        (Matrix.fromBlocks ρ.m (c • X) (star (c • X))
          ((MState.uniform : MState a).prod σ).m :
          CMatrix ((a × b) ⊕ (a × b))) := by
    dsimp [D]
    simp_rw [Matrix.star_eq_conjTranspose]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;> simp [← mul_assoc, hc'']
  rw [hEq] at hconj
  exact hconj

/-- For each side state `σ_B`, the fidelity block SDP has a feasible point
whose absolute trace objective attains the root fidelity
`F(ρ_AB, π_A ⊗ σ_B)`. -/
theorem exists_ConditionalMaxFidelityBlockFeasible_abs_trace_eq_fidelity
    [Nonempty a] (ρ : MState (a × b)) (σ : MState b) :
    ∃ X : CMatrix (a × b),
      ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
         ‖X.trace‖ =
          ρ.fidelity ((MState.uniform : MState a).prod σ) := by
  let τ : MState (a × b) := (MState.uniform : MState a).prod σ
  obtain ⟨U, hU⟩ :=
    traceNorm_variational_exists_unitary_abs_trace (τ.sqrtMatrix * ρ.sqrtMatrix)
  let X : CMatrix (a × b) := ρ.sqrtMatrix * (U : CMatrix (a × b)) * τ.sqrtMatrix
  refine ⟨X, ?_, ?_⟩
  · exact ConditionalMaxFidelityBlockFeasible.of_unitary_sqrt (a := a) ρ σ U
  · have htrace :
        X.trace = ((τ.sqrtMatrix * ρ.sqrtMatrix) * (U : CMatrix (a × b))).trace := by
      calc
        X.trace = ((ρ.sqrtMatrix * (U : CMatrix (a × b))) * τ.sqrtMatrix).trace := by
          simp [X, Matrix.mul_assoc]
        _ = (τ.sqrtMatrix * (ρ.sqrtMatrix * (U : CMatrix (a × b)))).trace := by
          rw [Matrix.trace_mul_comm]
        _ = ((τ.sqrtMatrix * ρ.sqrtMatrix) * (U : CMatrix (a × b))).trace := by
          rw [Matrix.mul_assoc]
    have hconj :
        τ.sqrtMatrix * ρ.sqrtMatrix =
          Matrix.conjTranspose (ρ.sqrtMatrix * τ.sqrtMatrix) := by
      rw [Matrix.conjTranspose_mul, ρ.sqrtMatrix_isHermitian.eq,
        τ.sqrtMatrix_isHermitian.eq]
    calc
       ‖X.trace‖ =
           ‖((τ.sqrtMatrix * ρ.sqrtMatrix) *
            (U : CMatrix (a × b))).trace‖ := by rw [htrace]
      _ = traceNorm (τ.sqrtMatrix * ρ.sqrtMatrix) := hU
      _ = traceNorm (ρ.sqrtMatrix * τ.sqrtMatrix) := by
        rw [hconj, traceNorm_conjTranspose]
      _ = ρ.fidelity τ := by rfl

/-- For each side state `σ_B`, the fidelity block SDP has a feasible point
whose real trace objective attains the root fidelity. -/
theorem exists_ConditionalMaxFidelityBlockFeasible_trace_re_eq_fidelity
    [Nonempty a] (ρ : MState (a × b)) (σ : MState b) :
    ∃ X : CMatrix (a × b),
      ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
        conditionalMaxFidelityBlockValue X =
          ρ.fidelity ((MState.uniform : MState a).prod σ) := by
  rcases exists_ConditionalMaxFidelityBlockFeasible_abs_trace_eq_fidelity
      (a := a) ρ σ with ⟨X, hX, hXtrace⟩
  rcases exists_complex_phase_mul_re_eq_abs X.trace with ⟨c, hc, hcTrace⟩
  refine ⟨c • X, ?_, ?_⟩
  · exact ConditionalMaxFidelityBlockFeasible.smul_phase (a := a) hc hX
  · have htrace : (c • X).trace = c * X.trace := by
      simp [Matrix.trace, Finset.mul_sum]
    calc
      conditionalMaxFidelityBlockValue (c • X) = (c * X.trace).re := by
        simp [conditionalMaxFidelityBlockValue, htrace]
      _ = ‖X.trace‖ := hcTrace
      _ = ρ.fidelity ((MState.uniform : MState a).prod σ) := hXtrace

/-- Feasible objective values for the block-SDP representation of the
conditional max-fidelity endpoint. -/
def conditionalMaxFidelityBlockValueSet [Nonempty a]
    (ρ : MState (a × b)) : Set ℝ :=
  {v : ℝ | ∃ σ : MState b, ∃ X : CMatrix (a × b),
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
      v = conditionalMaxFidelityBlockValue X}

/-- Squared and dimension-scaled feasible endpoint values for the block-SDP
representation. -/
def conditionalMaxFidelityBlockExponentValueSet [Nonempty a]
    (ρ : MState (a × b)) : Set ℝ :=
  {v : ℝ | ∃ σ : MState b, ∃ X : CMatrix (a × b),
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
      v = conditionalMaxFidelityBlockExponentValue (a := a) X}

/-- Every definition-level max-entropy exponent candidate is realized by the
block-SDP endpoint surface. -/
theorem conditionalMaxEntropyExponentValueSet_subset_conditionalMaxFidelityBlockExponentValueSet
    [Nonempty a] (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyExponentValueSet (a := a) ⊆
      ρ.conditionalMaxFidelityBlockExponentValueSet (a := a) := by
  intro v hv
  rcases hv with ⟨σ, rfl⟩
  rcases ρ.exists_ConditionalMaxFidelityBlockFeasible_trace_re_eq_fidelity
      (a := a) σ with ⟨X, hX, hval⟩
  refine ⟨σ, X, hX, ?_⟩
  rw [conditionalMaxFidelityBlockExponentValue, hval]
  rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
    (a := a) ρ σ]
  rw [MState.squaredFidelity_eq_fidelity_sq]

theorem conditionalMaxFidelityBlockValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    (ρ.conditionalMaxFidelityBlockValueSet (a := a)).Nonempty := by
  refine ⟨0, (MState.uniform : MState b), 0, ?_, ?_⟩
  · exact ρ.ConditionalMaxFidelityBlockFeasible_zero (a := a) (MState.uniform : MState b)
  · simp [conditionalMaxFidelityBlockValue]

theorem conditionalMaxFidelityBlockExponentValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)).Nonempty := by
  refine ⟨0, (MState.uniform : MState b), 0, ?_, ?_⟩
  · exact ρ.ConditionalMaxFidelityBlockFeasible_zero (a := a) (MState.uniform : MState b)
  · simp [conditionalMaxFidelityBlockExponentValue, conditionalMaxFidelityBlockValue]

theorem conditionalMaxEntropyExponentValueSet_eq_card_mul_fidelityValueSet
    [Nonempty a] (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyExponentValueSet (a := a) =
      (fun x : ℝ => (Fintype.card a : ℝ) * x) ''
        ρ.conditionalMaxEntropyFidelityValueSet (a := a) := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨ρ.squaredFidelity ((MState.uniform : MState a).prod σ), ?_, ?_⟩
    · exact ⟨σ, rfl⟩
    · exact (conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
        (a := a) ρ σ
      ).symm
  · rintro ⟨y, ⟨σ, rfl⟩, rfl⟩
    refine ⟨σ, ?_⟩
    exact (conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
      (a := a) ρ σ).symm

theorem conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyExponent (a := a) =
      (Fintype.card a : ℝ) *
        sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  rw [conditionalMaxEntropyExponent, conditionalMaxEntropyExponentValueSet_eq_card_mul_fidelityValueSet
    (a := a) ρ]
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  exact mul_sSup_image_eq
    (ρ.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
    (ρ.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hcard_pos

/-- Positive raw max-entropy exponent candidate values.

The positivity filter is mathematically necessary for transporting `log₂`
through `sSup`: with the repository convention `log 0 = 0`, zero candidates
cannot be kept in the logarithmic candidate set without changing the supremum. -/
def conditionalMaxEntropyPositiveExponentValueSet (ρ : MState (a × b)) : Set ℝ :=
  {x : ℝ | ∃ σ : MState b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

/-- Definition-level max-entropy candidates whose raw exponent is strictly
positive. -/
def conditionalMaxEntropyPositiveValueSet (ρ : MState (a × b)) : Set ℝ :=
  {h : ℝ | ∃ σ : MState b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      h = ρ.conditionalMaxEntropyCandidate σ}

/-- The conditional max-entropy, presented as a supremum over the candidates whose raw exponent is
strictly positive.  That candidate set is definitionally `conditionalMaxEntropyValueSet`, so this
agrees with `conditionalMaxEntropy`; the separate name is what the endpoint-duality proofs use when
they need the positive raw exponent in scope. -/
def conditionalMaxEntropyPositive (ρ : MState (a × b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a))

/-- The positive-candidate raw endpoint exponent. -/
def conditionalMaxEntropyPositiveExponent (ρ : MState (a × b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))

theorem conditionalMaxEntropyPositiveExponentValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) (MState.uniform : MState b),
    (MState.uniform : MState b), ρ.conditionalMaxEntropyExponentCandidate_uniform_pos (a := a), rfl⟩

theorem conditionalMaxEntropyPositiveExponentValueSet_bddAbove
    [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) := by
  refine ⟨(Fintype.card (a × b) : ℝ) * (Fintype.card a : ℝ), ?_⟩
  intro x hx
  rcases hx with ⟨σ, _hpos, rfl⟩
  exact ρ.conditionalMaxEntropyExponentCandidate_le_card (a := a) σ

theorem conditionalMaxEntropyExponentValueSet_bddAbove
    [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    BddAbove (ρ.conditionalMaxEntropyExponentValueSet (a := a)) := by
  refine ⟨(Fintype.card (a × b) : ℝ) * (Fintype.card a : ℝ), ?_⟩
  intro x hx
  rcases hx with ⟨σ, rfl⟩
  exact ρ.conditionalMaxEntropyExponentCandidate_le_card (a := a) σ

theorem conditionalMaxEntropyExponentValueSet_nonempty
    [Nonempty b] (ρ : MState (a × b)) :
    (ρ.conditionalMaxEntropyExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) (MState.uniform : MState b),
    (MState.uniform : MState b), rfl⟩

theorem ConditionalMaxFidelityBlockFeasible.blockExponentValue_le_conditionalMaxEntropyExponent
    [Nonempty a] [Nonempty b] {ρ : MState (a × b)} {σ : MState b}
    {X : CMatrix (a × b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    conditionalMaxFidelityBlockExponentValue (a := a) X ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  calc
    conditionalMaxFidelityBlockExponentValue (a := a) X
        ≤ ρ.conditionalMaxEntropyExponentCandidate (a := a) σ :=
          hX.blockExponentValue_le_exponentCandidate
    _ ≤ ρ.conditionalMaxEntropyExponent (a := a) := by
          rw [conditionalMaxEntropyExponent]
          exact le_csSup (ρ.conditionalMaxEntropyExponentValueSet_bddAbove (a := a))
            ⟨σ, rfl⟩

theorem conditionalMaxFidelityBlockExponentValueSet_sSup_le_conditionalMaxEntropyExponent
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    sSup (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  refine csSup_le (ρ.conditionalMaxFidelityBlockExponentValueSet_nonempty (a := a)) ?_
  intro v hv
  rcases hv with ⟨σ, X, hX, rfl⟩
  exact hX.blockExponentValue_le_conditionalMaxEntropyExponent

/-- The block-SDP endpoint surface is bounded above by the definition-level
conditional max-entropy exponent. -/
theorem conditionalMaxFidelityBlockExponentValueSet_bddAbove
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    BddAbove (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) := by
  refine ⟨ρ.conditionalMaxEntropyExponent (a := a), ?_⟩
  intro x hx
  rcases hx with ⟨σ, X, hX, rfl⟩
  exact hX.blockExponentValue_le_conditionalMaxEntropyExponent

/-- The fidelity block-SDP endpoint has the same optimum as the
definition-level conditional max-entropy exponent. -/
theorem sSup_conditionalMaxFidelityBlockExponentValueSet_eq_conditionalMaxEntropyExponent
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    sSup (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) =
      ρ.conditionalMaxEntropyExponent (a := a) := by
  refine le_antisymm
    (ρ.conditionalMaxFidelityBlockExponentValueSet_sSup_le_conditionalMaxEntropyExponent
      (a := a)) ?_
  rw [conditionalMaxEntropyExponent]
  refine csSup_le (ρ.conditionalMaxEntropyExponentValueSet_nonempty (a := a)) ?_
  intro x hx
  exact le_csSup (ρ.conditionalMaxFidelityBlockExponentValueSet_bddAbove (a := a))
    (ρ.conditionalMaxEntropyExponentValueSet_subset_conditionalMaxFidelityBlockExponentValueSet
      (a := a) hx)

/-- The raw fidelity endpoint and the block-SDP endpoint have the same
dimension-scaled optimum. -/
theorem card_mul_sSup_fidelityValueSet_eq_sSup_conditionalMaxFidelityBlockExponentValueSet
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    (Fintype.card a : ℝ) *
        sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) =
      sSup (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) := by
  rw [sSup_conditionalMaxFidelityBlockExponentValueSet_eq_conditionalMaxEntropyExponent
    (a := a) ρ]
  exact (conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
    (a := a) ρ).symm

theorem conditionalMaxEntropyPositiveExponent_le_exponent
    [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyPositiveExponent (a := a) ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  rw [conditionalMaxEntropyPositiveExponent, conditionalMaxEntropyExponent]
  refine csSup_le (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a)) ?_
  intro x hx
  rcases hx with ⟨σ, _hpos, rfl⟩
  exact le_csSup (ρ.conditionalMaxEntropyExponentValueSet_bddAbove (a := a))
    ⟨σ, rfl⟩

theorem conditionalMaxEntropyExponent_le_positiveExponent
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyExponent (a := a) ≤
      ρ.conditionalMaxEntropyPositiveExponent (a := a) := by
  rw [conditionalMaxEntropyExponent, conditionalMaxEntropyPositiveExponent]
  have hne :
      (ρ.conditionalMaxEntropyExponentValueSet (a := a)).Nonempty := by
    rcases ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a) with
      ⟨_, σ, _hpos, rfl⟩
    exact ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) σ, σ, rfl⟩
  refine csSup_le hne ?_
  intro x hx
  rcases hx with ⟨σ, rfl⟩
  by_cases hpos : 0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ
  · exact le_csSup (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))
      ⟨σ, hpos, rfl⟩
  · have hzero : ρ.conditionalMaxEntropyExponentCandidate (a := a) σ = 0 := by
      exact le_antisymm (le_of_not_gt hpos)
        (conditionalMaxEntropyExponentCandidate_nonneg (a := a) ρ σ)
    rw [hzero]
    rcases ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a) with ⟨y, hy⟩
    rcases hy with ⟨τ, hτpos, rfl⟩
    exact le_trans (le_of_lt hτpos)
      (le_csSup (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))
        ⟨τ, hτpos, rfl⟩)

theorem conditionalMaxEntropyExponent_eq_positiveExponent
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyExponent (a := a) =
      ρ.conditionalMaxEntropyPositiveExponent (a := a) :=
  le_antisymm
    (ρ.conditionalMaxEntropyExponent_le_positiveExponent (a := a))
    (ρ.conditionalMaxEntropyPositiveExponent_le_exponent (a := a))

theorem conditionalMaxEntropyExponent_pos
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    0 < ρ.conditionalMaxEntropyExponent (a := a) := by
  rw [ρ.conditionalMaxEntropyExponent_eq_positiveExponent (a := a)]
  rcases ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a) with ⟨x, hx⟩
  rcases hx with ⟨σ, hσpos, rfl⟩
  exact lt_of_lt_of_le hσpos
    (le_csSup (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))
      ⟨σ, hσpos, rfl⟩)

theorem conditionalMaxEntropyPositiveValueSet_eq_log2_image
    (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyPositiveValueSet (a := a) =
      log2 '' ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a) := by
  ext h
  constructor
  · rintro ⟨σ, hpos, rfl⟩
    refine ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) σ, ?_, ?_⟩
    · exact ⟨σ, hpos, rfl⟩
    · exact (ρ.conditionalMaxEntropyCandidate_eq_log2_exponentCandidate σ).symm
  · rintro ⟨x, ⟨σ, hpos, rfl⟩, rfl⟩
    exact ⟨σ, hpos, ρ.conditionalMaxEntropyCandidate_eq_log2_exponentCandidate σ⟩

/-- Positive endpoint candidates are definition-level conditional max-entropy candidates.  The two
sets are in fact definitionally equal, by `conditionalMaxEntropyValueSet_eq_positiveValueSet`; this
is the inclusion form, for the steps that want a monotonicity argument. -/
theorem conditionalMaxEntropyPositiveValueSet_subset_conditionalMaxEntropyValueSet
    (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyPositiveValueSet (a := a) ⊆
      ρ.conditionalMaxEntropyValueSet (a := a) := by
  intro h hh
  rcases hh with ⟨σ, _hpos, rfl⟩
  exact ⟨σ, _hpos, rfl⟩

theorem conditionalMaxEntropyValueSet_eq_positiveValueSet
    (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyValueSet (a := a) =
      ρ.conditionalMaxEntropyPositiveValueSet (a := a) := rfl

theorem conditionalMaxEntropy_eq_positive [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropy = ρ.conditionalMaxEntropyPositive := by
  rw [conditionalMaxEntropy_eq_sSup_valueSet, conditionalMaxEntropyPositive,
    conditionalMaxEntropyValueSet_eq_positiveValueSet]

/-- The positive-endpoint conditional max-entropy is bounded by the definition-level value.  The
two candidate sets are definitionally the same, so this is really an equality; see
`conditionalMaxEntropy_eq_positive`. -/
theorem conditionalMaxEntropyPositive_le_conditionalMaxEntropy
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyPositive ≤ ρ.conditionalMaxEntropy := by
  rw [conditionalMaxEntropyPositive, conditionalMaxEntropy_eq_sSup_valueSet]
  refine csSup_le ?_ ?_
  · rw [conditionalMaxEntropyPositiveValueSet_eq_log2_image]
    exact Set.Nonempty.image _ (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty
      (a := a))
  · intro h hh
    exact le_csSup (ρ.conditionalMaxEntropyValueSet_bddAbove (a := a))
      (ρ.conditionalMaxEntropyPositiveValueSet_subset_conditionalMaxEntropyValueSet
        (a := a) hh)

theorem conditionalMaxEntropyPositive_eq_log2_positiveExponent
    (ρ : MState (a × b))
    (hne : (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty)
    (hbdd : BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) := by
  have hpos : ∀ x ∈ ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a), 0 < x := by
    intro x hx
    rcases hx with ⟨σ, hσpos, rfl⟩
    exact hσpos
  rw [conditionalMaxEntropyPositive, conditionalMaxEntropyPositiveExponent,
    conditionalMaxEntropyPositiveValueSet_eq_log2_image]
  exact log2_sSup_image_eq hne hbdd hpos

theorem conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_bddAbove
    [Nonempty a] [Nonempty b] (ρ : MState (a × b))
    (hbdd : BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) :=
  ρ.conditionalMaxEntropyPositive_eq_log2_positiveExponent
    (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a)) hbdd

theorem conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) :=
  ρ.conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_bddAbove
    (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))

theorem conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyExponent (a := a)) := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_nonempty (a := a),
    ρ.conditionalMaxEntropyExponent_eq_positiveExponent (a := a)]

/-! ## Conditional min-entropy scale -/

/-- Feasibility for the unnormalized side-operator form of conditional
min-entropy:
`ρ_AB ≤ I_A ⊗ T_B`, with `T_B ≥ 0`. -/
def ConditionalMinEntropyScaleFeasible (ρ : MState (a × b)) (T : CMatrix b) :
    Prop :=
  T.PosSemidef ∧ ρ.m ≤ (1 : CMatrix a) ⊗ₖ T

@[simp]
theorem ConditionalMinEntropyScaleFeasible_eq
    (ρ : MState (a × b)) (T : CMatrix b) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ↔
      T.PosSemidef ∧ ρ.m ≤ (1 : CMatrix a) ⊗ₖ T :=
  Iff.rfl

/-- Conditioning-register isometries transport unnormalized conditional-min
feasible side operators.  If `ρ_AB ≤ I_A ⊗ T_B`, then after applying an
isometry `V : B → B⁺` to the conditioning register, the pushed side operator
`V T_B V†` remains feasible. -/
theorem ConditionalMinEntropyScaleFeasible.apply_conditioningIsometry
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {ρ : MState (a × b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (V : ReferenceIsometry b bPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) (ρ.conditioningIsometryApply V)
      (MatrixMap.ofReferenceIsometry V T) := by
  constructor
  · exact MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V) T hT.1
  · let Φ : MatrixMap (a × b) (a × bPlus) :=
      MatrixMap.kron (CPTPOp.id (dIn := a)).map (MatrixMap.ofReferenceIsometry V)
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.IsCompletelyPositive.kron (CPTPOp.id (dIn := a)).map_cp
        (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)
    have hdiff : ((1 : CMatrix a) ⊗ₖ T - ρ.m).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      ((1 : CMatrix a) ⊗ₖ T - ρ.m) hdiff
    change (((1 : CMatrix a) ⊗ₖ
        (MatrixMap.ofReferenceIsometry V T)) -
        (ρ.conditioningIsometryApply V).m).PosSemidef
    rw [conditioningIsometryApply_matrix]
    convert hmap using 1
    simp only [Φ, map_sub]
    rw [MatrixMap.kron_map_of_kron_state]
    rw [MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight]
    simp [CPTPOp.id_map]

theorem trace_ofReferenceIsometry_apply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    (V : ReferenceIsometry b bPlus) (T : CMatrix b) :
    (MatrixMap.ofReferenceIsometry V T).trace.re = T.trace.re := by
  have h := MatrixMap.ofReferenceIsometry_isTracePreserving V T
  rw [h]

omit [DecidableEq b] in
/-- The lower-right principal block of a PSD `Sum`-indexed matrix has trace no
larger than the full matrix. -/
theorem sumBlock22_trace_re_le_of_posSemidef
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    (T : CMatrix (extra ⊕ b)) (hT : T.PosSemidef) :
    (Matrix.sumBlock22 T).trace.re ≤ T.trace.re := by
  have hsplit :
      T.trace.re =
        (Matrix.sumBlock11 T).trace.re + (Matrix.sumBlock22 T).trace.re := by
    simp [Matrix.trace, Matrix.sumBlock11, Matrix.sumBlock22,
      Fintype.sum_sum_type, Complex.add_re, add_comm]
  have h11_nonneg :
      0 ≤ (Matrix.sumBlock11 T).trace.re :=
    (Matrix.PosSemidef.trace_nonneg (Matrix.sumBlock11_posSemidef hT)).1
  linarith

/-- For the concrete right-summand embedding used by the purification transport
layer, feasible enlarged side operators compress back to feasible old side
operators by taking the lower-right principal block. -/
theorem ConditionalMinEntropyScaleFeasible.compress_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    {ρ : MState (a × b)} {TPlus : CMatrix (extra ⊕ b)}
    (hT : ConditionalMinEntropyScaleFeasible (a := a)
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) TPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ (Matrix.sumBlock22 TPlus) := by
  constructor
  · exact Matrix.sumBlock22_posSemidef hT.1
  · have hsub := hT.2.submatrix (fun x : a × b => (x.1, Sum.inr x.2))
    have heq :
        ((1 : CMatrix a) ⊗ₖ TPlus -
              (ρ.conditioningIsometryApply
                (ReferenceIsometry.sumInr extra b)).m).submatrix
            (fun x : a × b => (x.1, Sum.inr x.2))
            (fun x : a × b => (x.1, Sum.inr x.2)) =
          (1 : CMatrix a) ⊗ₖ (Matrix.sumBlock22 TPlus) - ρ.m := by
      ext x y
      simp [Matrix.sumBlock22, conditioningIsometryApply_matrix,
        ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
        ReferenceIsometry.sumInr, Matrix.mul_apply]
    change ((1 : CMatrix a) ⊗ₖ (Matrix.sumBlock22 TPlus) -
      ρ.m).PosSemidef
    rw [← heq]
    exact hsub

/-- The raw endpoint scale
`inf {Tr T_B | T_B ≥ 0, ρ_AB ≤ I_A ⊗ T_B}`. -/
def conditionalMinEntropyScale (ρ : MState (a × b)) : ℝ :=
  sInf {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScale_eq (ρ : MState (a × b)) :
    ρ.conditionalMinEntropyScale =
      sInf {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

/-- The unnormalized side-operator scale values
`Tr T_B` with `T_B ≥ 0` and `ρ_AB ≤ I_A ⊗ T_B`. -/
def conditionalMinEntropyScaleValueSet (ρ : MState (a × b)) : Set ℝ :=
  {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScaleValueSet_eq (ρ : MState (a × b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) =
      {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

/-- Dual-effect feasibility for the endpoint conditional-min SDP:
`M_AC ≥ 0` and `Tr_A M_AC ≤ I_C`. -/
def ConditionalMinEntropyDualEffectFeasible (M : CMatrix (a × b)) : Prop :=
  M.PosSemidef ∧ Matrix.traceLeft M ≤ 1

/-- The linear dual-effect value set for the endpoint conditional-min SDP:
`{Tr(ρ_AB M_AB) | M_AB ≥ 0, Tr_A M_AB ≤ I_B}`. -/
def conditionalMinEntropyDualEffectValueSet (ρ : MState (a × b)) : Set ℝ :=
  {v : ℝ | ∃ M : CMatrix (a × b),
    ConditionalMinEntropyDualEffectFeasible (a := a) M ∧
      v = ((ρ.m * M).trace).re}

/-- Reindex an `A ⊗ B` dual effect as the Choi matrix of a map `B → A`. -/
def conditionalMinEntropyDualEffectChoiMatrix (M : CMatrix (a × b)) :
    CMatrix (b × a) :=
  fun x y => M (x.2, x.1) (y.2, y.1)

/-- The matrix map `B → A` represented by a conditional-min dual effect
`M_AC`. -/
def conditionalMinEntropyDualEffectMatrixMap (M : CMatrix (a × b)) :
    MatrixMap b a :=
  MatrixMap.ofChoiMatrix (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b) M)

/-- Transpose-Choi orientation of an `A ⊗ B` dual effect as a map `B → A`.

This is the orientation that pairs directly with the repository's
`MatrixMap.choi` convention and the `AA'` maximally-entangled projector in the
endpoint link-map proof. -/
def conditionalMinEntropyDualEffectTransposeChoiMatrix (M : CMatrix (a × b)) :
    CMatrix (b × a) :=
  Matrix.transpose (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b) M)

/-- The transpose-Choi matrix map `B → A` induced by a conditional-min dual
effect. -/
def conditionalMinEntropyDualEffectTransposeMatrixMap (M : CMatrix (a × b)) :
    MatrixMap b a :=
  MatrixMap.ofChoiMatrix
    (conditionalMinEntropyDualEffectTransposeChoiMatrix (a := a) (b := b) M)

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem conditionalMinEntropyDualEffectChoiMatrix_posSemidef
    {M : CMatrix (a × b)} (hM : M.PosSemidef) :
    (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b) M).PosSemidef := by
  exact hM.submatrix (fun x : b × a => (x.2, x.1))

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem conditionalMinEntropyDualEffectTransposeChoiMatrix_posSemidef
    {M : CMatrix (a × b)} (hM : M.PosSemidef) :
    (conditionalMinEntropyDualEffectTransposeChoiMatrix (a := a) (b := b) M).PosSemidef := by
  exact (conditionalMinEntropyDualEffectChoiMatrix_posSemidef
    (a := a) (b := b) hM).transpose

/-- Positive dual effects define completely positive finite matrix maps. -/
theorem conditionalMinEntropyDualEffectMatrixMap_isCompletelyPositive
    {M : CMatrix (a × b)} (hM : M.PosSemidef) :
    MatrixMap.IsCompletelyPositive
      (conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) := by
  exact MatrixMap.ofChoiMatrix_isCompletelyPositive
    (conditionalMinEntropyDualEffectChoiMatrix_posSemidef (a := a) (b := b) hM)

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_isCompletelyPositive
    {M : CMatrix (a × b)} (hM : M.PosSemidef) :
    MatrixMap.IsCompletelyPositive
      (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) := by
  exact MatrixMap.ofChoiMatrix_isCompletelyPositive
    (conditionalMinEntropyDualEffectTransposeChoiMatrix_posSemidef
      (a := a) (b := b) hM)

theorem conditionalMinEntropyDualEffectMatrixMap_trace
    (M : CMatrix (a × b)) (X : CMatrix b) :
    ((conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) X).trace =
      (X * Matrix.transpose (Matrix.traceLeft M)).trace := by
  classical
  simp [conditionalMinEntropyDualEffectMatrixMap,
    conditionalMinEntropyDualEffectChoiMatrix, Matrix.trace, Matrix.mul_apply,
    Matrix.traceLeft]
  calc
    (∑ x : a, ∑ x_1 : b, ∑ x_2 : b, X x_1 x_2 * M (x, x_1) (x, x_2)) =
        ∑ x_1 : b, ∑ x : a, ∑ x_2 : b, X x_1 x_2 * M (x, x_1) (x, x_2) := by
      rw [Finset.sum_comm]
    _ = ∑ x_1 : b, ∑ x_2 : b, ∑ x : a, X x_1 x_2 * M (x, x_1) (x, x_2) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      rw [Finset.sum_comm]
    _ = ∑ x_1 : b, ∑ x_2 : b, X x_1 x_2 * ∑ x : a, M (x, x_1) (x, x_2) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      apply Finset.sum_congr rfl
      intro x_2 _
      rw [Finset.mul_sum]

/-- Dual-effect feasible matrices define trace-nonincreasing CP maps under the
Choi interpretation `B → A`. -/
theorem conditionalMinEntropyDualEffectMatrixMap_traceNonincreasing
    {M : CMatrix (a × b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.IsTraceNonincreasing
      (conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) := by
  intro X hX
  rw [conditionalMinEntropyDualEffectMatrixMap_trace (a := a) (b := b) M X]
  have hcomp : ((1 : CMatrix b) - Matrix.traceLeft M).PosSemidef := by
    simpa [Matrix.le_iff] using hM.2
  have hcompT :
      ((1 : CMatrix b) - Matrix.transpose (Matrix.traceLeft M)).PosSemidef := by
    simpa [Matrix.transpose_sub, Matrix.transpose_one] using hcomp.transpose
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hcompT
  have htrace :
      ((X * ((1 : CMatrix b) -
          Matrix.transpose (Matrix.traceLeft M))).trace).re =
        X.trace.re -
          ((X * Matrix.transpose (Matrix.traceLeft M)).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  rw [htrace] at hnonneg
  linarith

theorem conditionalMinEntropyDualEffectMatrixMap_traceNonincreasingCP
    {M : CMatrix (a × b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.TraceNonincreasingCP
      (conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) where
  completelyPositive :=
    conditionalMinEntropyDualEffectMatrixMap_isCompletelyPositive (a := a) (b := b) hM.1
  traceNonincreasing :=
    conditionalMinEntropyDualEffectMatrixMap_traceNonincreasing (a := a) (b := b) hM

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_trace
    (M : CMatrix (a × b)) (X : CMatrix b) :
    ((conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) X).trace =
      (X * Matrix.traceLeft M).trace := by
  classical
  simp [conditionalMinEntropyDualEffectTransposeMatrixMap,
    conditionalMinEntropyDualEffectTransposeChoiMatrix,
    conditionalMinEntropyDualEffectChoiMatrix, Matrix.trace, Matrix.mul_apply,
    Matrix.traceLeft, Matrix.transpose]
  calc
    (∑ x : a, ∑ x_1 : b, ∑ x_2 : b, X x_1 x_2 * M (x, x_2) (x, x_1)) =
        ∑ x_1 : b, ∑ x : a, ∑ x_2 : b, X x_1 x_2 * M (x, x_2) (x, x_1) := by
      rw [Finset.sum_comm]
    _ = ∑ x_1 : b, ∑ x_2 : b, ∑ x : a, X x_1 x_2 * M (x, x_2) (x, x_1) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      rw [Finset.sum_comm]
    _ = ∑ x_1 : b, ∑ x_2 : b, X x_1 x_2 * ∑ x : a, M (x, x_2) (x, x_1) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      apply Finset.sum_congr rfl
      intro x_2 _
      rw [Finset.mul_sum]

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasing
    {M : CMatrix (a × b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.IsTraceNonincreasing
      (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) := by
  intro X hX
  rw [conditionalMinEntropyDualEffectTransposeMatrixMap_trace (a := a) (b := b) M X]
  have hcomp : ((1 : CMatrix b) - Matrix.traceLeft M).PosSemidef := by
    simpa [Matrix.le_iff] using hM.2
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hcomp
  have htrace :
      ((X * ((1 : CMatrix b) - Matrix.traceLeft M)).trace).re =
        X.trace.re - ((X * Matrix.traceLeft M).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  rw [htrace] at hnonneg
  linarith

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasingCP
    {M : CMatrix (a × b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.TraceNonincreasingCP
      (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) where
  completelyPositive :=
    conditionalMinEntropyDualEffectTransposeMatrixMap_isCompletelyPositive
      (a := a) (b := b) hM.1
  traceNonincreasing :=
    conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasing
      (a := a) (b := b) hM

/-- The `AC` dual effect generated by a Kraus stack `K : C → A`.

The orientation is chosen so that
`conditionalMinEntropyDualEffectTransposeMatrixMap` has exactly the Kraus
representation `MatrixMap.ofKraus K`. -/
def conditionalMinEntropyDualEffectOfKraus
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ) : CMatrix (a × b) :=
  fun x y => ∑ l : κ, K l y.1 y.2 * star (K l x.1 x.2)

theorem conditionalMinEntropyDualEffectOfKraus_transposeMatrixMap_eq_ofKraus
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ) :
    conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b)
        (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K) =
      MatrixMap.ofKraus K := by
  apply MatrixMap.choi_inj
  rw [conditionalMinEntropyDualEffectTransposeMatrixMap, MatrixMap.choi_ofChoiMatrix,
    MatrixMap.choi_ofKraus]
  ext x y
  rcases x with ⟨z, i⟩
  rcases y with ⟨z', i'⟩
  simp [conditionalMinEntropyDualEffectTransposeChoiMatrix,
    conditionalMinEntropyDualEffectChoiMatrix,
    conditionalMinEntropyDualEffectOfKraus, Matrix.transpose, Matrix.sum_apply,
    Matrix.vecMulVec_apply]

theorem conditionalMinEntropyDualEffectOfKraus_posSemidef
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ) :
    (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K).PosSemidef := by
  have hCPK : MatrixMap.IsCompletelyPositive (MatrixMap.ofKraus K) := by
    rw [MatrixMap.isCompletelyPositive_iff_choi, MatrixMap.choi_ofKraus]
    exact Matrix.posSemidef_sum Finset.univ fun l _ =>
      Matrix.posSemidef_vecMulVec_self_star _
  have hCP :
      MatrixMap.IsCompletelyPositive
        (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b)
          (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K)) := by
    simpa [conditionalMinEntropyDualEffectOfKraus_transposeMatrixMap_eq_ofKraus
      (a := a) (b := b) K] using hCPK
  rw [MatrixMap.isCompletelyPositive_iff_choi, conditionalMinEntropyDualEffectTransposeMatrixMap,
    MatrixMap.choi_ofChoiMatrix] at hCP
  have hchoi :
      (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b)
        (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K)).PosSemidef := by
    simpa [conditionalMinEntropyDualEffectTransposeChoiMatrix] using hCP.transpose
  exact hchoi.submatrix (fun x : a × b => (x.2, x.1))

omit [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem traceLeft_conditionalMinEntropyDualEffectOfKraus
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ) :
    Matrix.traceLeft
        (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K) =
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K := by
  classical
  ext z z'
  simp [Matrix.traceLeft, conditionalMinEntropyDualEffectOfKraus,
    MatrixMap.smoothEndpointKrausStack, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, mul_comm]
  rw [Finset.sum_comm]

theorem conditionalMinEntropyDualEffectOfKraus_feasible
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ)
    (hK :
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
          MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix b)) :
    ConditionalMinEntropyDualEffectFeasible (a := a)
      (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K) := by
  constructor
  · exact conditionalMinEntropyDualEffectOfKraus_posSemidef (a := a) (b := b) K
  · rw [traceLeft_conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K]
    exact hK

theorem exists_krausStack_contraction_conditionalMinEntropyDualEffectTransposeMatrixMap
    {M : CMatrix (a × b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    ∃ K : (b × a) → Matrix a b ℂ,
      conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M =
        MatrixMap.ofKraus K ∧
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
          MatrixMap.smoothEndpointKrausStack K ≤ (1 : CMatrix b) := by
  classical
  let T : MatrixMap b a :=
    conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M
  have hCP : MatrixMap.IsCompletelyPositive T :=
    conditionalMinEntropyDualEffectTransposeMatrixMap_isCompletelyPositive
      (a := a) (b := b) hM.1
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd T hCP
  refine ⟨K, hK, ?_⟩
  have hTNI : MatrixMap.IsTraceNonincreasing (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasing
      (a := a) (b := b) hM
  exact MatrixMap.smoothEndpointKrausStack_contraction_of_traceNonincreasing K hTNI

theorem conditionalMinEntropyDualEffectValueSet_nonempty
    (ρ : MState (a × b)) :
    (ρ.conditionalMinEntropyDualEffectValueSet (a := a)).Nonempty := by
  refine ⟨0, 0, ?_, ?_⟩
  · constructor
    · exact Matrix.PosSemidef.zero
    · have hzero :
          Matrix.traceLeft (0 : CMatrix (a × b)) = 0 := by
        ext i j
        simp [Matrix.traceLeft]
      rw [Matrix.le_iff, hzero]
      simpa using (Matrix.PosSemidef.one : (1 : CMatrix b).PosSemidef)
  · simp

/-- Weak duality between the endpoint conditional-min scale side and the
dual-effect SDP side. -/
theorem conditionalMinEntropyDualEffectValue_le_scaleValue
    {ρ : MState (a × b)} {M : CMatrix (a × b)} {T : CMatrix b}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M)
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    ((ρ.m * M).trace).re ≤ T.trace.re := by
  have hdiff : ((1 : CMatrix a) ⊗ₖ T - ρ.m).PosSemidef := hT.2
  have hnonneg₁ := cMatrix_trace_mul_posSemidef_re_nonneg hdiff hM.1
  have hle₁ :
      ((ρ.m * M).trace).re ≤
        ((((1 : CMatrix a) ⊗ₖ T) * M).trace).re := by
    have htrace :
        ((((1 : CMatrix a) ⊗ₖ T - ρ.m) * M).trace).re =
          ((((1 : CMatrix a) ⊗ₖ T) * M).trace).re -
            ((ρ.m * M).trace).re := by
      simp [Matrix.sub_mul, Matrix.trace_sub]
    linarith
  have hptr_psd : (Matrix.traceLeft M).PosSemidef :=
    traceLeft_posSemidef hM.1
  have hslack : ((1 : CMatrix b) - Matrix.traceLeft M).PosSemidef := by
    simpa [Matrix.le_iff] using hM.2
  have hnonneg₂ := cMatrix_trace_mul_posSemidef_re_nonneg hT.1 hslack
  have hle₂ :
      ((T * Matrix.traceLeft M).trace).re ≤ T.trace.re := by
    have htrace :
        ((T * ((1 : CMatrix b) - Matrix.traceLeft M)).trace).re =
          T.trace.re -
            ((T * Matrix.traceLeft M).trace).re := by
      simp [Matrix.mul_sub, Matrix.trace_sub]
    linarith
  calc
    ((ρ.m * M).trace).re ≤
        ((((1 : CMatrix a) ⊗ₖ T) * M).trace).re := hle₁
    _ = ((T * Matrix.traceLeft M).trace).re :=
        congrArg Complex.re (trace_kronecker_one_mul_eq_trace_mul_traceLeft M T)
    _ ≤ T.trace.re := hle₂

theorem conditionalMinEntropyScale_eq_sInf_scaleValueSet
    (ρ : MState (a × b)) :
    ρ.conditionalMinEntropyScale =
      sInf (ρ.conditionalMinEntropyScaleValueSet (a := a)) :=
  rfl

/-- Normalize a positive semidefinite matrix with strictly positive trace into
a finite-dimensional state. -/
def ofPosSemidefTracePos (T : CMatrix b) (hT : T.PosSemidef)
    (htr : 0 < T.trace.re) : MState b := .ofMatrix
  (matrix := (((T.trace.re)⁻¹ : ℝ) : ℂ) • T)
  (pos := by
    have hscale : (0 : ℂ) ≤ (((T.trace.re)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast inv_nonneg.mpr (le_of_lt htr)
    exact Matrix.PosSemidef.smul hT hscale)
  (trace_eq_one := by
    rw [Matrix.trace_smul]
    have htrace_real : T.trace = ((T.trace.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using (Matrix.PosSemidef.trace_nonneg hT).2.symm
    rw [htrace_real]
    simp [htr.ne'])

@[simp]
theorem ofPosSemidefTracePos_matrix (T : CMatrix b) (hT : T.PosSemidef)
    (htr : 0 < T.trace.re) :
    (ofPosSemidefTracePos T hT htr).m =
      (((T.trace.re)⁻¹ : ℝ) : ℂ) • T :=
  MState.matrix_ofMatrix _ _ _

theorem smul_ofPosSemidefTracePos_matrix
    (T : CMatrix b) (hT : T.PosSemidef) (htr : 0 < T.trace.re) :
    ((T.trace.re : ℂ) • (ofPosSemidefTracePos T hT htr).m) = T := by
  simp [ofPosSemidefTracePos_matrix, smul_smul, htr.ne']

/-- A normalized conditional-min feasible pair gives an unnormalized scale
feasible side operator. -/
theorem conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : MState (a × b)} {σ : MState b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ
      ((Real.rpow 2 (-lam) : ℂ) • σ.m) := by
  constructor
  · have hscale : (0 : ℂ) ≤ ((Real.rpow 2 (-lam) : ℝ) : ℂ) := by
      exact_mod_cast (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam))
    exact Matrix.PosSemidef.smul σ.psd hscale
  · simpa [ConditionalMinEntropyFeasible, ConditionalMinEntropyScaleFeasible,
      identityTensorStateMatrix, Matrix.kronecker_smul] using h

/-- The trace of the unnormalized side operator induced by a normalized
conditional-min feasible pair is exactly `2^{-λ}`. -/
theorem trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : MState (a × b)} {σ : MState b} {lam : ℝ}
    (_h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (((Real.rpow 2 (-lam) : ℂ) • σ.m).trace).re = Real.rpow 2 (-lam) := by
  rw [Matrix.trace_smul, σ.tr']
  simp

theorem conditionalMinEntropyFeasible_uniform [Nonempty b]
    (ρ : MState (a × b)) :
    ConditionalMinEntropyFeasible (a := a) ρ (MState.uniform : MState b)
      (-log2 (Fintype.card b : ℝ)) := by
  rw [ConditionalMinEntropyFeasible]
  rw [identityTensorStateMatrix_uniform (a := a) (b := b)]
  have hrpow : Real.rpow 2 (-(-log2 (Fintype.card b : ℝ))) =
      (Fintype.card b : ℝ) := by
    simpa using (rpow_two_log2_card (b := b))
  rw [hrpow]
  have hcardC : ((Fintype.card b : ℂ) *
      (((Fintype.card b : ℝ)⁻¹ : ℝ) : ℂ)) = 1 := by
    have hcard_ne : (Fintype.card b : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    norm_num [hcard_ne]
  simpa [smul_smul, hcardC] using ρ.matrix_le_one

theorem conditionalMinEntropyScaleValueSet_nonempty [Nonempty b]
    (ρ : MState (a × b)) :
    (ρ.conditionalMinEntropyScaleValueSet (a := a)).Nonempty := by
  let σ : MState b := (MState.uniform : MState b)
  let lam : ℝ := -log2 (Fintype.card b : ℝ)
  let T : CMatrix b := (Real.rpow 2 (-lam) : ℂ) • σ.m
  have hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam :=
    ρ.conditionalMinEntropyFeasible_uniform (a := a)
  refine ⟨T.trace.re, T, ?_, rfl⟩
  exact conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible hfeas

/-- Weak-duality value-set form:
the dual-effect supremum is bounded by the min-entropy scale infimum. -/
theorem sSup_conditionalMinEntropyDualEffectValueSet_le_conditionalMinEntropyScale
    [Nonempty b] (ρ : MState (a × b)) :
    sSup (ρ.conditionalMinEntropyDualEffectValueSet (a := a)) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine csSup_le (ρ.conditionalMinEntropyDualEffectValueSet_nonempty (a := a)) ?_
  intro x hx
  rcases hx with ⟨M, hM, rfl⟩
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro y hy
  rcases hy with ⟨T, hT, rfl⟩
  exact conditionalMinEntropyDualEffectValue_le_scaleValue (a := a) hM hT

/-- A concrete scale-feasible point bounds the endpoint dual-effect value set
above.  This is the boundedness half needed for `sSup` arguments on the
dual-effect side. -/
theorem conditionalMinEntropyDualEffectValueSet_bddAbove [Nonempty b]
    (ρ : MState (a × b)) :
    BddAbove (ρ.conditionalMinEntropyDualEffectValueSet (a := a)) := by
  rcases ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨y, hy⟩
  rcases hy with ⟨T, hT, rfl⟩
  refine ⟨T.trace.re, ?_⟩
  intro x hx
  rcases hx with ⟨M, hM, rfl⟩
  exact conditionalMinEntropyDualEffectValue_le_scaleValue (a := a) hM hT

/-! ### Linear SDP surface for the endpoint min-entropy scale -/

/-- The block SDP equality map
`Z ↦ Tr_A Z₁₁ + Z₂₂`, where `Z₁₁` is the `AC` block and `Z₂₂`
is the slack block on `C`. -/
noncomputable def conditionalMinEntropyDualEffectConstraintCLM :
    CMatrix ((a × b) ⊕ b) →L[ℝ] CMatrix b :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun Z =>
        Matrix.traceLeft (Matrix.sumBlock11 Z) + Matrix.sumBlock22 Z
       map_add' := by
        intro X Y
        ext i j
        simp [Matrix.traceLeft, Matrix.sumBlock11, Matrix.sumBlock22, Finset.sum_add_distrib,
          add_assoc, add_left_comm, add_comm]
       map_smul' := by
        intro c X
        ext i j
        simp [Matrix.traceLeft, Matrix.sumBlock11, Matrix.sumBlock22, Finset.mul_sum] } :
      CMatrix ((a × b) ⊕ b) →ₗ[ℝ] CMatrix b)

/-- The block SDP objective `Z ↦ Re Tr(ρ_AC Z₁₁)`. -/
noncomputable def conditionalMinEntropyDualEffectObjectiveCLM
    (ρ : MState (a × b)) :
    CMatrix ((a × b) ⊕ b) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun Z => (ρ.m * Matrix.sumBlock11 Z).trace
         map_add' := by
          intro X Y
          have hblock :
              Matrix.sumBlock11 (X + Y) =
                Matrix.sumBlock11 X + Matrix.sumBlock11 Y := by
            ext i j
            simp [Matrix.sumBlock11]
          rw [hblock, Matrix.mul_add, Matrix.trace_add]
         map_smul' := by
          intro c X
          have hblock :
              Matrix.sumBlock11 (c • X) = c • Matrix.sumBlock11 X := by
            ext i j
            simp [Matrix.sumBlock11]
          rw [hblock]
          simp [Matrix.trace_smul, Complex.real_smul] } :
        CMatrix ((a × b) ⊕ b) →ₗ[ℝ] ℂ))

@[simp]
theorem conditionalMinEntropyDualEffectObjectiveCLM_apply
    (ρ : MState (a × b)) (Z : CMatrix ((a × b) ⊕ b)) :
    conditionalMinEntropyDualEffectObjectiveCLM (a := a) ρ Z =
      ((ρ.m * Matrix.sumBlock11 Z).trace).re :=
  rfl

/-- The finite-dimensional conic SDP whose primal is the dual-effect endpoint:
maximize `Tr(ρ_AC M)` over `M ≥ 0`, `Tr_A M ≤ I_C`, represented with a PSD
slack block. -/
noncomputable def conditionalMinEntropyDualEffectProgram
    (ρ : MState (a × b)) :
    SDP.ContinuousConeProgram (CMatrix ((a × b) ⊕ b)) (CMatrix b) where
  K := psdCone ((a × b) ⊕ b)
  A := conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b)
  b := 1
  c := conditionalMinEntropyDualEffectObjectiveCLM (a := a) ρ

/-- The conic primal value set is exactly the dual-effect endpoint value set. -/
theorem conditionalMinEntropyDualEffectProgram_primalValueSet_eq
    (ρ : MState (a × b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet =
      ρ.conditionalMinEntropyDualEffectValueSet (a := a) := by
  classical
  ext v
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    let M : CMatrix (a × b) := Matrix.sumBlock11 Z
    have hZpsd : Z.PosSemidef := by
      simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZ.1
    refine ⟨M, ?_, ?_⟩
    · constructor
      · exact Matrix.sumBlock11_posSemidef hZpsd
      · have hSpsd : (Matrix.sumBlock22 Z).PosSemidef :=
          Matrix.sumBlock22_posSemidef hZpsd
        have hconstraint :
            Matrix.traceLeft M + Matrix.sumBlock22 Z =
              (1 : CMatrix b) := by
          simpa [conditionalMinEntropyDualEffectProgram,
            conditionalMinEntropyDualEffectConstraintCLM, M] using hZ.2
        rw [Matrix.le_iff]
        have hEq :
            (1 : CMatrix b) - Matrix.traceLeft M =
              Matrix.sumBlock22 Z := by
          rw [← hconstraint]
          abel
        simpa [hEq] using hSpsd
    · exact (conditionalMinEntropyDualEffectObjectiveCLM_apply (a := a) ρ Z).symm
  · rintro ⟨M, hM, rfl⟩
    let S : CMatrix b := (1 : CMatrix b) - Matrix.traceLeft M
    let Z : CMatrix ((a × b) ⊕ b) := Matrix.fromBlocks M 0 0 S
    refine ⟨Z, ?_, ?_⟩
    · constructor
      · have hS : S.PosSemidef := by
          simpa [S, Matrix.le_iff] using hM.2
        simpa [conditionalMinEntropyDualEffectProgram, Z, psdCone_mem] using
          (cMatrix_fromBlocks_diagonal_posSemidef (a := a × b) (b := b)
            hM.1 hS)
      · have h11 : Matrix.sumBlock11 Z = M := by
          ext i j
          simp [Z, Matrix.sumBlock11]
        have h22 : Matrix.sumBlock22 Z = S := by
          ext i j
          simp [Z, S, Matrix.sumBlock22]
        change Matrix.traceLeft (Matrix.sumBlock11 Z) +
            Matrix.sumBlock22 Z = (1 : CMatrix b)
        rw [h11, h22]
        ext i j
        simp [S]
    · change (ρ.m * M).trace.re = ρ.conditionalMinEntropyDualEffectObjectiveCLM Z
      rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
      have h11 : Matrix.sumBlock11 Z = M := by
        ext i j
        simp [Z, Matrix.sumBlock11]
      rw [h11]

/-- A feasible min-entropy scale matrix induces a feasible conic dual
functional for the dual-effect SDP. -/
theorem conditionalMinEntropyDualEffectProgram_dualFeasible_of_scaleFeasible
    {ρ : MState (a × b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).IsDualFeasible
      (cMatrixTracePairingCLM T) := by
  classical
  intro Z hZ
  let M : CMatrix (a × b) := Matrix.sumBlock11 Z
  let S : CMatrix b := Matrix.sumBlock22 Z
  have hZpsd : Z.PosSemidef := by
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZ
  have hM : M.PosSemidef := Matrix.sumBlock11_posSemidef hZpsd
  have hS : S.PosSemidef := Matrix.sumBlock22_posSemidef hZpsd
  have hdiff : ((1 : CMatrix a) ⊗ₖ T - ρ.m).PosSemidef := hT.2
  have hmain_nonneg := cMatrix_trace_mul_posSemidef_re_nonneg hdiff hM
  have hmain_trace :
      ((((1 : CMatrix a) ⊗ₖ T - ρ.m) * M).trace).re =
        ((T * Matrix.traceLeft M).trace).re -
          ((ρ.m * M).trace).re := by
    calc
      ((((1 : CMatrix a) ⊗ₖ T - ρ.m) * M).trace).re =
          (((((1 : CMatrix a) ⊗ₖ T) * M -
              ρ.m * M)).trace).re := by
        simp [Matrix.sub_mul]
      _ = ((((1 : CMatrix a) ⊗ₖ T) * M).trace).re -
            ((ρ.m * M).trace).re := by
        simp [Matrix.trace_sub]
      _ = ((T * Matrix.traceLeft M).trace).re -
            ((ρ.m * M).trace).re := by
        rw [trace_kronecker_one_mul_eq_trace_mul_traceLeft]
  have hmain :
      ((ρ.m * M).trace).re ≤
        ((T * Matrix.traceLeft M).trace).re := by
    linarith
  have hslack_nonneg := cMatrix_trace_mul_posSemidef_re_nonneg hT.1 hS
  calc
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z =
        ((ρ.m * M).trace).re := by
      change ρ.conditionalMinEntropyDualEffectObjectiveCLM Z =
        ((ρ.m * M).trace).re
      rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
    _ ≤ ((T * Matrix.traceLeft M).trace).re +
          ((T * S).trace).re := by
      linarith
    _ = cMatrixTracePairingCLM T
          ((ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z) := by
      have hA :
          (ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z =
            Matrix.traceLeft M + S := by
        change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z =
          Matrix.traceLeft M + S
        rfl
      rw [hA]
      simp [Matrix.mul_add, Matrix.trace_add]

/-- Matrix-order scale values are conic dual values of the dual-effect SDP. -/
theorem conditionalMinEntropyScaleValueSet_subset_dualValueSet
    (ρ : MState (a × b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) ⊆
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).dualValueSet := by
  rintro value ⟨T, hT, rfl⟩
  refine ⟨cMatrixTracePairingCLM T,
    conditionalMinEntropyDualEffectProgram_dualFeasible_of_scaleFeasible (a := a) hT, ?_⟩
  change T.trace.re = cMatrixTracePairingCLM T (1 : CMatrix b)
  rw [cMatrixTracePairingCLM_apply]
  simp

/-- Testing a conic dual functional on a slack-only block gives positivity. -/
theorem conditionalMinEntropyDualEffectProgram_dualFeasible_slack_nonneg
    (ρ : MState (a × b)) {y : CMatrix b →L[ℝ] ℝ}
    (hy : (ρ.conditionalMinEntropyDualEffectProgram (a := a)).IsDualFeasible y)
    {A : CMatrix b} (hA : A.PosSemidef) :
    0 ≤ y A := by
  let Z : CMatrix ((a × b) ⊕ b) := Matrix.fromBlocks 0 0 0 A
  have hZpsd : Z.PosSemidef := by
    simpa [Z] using
      (cMatrix_fromBlocks_diagonal_posSemidef (a := a × b) (b := b)
        (Matrix.PosSemidef.zero : (0 : CMatrix (a × b)).PosSemidef) hA)
  have hdual := hy Z (by
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZpsd)
  have hobj :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z = 0 := by
    change ρ.conditionalMinEntropyDualEffectObjectiveCLM Z = 0
    rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
    have h11 : Matrix.sumBlock11 Z = (0 : CMatrix (a × b)) := by
      ext i j
      simp [Z, Matrix.sumBlock11]
    rw [h11]
    simp
  have hAmap :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z = A := by
    change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z = A
    ext i j
    simp [conditionalMinEntropyDualEffectConstraintCLM, Z, Matrix.sumBlock11,
      Matrix.sumBlock22, Matrix.traceLeft]
  simpa [hobj, hAmap] using hdual

/-- Testing a conic dual functional on an effect-only block gives the
pointwise domination inequality. -/
theorem conditionalMinEntropyDualEffectProgram_dualFeasible_effect_le
    (ρ : MState (a × b)) {y : CMatrix b →L[ℝ] ℝ}
    (hy : (ρ.conditionalMinEntropyDualEffectProgram (a := a)).IsDualFeasible y)
    {A : CMatrix (a × b)} (hA : A.PosSemidef) :
    ((ρ.m * A).trace).re ≤ y (Matrix.traceLeft A) := by
  let Z : CMatrix ((a × b) ⊕ b) := Matrix.fromBlocks A 0 0 0
  have hZpsd : Z.PosSemidef := by
    simpa [Z] using
      (cMatrix_fromBlocks_diagonal_posSemidef (a := a × b) (b := b)
        hA (Matrix.PosSemidef.zero : (0 : CMatrix b).PosSemidef))
  have hdual := hy Z (by
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZpsd)
  have hobj :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z =
        ((ρ.m * A).trace).re := by
    change ρ.conditionalMinEntropyDualEffectObjectiveCLM Z =
      ((ρ.m * A).trace).re
    rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
    have h11 : Matrix.sumBlock11 Z = A := by
      ext i j
      simp [Z, Matrix.sumBlock11]
    rw [h11]
  have hAmap :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z =
        Matrix.traceLeft A := by
    change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z =
      Matrix.traceLeft A
    have h11 : Matrix.sumBlock11 Z = A := by
      ext i j
      simp [Z, Matrix.sumBlock11]
    ext i j
    simp [conditionalMinEntropyDualEffectConstraintCLM, Z, h11, Matrix.sumBlock22]
  simpa [hobj, hAmap] using hdual

/-- Every conic dual value is represented by a matrix-order min-entropy scale
feasible point. -/
theorem conditionalMinEntropyDualEffectProgram_dualValueSet_subset_scaleValueSet
    (ρ : MState (a × b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).dualValueSet ⊆
      ρ.conditionalMinEntropyScaleValueSet (a := a) := by
  classical
  rintro value ⟨y, hy, rfl⟩
  let yH : HermitianDual b :=
    y.comp (hermitianInclusion : HermitianMatrix b →L[ℝ] CMatrix b)
  rcases exists_hermitian_tracePairing_representation (n := b) yH with ⟨T, hTrep⟩
  have hrep_psd (A : CMatrix b) (hA : A.PosSemidef) :
      y A = ((T.val * A).trace).re := by
    let X : HermitianMatrix b := ⟨A, hA.1⟩
    have h := hTrep X
    simpa [yH, X, tracePairing] using h
  refine ⟨T.val, ?_, ?_⟩
  · constructor
    · refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg T.isHermitian).2 ?_
      intro A hA
      have hyA := conditionalMinEntropyDualEffectProgram_dualFeasible_slack_nonneg
        (a := a) ρ hy hA
      have hrep := hrep_psd A hA
      calc
        0 ≤ y A := hyA
        _ = ((T.val * A).trace).re := hrep
    · rw [Matrix.le_iff]
      have hK : ((1 : CMatrix a) ⊗ₖ T.val).IsHermitian := by
        rw [Matrix.IsHermitian]
        calc
          ((1 : CMatrix a) ⊗ₖ T.val)ᴴ =
              ((1 : CMatrix a)ᴴ) ⊗ₖ (T.valᴴ) := by
            simpa using
              (Matrix.conjTranspose_kronecker (1 : CMatrix a) T.val)
          _ = (1 : CMatrix a) ⊗ₖ T.val := by
            rw [Matrix.conjTranspose_one, T.isHermitian.eq]
      have hHerm : ((1 : CMatrix a) ⊗ₖ T.val - ρ.m).IsHermitian :=
        hK.sub ρ.psd.1
      refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hHerm).2 ?_
      intro A hA
      have heffect := conditionalMinEntropyDualEffectProgram_dualFeasible_effect_le
        (a := a) ρ hy hA
      have hrep := hrep_psd (Matrix.traceLeft A)
        (traceLeft_posSemidef hA)
      have htrace :
          ((((1 : CMatrix a) ⊗ₖ T.val - ρ.m) * A).trace).re =
            ((T.val * Matrix.traceLeft A).trace).re -
              ((ρ.m * A).trace).re := by
        calc
          ((((1 : CMatrix a) ⊗ₖ T.val - ρ.m) * A).trace).re =
              (((((1 : CMatrix a) ⊗ₖ T.val) * A -
                  ρ.m * A)).trace).re := by
            simp [Matrix.sub_mul]
          _ = ((((1 : CMatrix a) ⊗ₖ T.val) * A).trace).re -
                ((ρ.m * A).trace).re := by
            simp [Matrix.trace_sub]
          _ = ((T.val * Matrix.traceLeft A).trace).re -
                ((ρ.m * A).trace).re := by
            rw [trace_kronecker_one_mul_eq_trace_mul_traceLeft]
      have heffect' :
          ((ρ.m * A).trace).re ≤
            ((T.val * Matrix.traceLeft A).trace).re := by
        calc
          ((ρ.m * A).trace).re ≤
              y (Matrix.traceLeft A) := heffect
          _ = ((T.val * Matrix.traceLeft A).trace).re := hrep
      linarith
  · have hrep_one : y (1 : CMatrix b) = T.val.trace.re := by
      let X : HermitianMatrix b := ⟨1, Matrix.PosSemidef.one.1⟩
      have h := hTrep X
      simpa [yH, X, tracePairing] using h
    change y (1 : CMatrix b) = T.val.trace.re
    exact hrep_one

/-- The conic and matrix-order dual value sets coincide. -/
theorem conditionalMinEntropyDualEffectProgram_dualValueSet_eq_scaleValueSet
    (ρ : MState (a × b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).dualValueSet =
      ρ.conditionalMinEntropyScaleValueSet (a := a) :=
  Set.Subset.antisymm
    (conditionalMinEntropyDualEffectProgram_dualValueSet_subset_scaleValueSet (a := a) ρ)
    (conditionalMinEntropyScaleValueSet_subset_dualValueSet (a := a) ρ)

/-- The endpoint dual-effect conic primal is feasible. -/
theorem conditionalMinEntropyDualEffectProgram_primalValueSet_nonempty
    (ρ : MState (a × b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet.Nonempty := by
  classical
  let Z : CMatrix ((a × b) ⊕ b) :=
    Matrix.fromBlocks 0 0 0 (1 : CMatrix b)
  refine ⟨(ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z, Z, ?_, rfl⟩
  constructor
  · have hZpsd : Z.PosSemidef := by
      simpa [Z] using
        (cMatrix_fromBlocks_diagonal_posSemidef (a := a × b) (b := b)
          (Matrix.PosSemidef.zero : (0 : CMatrix (a × b)).PosSemidef)
          (Matrix.PosSemidef.one : (1 : CMatrix b).PosSemidef))
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZpsd
  · change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z =
      (1 : CMatrix b)
    ext i j
    simp [conditionalMinEntropyDualEffectConstraintCLM, Z, Matrix.sumBlock11,
      Matrix.sumBlock22, Matrix.traceLeft]

/-- A concrete scale-feasible point bounds the dual-effect primal value set
above. -/
theorem conditionalMinEntropyDualEffectProgram_primalValueSet_bddAbove
    [Nonempty b] (ρ : MState (a × b)) :
    BddAbove (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet := by
  rcases ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨v, hv⟩
  rcases hv with ⟨T, hT, rfl⟩
  exact (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet_bddAbove_of_dualFeasible
    (conditionalMinEntropyDualEffectProgram_dualFeasible_of_scaleFeasible (a := a) hT)

/-- The block SDP constraint preserves trace: `Tr(Tr_A Z₁₁ + Z₂₂) = Tr Z`. -/
theorem conditionalMinEntropyDualEffectConstraint_trace_re
    (Z : CMatrix ((a × b) ⊕ b)) :
    ((conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z).trace).re =
      Z.trace.re := by
  have hptr :
      (Matrix.traceLeft (Matrix.sumBlock11 Z)).trace =
        (Matrix.sumBlock11 Z).trace :=
    Matrix.traceLeft_trace (Matrix.sumBlock11 Z)
  have hsplit :
      Z.trace = (Matrix.sumBlock11 Z).trace + (Matrix.sumBlock22 Z).trace := by
    simp [Matrix.trace, Matrix.sumBlock11, Matrix.sumBlock22,
      Fintype.sum_sum_type, add_comm]
  calc
    ((conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z).trace).re =
        ((Matrix.traceLeft (Matrix.sumBlock11 Z) +
            Matrix.sumBlock22 Z).trace).re := rfl
    _ = ((Matrix.traceLeft (Matrix.sumBlock11 Z)).trace +
          (Matrix.sumBlock22 Z).trace).re := by
      rw [Matrix.trace_add]
    _ = ((Matrix.sumBlock11 Z).trace + (Matrix.sumBlock22 Z).trace).re := by
      rw [hptr]
    _ = Z.trace.re := by rw [hsplit]

/-- The dual-effect primal hypograph is closed.  The key finite-dimensional
estimate is that PSD block variables are norm-bounded by the trace of their
constraint value. -/
theorem conditionalMinEntropyDualEffectProgram_hasClosedPrimalHypograph
    (ρ : MState (a × b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).HasClosedPrimalHypograph := by
  classical
  let P := ρ.conditionalMinEntropyDualEffectProgram (a := a)
  refine IsSeqClosed.isClosed ?_
  intro ztSeq zt hztSeq hztLim
  choose Z hZK hA ht using hztSeq
  have hYLim : Tendsto (fun n => (ztSeq n).1) atTop (𝓝 zt.1) :=
    continuous_fst.tendsto zt |>.comp hztLim
  have hYBounded : Bornology.IsBounded (Set.range fun n => (ztSeq n).1) :=
    Metric.isBounded_range_of_tendsto _ hYLim
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le hYBounded
  have hC_nonneg : 0 ≤ C := by
    exact (norm_nonneg ((ztSeq 0).1)).trans (hC ((ztSeq 0).1) (Set.mem_range_self 0))
  let trCLM : CMatrix b →L[ℝ] ℝ :=
    cMatrixTracePairingCLM (1 : CMatrix b)
  let oneZ : CMatrix ((a × b) ⊕ b) := 1
  have hZ_norm_le (n : ℕ) :
      ‖Z n‖ ≤ ((‖trCLM‖ * C) * ‖oneZ‖) := by
    have hZpsd : (Z n).PosSemidef := by
      simpa [P, conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZK n
    have hnormZ :=
      norm_le_trace_re_mul_norm_one_of_posSemidef (a := (a × b) ⊕ b) hZpsd
    have htrace_eq :
        (Z n).trace.re = ((ztSeq n).1).trace.re := by
      have hconstraint :
          (ztSeq n).1 = conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) (Z n) := by
        simpa [P, conditionalMinEntropyDualEffectProgram] using hA n
      rw [hconstraint]
      exact (conditionalMinEntropyDualEffectConstraint_trace_re (a := a) (b := b) (Z n)).symm
    have htrace_abs :
        ((ztSeq n).1).trace.re ≤ ‖trCLM ((ztSeq n).1)‖ := by
      change ((ztSeq n).1).trace.re ≤ ‖cMatrixTracePairingCLM
        (1 : CMatrix b) ((ztSeq n).1)‖
      rw [cMatrixTracePairingCLM_apply]
      simp
      exact le_abs_self _
    have hop :
        ‖trCLM ((ztSeq n).1)‖ ≤ ‖trCLM‖ * ‖(ztSeq n).1‖ :=
      trCLM.le_opNorm ((ztSeq n).1)
    have hYnorm : ‖(ztSeq n).1‖ ≤ C :=
      hC ((ztSeq n).1) (Set.mem_range_self n)
    have htrace_le :
        ((ztSeq n).1).trace.re ≤ ‖trCLM‖ * C := by
      calc
        ((ztSeq n).1).trace.re ≤ ‖trCLM ((ztSeq n).1)‖ := htrace_abs
        _ ≤ ‖trCLM‖ * ‖(ztSeq n).1‖ := hop
        _ ≤ ‖trCLM‖ * C := by
          exact mul_le_mul_of_nonneg_left hYnorm (norm_nonneg trCLM)
    calc
      ‖Z n‖ ≤ (Z n).trace.re * ‖(1 : CMatrix ((a × b) ⊕ b))‖ := hnormZ
      _ = ((ztSeq n).1).trace.re * ‖oneZ‖ := by
        rw [htrace_eq]
      _ ≤ (‖trCLM‖ * C) * ‖oneZ‖ := by
        exact mul_le_mul_of_nonneg_right htrace_le (norm_nonneg oneZ)
  have hZ_bounded : Bornology.IsBounded (Set.range Z) :=
    (isBounded_iff_forall_norm_le).2
      ⟨((‖trCLM‖ * C) * ‖oneZ‖), by
        rintro _ ⟨n, rfl⟩
        exact hZ_norm_le n⟩
  obtain ⟨Zlim, -, φ, hφ, hZtend⟩ :=
    tendsto_subseq_of_bounded hZ_bounded (x := Z) (fun n => Set.mem_range_self n)
  have hZlimK : Zlim ∈ P.K :=
    P.K.isClosed.mem_of_tendsto hZtend
      (Eventually.of_forall fun n => hZK (φ n))
  have hYLimSub : Tendsto (fun n => (ztSeq (φ n)).1) atTop (𝓝 zt.1) :=
    hYLim.comp hφ.tendsto_atTop
  have hAZlim :
      Tendsto (fun n => (ztSeq (φ n)).1) atTop (𝓝 (P.A Zlim)) := by
    have hcont :
        Tendsto (fun n => P.A (Z (φ n))) atTop (𝓝 (P.A Zlim)) :=
      P.A.continuous.continuousAt.tendsto.comp hZtend
    have hfun :
        (fun n => (ztSeq (φ n)).1) = fun n => P.A (Z (φ n)) := by
      funext n
      exact hA (φ n)
    simpa [hfun] using hcont
  have hAeq : zt.1 = P.A Zlim :=
    tendsto_nhds_unique hYLimSub hAZlim
  have htLimSub : Tendsto (fun n => (ztSeq (φ n)).2) atTop (𝓝 zt.2) :=
    (continuous_snd.tendsto zt |>.comp hztLim).comp hφ.tendsto_atTop
  have hValueLim :
      Tendsto (fun n => P.primalValue (Z (φ n))) atTop
        (𝓝 (P.primalValue Zlim)) :=
    P.c.continuous.continuousAt.tendsto.comp hZtend
  have htle : zt.2 ≤ P.primalValue Zlim :=
    le_of_tendsto_of_tendsto' htLimSub hValueLim fun n => ht (φ n)
  exact ⟨Zlim, hZlimK, hAeq, htle⟩

/-- Endpoint min-entropy scale strong duality in value-set form.

The unnormalized side-operator infimum equals the supremum over dual effects
`M ≥ 0` satisfying `Tr_A M ≤ I`. -/
theorem conditionalMinEntropyScale_eq_sSup_dualEffectValueSet [Nonempty b]
    (ρ : MState (a × b)) :
    ρ.conditionalMinEntropyScale (a := a) =
      sSup (ρ.conditionalMinEntropyDualEffectValueSet (a := a)) := by
  classical
  let P := ρ.conditionalMinEntropyDualEffectProgram (a := a)
  have hsd :
      sSup P.primalValueSet = sInf P.dualValueSet :=
    P.sSup_primalValueSet_eq_sInf_dualValueSet_of_hasClosedPrimalHypograph
      (conditionalMinEntropyDualEffectProgram_hasClosedPrimalHypograph (a := a) ρ)
      (conditionalMinEntropyDualEffectProgram_primalValueSet_nonempty (a := a) ρ)
      (conditionalMinEntropyDualEffectProgram_primalValueSet_bddAbove (a := a) ρ)
  have hpr :
      P.primalValueSet = ρ.conditionalMinEntropyDualEffectValueSet (a := a) :=
    conditionalMinEntropyDualEffectProgram_primalValueSet_eq (a := a) ρ
  have hdu :
      P.dualValueSet = ρ.conditionalMinEntropyScaleValueSet (a := a) :=
    conditionalMinEntropyDualEffectProgram_dualValueSet_eq_scaleValueSet (a := a) ρ
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  rw [← hdu, ← hsd, hpr]

theorem conditionalMinEntropyFeasible_scale_lower_bound [Nonempty a]
    {ρ : MState (a × b)} {σ : MState b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (Fintype.card a : ℝ)⁻¹ ≤ Real.rpow 2 (-lam) := by
  have htrace := cMatrix_trace_re_le_of_le h
  have hleft : ρ.m.trace.re = 1 := by
    rw [ρ.tr']
    norm_num
  have hright :
      (((Real.rpow 2 (-lam) : ℂ) • identityTensorStateMatrix (a := a) σ).trace).re =
        Real.rpow 2 (-lam) * (Fintype.card a : ℝ) := by
    rw [Matrix.trace_smul]
    simp [identityTensorStateMatrix_trace_re (a := a) σ]
  rw [hleft, hright] at htrace
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  rw [inv_le_iff_one_le_mul₀ hcard_pos]
  simpa [mul_comm] using htrace

/-- Any feasible normalized conditional-min exponent is bounded by the
classical-register dimension. -/
theorem conditionalMinEntropyFeasible_le_log2_card_left
    {ρ : MState (a × b)} {σ : MState b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ log2 (Fintype.card a : ℝ) := by
  classical
  have : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
  have hscale := conditionalMinEntropyFeasible_scale_lower_bound (a := a) h
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hlog := Real.log_le_log (inv_pos.mpr hcard_pos) hscale
  have hlog2_nonneg : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos one_lt_two)
  have hdiv := div_le_div_of_nonneg_right hlog hlog2_nonneg
  change log2 ((Fintype.card a : ℝ)⁻¹) ≤
    log2 (Real.rpow 2 (-lam)) at hdiv
  have hneg := neg_le_neg hdiv
  have hcard :
      -log2 ((Fintype.card a : ℝ)⁻¹) = log2 (Fintype.card a : ℝ) := by
    unfold log2
    rw [Real.log_inv]
    ring
  rw [neg_log2_rpow_two_neg lam, hcard] at hneg
  exact hneg

/-- A conditional-min-entropy feasible bound controls every diagonal classical
block. -/
theorem block_le_of_conditionalMinEntropyFeasible
    (ρ : MState (a × b)) (σ : MState b) (x : a) {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    Classical.block ρ.m x x ≤ (Real.rpow 2 (-lam) : ℂ) • σ.m := by
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  rw [Matrix.le_iff]
  have hdiff :
      (c • MState.identityTensorStateMatrix (a := a) σ - ρ.m).PosSemidef := by
    simpa [c, ConditionalMinEntropyFeasible, Matrix.le_iff] using h
  have hblock := hdiff.submatrix (fun i : b => (x, i))
  have hblock_eq :
      Matrix.submatrix
          (c • MState.identityTensorStateMatrix (a := a) σ - ρ.m)
          (fun i : b => (x, i)) (fun i : b => (x, i)) =
        c • σ.m - Classical.block ρ.m x x := by
    ext i j
    simp [Classical.block, MState.identityTensorStateMatrix, Matrix.kroneckerMap_apply, c]
  rwa [hblock_eq] at hblock

theorem conditionalMinEntropyScaleFeasible_trace_lower_bound [Nonempty a]
    {ρ : MState (a × b)} {T : CMatrix b}
    (h : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    (Fintype.card a : ℝ)⁻¹ ≤ T.trace.re := by
  have htrace := cMatrix_trace_re_le_of_le h.2
  have hleft : ρ.m.trace.re = 1 := by
    rw [ρ.tr']
    norm_num
  have hright :
      ((1 : CMatrix a) ⊗ₖ T).trace.re =
        (Fintype.card a : ℝ) * T.trace.re := by
    rw [show (1 : CMatrix a) ⊗ₖ T =
        (1 : CMatrix a) ⊗ₖ T by rfl]
    rw [Matrix.trace_kronecker, Matrix.trace_one]
    simp [Complex.mul_re]
  rw [hleft, hright] at htrace
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  rw [inv_le_iff_one_le_mul₀ hcard_pos]
  simpa [mul_comm] using htrace

/-- Feasible conditional-min exponents. -/
def conditionalMinEntropyFeasibleExponentValueSet (ρ : MState (a × b)) : Set ℝ :=
  {lam : ℝ | ∃ σ : MState b, ConditionalMinEntropyFeasible (a := a) ρ σ lam}

/-- The normalized conditional-min feasible exponent set is bounded above. -/
theorem conditionalMinEntropyFeasibleExponentValueSet_bddAbove
    (ρ : MState (a × b)) :
    BddAbove (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)) := by
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro lam hlam
  rcases hlam with ⟨σ, hσ⟩
  exact conditionalMinEntropyFeasible_le_log2_card_left (a := a) hσ

/-- A uniform classical register independent of the side information has
conditional min-entropy at least the logarithm of its alphabet size. -/
theorem conditionalMinEntropyFeasible_uniform_prod
    [Nonempty a] (σ : MState b) :
    ConditionalMinEntropyFeasible (a := a)
      ((MState.uniform : MState a).prod σ) σ (log2 (Fintype.card a : ℝ)) := by
  rw [ConditionalMinEntropyFeasible]
  rw [MState.identityTensorStateMatrix_eq_card_smul_uniform_prod (a := a) σ]
  have hrpow :
      Real.rpow 2 (-(log2 (Fintype.card a : ℝ))) =
        (Fintype.card a : ℝ)⁻¹ := by
    calc
      Real.rpow 2 (-(log2 (Fintype.card a : ℝ))) =
          (Real.rpow 2 (log2 (Fintype.card a : ℝ)))⁻¹ := by
            exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _
      _ = (Fintype.card a : ℝ)⁻¹ := by
            rw [MState.rpow_two_log2_card (b := a)]
  have hcard_ne : (Fintype.card a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [hrpow]
  simp [smul_smul, hcard_ne]

/-- The normalized scale values `2^{-λ}` coming from normalized
conditional-min feasible pairs. -/
def conditionalMinEntropyNormalizedScaleValueSet (ρ : MState (a × b)) : Set ℝ :=
  {t : ℝ | ∃ σ : MState b, ∃ lam : ℝ,
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ∧ t = Real.rpow 2 (-lam)}

/-- The infimum of normalized conditional-min scale values. -/
def conditionalMinEntropyNormalizedScale (ρ : MState (a × b)) : ℝ :=
  sInf (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a))

theorem conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet
    [Nonempty a] (ρ : MState (a × b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) =
      ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a) := by
  ext t
  constructor
  · rintro ⟨T, hTfeas, rfl⟩
    have htr_lower :
        (Fintype.card a : ℝ)⁻¹ ≤ T.trace.re :=
      conditionalMinEntropyScaleFeasible_trace_lower_bound (a := a) hTfeas
    have hcard_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have htr_pos : 0 < T.trace.re := lt_of_lt_of_le (inv_pos.mpr hcard_pos) htr_lower
    let σ : MState b := ofPosSemidefTracePos T hTfeas.1 htr_pos
    let lam : ℝ := -log2 T.trace.re
    refine ⟨σ, lam, ?_, ?_⟩
    · rw [ConditionalMinEntropyFeasible]
      have hrpow : Real.rpow 2 (-lam) = T.trace.re := by
        dsimp [lam]
        rw [neg_neg]
        change Real.rpow 2 (log2 T.trace.re) = T.trace.re
        exact rpow_two_log2_pos htr_pos
      have hside :
          ((T.trace.re : ℂ) • identityTensorStateMatrix (a := a) σ) =
            (1 : CMatrix a) ⊗ₖ T := by
        rw [identityTensorStateMatrix]
        rw [show (1 : CMatrix a) ⊗ₖ T =
            (1 : CMatrix a) ⊗ₖ T by rfl]
        change ((T.trace.re : ℂ) •
            ((1 : CMatrix a) ⊗ₖ σ.m)) =
          (1 : CMatrix a) ⊗ₖ T
        rw [← Matrix.kronecker_smul]
        rw [show ((T.trace.re : ℂ) • σ.m) = T by
          exact smul_ofPosSemidefTracePos_matrix T hTfeas.1 htr_pos]
      rw [hrpow, hside]
      exact hTfeas.2
    · dsimp [lam]
      rw [neg_neg]
      change T.trace.re = Real.rpow 2 (log2 T.trace.re)
      exact (rpow_two_log2_pos htr_pos).symm
  · rintro ⟨σ, lam, hfeas, rfl⟩
    refine ⟨((Real.rpow 2 (-lam) : ℂ) • σ.m), ?_, ?_⟩
    · exact conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible hfeas
    · exact (trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible hfeas).symm

theorem conditionalMinEntropyScale_eq_normalizedScale
    [Nonempty a] (ρ : MState (a × b)) :
    ρ.conditionalMinEntropyScale (a := a) =
      ρ.conditionalMinEntropyNormalizedScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet, conditionalMinEntropyNormalizedScale,
    conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]

theorem conditionalMinEntropyFeasibleExponentValueSet_nonempty [Nonempty b]
    (ρ : MState (a × b)) :
    (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)).Nonempty := by
  exact ⟨-log2 (Fintype.card b : ℝ), (MState.uniform : MState b),
    ρ.conditionalMinEntropyFeasible_uniform (a := a)⟩

theorem conditionalMinEntropyNormalizedScaleValueSet_nonempty [Nonempty b]
    (ρ : MState (a × b)) :
    (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)).Nonempty := by
  refine ⟨Real.rpow 2 (-(-log2 (Fintype.card b : ℝ))), (MState.uniform : MState b),
    -log2 (Fintype.card b : ℝ), ?_, rfl⟩
  exact ρ.conditionalMinEntropyFeasible_uniform (a := a)

theorem conditionalMinEntropyNormalizedScaleValueSet_pos
    {ρ : MState (a × b)} {t : ℝ}
    (ht : t ∈ ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)) :
    0 < t := by
  rcases ht with ⟨σ, lam, hfeas, rfl⟩
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lam)

theorem conditionalMinEntropyNormalizedScaleValueSet_bddBelow
    (ρ : MState (a × b)) :
    BddBelow (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)) := by
  refine ⟨0, ?_⟩
  intro t ht
  exact le_of_lt (conditionalMinEntropyNormalizedScaleValueSet_pos (a := a) ht)

/-- Enlarging the conditioning register by an isometry cannot increase the
unnormalized conditional-min endpoint scale.  This is the easy direction of
isometric invariance: every old side operator `T_B` pushes forward to a feasible
side operator `V T_B V†` with the same trace. -/
theorem conditionalMinEntropyScale_conditioningIsometryApply_le
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : MState (a × b)) (V : ReferenceIsometry b bPlus) :
    (ρ.conditioningIsometryApply V).conditionalMinEntropyScale (a := a) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro t ht
  rcases ht with ⟨T, hT, rfl⟩
  have hbddNew :
      BddBelow ((ρ.conditioningIsometryApply V).conditionalMinEntropyScaleValueSet
        (a := a)) := by
    rw [conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
    exact (ρ.conditioningIsometryApply V).conditionalMinEntropyNormalizedScaleValueSet_bddBelow
      (a := a)
  exact csInf_le hbddNew
    ⟨MatrixMap.ofReferenceIsometry V T,
      hT.apply_conditioningIsometry V,
      (trace_ofReferenceIsometry_apply V T).symm⟩

/-- For the concrete `B ↪ extra ⊕ B` padding used by embedded purification
transport, the conditional-min endpoint scale also cannot increase when
compressing back to the original summand. -/
theorem conditionalMinEntropyScale_le_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    ρ.conditionalMinEntropyScale (a := a) ≤
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScale
        (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet,
    conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine le_csInf
    ((ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScaleValueSet_nonempty
      (a := a)) ?_
  intro t ht
  rcases ht with ⟨TPlus, hTPlus, rfl⟩
  have hbddOld : BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) := by
    rw [conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)
  exact le_trans
    (csInf_le hbddOld
      ⟨Matrix.sumBlock22 TPlus, hTPlus.compress_sumInr, rfl⟩)
    (sumBlock22_trace_re_le_of_posSemidef TPlus hTPlus.1)

theorem conditionalMinEntropyNormalizedScaleValueSet_lower_bound [Nonempty a]
    {ρ : MState (a × b)} {t : ℝ}
    (ht : t ∈ ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)) :
    (Fintype.card a : ℝ)⁻¹ ≤ t := by
  rcases ht with ⟨σ, lam, hfeas, rfl⟩
  exact conditionalMinEntropyFeasible_scale_lower_bound (a := a) hfeas

theorem conditionalMinEntropyNormalizedScale_inf_pos [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    0 < ρ.conditionalMinEntropyNormalizedScale (a := a) := by
  have hne := ρ.conditionalMinEntropyNormalizedScaleValueSet_nonempty (a := a)
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hbound :
      ∀ t ∈ ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a),
        (Fintype.card a : ℝ)⁻¹ ≤ t := by
    intro t ht
    exact conditionalMinEntropyNormalizedScaleValueSet_lower_bound (a := a) ht
  exact lt_of_lt_of_le (inv_pos.mpr hcard_pos) (le_csInf hne hbound)

theorem negLog2_image_conditionalMinEntropyNormalizedScaleValueSet_eq
    (ρ : MState (a × b)) :
    (fun t : ℝ => -log2 t) ''
        ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a) =
      ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a) := by
  ext lam
  constructor
  · rintro ⟨t, ⟨σ, mu, hfeas, rfl⟩, rfl⟩
    refine ⟨σ, ?_⟩
    convert hfeas using 1
    exact neg_log2_rpow_two_neg mu
  · rintro ⟨σ, hfeas⟩
    refine ⟨Real.rpow 2 (-lam), ?_, ?_⟩
    · exact ⟨σ, lam, hfeas, rfl⟩
    · exact neg_log2_rpow_two_neg lam

theorem conditionalMinEntropy_eq_neg_log2_normalizedScale
    (ρ : MState (a × b))
    (hne : (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)).Nonempty)
    (hbdd : BddBelow (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)))
    (hinf_pos : 0 < ρ.conditionalMinEntropyNormalizedScale (a := a)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyNormalizedScale (a := a)) := by
  rw [conditionalMinEntropy, conditionalMinEntropyNormalizedScale]
  change sSup (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)) =
    -log2 (sInf (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)))
  rw [← negLog2_image_conditionalMinEntropyNormalizedScaleValueSet_eq]
  exact neg_log2_sInf_image_eq hne hbdd hinf_pos

theorem conditionalMinEntropy_eq_neg_log2_normalizedScale_of_inf_pos
    (ρ : MState (a × b))
    (hne : (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)).Nonempty)
    (hinf_pos : 0 < ρ.conditionalMinEntropyNormalizedScale (a := a)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyNormalizedScale (a := a)) :=
  ρ.conditionalMinEntropy_eq_neg_log2_normalizedScale hne
    (ρ.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)) hinf_pos

theorem conditionalMinEntropy_eq_neg_log2_normalizedScale_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyNormalizedScale (a := a)) :=
  ρ.conditionalMinEntropy_eq_neg_log2_normalizedScale_of_inf_pos
    (ρ.conditionalMinEntropyNormalizedScaleValueSet_nonempty (a := a))
    (ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a))

theorem conditionalMinEntropy_eq_neg_log2_scale_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyScale (a := a)) := by
  rw [ρ.conditionalMinEntropy_eq_neg_log2_normalizedScale_of_nonempty (a := a),
    ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]

/-- A normalized finite-dimensional conditional min-entropy is bounded above by
the logarithm of the conditioned register dimension. -/
theorem conditionalMinEntropy_le_log2_card_left
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMinEntropy ≤ log2 (Fintype.card a : ℝ) := by
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hscale_lb :
      (Fintype.card a : ℝ)⁻¹ ≤ ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a),
      conditionalMinEntropyNormalizedScale]
    exact le_csInf
      (ρ.conditionalMinEntropyNormalizedScaleValueSet_nonempty (a := a))
      (fun t ht => conditionalMinEntropyNormalizedScaleValueSet_lower_bound (a := a) ht)
  rw [ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  unfold log2
  have hlog := Real.log_le_log (inv_pos.mpr hcard_pos) hscale_lb
  have hlog_inv :
      Real.log ((Fintype.card a : ℝ)⁻¹) = -Real.log (Fintype.card a : ℝ) := by
    rw [Real.log_inv]
  rw [hlog_inv] at hlog
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hdiv :=
    div_le_div_of_nonneg_right hlog (le_of_lt hlog2_pos)
  simpa [neg_div] using neg_le_neg hdiv

/-- The conditional min-entropy of an ideal uniform classical register
independent of side information is exactly `log₂ |a|`. -/
theorem conditionalMinEntropy_uniform_prod
    [Nonempty a] (σ : MState b) :
    (MState.prod (MState.uniform : MState a) σ).conditionalMinEntropy =
      log2 (Fintype.card a : ℝ) := by
  classical
  let : Nonempty b := σ.nonempty
  have hle :
      (MState.prod (MState.uniform : MState a) σ).conditionalMinEntropy ≤
        log2 (Fintype.card a : ℝ) :=
    (MState.prod (MState.uniform : MState a) σ).conditionalMinEntropy_le_log2_card_left
      (a := a) (b := b)
  have hbdd :
      BddAbove
        ((MState.prod (MState.uniform : MState a) σ).conditionalMinEntropyFeasibleExponentValueSet
          (a := a)) := by
    exact conditionalMinEntropyFeasibleExponentValueSet_bddAbove
      (a := a) (MState.prod (MState.uniform : MState a) σ)
  have hmem :
      log2 (Fintype.card a : ℝ) ∈
        (MState.prod (MState.uniform : MState a) σ).conditionalMinEntropyFeasibleExponentValueSet
          (a := a) := by
    exact ⟨σ, conditionalMinEntropyFeasible_uniform_prod (a := a) σ⟩
  have hge :
      log2 (Fintype.card a : ℝ) ≤
        (MState.prod (MState.uniform : MState a) σ).conditionalMinEntropy := by
    rw [MState.conditionalMinEntropy_eq]
    exact le_csSup hbdd hmem
  exact le_antisymm hle hge

/-- One entropy-level consequence of the scale pushforward: applying an
isometry to the conditioning register cannot decrease the conditional
min-entropy. -/
theorem conditionalMinEntropy_le_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : MState (a × b)) (V : ReferenceIsometry b bPlus) :
    ρ.conditionalMinEntropy ≤
      (ρ.conditioningIsometryApply V).conditionalMinEntropy := by
  rw [ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
    (ρ.conditioningIsometryApply V).conditionalMinEntropy_eq_neg_log2_scale_of_nonempty
      (a := a)]
  have hle := ρ.conditionalMinEntropyScale_conditioningIsometryApply_le (a := a) V
  have hnew_pos : 0 < (ρ.conditioningIsometryApply V).conditionalMinEntropyScale
      (a := a) := by
    rw [(ρ.conditioningIsometryApply V).conditionalMinEntropyScale_eq_normalizedScale
      (a := a)]
    exact (ρ.conditioningIsometryApply V).conditionalMinEntropyNormalizedScale_inf_pos
      (a := a)
  unfold log2
  have hlog :
      Real.log ((ρ.conditioningIsometryApply V).conditionalMinEntropyScale (a := a)) /
          Real.log 2 ≤
        Real.log (ρ.conditionalMinEntropyScale (a := a)) / Real.log 2 := by
    exact div_le_div_of_nonneg_right (Real.log_le_log hnew_pos hle)
      (le_of_lt (Real.log_pos one_lt_two))
  simpa using (neg_le_neg hlog)

/-- For the concrete right-summand padding `B ↪ extra ⊕ B`, conditional
min-entropy also cannot increase. -/
theorem conditionalMinEntropy_conditioningIsometryApply_sumInr_le
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy ≤
      ρ.conditionalMinEntropy := by
  rw [(ρ.conditioningIsometryApply
        (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy_eq_neg_log2_scale_of_nonempty
      (a := a),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hle := ρ.conditionalMinEntropyScale_le_conditioningIsometryApply_sumInr
    (a := a) (extra := extra)
  have hold_pos : 0 < ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  have hlog :
      Real.log (ρ.conditionalMinEntropyScale (a := a)) / Real.log 2 ≤
        Real.log
          ((ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropyScale
            (a := a)) / Real.log 2 := by
    exact div_le_div_of_nonneg_right (Real.log_le_log hold_pos hle)
      (le_of_lt (Real.log_pos one_lt_two))
  simpa using (neg_le_neg hlog)

/-- Conditional min-entropy is invariant under the concrete right-summand
reference padding used by embedded purification-ball transport. -/
theorem conditionalMinEntropy_conditioningIsometryApply_sumInr
    {extra : Type*} [Fintype extra] [DecidableEq extra]
    [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy =
      ρ.conditionalMinEntropy := by
  exact le_antisymm
    (ρ.conditionalMinEntropy_conditioningIsometryApply_sumInr_le (a := a) (extra := extra))
    (ρ.conditionalMinEntropy_le_conditioningIsometryApply (a := a)
      (ReferenceIsometry.sumInr extra b))

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_exponent_eq_scale
    [Nonempty a] [Nonempty b] (ρ : MState (a × b))
    (hscale :
      ρ.conditionalMaxEntropyExponent (a := a) =
        ρ.conditionalMinEntropyScale (a := a)) :
    ρ.conditionalMaxEntropyPositive = -ρ.conditionalMinEntropy := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
    hscale]
  simp

/-- Order-theoretic endpoint weak-duality bridge.

It remains to prove the source-shaped pointwise matrix inequality. Once every
max-entropy exponent candidate is bounded by every feasible min-entropy side
operator trace, this theorem packages the `sSup ≤ sInf` step. -/
theorem conditionalMaxEntropyExponent_le_minEntropyScale_of_pointwise_le
    [Nonempty b] (ρ : MState (a × b))
    (hpoint : ∀ σ : MState b, ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ≤ T.trace.re) :
    ρ.conditionalMaxEntropyExponent (a := a) ≤
      ρ.conditionalMinEntropyScale (a := a) := by
  rw [conditionalMaxEntropyExponent, conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  refine csSup_le (ρ.conditionalMaxEntropyExponentValueSet_nonempty (a := a)) ?_
  intro x hx
  rcases hx with ⟨σ, rfl⟩
  refine le_csInf (ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
  intro y hy
  rcases hy with ⟨T, hTfeas, rfl⟩
  exact hpoint σ T hTfeas

theorem conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_pointwise_le
    [Nonempty a] [Nonempty b] (ρ : MState (a × b))
    (hpoint : ∀ σ : MState b, ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ≤ T.trace.re) :
    ρ.conditionalMaxEntropyPositive ≤ -ρ.conditionalMinEntropy := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hpos := ρ.conditionalMaxEntropyExponent_pos (a := a)
  have hle := ρ.conditionalMaxEntropyExponent_le_minEntropyScale_of_pointwise_le
    (a := a) hpoint
  have hscale_pos : 0 < ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hpos hle)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Reverse endpoint order bridge: if every feasible unnormalized
conditional-min side operator has trace bounded by the max-entropy exponent,
then the min-entropy scale is bounded by that exponent.

This is an order-theoretic assembly lemma only; the pointwise matrix/SDP
inequality `hpoint` comes from the source-shaped pure-state argument. -/
theorem conditionalMinEntropyScale_le_conditionalMaxEntropyExponent_of_feasible_le
    [Nonempty a] [Nonempty b] (ρ : MState (a × b))
    (hpoint : ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        T.trace.re ≤ ρ.conditionalMaxEntropyExponent (a := a)) :
    ρ.conditionalMinEntropyScale (a := a) ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
  have hbdd : BddBelow (ρ.conditionalMinEntropyScaleValueSet (a := a)) := by
    rw [ρ.conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)
  rcases ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨y, hy⟩
  calc
    sInf (ρ.conditionalMinEntropyScaleValueSet (a := a)) ≤ y := csInf_le hbdd hy
    _ ≤ ρ.conditionalMaxEntropyExponent (a := a) := by
      rcases hy with ⟨T, hTfeas, rfl⟩
      exact hpoint T hTfeas

theorem neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_feasible_le
    [Nonempty a] [Nonempty b] (ρ : MState (a × b))
    (hpoint : ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        T.trace.re ≤ ρ.conditionalMaxEntropyExponent (a := a)) :
    -ρ.conditionalMinEntropy ≤ ρ.conditionalMaxEntropyPositive := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a),
    ρ.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hscale_pos : 0 < ρ.conditionalMinEntropyScale (a := a) := by
    rw [ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  have hle := ρ.conditionalMinEntropyScale_le_conditionalMaxEntropyExponent_of_feasible_le
    (a := a) hpoint
  have hexp_pos := ρ.conditionalMaxEntropyExponent_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hscale_pos hle)
    (le_of_lt (Real.log_pos one_lt_two))

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_endpoint_bounds
    [Nonempty a] [Nonempty b] (ρ : MState (a × b))
    (hforward : ∀ σ : MState b, ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ≤ T.trace.re)
    (hreverse : ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        T.trace.re ≤ ρ.conditionalMaxEntropyExponent (a := a)) :
    ρ.conditionalMaxEntropyPositive = -ρ.conditionalMinEntropy :=
  le_antisymm
    (ρ.conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_pointwise_le
      (a := a) hforward)
    (ρ.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_feasible_le
      (a := a) hreverse)

theorem conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
    [Nonempty a] [Nonempty b] (ρ : MState (a × b)) :
    ρ.conditionalMaxEntropyPositive =
      log2 ((Fintype.card a : ℝ) *
        sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a))) := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a),
    ρ.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet (a := a)]

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_card_mul_sSup_fidelity_eq_scale
    [Nonempty a] [Nonempty b] (ρ : MState (a × b))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ρ.conditionalMinEntropyScale (a := a)) :
    ρ.conditionalMaxEntropyPositive = -ρ.conditionalMinEntropy := by
  refine ρ.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_exponent_eq_scale
    (a := a) ?_
  rw [ρ.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet (a := a),
    hscale]

theorem conditionalMaxEntropy_eq_neg_conditionalMinEntropy_of_card_mul_sSup_fidelity_eq_scale
    [Nonempty a] [Nonempty b] (ρ : MState (a × b))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ρ.conditionalMinEntropyScale (a := a)) :
    ρ.conditionalMaxEntropy = -ρ.conditionalMinEntropy := by
  rw [ρ.conditionalMaxEntropy_eq_positive (a := a)]
  exact ρ.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_card_mul_sSup_fidelity_eq_scale
    (a := a) hscale

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_fidelity_endpoint_bounds
    [Nonempty a] [Nonempty b] (ρ : MState (a × b))
    (hforward : ∀ σ : MState b, ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        (Fintype.card a : ℝ) *
          ρ.squaredFidelity ((MState.uniform : MState a).prod σ) ≤ T.trace.re)
    (hreverse : ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ρ.conditionalMaxEntropyPositive = -ρ.conditionalMinEntropy := by
  refine ρ.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_endpoint_bounds
    (a := a) ?_ ?_
  · intro σ T hT
    rw [conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
      (a := a) ρ σ]
    exact hforward σ T hT
  · intro T hT
    rw [ρ.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet (a := a)]
    exact hreverse T hT

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : MState (a × b)) (ρAC : MState (a × c))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ρAC.conditionalMinEntropyScale (a := a)) :
    ρAB.conditionalMaxEntropyPositive = -ρAC.conditionalMinEntropy := by
  rw [ρAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ρAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a),
    hscale]
  simp

theorem conditionalMaxEntropy_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : MState (a × b)) (ρAC : MState (a × c))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ρAC.conditionalMinEntropyScale (a := a)) :
    ρAB.conditionalMaxEntropy = -ρAC.conditionalMinEntropy := by
  rw [ρAB.conditionalMaxEntropy_eq_positive (a := a)]
  exact ρAB.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
    (a := a) ρAC hscale

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_fidelity_endpoint_bounds
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : MState (a × b)) (ρAC : MState (a × c))
    (hforward : ∀ σ : MState b, ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        (Fintype.card a : ℝ) *
          ρAB.squaredFidelity ((MState.uniform : MState a).prod σ) ≤ T.trace.re)
    (hreverse : ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ρAB.conditionalMaxEntropyPositive = -ρAC.conditionalMinEntropy := by
  have hle :
      (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) ≤
        ρAC.conditionalMinEntropyScale (a := a) := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    have hcard_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    rw [← mul_sSup_image_eq
      (ρAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
      (ρAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hcard_pos]
    refine csSup_le ?_ ?_
    · exact Set.Nonempty.image _ (ρAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
    · intro x hx
      rcases hx with ⟨y, ⟨σ, rfl⟩, rfl⟩
      refine le_csInf (ρAC.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
      intro z hz
      rcases hz with ⟨T, hT, rfl⟩
      exact hforward σ T hT
  have hge :
      ρAC.conditionalMinEntropyScale (a := a) ≤
        (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    have hbdd : BddBelow (ρAC.conditionalMinEntropyScaleValueSet (a := a)) := by
      rw [ρAC.conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
      exact ρAC.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)
    rcases ρAC.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨z, hz⟩
    calc
      sInf (ρAC.conditionalMinEntropyScaleValueSet (a := a)) ≤ z := csInf_le hbdd hz
      _ ≤ (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
          rcases hz with ⟨T, hT, rfl⟩
          exact hreverse T hT
  exact
    ρAB.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_card_mul_sSup_fidelity_eq_scale
      (a := a) ρAC (le_antisymm hle hge)

/-- Cross-register endpoint weak-duality direction.

The SDP/fidelity content sits entirely in `hforward`, which bounds the
`AB` max-entropy fidelity by every feasible `AC` min-entropy scale.  This
theorem contributes the order-theoretic `sSup ≤ sInf` step and the logarithm
transport. -/
theorem conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_cross_fidelity_forward_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : MState (a × b)) (ρAC : MState (a × c))
    (hforward : ∀ σ : MState b, ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        (Fintype.card a : ℝ) *
          ρAB.squaredFidelity ((MState.uniform : MState a).prod σ) ≤ T.trace.re) :
    ρAB.conditionalMaxEntropyPositive ≤ -ρAC.conditionalMinEntropy := by
  rw [ρAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ρAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hle :
      (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) ≤
        ρAC.conditionalMinEntropyScale (a := a) := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    have hcard_pos : 0 < (Fintype.card a : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    rw [← mul_sSup_image_eq
      (ρAB.conditionalMaxEntropyFidelityValueSet_nonempty (a := a))
      (ρAB.conditionalMaxEntropyFidelityValueSet_bddAbove (a := a)) hcard_pos]
    refine csSup_le ?_ ?_
    · exact Set.Nonempty.image _ (ρAB.conditionalMaxEntropyFidelityValueSet_nonempty
        (a := a))
    · intro x hx
      rcases hx with ⟨y, ⟨σ, rfl⟩, rfl⟩
      refine le_csInf (ρAC.conditionalMinEntropyScaleValueSet_nonempty (a := a)) ?_
      intro z hz
      rcases hz with ⟨T, hT, rfl⟩
      exact hforward σ T hT
  have hleft_pos :
      0 < (Fintype.card a : ℝ) *
        sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [← ρAB.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
      (a := a)]
    exact ρAB.conditionalMaxEntropyExponent_pos (a := a)
  have hscale_pos : 0 < ρAC.conditionalMinEntropyScale (a := a) := by
    rw [ρAC.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρAC.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hleft_pos hle)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Cross-register endpoint reverse-duality direction under a strong pointwise
side-operator hypothesis.

This wrapper is retained for local order-theoretic reuse, but its hypothesis is
stronger than the source endpoint SDP: feasible side operators can be scaled, so
the source-faithful reverse direction should usually use
`neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound`
instead. -/
theorem neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_fidelity_reverse_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : MState (a × b)) (ρAC : MState (a × c))
    (hreverse : ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        T.trace.re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    -ρAC.conditionalMinEntropy ≤ ρAB.conditionalMaxEntropyPositive := by
  rw [ρAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ρAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hge :
      ρAC.conditionalMinEntropyScale (a := a) ≤
        (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet]
    have hbdd : BddBelow (ρAC.conditionalMinEntropyScaleValueSet (a := a)) := by
      rw [ρAC.conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]
      exact ρAC.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)
    rcases ρAC.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨z, hz⟩
    calc
      sInf (ρAC.conditionalMinEntropyScaleValueSet (a := a)) ≤ z := csInf_le hbdd hz
      _ ≤ (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
          rcases hz with ⟨T, hT, rfl⟩
          exact hreverse T hT
  have hscale_pos : 0 < ρAC.conditionalMinEntropyScale (a := a) := by
    rw [ρAC.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρAC.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  have hright_pos :
      0 < (Fintype.card a : ℝ) *
        sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [← ρAB.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
      (a := a)]
    exact ρAB.conditionalMaxEntropyExponent_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hscale_pos hge)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Correct reverse endpoint order bridge through the dual-effect SDP.

Unlike a pointwise bound on every feasible side operator `T`, this hypothesis
is stable under scaling: it bounds the linear dual-effect objective
`Tr(ρ_AC M)` for every effect `M ≥ 0`, `Tr_A M ≤ I`.  The already-proved
endpoint strong duality
`conditionalMinEntropyScale_eq_sSup_dualEffectValueSet` then converts this
into the required scale bound. -/
theorem neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : MState (a × b)) (ρAC : MState (a × c))
    (hdual : ∀ M : CMatrix (a × c),
      ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ρAC.m * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    -ρAC.conditionalMinEntropy ≤ ρAB.conditionalMaxEntropyPositive := by
  rw [ρAB.conditionalMaxEntropyPositive_eq_log2_card_mul_sSup_fidelityValueSet
      (a := a),
    ρAC.conditionalMinEntropy_eq_neg_log2_scale_of_nonempty (a := a)]
  have hne :
      (ρAC.conditionalMinEntropyDualEffectValueSet (a := a)).Nonempty :=
    ρAC.conditionalMinEntropyDualEffectValueSet_nonempty (a := a)
  have hscale_le :
      ρAC.conditionalMinEntropyScale (a := a) ≤
        (Fintype.card a : ℝ) *
          sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [ρAC.conditionalMinEntropyScale_eq_sSup_dualEffectValueSet (a := a)]
    refine csSup_le hne ?_
    intro y hy
    rcases hy with ⟨M, hM, rfl⟩
    exact hdual M hM
  have hscale_pos : 0 < ρAC.conditionalMinEntropyScale (a := a) := by
    rw [ρAC.conditionalMinEntropyScale_eq_normalizedScale (a := a)]
    exact ρAC.conditionalMinEntropyNormalizedScale_inf_pos (a := a)
  have hright_pos :
      0 < (Fintype.card a : ℝ) *
        sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
    rw [← ρAB.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
      (a := a)]
    exact ρAB.conditionalMaxEntropyExponent_pos (a := a)
  unfold log2
  simpa using div_le_div_of_nonneg_right (Real.log_le_log hscale_pos hscale_le)
    (le_of_lt (Real.log_pos one_lt_two))

/-- Value-set version of the reverse endpoint bound through dual effects. -/
theorem sSup_conditionalMinEntropyDualEffectValueSet_le_card_mul_sSup_fidelityValueSet_of_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : MState (a × b)) (ρAC : MState (a × c))
    (hdual : ∀ M : CMatrix (a × c),
      ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ρAC.m * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    sSup (ρAC.conditionalMinEntropyDualEffectValueSet (a := a)) ≤
      (Fintype.card a : ℝ) *
        sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  refine csSup_le (ρAC.conditionalMinEntropyDualEffectValueSet_nonempty (a := a)) ?_
  intro y hy
  rcases hy with ⟨M, hM, rfl⟩
  exact hdual M hM

/-- Endpoint equality from the correct pair of one-sided bounds:
the forward side is the usual fidelity-vs-scale weak duality, while the
reverse side is stated through the dual-effect objective rather than through
arbitrarily scalable feasible side operators. -/
theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_cross_fidelity_forward_dualEffect_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : MState (a × b)) (ρAC : MState (a × c))
    (hforward : ∀ σ : MState b, ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        (Fintype.card a : ℝ) *
          ρAB.squaredFidelity ((MState.uniform : MState a).prod σ) ≤ T.trace.re)
    (hdual : ∀ M : CMatrix (a × c),
      ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ρAC.m * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ρAB.conditionalMaxEntropyPositive = -ρAC.conditionalMinEntropy :=
  le_antisymm
    (ρAB.conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_cross_fidelity_forward_bound
      (a := a) ρAC hforward)
    (ρAB.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
      (a := a) ρAC hdual)

end MState
