/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.OneShot.SmoothEndpoint.Order
public import QIT.OneShot.SmoothEndpoint.MaximallyEntangledProjector
public import QIT.States.MaximallyMixed
public import QIT.States.TraceNorm.Spectral

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal Pointwise
open scoped Topology
open Matrix
open Set Filter

namespace QIT

universe u v w x

noncomputable section


namespace State

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable {c : Type*} [Fintype c] [DecidableEq c]

noncomputable local instance normalizedCMatrixCStarAlgebra :
    CStarAlgebra (CMatrix a) := {}

local instance cMatrixNormedSpaceReal : NormedSpace ℝ (CMatrix b) :=
  inferInstance

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid NormedSpace.toModule
attribute [local instance 1001] PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-! ## Elementary state bounds and maximally mixed side states -/

/-- Every normalized finite-dimensional state is bounded above by the identity
operator. -/
theorem matrix_le_one (ρ : State a) :
    ρ.matrix ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := ρ.pos.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : ρ.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using ρ.pos.1.spectral_theorem
  have heig_sum : ∑ i, ρ.pos.1.eigenvalues i = 1 := by
    have hc : (∑ i, ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)) = 1 := by
      exact ρ.pos.1.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
    exact Complex.ofReal_injective (by simpa using hc)
  have heig_le_one : ∀ i, ρ.pos.1.eigenvalues i ≤ 1 := by
    intro i
    have hnonneg (j : a) : 0 ≤ ρ.pos.1.eigenvalues j :=
      ρ.pos.eigenvalues_nonneg j
    calc ρ.pos.1.eigenvalues i
        ≤ ρ.pos.1.eigenvalues i +
            ∑ j ∈ Finset.univ.erase i, ρ.pos.1.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
      _ = ∑ j, ρ.pos.1.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => ρ.pos.1.eigenvalues j) (Finset.mem_univ i)
      _ = 1 := heig_sum
  have hsub :
      1 - ρ.matrix = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
    rw [hdiag]
    have hUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
      simp
    calc
      1 - (U : CMatrix a) * D * star (U : CMatrix a) =
          (U : CMatrix a) * 1 * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
            rw [Matrix.mul_one, hUstar]
      _ = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
            noncomm_ring
  have hdiag_sub :
      (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((1 : ℝ) - ρ.pos.1.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (1 : ℝ) - ρ.pos.1.eigenvalues i := by
    exact sub_nonneg.mpr (heig_le_one i)
  exact_mod_cast hnonneg

theorem sqrtMatrix_trace_re_pos [Nonempty a] (ρ : State a) :
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
  have hrho_zero : ρ.matrix = 0 := by
    rw [← ρ.sqrtMatrix_mul_self, hsqrt_zero]
    simp
  have htrace : (ρ.matrix.trace : ℂ) = 0 := by simp [hrho_zero]
  rw [ρ.trace_eq_one] at htrace
  norm_num at htrace

omit [DecidableEq a] in theorem trace_re_le_of_le {X Y : CMatrix a} (hXY : X ≤ Y) :
    X.trace.re ≤ Y.trace.re := by
  have hnon : 0 ≤ (Y - X).trace.re := (Matrix.PosSemidef.trace_nonneg hXY).1
  have htrace : (Y - X).trace.re = Y.trace.re - X.trace.re := by
    simp [Matrix.trace_sub]
  linarith

/-- The maximally mixed state on a nonempty finite system. -/
theorem identityTensorStateMatrix_trace_re (σ : State b) :
    (identityTensorStateMatrix (a := a) σ).trace.re = (Fintype.card a : ℝ) := by
  change (Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) σ.matrix).trace.re =
    (Fintype.card a : ℝ)
  rw [Matrix.trace_kronecker, σ.trace_eq_one, Matrix.trace_one]
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
def conditionalMaxEntropyExponentCandidate (ρ : State (Prod a b)) (σ : State b) :
    ℝ :=
  (traceNorm (ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2

@[simp]
theorem conditionalMaxEntropyExponentCandidate_eq
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyExponentCandidate σ =
      (traceNorm (ρ.sqrtMatrix *
        psdSqrt (identityTensorStateMatrix (a := a) σ))) ^ 2 :=
  rfl

/-- The raw endpoint exponent
`sup_σ ‖√ρ_AB √(I_A ⊗ σ_B)‖₁²`. -/
def conditionalMaxEntropyExponentValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : State b,
    x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

/-- The raw endpoint exponent
`sup_σ ‖√ρ_AB √(I_A ⊗ σ_B)‖₁²`. -/
def conditionalMaxEntropyExponent (ρ : State (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyExponentValueSet (a := a))

@[simp]
theorem conditionalMaxEntropyExponent_eq (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyExponent =
      sSup (ρ.conditionalMaxEntropyExponentValueSet (a := a)) :=
  rfl

/-- The existing conditional max-entropy candidate is the logarithm of the raw
endpoint candidate. -/
theorem conditionalMaxEntropyCandidate_eq_log2_exponentCandidate
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyCandidate σ =
      log2 (ρ.conditionalMaxEntropyExponentCandidate (a := a) σ) :=
  rfl

theorem conditionalMaxEntropyExponentCandidate_nonneg
    (ρ : State (Prod a b)) (σ : State b) :
    0 ≤ ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  exact sq_nonneg _

theorem conditionalMaxEntropyExponentCandidate_maximallyMixed_pos
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) (maximallyMixed b) := by
  let c : ℝ := (Fintype.card b : ℝ)⁻¹
  have hc_nonneg : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hc_pos : 0 < Real.sqrt c := by
    have hcard_pos : 0 < (Fintype.card b : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    exact Real.sqrt_pos.mpr (inv_pos.mpr hcard_pos)
  have hsqrt_id :
      psdSqrt (identityTensorStateMatrix (a := a) (maximallyMixed b)) =
        (((Real.sqrt c : ℝ) : ℂ) • (1 : CMatrix (Prod a b))) := by
    rw [identityTensorStateMatrix_maximallyMixed (a := a) (b := b)]
    exact psdSqrt_real_smul_one (a := Prod a b) hc_nonneg
  have htrace_eq :
      (ρ.sqrtMatrix *
          psdSqrt (identityTensorStateMatrix (a := a) (maximallyMixed b))).trace =
        ((Real.sqrt c : ℝ) : ℂ) * ρ.sqrtMatrix.trace := by
    rw [hsqrt_id]
    simp [Matrix.trace_smul]
  have htrace_abs_pos :
      0 < Complex.abs ((ρ.sqrtMatrix *
          psdSqrt (identityTensorStateMatrix (a := a) (maximallyMixed b))).trace) := by
    rw [htrace_eq]
    change 0 < ‖((Real.sqrt c : ℝ) : ℂ) * ρ.sqrtMatrix.trace‖
    rw [norm_mul]
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
        psdSqrt (identityTensorStateMatrix (a := a) (maximallyMixed b))) :=
    lt_of_lt_of_le htrace_abs_pos (trace_abs_le_traceNorm _)
  unfold conditionalMaxEntropyExponentCandidate
  exact sq_pos_of_pos htn_pos

theorem psdSqrt_identityTensorStateMatrix (σ : State b) :
    psdSqrt (identityTensorStateMatrix (a := a) σ) =
      Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix := by
  change psdSqrt (Matrix.kronecker (1 : CMatrix a) σ.matrix) =
    Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix
  rw [psdSqrt_kronecker Matrix.PosSemidef.one σ.pos]
  have hone : psdSqrt (1 : CMatrix a) = (1 : CMatrix a) := by
    simpa using (psdSqrt_real_smul_one (a := a) (r := 1) (by norm_num))
  rw [hone]
  simp [State.sqrtMatrix]

theorem conditionalMaxEntropyExponentCandidate_eq_sqrt_identity
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ =
      (traceNorm (ρ.sqrtMatrix *
        Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix)) ^ 2 := by
  rw [conditionalMaxEntropyExponentCandidate_eq,
    psdSqrt_identityTensorStateMatrix (a := a) σ]

theorem conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
    [Nonempty a] (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ =
      (Fintype.card a : ℝ) *
        ρ.squaredFidelity ((maximallyMixed a).prod σ) := by
  let d : ℝ := Fintype.card a
  let M : CMatrix (Prod a b) :=
    ρ.sqrtMatrix * ((maximallyMixed a).prod σ).sqrtMatrix
  have hd_nonneg : 0 ≤ d := Nat.cast_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsqrt_sq : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd_nonneg
  have hrewrite :
      ρ.sqrtMatrix * Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix =
        (((Real.sqrt d : ℝ) : ℂ) • M) := by
    have hsqrt :
        Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix =
          (((Real.sqrt d : ℝ) : ℂ) • ((maximallyMixed a).prod σ).sqrtMatrix) := by
      dsimp [d]
      exact sqrt_identityTensorStateMatrix_eq_sqrt_card_smul_maximallyMixed_prod_sqrtMatrix
        (a := a) σ
    calc
      ρ.sqrtMatrix * Matrix.kronecker (1 : CMatrix a) σ.sqrtMatrix =
          ρ.sqrtMatrix *
            (((Real.sqrt d : ℝ) : ℂ) • ((maximallyMixed a).prod σ).sqrtMatrix) := by
            rw [hsqrt]
      _ = (((Real.sqrt d : ℝ) : ℂ) • M) := by
            dsimp [M]
            rw [Matrix.mul_smul]
  rw [conditionalMaxEntropyExponentCandidate_eq_sqrt_identity]
  rw [hrewrite]
  rw [traceNorm_real_smul_eq hsqrt_nonneg M]
  rw [State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq]
  dsimp [M, d]
  let t : ℝ := traceNorm (ρ.sqrtMatrix * ((maximallyMixed a).prod σ).sqrtMatrix)
  change (Real.sqrt (Fintype.card a : ℝ) * t) ^ 2 =
    (Fintype.card a : ℝ) * t ^ 2
  nlinarith [hsqrt_sq]

theorem conditionalMaxEntropy_hilbertSchmidt_trace_le
    (ρ : State (Prod a b)) (σ : State b) :
    ((star (ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ)) *
        (ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ))).trace).re ≤
      (Fintype.card a : ℝ) := by
  let S : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let T : CMatrix (Prod a b) := psdSqrt S
  have hSpos : S.PosSemidef := identityTensorStateMatrix_posSemidef (a := a) σ
  have hTstar : star T = T := (psdSqrt_isHermitian S).eq
  have hle : star T * ρ.matrix * T ≤ star T * (1 : CMatrix (Prod a b)) * T :=
    star_left_conjugate_le_conjugate (ρ.matrix_le_one) T
  have hleft_eq :
      star (ρ.sqrtMatrix * T) * (ρ.sqrtMatrix * T) = star T * ρ.matrix * T := by
    calc
      star (ρ.sqrtMatrix * T) * (ρ.sqrtMatrix * T)
          = Tᴴ * (ρ.sqrtMatrix * (ρ.sqrtMatrix * T)) := by
              simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
                ρ.sqrtMatrix_isHermitian.eq, Matrix.mul_assoc]
      _ = Tᴴ * ((ρ.sqrtMatrix * ρ.sqrtMatrix) * T) := by rw [Matrix.mul_assoc]
      _ = Tᴴ * (ρ.matrix * T) := by rw [ρ.sqrtMatrix_mul_self]
      _ = star T * ρ.matrix * T := by
          simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hright_eq : star T * (1 : CMatrix (Prod a b)) * T = S := by
    rw [hTstar]
    simp [T, psdSqrt_mul_self_of_posSemidef hSpos]
  have htrace_le := trace_re_le_of_le hle
  rw [hright_eq] at htrace_le
  change (star (ρ.sqrtMatrix * T) * (ρ.sqrtMatrix * T)).trace.re ≤
    (Fintype.card a : ℝ)
  rw [hleft_eq]
  exact htrace_le.trans_eq (identityTensorStateMatrix_trace_re (a := a) σ)

theorem conditionalMaxEntropyExponentCandidate_le_card
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ≤
      (Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ) := by
  let M : CMatrix (Prod a b) :=
    ρ.sqrtMatrix * psdSqrt (identityTensorStateMatrix (a := a) σ)
  have hhs : ((star M * M).trace).re ≤ (Fintype.card a : ℝ) :=
    conditionalMaxEntropy_hilbertSchmidt_trace_le (a := a) ρ σ
  have htn := traceNorm_sq_le_card_mul_hilbertSchmidt M
  unfold conditionalMaxEntropyExponentCandidate
  change traceNorm M ^ 2 ≤ (Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ)
  exact htn.trans (mul_le_mul_of_nonneg_left hhs (Nat.cast_nonneg _))

/-- The definition-level conditional max-entropy candidate set.

It filters out zero endpoint exponents before applying `log₂`, matching the
finite-real-valued convention used by `State.conditionalMaxEntropy`: this is the
real-valued replacement for the usual extended-real convention `log 0 = -∞`. -/
def conditionalMaxEntropyValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {h : ℝ | ∃ σ : State b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      h = conditionalMaxEntropyCandidate (a := a) ρ σ}

@[simp]
theorem conditionalMaxEntropyValueSet_eq (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyValueSet (a := a) =
      {h : ℝ | ∃ σ : State b,
        0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
          h = conditionalMaxEntropyCandidate (a := a) ρ σ} :=
  rfl

theorem conditionalMaxEntropy_eq_sSup_valueSet (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropy =
      sSup (ρ.conditionalMaxEntropyValueSet (a := a)) := by
  rfl

theorem conditionalMaxEntropyValueSet_nonempty [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    (ρ.conditionalMaxEntropyValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyCandidate (a := a) (maximallyMixed b),
    maximallyMixed b, ρ.conditionalMaxEntropyExponentCandidate_maximallyMixed_pos
      (a := a), rfl⟩

theorem conditionalMaxEntropyCandidate_le_log2_card_bound
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) (σ : State b) :
    ρ.conditionalMaxEntropyCandidate (a := a) σ ≤
      max 0 (log2 ((Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ))) := by
  by_cases hpos : 0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ
  · have hle := ρ.conditionalMaxEntropyExponentCandidate_le_card (a := a) σ
    have hbound_pos :
        0 < (Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ) := by
      have hprod : 0 < (Fintype.card (Prod a b) : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨Classical.arbitrary (Prod a b)⟩
      have ha : 0 < (Fintype.card a : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨Classical.arbitrary a⟩
      exact mul_pos hprod ha
    have hlog :
        log2 (ρ.conditionalMaxEntropyExponentCandidate (a := a) σ) ≤
          log2 ((Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ)) := by
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
    (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxEntropyValueSet (a := a)) := by
  refine ⟨max 0 (log2 ((Fintype.card (Prod a b) : ℝ) *
    (Fintype.card a : ℝ))), ?_⟩
  intro h hh
  rcases hh with ⟨σ, _hpos, rfl⟩
  exact ρ.conditionalMaxEntropyCandidate_le_log2_card_bound (a := a) σ

/-- The normalized fidelity form of the conditional max-entropy endpoint
optimization:
`{F(ρ_AB, π_A ⊗ σ_B)^2 | σ_B}`. -/
def conditionalMaxEntropyFidelityValueSet [Nonempty a]
    (ρ : State (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : State b,
    x = ρ.squaredFidelity ((maximallyMixed a).prod σ)}

theorem conditionalMaxEntropyFidelityValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxEntropyFidelityValueSet (a := a)).Nonempty :=
  ⟨ρ.squaredFidelity ((maximallyMixed a).prod (maximallyMixed b)),
    maximallyMixed b, rfl⟩

theorem conditionalMaxEntropyFidelityValueSet_bddAbove
    [Nonempty a] (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) := by
  refine ⟨(Fintype.card (Prod a b) : ℝ), ?_⟩
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
    (ρ : State (Prod a b)) (σ : State b) (X : CMatrix (Prod a b)) : Prop :=
  (Matrix.fromBlocks ρ.matrix X (star X) ((maximallyMixed a).prod σ).matrix :
      CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef

@[simp]
theorem ConditionalMaxFidelityBlockFeasible_eq [Nonempty a]
    (ρ : State (Prod a b)) (σ : State b) (X : CMatrix (Prod a b)) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ↔
      (Matrix.fromBlocks ρ.matrix X (star X) ((maximallyMixed a).prod σ).matrix :
        CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef :=
  Iff.rfl

/-- The linear objective in the fidelity block SDP.  The squared endpoint value
uses this quantity squared. -/
def conditionalMaxFidelityBlockValue (X : CMatrix (Prod a b)) : ℝ :=
  X.trace.re

omit [DecidableEq a] [DecidableEq b] in
@[simp]
theorem conditionalMaxFidelityBlockValue_eq (X : CMatrix (Prod a b)) :
    conditionalMaxFidelityBlockValue X = X.trace.re :=
  rfl

/-- The max-entropy endpoint value represented through a feasible block SDP
candidate. -/
def conditionalMaxFidelityBlockExponentValue [Nonempty a]
    (X : CMatrix (Prod a b)) : ℝ :=
  (Fintype.card a : ℝ) * (conditionalMaxFidelityBlockValue X) ^ 2

omit [DecidableEq a] [DecidableEq b] in
@[simp]
theorem conditionalMaxFidelityBlockExponentValue_eq [Nonempty a]
    (X : CMatrix (Prod a b)) :
    conditionalMaxFidelityBlockExponentValue (a := a) X =
      (Fintype.card a : ℝ) * X.trace.re ^ 2 :=
  rfl

/-- Zero off-diagonal block feasibility.  This proves the block SDP surface is
nonempty without using any fidelity or duality theorem. -/
theorem ConditionalMaxFidelityBlockFeasible_zero [Nonempty a]
    (ρ : State (Prod a b)) (σ : State b) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ 0 := by
  simpa [ConditionalMaxFidelityBlockFeasible] using
    cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) ρ.pos
      (((maximallyMixed a).prod σ).pos)

private def scaledBlockEmbeddingMatrix {α : Type*} [Fintype α] [DecidableEq α]
    (t : ℝ) : Matrix (Sum α α) α ℂ :=
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
          (((Real.sqrt t : ℝ) : ℂ) • τ) τ : CMatrix (Sum α α)) := by
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
    {ρ : State (Prod a b)} {σ : State b} {t : ℝ} (ht : 0 ≤ t)
    (hle : (((t : ℝ) : ℂ) • ((maximallyMixed a).prod σ).matrix) ≤ ρ.matrix) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ
      ((((Real.sqrt t : ℝ) : ℂ) • ((maximallyMixed a).prod σ).matrix)) := by
  classical
  let τ : CMatrix (Prod a b) := ((maximallyMixed a).prod σ).matrix
  have hdiff : (ρ.matrix - (((t : ℝ) : ℂ) • τ)).PosSemidef := by
    simpa [τ, Matrix.le_iff] using hle
  have hdiag :
      (Matrix.fromBlocks (ρ.matrix - (((t : ℝ) : ℂ) • τ)) 0 0
        (0 : CMatrix (Prod a b)) :
        CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef := by
    exact cMatrix_fromBlocks_diagonal_posSemidef hdiff Matrix.PosSemidef.zero
  have hrank :
      (Matrix.fromBlocks (((t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ) τ :
          CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef := by
    rw [← scaledBlockEmbeddingMatrix_block_eq (α := Prod a b) (τ := τ) ht]
    exact scaledBlockEmbeddingMatrix_mul_pos_mul_conjTranspose
      ((maximallyMixed a).prod σ).pos t
  have hsum :
      (Matrix.fromBlocks ρ.matrix
          ((((Real.sqrt t : ℝ) : ℂ) • τ))
          (Matrix.conjTranspose ((((Real.sqrt t : ℝ) : ℂ) • τ)))
          τ :
          CMatrix (Sum (Prod a b) (Prod a b))) =
        (Matrix.fromBlocks (ρ.matrix - (((t : ℝ) : ℂ) • τ)) 0 0
          (0 : CMatrix (Prod a b)) :
          CMatrix (Sum (Prod a b) (Prod a b))) +
        (Matrix.fromBlocks (((t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ)
          (((Real.sqrt t : ℝ) : ℂ) • τ) τ :
          CMatrix (Sum (Prod a b) (Prod a b))) := by
    ext x y
    cases x <;> cases y <;>
      simp [τ, Matrix.fromBlocks, Matrix.of_apply,
        Matrix.conjTranspose_smul, ((maximallyMixed a).prod σ).pos.isHermitian.eq]
  rw [ConditionalMaxFidelityBlockFeasible]
  change (Matrix.fromBlocks ρ.matrix
    ((((Real.sqrt t : ℝ) : ℂ) • τ))
    (Matrix.conjTranspose ((((Real.sqrt t : ℝ) : ℂ) • τ)))
    τ : CMatrix (Sum (Prod a b) (Prod a b))).PosSemidef
  rw [hsum]
  exact hdiag.add hrank

theorem ConditionalMaxFidelityBlockFeasible.of_scaled_le_blockExponentValue [Nonempty a]
    {σ : State b} {t : ℝ} (ht : 0 ≤ t) :
    conditionalMaxFidelityBlockExponentValue (a := a)
        ((((Real.sqrt t : ℝ) : ℂ) • ((maximallyMixed a).prod σ).matrix)) =
      (Fintype.card a : ℝ) * t := by
  have htrace :
      (((((Real.sqrt t : ℝ) : ℂ) • ((maximallyMixed a).prod σ).matrix)).trace).re =
        Real.sqrt t := by
    rw [Matrix.trace_smul, ((maximallyMixed a).prod σ).trace_eq_one]
    simp
  rw [conditionalMaxFidelityBlockExponentValue_eq, htrace]
  rw [Real.sq_sqrt ht]

/-! ### Block-SDP feasible points are fidelity-bounded -/

def pureVectorOfAmplitudeMatrix {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (A : Matrix α r ℂ) (htrace : (A * Aᴴ).trace = 1) :
    PureVector (Prod r α) where
  amp := fun x => A x.2 x.1
  trace_rankOne_eq_one := by
    classical
    calc
      (rankOneMatrix (fun x : Prod r α => A x.2 x.1)).trace =
          ∑ x : Prod r α, A x.2 x.1 * star (A x.2 x.1) := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = ∑ i : α, ∑ j : r, A i j * star (A i j) := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
      _ = (A * Aᴴ).trace := by
            simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = 1 := htrace

theorem pureVectorOfAmplitudeMatrix_amplitudeMatrix {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (A : Matrix α r ℂ) (htrace : (A * Aᴴ).trace = 1) :
    (pureVectorOfAmplitudeMatrix A htrace).amplitudeMatrix = A := by
  rfl

theorem pureVectorOfAmplitudeMatrix_purifies {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    {A : Matrix α r ℂ} {ρ : State α}
    (hgram : A * Aᴴ = ρ.matrix) (htrace : (A * Aᴴ).trace = 1) :
    (pureVectorOfAmplitudeMatrix A htrace).Purifies ρ := by
  rw [PureVector.purifies_iff]
  rw [PureVector.state_matrix]
  rw [PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose]
  simpa [pureVectorOfAmplitudeMatrix_amplitudeMatrix] using hgram

def pureVectorNormalize {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) : PureVector α where
  amp := fun x => (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x
  trace_rankOne_eq_one := by
    classical
    let t : ℝ := (rankOneMatrix v).trace.re
    have htpos : 0 < t := hpos
    have ht_nonneg : 0 ≤ t := le_of_lt htpos
    have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htpos)
    have htrace_im : (rankOneMatrix v).trace.im = 0 :=
      (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos v)).2.symm
    have htrace_complex : (rankOneMatrix v).trace = (t : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using htrace_im
    have hcoeff :
        (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (t : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt ht_nonneg]
    calc
      (rankOneMatrix
          (fun x => ((((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x))).trace =
          (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (rankOneMatrix v).trace) := by
            simp [rankOneMatrix_trace, dotProduct, t, Finset.mul_sum, mul_assoc,
              mul_left_comm, mul_comm]
      _ = (((((Real.sqrt t)⁻¹ : ℝ) : ℂ) *
              ((((Real.sqrt t)⁻¹ : ℝ) : ℂ))) * (t : ℂ)) := by
            rw [htrace_complex]
      _ = 1 := hcoeff

theorem pureVectorNormalize_amp {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℂ) (hpos : 0 < (rankOneMatrix v).trace.re) :
    (pureVectorNormalize v hpos).amp =
      fun x => (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) * v x :=
  rfl

def maxEntangledSideAmplitude {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a]
    (η : PureVector (Prod r b)) : Matrix (Prod a b) (Prod r a) ℂ :=
  fun x y =>
    (((Real.sqrt ((Fintype.card a : ℝ)⁻¹)) : ℝ) : ℂ) *
      (if y.2 = x.1 then η.amp (y.1, x.2) else 0)

theorem maxEntangledSideAmplitude_gram {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (η : PureVector (Prod r b)) :
    maxEntangledSideAmplitude (a := a) η *
        (maxEntangledSideAmplitude (a := a) η)ᴴ =
      ((State.maximallyMixed a).prod η.state.marginalB).matrix := by
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
      State.prod, State.maximallyMixed, State.marginalB, partialTraceA,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.mul_sum,
      Fintype.sum_prod_type,
      mul_assoc, mul_left_comm, mul_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, hcoeff_complex_inv]
    rw [Complex.ofReal_inv]
    norm_num
  · simp [maxEntangledSideAmplitude, Matrix.mul_apply, Matrix.conjTranspose_apply,
      State.prod, State.maximallyMixed, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, hxy]

def maxEntangledSidePureVector {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (η : PureVector (Prod r b)) :
    PureVector (Prod (Prod r a) (Prod a b)) :=
  pureVectorOfAmplitudeMatrix (maxEntangledSideAmplitude (a := a) η) (by
    rw [maxEntangledSideAmplitude_gram]
    exact ((State.maximallyMixed a).prod η.state.marginalB).trace_eq_one)

theorem maxEntangledSidePureVector_purifies {r : Type*} {a : Type*} {b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (η : PureVector (Prod r b)) :
    (maxEntangledSidePureVector (a := a) η).Purifies
      ((State.maximallyMixed a).prod η.state.marginalB) := by
  exact pureVectorOfAmplitudeMatrix_purifies
    (maxEntangledSideAmplitude_gram (a := a) η)
    (by
      rw [maxEntangledSideAmplitude_gram]
      exact ((State.maximallyMixed a).prod η.state.marginalB).trace_eq_one)

private def blockSqrtTopRow {α : Type*} [Fintype α] [DecidableEq α]
    (S : CMatrix (Sum α α)) : Matrix α (Sum α α) ℂ :=
  fun i j => S (Sum.inl i) j

private def blockSqrtBottomRow {α : Type*} [Fintype α] [DecidableEq α]
    (S : CMatrix (Sum α α)) : Matrix α (Sum α α) ℂ :=
  fun i j => S (Sum.inr i) j

private theorem blockSqrtTopRow_mul_conjTranspose {α : Type*}
    [Fintype α] [DecidableEq α] (S : CMatrix (Sum α α)) (hS : S.IsHermitian) :
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
    [Fintype α] [DecidableEq α] (S : CMatrix (Sum α α)) (hS : S.IsHermitian) :
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
    [Fintype α] [DecidableEq α] (S : CMatrix (Sum α α)) (hS : S.IsHermitian) :
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

theorem pureVector_abs_overlap_le_fidelity {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    {Ψ Φ : PureVector (Prod r α)} {ρ σ : State α}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies σ) :
    Complex.abs (Ψ.overlap Φ) ≤ ρ.fidelity σ := by
  have hsq := PureVector.overlapSq_le_squaredFidelity_of_purifies hΨ hΦ
  rw [PureVector.overlapSq_eq_normSq, State.squaredFidelity_eq_fidelity_sq] at hsq
  have hleft_nonneg : 0 ≤ Complex.abs (Ψ.overlap Φ) := norm_nonneg _
  have hfid_nonneg : 0 ≤ ρ.fidelity σ := traceNorm_nonneg _
  rw [Complex.normSq_eq_norm_sq] at hsq
  exact (sq_le_sq₀ hleft_nonneg hfid_nonneg).mp hsq

private theorem abs_trace_eq_abs_overlap_of_amplitude_gram {r : Type*} {α : Type*}
    [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    {A B : Matrix α r ℂ} {X : CMatrix α}
    (hX : A * Bᴴ = X) {hAtrace : (A * Aᴴ).trace = 1}
    {hBtrace : (B * Bᴴ).trace = 1} :
    Complex.abs X.trace =
      Complex.abs ((pureVectorOfAmplitudeMatrix A hAtrace).overlap
        (pureVectorOfAmplitudeMatrix B hBtrace)) := by
  let Ψ := pureVectorOfAmplitudeMatrix A hAtrace
  let Φ := pureVectorOfAmplitudeMatrix B hBtrace
  have hoverlap :
      Ψ.overlap Φ = (Aᴴ * B).trace := by
    rw [PureVector.overlap_eq_trace_conjTranspose_amplitudeMatrix_mul]
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
    {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    Complex.abs X.trace ≤ ρ.fidelity ((maximallyMixed a).prod σ) := by
  classical
  let α := Prod a b
  let τ : State α := (maximallyMixed a).prod σ
  let H : CMatrix (Sum α α) := Matrix.fromBlocks ρ.matrix X (star X) τ.matrix
  let S : CMatrix (Sum α α) := psdSqrt H
  let A : Matrix α (Sum α α) ℂ := blockSqrtTopRow S
  let B : Matrix α (Sum α α) ℂ := blockSqrtBottomRow S
  have hH : H.PosSemidef := hX
  have hS : S.IsHermitian := psdSqrt_isHermitian H
  have hSsq : S * S = H := psdSqrt_mul_self_of_posSemidef hH
  have hAgram : A * Aᴴ = ρ.matrix := by
    calc
      A * Aᴴ = Matrix.sumBlock11 (S * S) :=
        blockSqrtTopRow_mul_conjTranspose S hS
      _ = Matrix.sumBlock11 H := by rw [hSsq]
      _ = ρ.matrix := by rfl
  have hBgram : B * Bᴴ = τ.matrix := by
    calc
      B * Bᴴ = Matrix.sumBlock22 (S * S) :=
        blockSqrtBottomRow_mul_conjTranspose S hS
      _ = Matrix.sumBlock22 H := by rw [hSsq]
      _ = τ.matrix := by rfl
  have hAB : A * Bᴴ = X := by
    calc
      A * Bᴴ = Matrix.sumBlock12 (S * S) :=
        blockSqrtTopRow_mul_bottomRow_conjTranspose S hS
      _ = Matrix.sumBlock12 H := by rw [hSsq]
      _ = X := by rfl
  have hAtrace : (A * Aᴴ).trace = 1 := by
    rw [hAgram, ρ.trace_eq_one]
  have hBtrace : (B * Bᴴ).trace = 1 := by
    rw [hBgram, τ.trace_eq_one]
  let Ψ : PureVector (Prod (Sum α α) α) := pureVectorOfAmplitudeMatrix A hAtrace
  let Φ : PureVector (Prod (Sum α α) α) := pureVectorOfAmplitudeMatrix B hBtrace
  have hΨ : Ψ.Purifies ρ := pureVectorOfAmplitudeMatrix_purifies hAgram hAtrace
  have hΦ : Φ.Purifies τ := pureVectorOfAmplitudeMatrix_purifies hBgram hBtrace
  have habs :
      Complex.abs X.trace = Complex.abs (Ψ.overlap Φ) :=
    abs_trace_eq_abs_overlap_of_amplitude_gram hAB
  rw [habs]
  exact pureVector_abs_overlap_le_fidelity hΨ hΦ

theorem ConditionalMaxFidelityBlockFeasible.trace_re_le_fidelity [Nonempty a]
    {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    X.trace.re ≤ ρ.fidelity ((maximallyMixed a).prod σ) :=
  (Complex.re_le_norm X.trace).trans hX.abs_trace_le_fidelity

theorem ConditionalMaxFidelityBlockFeasible.blockValue_le_fidelity [Nonempty a]
    {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    conditionalMaxFidelityBlockValue X ≤
      ρ.fidelity ((maximallyMixed a).prod σ) := by
  simpa [conditionalMaxFidelityBlockValue] using hX.trace_re_le_fidelity

theorem ConditionalMaxFidelityBlockFeasible.blockExponentValue_le_exponentCandidate
    [Nonempty a] {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    conditionalMaxFidelityBlockExponentValue (a := a) X ≤
      ρ.conditionalMaxEntropyExponentCandidate (a := a) σ := by
  rw [conditionalMaxFidelityBlockExponentValue_eq,
    conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity,
    State.squaredFidelity_eq_fidelity_sq]
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by exact_mod_cast Nat.zero_le _
  have habs_sq :
      X.trace.re ^ 2 ≤ ρ.fidelity ((maximallyMixed a).prod σ) ^ 2 := by
    have hre_abs : |X.trace.re| ≤ Complex.abs X.trace :=
      Complex.abs_re_le_norm X.trace
    have hle_abs : |X.trace.re| ≤ ρ.fidelity ((maximallyMixed a).prod σ) :=
      hre_abs.trans hX.abs_trace_le_fidelity
    have hleft : 0 ≤ |X.trace.re| := abs_nonneg _
    have hright : 0 ≤ ρ.fidelity ((maximallyMixed a).prod σ) :=
      traceNorm_nonneg _
    have hsquare := (sq_le_sq₀ hleft hright).mpr hle_abs
    simpa [sq_abs] using hsquare
  exact mul_le_mul_of_nonneg_left habs_sq hcard_nonneg

/-- Unitary polar factors produce feasible points of the fidelity block SDP:
`X = √ρ U √(π_A ⊗ σ_B)`. -/
theorem ConditionalMaxFidelityBlockFeasible.of_unitary_sqrt [Nonempty a]
    (ρ : State (Prod a b)) (σ : State b)
    (U : Matrix.unitaryGroup (Prod a b) ℂ) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ
      (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) *
        ((maximallyMixed a).prod σ).sqrtMatrix) := by
  let τ : State (Prod a b) := (maximallyMixed a).prod σ
  let H : CMatrix (Sum (Prod a b) (Prod a b)) :=
    Matrix.fromBlocks (1 : CMatrix (Prod a b)) (U : CMatrix (Prod a b))
      (star (U : CMatrix (Prod a b))) 1
  let S : CMatrix (Sum (Prod a b) (Prod a b)) :=
    Matrix.fromBlocks ρ.sqrtMatrix 0 0 τ.sqrtMatrix
  have hH : H.PosSemidef := by
    simpa [H] using cMatrix_fromBlocks_unitary_posSemidef U
  have hconj : (S * H * star S).PosSemidef := by
    simpa [Matrix.mul_assoc] using hH.mul_mul_conjTranspose_same S
  have hEq :
      S * H * star S =
        (Matrix.fromBlocks ρ.matrix
          (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix)
          (star (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix))
          τ.matrix : CMatrix (Sum (Prod a b) (Prod a b))) := by
    have hρH : ρ.sqrtMatrixᴴ = ρ.sqrtMatrix := ρ.sqrtMatrix_isHermitian.eq
    have hτH : τ.sqrtMatrixᴴ = τ.sqrtMatrix := τ.sqrtMatrix_isHermitian.eq
    have hρsq : ρ.sqrtMatrix * ρ.sqrtMatrix = ρ.matrix := ρ.sqrtMatrix_mul_self
    have hτsq : τ.sqrtMatrix * τ.sqrtMatrix = τ.matrix := τ.sqrtMatrix_mul_self
    dsimp [S, H]
    change
      Matrix.fromBlocks ρ.sqrtMatrix 0 0 τ.sqrtMatrix *
          Matrix.fromBlocks (1 : CMatrix (Prod a b)) (U : CMatrix (Prod a b))
            (star (U : CMatrix (Prod a b))) 1 *
            (Matrix.fromBlocks ρ.sqrtMatrix 0 0 τ.sqrtMatrix)ᴴ =
        (Matrix.fromBlocks ρ.matrix
          (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix)
          (star (ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix))
          τ.matrix :
          CMatrix (Sum (Prod a b) (Prod a b)))
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
    {ρ : State (Prod a b)} {σ : State b} {X : CMatrix (Prod a b)}
    {c : ℂ} (hc : c * star c = 1)
    (hX : ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X) :
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ (c • X) := by
  let D : CMatrix (Sum (Prod a b) (Prod a b)) :=
    Matrix.fromBlocks (1 : CMatrix (Prod a b)) 0 0
      ((star c) • (1 : CMatrix (Prod a b)))
  have hc'' : c * (starRingEnd ℂ) c = 1 := by
    simpa using hc
  have hconj :
      (D *
          (Matrix.fromBlocks ρ.matrix X (star X) ((maximallyMixed a).prod σ).matrix :
            CMatrix (Sum (Prod a b) (Prod a b))) *
            star D).PosSemidef :=
    hX.mul_mul_conjTranspose_same D
  have hEq :
      D *
          (Matrix.fromBlocks ρ.matrix X (star X) ((maximallyMixed a).prod σ).matrix :
            CMatrix (Sum (Prod a b) (Prod a b))) *
            star D =
        (Matrix.fromBlocks ρ.matrix (c • X) (star (c • X))
          ((maximallyMixed a).prod σ).matrix :
          CMatrix (Sum (Prod a b) (Prod a b))) := by
    dsimp [D]
    simp_rw [Matrix.star_eq_conjTranspose]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;> simp [← mul_assoc, hc'']
  simpa [ConditionalMaxFidelityBlockFeasible, hEq] using hconj

/-- For each side state `σ_B`, the fidelity block SDP has a feasible point
whose absolute trace objective attains the root fidelity
`F(ρ_AB, π_A ⊗ σ_B)`. -/
theorem exists_ConditionalMaxFidelityBlockFeasible_abs_trace_eq_fidelity
    [Nonempty a] (ρ : State (Prod a b)) (σ : State b) :
    ∃ X : CMatrix (Prod a b),
      ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
        Complex.abs X.trace =
          ρ.fidelity ((maximallyMixed a).prod σ) := by
  let τ : State (Prod a b) := (maximallyMixed a).prod σ
  obtain ⟨U, hU⟩ :=
    traceNorm_variational_exists_unitary_abs_trace (τ.sqrtMatrix * ρ.sqrtMatrix)
  let X : CMatrix (Prod a b) := ρ.sqrtMatrix * (U : CMatrix (Prod a b)) * τ.sqrtMatrix
  refine ⟨X, ?_, ?_⟩
  · exact ConditionalMaxFidelityBlockFeasible.of_unitary_sqrt (a := a) ρ σ U
  · have htrace :
        X.trace = ((τ.sqrtMatrix * ρ.sqrtMatrix) * (U : CMatrix (Prod a b))).trace := by
      calc
        X.trace = ((ρ.sqrtMatrix * (U : CMatrix (Prod a b))) * τ.sqrtMatrix).trace := by
          simp [X, Matrix.mul_assoc]
        _ = (τ.sqrtMatrix * (ρ.sqrtMatrix * (U : CMatrix (Prod a b)))).trace := by
          rw [Matrix.trace_mul_comm]
        _ = ((τ.sqrtMatrix * ρ.sqrtMatrix) * (U : CMatrix (Prod a b))).trace := by
          rw [Matrix.mul_assoc]
    have hconj :
        τ.sqrtMatrix * ρ.sqrtMatrix =
          Matrix.conjTranspose (ρ.sqrtMatrix * τ.sqrtMatrix) := by
      rw [Matrix.conjTranspose_mul, ρ.sqrtMatrix_isHermitian.eq,
        τ.sqrtMatrix_isHermitian.eq]
    calc
      Complex.abs X.trace =
          Complex.abs (((τ.sqrtMatrix * ρ.sqrtMatrix) *
            (U : CMatrix (Prod a b))).trace) := by rw [htrace]
      _ = traceNorm (τ.sqrtMatrix * ρ.sqrtMatrix) := hU
      _ = traceNorm (ρ.sqrtMatrix * τ.sqrtMatrix) := by
        rw [hconj, traceNorm_conjTranspose]
      _ = ρ.fidelity τ := by rfl

/-- For each side state `σ_B`, the fidelity block SDP has a feasible point
whose real trace objective attains the root fidelity. -/
theorem exists_ConditionalMaxFidelityBlockFeasible_trace_re_eq_fidelity
    [Nonempty a] (ρ : State (Prod a b)) (σ : State b) :
    ∃ X : CMatrix (Prod a b),
      ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
        conditionalMaxFidelityBlockValue X =
          ρ.fidelity ((maximallyMixed a).prod σ) := by
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
      _ = Complex.abs X.trace := hcTrace
      _ = ρ.fidelity ((maximallyMixed a).prod σ) := hXtrace

/-- Feasible objective values for the block-SDP representation of the
conditional max-fidelity endpoint. -/
def conditionalMaxFidelityBlockValueSet [Nonempty a]
    (ρ : State (Prod a b)) : Set ℝ :=
  {v : ℝ | ∃ σ : State b, ∃ X : CMatrix (Prod a b),
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
      v = conditionalMaxFidelityBlockValue X}

/-- Squared and dimension-scaled feasible endpoint values for the block-SDP
representation. -/
def conditionalMaxFidelityBlockExponentValueSet [Nonempty a]
    (ρ : State (Prod a b)) : Set ℝ :=
  {v : ℝ | ∃ σ : State b, ∃ X : CMatrix (Prod a b),
    ConditionalMaxFidelityBlockFeasible (a := a) ρ σ X ∧
      v = conditionalMaxFidelityBlockExponentValue (a := a) X}

/-- Every definition-level max-entropy exponent candidate is realized by the
block-SDP endpoint surface. -/
theorem conditionalMaxEntropyExponentValueSet_subset_conditionalMaxFidelityBlockExponentValueSet
    [Nonempty a] (ρ : State (Prod a b)) :
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
  rw [State.squaredFidelity_eq_fidelity_sq]

theorem conditionalMaxFidelityBlockValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxFidelityBlockValueSet (a := a)).Nonempty := by
  refine ⟨0, maximallyMixed b, 0, ?_, ?_⟩
  · exact ρ.ConditionalMaxFidelityBlockFeasible_zero (a := a) (maximallyMixed b)
  · simp [conditionalMaxFidelityBlockValue]

theorem conditionalMaxFidelityBlockExponentValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)).Nonempty := by
  refine ⟨0, maximallyMixed b, 0, ?_, ?_⟩
  · exact ρ.ConditionalMaxFidelityBlockFeasible_zero (a := a) (maximallyMixed b)
  · simp [conditionalMaxFidelityBlockExponentValue, conditionalMaxFidelityBlockValue]

theorem conditionalMaxEntropyExponentValueSet_eq_card_mul_fidelityValueSet
    [Nonempty a] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyExponentValueSet (a := a) =
      (fun x : ℝ => (Fintype.card a : ℝ) * x) ''
        ρ.conditionalMaxEntropyFidelityValueSet (a := a) := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨ρ.squaredFidelity ((maximallyMixed a).prod σ), ?_, ?_⟩
    · exact ⟨σ, rfl⟩
    · exact (conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
        (a := a) ρ σ
      ).symm
  · rintro ⟨y, ⟨σ, rfl⟩, rfl⟩
    refine ⟨σ, ?_⟩
    exact (conditionalMaxEntropyExponentCandidate_eq_card_mul_squaredFidelity
      (a := a) ρ σ).symm

theorem conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
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
def conditionalMaxEntropyPositiveExponentValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {x : ℝ | ∃ σ : State b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      x = ρ.conditionalMaxEntropyExponentCandidate (a := a) σ}

/-- Definition-level max-entropy candidates whose raw exponent is strictly
positive. -/
def conditionalMaxEntropyPositiveValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {h : ℝ | ∃ σ : State b,
    0 < ρ.conditionalMaxEntropyExponentCandidate (a := a) σ ∧
      h = ρ.conditionalMaxEntropyCandidate σ}

/-- Compatibility name for the positive-candidate conditional max-entropy.

After the real-valued convention correction, this agrees with
`conditionalMaxEntropy`; the separate name remains useful for endpoint-duality
proofs that explicitly expose the positive raw exponent. -/
def conditionalMaxEntropyPositive (ρ : State (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveValueSet (a := a))

/-- The positive-candidate raw endpoint exponent. -/
def conditionalMaxEntropyPositiveExponent (ρ : State (Prod a b)) : ℝ :=
  sSup (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))

theorem conditionalMaxEntropyPositiveExponentValueSet_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) (maximallyMixed b),
    maximallyMixed b, ρ.conditionalMaxEntropyExponentCandidate_maximallyMixed_pos (a := a), rfl⟩

theorem conditionalMaxEntropyPositiveExponentValueSet_bddAbove
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a)) := by
  refine ⟨(Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ), ?_⟩
  intro x hx
  rcases hx with ⟨σ, _hpos, rfl⟩
  exact ρ.conditionalMaxEntropyExponentCandidate_le_card (a := a) σ

theorem conditionalMaxEntropyExponentValueSet_bddAbove
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxEntropyExponentValueSet (a := a)) := by
  refine ⟨(Fintype.card (Prod a b) : ℝ) * (Fintype.card a : ℝ), ?_⟩
  intro x hx
  rcases hx with ⟨σ, rfl⟩
  exact ρ.conditionalMaxEntropyExponentCandidate_le_card (a := a) σ

theorem conditionalMaxEntropyExponentValueSet_nonempty
    [Nonempty b] (ρ : State (Prod a b)) :
    (ρ.conditionalMaxEntropyExponentValueSet (a := a)).Nonempty :=
  ⟨ρ.conditionalMaxEntropyExponentCandidate (a := a) (maximallyMixed b),
    maximallyMixed b, rfl⟩

theorem ConditionalMaxFidelityBlockFeasible.blockExponentValue_le_conditionalMaxEntropyExponent
    [Nonempty a] [Nonempty b] {ρ : State (Prod a b)} {σ : State b}
    {X : CMatrix (Prod a b)}
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
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    sSup (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  refine csSup_le (ρ.conditionalMaxFidelityBlockExponentValueSet_nonempty (a := a)) ?_
  intro v hv
  rcases hv with ⟨σ, X, hX, rfl⟩
  exact hX.blockExponentValue_le_conditionalMaxEntropyExponent

/-- The block-SDP endpoint surface is bounded above by the definition-level
conditional max-entropy exponent. -/
theorem conditionalMaxFidelityBlockExponentValueSet_bddAbove
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) := by
  refine ⟨ρ.conditionalMaxEntropyExponent (a := a), ?_⟩
  intro x hx
  rcases hx with ⟨σ, X, hX, rfl⟩
  exact hX.blockExponentValue_le_conditionalMaxEntropyExponent

/-- The fidelity block-SDP endpoint has the same optimum as the
definition-level conditional max-entropy exponent. -/
theorem sSup_conditionalMaxFidelityBlockExponentValueSet_eq_conditionalMaxEntropyExponent
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
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
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    (Fintype.card a : ℝ) *
        sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) =
      sSup (ρ.conditionalMaxFidelityBlockExponentValueSet (a := a)) := by
  rw [sSup_conditionalMaxFidelityBlockExponentValueSet_eq_conditionalMaxEntropyExponent
    (a := a) ρ]
  exact (conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet
    (a := a) ρ).symm

theorem conditionalMaxEntropyPositiveExponent_le_exponent
    [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveExponent (a := a) ≤
      ρ.conditionalMaxEntropyExponent (a := a) := by
  rw [conditionalMaxEntropyPositiveExponent, conditionalMaxEntropyExponent]
  refine csSup_le (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a)) ?_
  intro x hx
  rcases hx with ⟨σ, _hpos, rfl⟩
  exact le_csSup (ρ.conditionalMaxEntropyExponentValueSet_bddAbove (a := a))
    ⟨σ, rfl⟩

theorem conditionalMaxEntropyExponent_le_positiveExponent
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
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
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyExponent (a := a) =
      ρ.conditionalMaxEntropyPositiveExponent (a := a) :=
  le_antisymm
    (ρ.conditionalMaxEntropyExponent_le_positiveExponent (a := a))
    (ρ.conditionalMaxEntropyPositiveExponent_le_exponent (a := a))

theorem conditionalMaxEntropyExponent_pos
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    0 < ρ.conditionalMaxEntropyExponent (a := a) := by
  rw [ρ.conditionalMaxEntropyExponent_eq_positiveExponent (a := a)]
  rcases ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a) with ⟨x, hx⟩
  rcases hx with ⟨σ, hσpos, rfl⟩
  exact lt_of_lt_of_le hσpos
    (le_csSup (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))
      ⟨σ, hσpos, rfl⟩)

theorem conditionalMaxEntropyPositiveValueSet_eq_log2_image
    (ρ : State (Prod a b)) :
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

/-- Positive endpoint candidates are definition-level conditional max-entropy
candidates. After the convention correction this is essentially an identity
of candidate sets, kept as a monotonicity helper for existing proofs. -/
theorem conditionalMaxEntropyPositiveValueSet_subset_conditionalMaxEntropyValueSet
    (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositiveValueSet (a := a) ⊆
      ρ.conditionalMaxEntropyValueSet (a := a) := by
  intro h hh
  rcases hh with ⟨σ, _hpos, rfl⟩
  exact ⟨σ, _hpos, rfl⟩

theorem conditionalMaxEntropyValueSet_eq_positiveValueSet
    (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyValueSet (a := a) =
      ρ.conditionalMaxEntropyPositiveValueSet (a := a) := rfl

theorem conditionalMaxEntropy_eq_positive [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropy = ρ.conditionalMaxEntropyPositive := by
  rw [conditionalMaxEntropy_eq_sSup_valueSet, conditionalMaxEntropyPositive,
    conditionalMaxEntropyValueSet_eq_positiveValueSet]

/-- The positive-endpoint conditional max-entropy is bounded by the
definition-level value; after the real-valued convention correction these are
definitionally the same candidate set. -/
theorem conditionalMaxEntropyPositive_le_conditionalMaxEntropy
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
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
    (ρ : State (Prod a b))
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
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hbdd : BddAbove (ρ.conditionalMaxEntropyPositiveExponentValueSet (a := a))) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) :=
  ρ.conditionalMaxEntropyPositive_eq_log2_positiveExponent
    (ρ.conditionalMaxEntropyPositiveExponentValueSet_nonempty (a := a)) hbdd

theorem conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyPositiveExponent (a := a)) :=
  ρ.conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_bddAbove
    (ρ.conditionalMaxEntropyPositiveExponentValueSet_bddAbove (a := a))

theorem conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositive =
      log2 (ρ.conditionalMaxEntropyExponent (a := a)) := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_positiveExponent_of_nonempty (a := a),
    ρ.conditionalMaxEntropyExponent_eq_positiveExponent (a := a)]

/-! ## Conditional min-entropy scale -/

/-- Feasibility for the unnormalized side-operator form of conditional
min-entropy:
`ρ_AB ≤ I_A ⊗ T_B`, with `T_B ≥ 0`. -/
def ConditionalMinEntropyScaleFeasible (ρ : State (Prod a b)) (T : CMatrix b) :
    Prop :=
  T.PosSemidef ∧ ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T

@[simp]
theorem ConditionalMinEntropyScaleFeasible_eq
    (ρ : State (Prod a b)) (T : CMatrix b) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ↔
      T.PosSemidef ∧ ρ.matrix ≤ Matrix.kronecker (1 : CMatrix a) T :=
  Iff.rfl

/-- Conditioning-register isometries transport unnormalized conditional-min
feasible side operators.  If `ρ_AB ≤ I_A ⊗ T_B`, then after applying an
isometry `V : B → B⁺` to the conditioning register, the pushed side operator
`V T_B V†` remains feasible. -/
theorem ConditionalMinEntropyScaleFeasible.apply_conditioningIsometry
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    {ρ : State (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T)
    (V : ReferenceIsometry b bPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) (ρ.conditioningIsometryApply V)
      (MatrixMap.ofReferenceIsometry V T) := by
  constructor
  · exact MatrixMap.isCompletelyPositive_mapsPositive
      (MatrixMap.ofReferenceIsometry V)
      (MatrixMap.ofReferenceIsometry_isCompletelyPositive V) T hT.1
  · let Φ : MatrixMap (Prod a b) (Prod a bPlus) :=
      MatrixMap.kron (Channel.idChannel a).map (MatrixMap.ofReferenceIsometry V)
    have hCP : MatrixMap.IsCompletelyPositive Φ :=
      MatrixMap.isCompletelyPositive_kron (Channel.idChannel a).map
        (MatrixMap.ofReferenceIsometry V)
        (Channel.idChannel a).completelyPositive
        (MatrixMap.ofReferenceIsometry_isCompletelyPositive V)
    have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := hT.2
    have hmap := MatrixMap.isCompletelyPositive_mapsPositive Φ hCP
      (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) hdiff
    change ((Matrix.kronecker (1 : CMatrix a)
        (MatrixMap.ofReferenceIsometry V T)) -
        (ρ.conditioningIsometryApply V).matrix).PosSemidef
    rw [conditioningIsometryApply_matrix]
    convert hmap using 1
    simp only [Φ, map_sub]
    rw [MatrixMap.kron_apply_kronecker]
    rw [MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight]
    simp [Channel.idChannel, MatrixMap.ofKraus]

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
    (T : CMatrix (Sum extra b)) (hT : T.PosSemidef) :
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
    {ρ : State (Prod a b)} {TPlus : CMatrix (Sum extra b)}
    (hT : ConditionalMinEntropyScaleFeasible (a := a)
      (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)) TPlus) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ (Matrix.sumBlock22 TPlus) := by
  constructor
  · exact Matrix.sumBlock22_posSemidef hT.1
  · have hsub := hT.2.submatrix (fun x : Prod a b => (x.1, Sum.inr x.2))
    change (Matrix.kronecker (1 : CMatrix a) (Matrix.sumBlock22 TPlus) -
      ρ.matrix).PosSemidef
    convert hsub using 1
    ext x y
    simp [Matrix.kronecker, Matrix.sumBlock22, conditioningIsometryApply_matrix,
      ReferenceIsometry.applyMatrixRight, ReferenceIsometry.rightBlock,
      ReferenceIsometry.sumInr, Matrix.mul_apply]

/-- The raw endpoint scale
`inf {Tr T_B | T_B ≥ 0, ρ_AB ≤ I_A ⊗ T_B}`. -/
def conditionalMinEntropyScale (ρ : State (Prod a b)) : ℝ :=
  sInf {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScale_eq (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScale =
      sInf {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

/-- The unnormalized side-operator scale values
`Tr T_B` with `T_B ≥ 0` and `ρ_AB ≤ I_A ⊗ T_B`. -/
def conditionalMinEntropyScaleValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {t : ℝ | ∃ T : CMatrix b,
    ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re}

@[simp]
theorem conditionalMinEntropyScaleValueSet_eq (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) =
      {t : ℝ | ∃ T : CMatrix b,
        ConditionalMinEntropyScaleFeasible (a := a) ρ T ∧ t = T.trace.re} :=
  rfl

/-- Dual-effect feasibility for the endpoint conditional-min SDP:
`M_AC ≥ 0` and `Tr_A M_AC ≤ I_C`. -/
def ConditionalMinEntropyDualEffectFeasible (M : CMatrix (Prod a b)) : Prop :=
  M.PosSemidef ∧ partialTraceA (a := a) (b := b) M ≤ 1

/-- The linear dual-effect value set for the endpoint conditional-min SDP:
`{Tr(ρ_AB M_AB) | M_AB ≥ 0, Tr_A M_AB ≤ I_B}`. -/
def conditionalMinEntropyDualEffectValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {v : ℝ | ∃ M : CMatrix (Prod a b),
    ConditionalMinEntropyDualEffectFeasible (a := a) M ∧
      v = ((ρ.matrix * M).trace).re}

/-- Reindex an `A ⊗ B` dual effect as the Choi matrix of a map `B → A`. -/
def conditionalMinEntropyDualEffectChoiMatrix (M : CMatrix (Prod a b)) :
    CMatrix (Prod b a) :=
  fun x y => M (x.2, x.1) (y.2, y.1)

/-- The matrix map `B → A` represented by a conditional-min dual effect
`M_AC`. -/
def conditionalMinEntropyDualEffectMatrixMap (M : CMatrix (Prod a b)) :
    MatrixMap b a :=
  MatrixMap.ofChoiMatrix (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b) M)

/-- Transpose-Choi orientation of an `A ⊗ B` dual effect as a map `B → A`.

This is the orientation that pairs directly with the repository's
`MatrixMap.choi` convention and the `AA'` maximally-entangled projector in the
endpoint link-map proof. -/
def conditionalMinEntropyDualEffectTransposeChoiMatrix (M : CMatrix (Prod a b)) :
    CMatrix (Prod b a) :=
  Matrix.transpose (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b) M)

/-- The transpose-Choi matrix map `B → A` induced by a conditional-min dual
effect. -/
def conditionalMinEntropyDualEffectTransposeMatrixMap (M : CMatrix (Prod a b)) :
    MatrixMap b a :=
  MatrixMap.ofChoiMatrix
    (conditionalMinEntropyDualEffectTransposeChoiMatrix (a := a) (b := b) M)

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem conditionalMinEntropyDualEffectChoiMatrix_posSemidef
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b) M).PosSemidef := by
  simpa [conditionalMinEntropyDualEffectChoiMatrix] using
    hM.submatrix (fun x : Prod b a => (x.2, x.1))

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem conditionalMinEntropyDualEffectTransposeChoiMatrix_posSemidef
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    (conditionalMinEntropyDualEffectTransposeChoiMatrix (a := a) (b := b) M).PosSemidef := by
  exact (conditionalMinEntropyDualEffectChoiMatrix_posSemidef
    (a := a) (b := b) hM).transpose

/-- Positive dual effects define Choi-positive, hence completely positive,
finite matrix maps. -/
theorem conditionalMinEntropyDualEffectMatrixMap_isCompletelyPositive
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    MatrixMap.IsCompletelyPositive
      (conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) := by
  exact MatrixMap.ofChoiMatrix_isCompletelyPositive
    (conditionalMinEntropyDualEffectChoiMatrix_posSemidef (a := a) (b := b) hM)

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_isCompletelyPositive
    {M : CMatrix (Prod a b)} (hM : M.PosSemidef) :
    MatrixMap.IsCompletelyPositive
      (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) := by
  exact MatrixMap.ofChoiMatrix_isCompletelyPositive
    (conditionalMinEntropyDualEffectTransposeChoiMatrix_posSemidef
      (a := a) (b := b) hM)

theorem conditionalMinEntropyDualEffectMatrixMap_trace
    (M : CMatrix (Prod a b)) (X : CMatrix b) :
    ((conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) X).trace =
      (X * Matrix.transpose (partialTraceA (a := a) (b := b) M)).trace := by
  classical
  simp [conditionalMinEntropyDualEffectMatrixMap,
    conditionalMinEntropyDualEffectChoiMatrix, Matrix.trace, Matrix.mul_apply,
    partialTraceA]
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
    {M : CMatrix (Prod a b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.IsTraceNonincreasing
      (conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) := by
  intro X hX
  rw [conditionalMinEntropyDualEffectMatrixMap_trace (a := a) (b := b) M X]
  have hcomp : ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M).PosSemidef := by
    simpa [Matrix.le_iff] using hM.2
  have hcompT :
      ((1 : CMatrix b) - Matrix.transpose (partialTraceA (a := a) (b := b) M)).PosSemidef := by
    simpa [Matrix.transpose_sub, Matrix.transpose_one] using hcomp.transpose
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hcompT
  have htrace :
      ((X * ((1 : CMatrix b) -
          Matrix.transpose (partialTraceA (a := a) (b := b) M))).trace).re =
        X.trace.re -
          ((X * Matrix.transpose (partialTraceA (a := a) (b := b) M)).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  rw [htrace] at hnonneg
  linarith

theorem conditionalMinEntropyDualEffectMatrixMap_traceNonincreasingCP
    {M : CMatrix (Prod a b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.TraceNonincreasingCP
      (conditionalMinEntropyDualEffectMatrixMap (a := a) (b := b) M) where
  completelyPositive :=
    conditionalMinEntropyDualEffectMatrixMap_isCompletelyPositive (a := a) (b := b) hM.1
  traceNonincreasing :=
    conditionalMinEntropyDualEffectMatrixMap_traceNonincreasing (a := a) (b := b) hM

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_trace
    (M : CMatrix (Prod a b)) (X : CMatrix b) :
    ((conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) X).trace =
      (X * partialTraceA (a := a) (b := b) M).trace := by
  classical
  simp [conditionalMinEntropyDualEffectTransposeMatrixMap,
    conditionalMinEntropyDualEffectTransposeChoiMatrix,
    conditionalMinEntropyDualEffectChoiMatrix, Matrix.trace, Matrix.mul_apply,
    partialTraceA, Matrix.transpose]
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
    {M : CMatrix (Prod a b)}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M) :
    MatrixMap.IsTraceNonincreasing
      (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b) M) := by
  intro X hX
  rw [conditionalMinEntropyDualEffectTransposeMatrixMap_trace (a := a) (b := b) M X]
  have hcomp : ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M).PosSemidef := by
    simpa [Matrix.le_iff] using hM.2
  have hnonneg := cMatrix_trace_mul_posSemidef_re_nonneg hX hcomp
  have htrace :
      ((X * ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M)).trace).re =
        X.trace.re - ((X * partialTraceA (a := a) (b := b) M).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  rw [htrace] at hnonneg
  linarith

theorem conditionalMinEntropyDualEffectTransposeMatrixMap_traceNonincreasingCP
    {M : CMatrix (Prod a b)}
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
    (K : κ → Matrix a b ℂ) : CMatrix (Prod a b) :=
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
    rw [MatrixMap.IsCompletelyPositive, MatrixMap.choi_ofKraus]
    exact Matrix.posSemidef_sum Finset.univ fun l _ =>
      Matrix.posSemidef_vecMulVec_self_star _
  have hCP :
      MatrixMap.IsCompletelyPositive
        (conditionalMinEntropyDualEffectTransposeMatrixMap (a := a) (b := b)
          (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K)) := by
    simpa [conditionalMinEntropyDualEffectOfKraus_transposeMatrixMap_eq_ofKraus
      (a := a) (b := b) K] using hCPK
  rw [MatrixMap.IsCompletelyPositive, conditionalMinEntropyDualEffectTransposeMatrixMap,
    MatrixMap.choi_ofChoiMatrix] at hCP
  have hchoi :
      (conditionalMinEntropyDualEffectChoiMatrix (a := a) (b := b)
        (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K)).PosSemidef := by
    simpa [conditionalMinEntropyDualEffectTransposeChoiMatrix] using hCP.transpose
  simpa [conditionalMinEntropyDualEffectChoiMatrix] using
    hchoi.submatrix (fun x : Prod a b => (x.2, x.1))

omit [DecidableEq a] [Fintype b] [DecidableEq b] in
theorem partialTraceA_conditionalMinEntropyDualEffectOfKraus
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix a b ℂ) :
    partialTraceA (a := a) (b := b)
        (conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K) =
      Matrix.conjTranspose (MatrixMap.smoothEndpointKrausStack K) *
        MatrixMap.smoothEndpointKrausStack K := by
  classical
  ext z z'
  simp [partialTraceA, conditionalMinEntropyDualEffectOfKraus,
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
  · rw [partialTraceA_conditionalMinEntropyDualEffectOfKraus (a := a) (b := b) K]
    exact hK

theorem exists_krausStack_contraction_conditionalMinEntropyDualEffectTransposeMatrixMap
    {M : CMatrix (Prod a b)}
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
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectValueSet (a := a)).Nonempty := by
  refine ⟨0, 0, ?_, ?_⟩
  · constructor
    · exact Matrix.PosSemidef.zero
    · have hzero :
          partialTraceA (a := a) (b := b) (0 : CMatrix (Prod a b)) = 0 := by
        ext i j
        simp [partialTraceA]
      rw [Matrix.le_iff, hzero]
      simpa using (Matrix.PosSemidef.one : (1 : CMatrix b).PosSemidef)
  · simp

omit [DecidableEq b] in
private theorem partialTraceA_mul_kronecker_one_right
    (X : CMatrix (Prod a b)) (U : CMatrix b) :
    partialTraceA (a := a) (b := b) (X * Matrix.kronecker (1 : CMatrix a) U) =
      partialTraceA (a := a) (b := b) X * U := by
  ext j j'
  simp [partialTraceA, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq b] in
private theorem partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right
    (X : CMatrix (Prod a b)) (U : CMatrix b) :
    ((partialTraceA (a := a) (b := b) X) * U).trace =
      (X * Matrix.kronecker (1 : CMatrix a) U).trace := by
  rw [← partialTraceA_mul_kronecker_one_right X U]
  exact partialTraceA_trace (a := a) (b := b)
    (X * Matrix.kronecker (1 : CMatrix a) U)

omit [DecidableEq b] in
private theorem trace_kronecker_one_mul_eq_trace_mul_partialTraceA
    (M : CMatrix (Prod a b)) (T : CMatrix b) :
    ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re =
      ((T * partialTraceA (a := a) (b := b) M).trace).re := by
  have h₁ :
      (Matrix.kronecker (1 : CMatrix a) T * M).trace =
        (M * Matrix.kronecker (1 : CMatrix a) T).trace := by
    rw [Matrix.trace_mul_comm]
  have h₂ :
      (M * Matrix.kronecker (1 : CMatrix a) T).trace =
        ((partialTraceA (a := a) (b := b) M) * T).trace := by
    exact (partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right
      (a := a) (b := b) M T).symm
  calc
    ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re =
        ((M * Matrix.kronecker (1 : CMatrix a) T).trace).re := by rw [h₁]
    _ = (((partialTraceA (a := a) (b := b) M) * T).trace).re := by rw [h₂]
    _ = ((T * partialTraceA (a := a) (b := b) M).trace).re := by
      rw [Matrix.trace_mul_comm]

/-- Weak duality between the endpoint conditional-min scale side and the
dual-effect SDP side. -/
theorem conditionalMinEntropyDualEffectValue_le_scaleValue
    {ρ : State (Prod a b)} {M : CMatrix (Prod a b)} {T : CMatrix b}
    (hM : ConditionalMinEntropyDualEffectFeasible (a := a) M)
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    ((ρ.matrix * M).trace).re ≤ T.trace.re := by
  have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := hT.2
  have hnonneg₁ := cMatrix_trace_mul_posSemidef_re_nonneg hdiff hM.1
  have hle₁ :
      ((ρ.matrix * M).trace).re ≤
        ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re := by
    have htrace :
        (((Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) * M).trace).re =
          ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re -
            ((ρ.matrix * M).trace).re := by
      simp [Matrix.sub_mul, Matrix.trace_sub]
    linarith
  have hptr_psd : (partialTraceA (a := a) (b := b) M).PosSemidef :=
    partialTraceA_posSemidef hM.1
  have hslack : ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M).PosSemidef := by
    simpa [Matrix.le_iff] using hM.2
  have hnonneg₂ := cMatrix_trace_mul_posSemidef_re_nonneg hT.1 hslack
  have hle₂ :
      ((T * partialTraceA (a := a) (b := b) M).trace).re ≤ T.trace.re := by
    have htrace :
        ((T * ((1 : CMatrix b) - partialTraceA (a := a) (b := b) M)).trace).re =
          T.trace.re -
            ((T * partialTraceA (a := a) (b := b) M).trace).re := by
      simp [Matrix.mul_sub, Matrix.trace_sub]
    linarith
  calc
    ((ρ.matrix * M).trace).re ≤
        ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re := hle₁
    _ = ((T * partialTraceA (a := a) (b := b) M).trace).re :=
        trace_kronecker_one_mul_eq_trace_mul_partialTraceA (a := a) (b := b) M T
    _ ≤ T.trace.re := hle₂

theorem conditionalMinEntropyScale_eq_sInf_scaleValueSet
    (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScale =
      sInf (ρ.conditionalMinEntropyScaleValueSet (a := a)) :=
  rfl

/-- Normalize a positive semidefinite matrix with strictly positive trace into
a finite-dimensional state. -/
def ofPosSemidefTracePos (T : CMatrix b) (hT : T.PosSemidef)
    (htr : 0 < T.trace.re) : State b where
  matrix := (((T.trace.re)⁻¹ : ℝ) : ℂ) • T
  pos := by
    have hscale : (0 : ℂ) ≤ (((T.trace.re)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast inv_nonneg.mpr (le_of_lt htr)
    exact Matrix.PosSemidef.smul hT hscale
  trace_eq_one := by
    rw [Matrix.trace_smul]
    have htrace_real : T.trace = ((T.trace.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using (Matrix.PosSemidef.trace_nonneg hT).2.symm
    rw [htrace_real]
    simp [htr.ne']

@[simp]
theorem ofPosSemidefTracePos_matrix (T : CMatrix b) (hT : T.PosSemidef)
    (htr : 0 < T.trace.re) :
    (ofPosSemidefTracePos T hT htr).matrix =
      (((T.trace.re)⁻¹ : ℝ) : ℂ) • T :=
  rfl

theorem smul_ofPosSemidefTracePos_matrix
    (T : CMatrix b) (hT : T.PosSemidef) (htr : 0 < T.trace.re) :
    ((T.trace.re : ℂ) • (ofPosSemidefTracePos T hT htr).matrix) = T := by
  simp [ofPosSemidefTracePos, smul_smul, htr.ne']

/-- A normalized conditional-min feasible pair gives an unnormalized scale
feasible side operator. -/
theorem conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    ConditionalMinEntropyScaleFeasible (a := a) ρ
      ((Real.rpow 2 (-lam) : ℂ) • σ.matrix) := by
  constructor
  · have hscale : (0 : ℂ) ≤ ((Real.rpow 2 (-lam) : ℝ) : ℂ) := by
      exact_mod_cast (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-lam))
    exact Matrix.PosSemidef.smul σ.pos hscale
  · simpa [ConditionalMinEntropyFeasible, ConditionalMinEntropyScaleFeasible,
      identityTensorStateMatrix, Matrix.kronecker_smul] using h

/-- The trace of the unnormalized side operator induced by a normalized
conditional-min feasible pair is exactly `2^{-λ}`. -/
theorem trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (_h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (((Real.rpow 2 (-lam) : ℂ) • σ.matrix).trace).re = Real.rpow 2 (-lam) := by
  rw [Matrix.trace_smul, σ.trace_eq_one]
  simp

theorem conditionalMinEntropyFeasible_maximallyMixed [Nonempty b]
    (ρ : State (Prod a b)) :
    ConditionalMinEntropyFeasible (a := a) ρ (maximallyMixed b)
      (-log2 (Fintype.card b : ℝ)) := by
  rw [ConditionalMinEntropyFeasible]
  rw [identityTensorStateMatrix_maximallyMixed (a := a) (b := b)]
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
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyScaleValueSet (a := a)).Nonempty := by
  let σ : State b := maximallyMixed b
  let lam : ℝ := -log2 (Fintype.card b : ℝ)
  let T : CMatrix b := (Real.rpow 2 (-lam) : ℂ) • σ.matrix
  have hfeas : ConditionalMinEntropyFeasible (a := a) ρ σ lam :=
    ρ.conditionalMinEntropyFeasible_maximallyMixed (a := a)
  refine ⟨T.trace.re, T, ?_, rfl⟩
  exact conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible hfeas

/-- Weak-duality value-set form:
the dual-effect supremum is bounded by the min-entropy scale infimum. -/
theorem sSup_conditionalMinEntropyDualEffectValueSet_le_conditionalMinEntropyScale
    [Nonempty b] (ρ : State (Prod a b)) :
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
    (ρ : State (Prod a b)) :
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
    CMatrix (Sum (Prod a b) b) →L[ℝ] CMatrix b :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun Z =>
        partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z) + Matrix.sumBlock22 Z
       map_add' := by
        intro X Y
        ext i j
        simp [partialTraceA, Matrix.sumBlock11, Matrix.sumBlock22, Finset.sum_add_distrib,
          add_assoc, add_left_comm, add_comm]
       map_smul' := by
        intro c X
        ext i j
        simp [partialTraceA, Matrix.sumBlock11, Matrix.sumBlock22, Finset.mul_sum] } :
      CMatrix (Sum (Prod a b) b) →ₗ[ℝ] CMatrix b)

/-- The block SDP objective `Z ↦ Re Tr(ρ_AC Z₁₁)`. -/
noncomputable def conditionalMinEntropyDualEffectObjectiveCLM
    (ρ : State (Prod a b)) :
    CMatrix (Sum (Prod a b) b) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun Z => (ρ.matrix * Matrix.sumBlock11 Z).trace
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
        CMatrix (Sum (Prod a b) b) →ₗ[ℝ] ℂ))

@[simp]
theorem conditionalMinEntropyDualEffectObjectiveCLM_apply
    (ρ : State (Prod a b)) (Z : CMatrix (Sum (Prod a b) b)) :
    conditionalMinEntropyDualEffectObjectiveCLM (a := a) ρ Z =
      ((ρ.matrix * Matrix.sumBlock11 Z).trace).re :=
  rfl

/-- Real trace pairing against a fixed side-register matrix.  This local copy
keeps the endpoint SDP layer independent from the cq-guessing module. -/
noncomputable def conditionalMinEntropyTracePairingCLM (T : CMatrix b) :
    CMatrix b →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun A => (T * A).trace
         map_add' := by
          intro A B
          simp [Matrix.mul_add, Matrix.trace_add]
         map_smul' := by
          intro c A
          simp [Matrix.trace_smul, Complex.real_smul] } :
        CMatrix b →ₗ[ℝ] ℂ))

@[simp]
theorem conditionalMinEntropyTracePairingCLM_apply (T A : CMatrix b) :
    conditionalMinEntropyTracePairingCLM T A = ((T * A).trace).re :=
  rfl

/-- The finite-dimensional conic SDP whose primal is the dual-effect endpoint:
maximize `Tr(ρ_AC M)` over `M ≥ 0`, `Tr_A M ≤ I_C`, represented with a PSD
slack block. -/
noncomputable def conditionalMinEntropyDualEffectProgram
    (ρ : State (Prod a b)) :
    SDP.ContinuousConeProgram (CMatrix (Sum (Prod a b) b)) (CMatrix b) where
  K := psdCone (Sum (Prod a b) b)
  A := conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b)
  b := 1
  c := conditionalMinEntropyDualEffectObjectiveCLM (a := a) ρ

/-- The conic primal value set is exactly the dual-effect endpoint value set. -/
theorem conditionalMinEntropyDualEffectProgram_primalValueSet_eq
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet =
      ρ.conditionalMinEntropyDualEffectValueSet (a := a) := by
  classical
  ext v
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    let M : CMatrix (Prod a b) := Matrix.sumBlock11 Z
    have hZpsd : Z.PosSemidef := by
      simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZ.1
    refine ⟨M, ?_, ?_⟩
    · constructor
      · exact Matrix.sumBlock11_posSemidef hZpsd
      · have hSpsd : (Matrix.sumBlock22 Z).PosSemidef :=
          Matrix.sumBlock22_posSemidef hZpsd
        have hconstraint :
            partialTraceA (a := a) (b := b) M + Matrix.sumBlock22 Z =
              (1 : CMatrix b) := by
          simpa [conditionalMinEntropyDualEffectProgram,
            conditionalMinEntropyDualEffectConstraintCLM, M] using hZ.2
        rw [Matrix.le_iff]
        have hEq :
            (1 : CMatrix b) - partialTraceA (a := a) (b := b) M =
              Matrix.sumBlock22 Z := by
          rw [← hconstraint]
          abel
        simpa [hEq] using hSpsd
    · exact (conditionalMinEntropyDualEffectObjectiveCLM_apply (a := a) ρ Z).symm
  · rintro ⟨M, hM, rfl⟩
    let S : CMatrix b := (1 : CMatrix b) - partialTraceA (a := a) (b := b) M
    let Z : CMatrix (Sum (Prod a b) b) := Matrix.fromBlocks M 0 0 S
    refine ⟨Z, ?_, ?_⟩
    · constructor
      · have hS : S.PosSemidef := by
          simpa [S, Matrix.le_iff] using hM.2
        simpa [conditionalMinEntropyDualEffectProgram, Z, psdCone_mem] using
          (cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) (b := b)
            hM.1 hS)
      · have h11 : Matrix.sumBlock11 Z = M := by
          ext i j
          simp [Z, Matrix.sumBlock11]
        have h22 : Matrix.sumBlock22 Z = S := by
          ext i j
          simp [Z, S, Matrix.sumBlock22]
        change partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z) +
            Matrix.sumBlock22 Z = (1 : CMatrix b)
        rw [h11, h22]
        ext i j
        simp [S]
    · change (ρ.matrix * M).trace.re = ρ.conditionalMinEntropyDualEffectObjectiveCLM Z
      rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
      have h11 : Matrix.sumBlock11 Z = M := by
        ext i j
        simp [Z, Matrix.sumBlock11]
      rw [h11]

/-- A feasible min-entropy scale matrix induces a feasible conic dual
functional for the dual-effect SDP. -/
theorem conditionalMinEntropyDualEffectProgram_dualFeasible_of_scaleFeasible
    {ρ : State (Prod a b)} {T : CMatrix b}
    (hT : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).IsDualFeasible
      (conditionalMinEntropyTracePairingCLM T) := by
  classical
  intro Z hZ
  let M : CMatrix (Prod a b) := Matrix.sumBlock11 Z
  let S : CMatrix b := Matrix.sumBlock22 Z
  have hZpsd : Z.PosSemidef := by
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZ
  have hM : M.PosSemidef := Matrix.sumBlock11_posSemidef hZpsd
  have hS : S.PosSemidef := Matrix.sumBlock22_posSemidef hZpsd
  have hdiff : (Matrix.kronecker (1 : CMatrix a) T - ρ.matrix).PosSemidef := hT.2
  have hmain_nonneg := cMatrix_trace_mul_posSemidef_re_nonneg hdiff hM
  have hmain_trace :
      (((Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) * M).trace).re =
        ((T * partialTraceA (a := a) (b := b) M).trace).re -
          ((ρ.matrix * M).trace).re := by
    calc
      (((Matrix.kronecker (1 : CMatrix a) T - ρ.matrix) * M).trace).re =
          (((Matrix.kronecker (1 : CMatrix a) T * M -
              ρ.matrix * M)).trace).re := by
        simp [Matrix.sub_mul]
      _ = ((Matrix.kronecker (1 : CMatrix a) T * M).trace).re -
            ((ρ.matrix * M).trace).re := by
        simp [Matrix.trace_sub]
      _ = ((T * partialTraceA (a := a) (b := b) M).trace).re -
            ((ρ.matrix * M).trace).re := by
        rw [trace_kronecker_one_mul_eq_trace_mul_partialTraceA]
  have hmain :
      ((ρ.matrix * M).trace).re ≤
        ((T * partialTraceA (a := a) (b := b) M).trace).re := by
    linarith
  have hslack_nonneg := cMatrix_trace_mul_posSemidef_re_nonneg hT.1 hS
  calc
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z =
        ((ρ.matrix * M).trace).re := by
      change ρ.conditionalMinEntropyDualEffectObjectiveCLM Z =
        ((ρ.matrix * M).trace).re
      rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
    _ ≤ ((T * partialTraceA (a := a) (b := b) M).trace).re +
          ((T * S).trace).re := by
      linarith
    _ = conditionalMinEntropyTracePairingCLM T
          ((ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z) := by
      have hA :
          (ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z =
            partialTraceA (a := a) (b := b) M + S := by
        change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z =
          partialTraceA (a := a) (b := b) M + S
        rfl
      rw [hA]
      simp [Matrix.mul_add, Matrix.trace_add]

/-- Matrix-order scale values are conic dual values of the dual-effect SDP. -/
theorem conditionalMinEntropyScaleValueSet_subset_dualValueSet
    (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScaleValueSet (a := a) ⊆
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).dualValueSet := by
  rintro value ⟨T, hT, rfl⟩
  refine ⟨conditionalMinEntropyTracePairingCLM T,
    conditionalMinEntropyDualEffectProgram_dualFeasible_of_scaleFeasible (a := a) hT, ?_⟩
  change T.trace.re = conditionalMinEntropyTracePairingCLM T (1 : CMatrix b)
  rw [conditionalMinEntropyTracePairingCLM_apply]
  simp

/-- Testing a conic dual functional on a slack-only block gives positivity. -/
theorem conditionalMinEntropyDualEffectProgram_dualFeasible_slack_nonneg
    (ρ : State (Prod a b)) {y : CMatrix b →L[ℝ] ℝ}
    (hy : (ρ.conditionalMinEntropyDualEffectProgram (a := a)).IsDualFeasible y)
    {A : CMatrix b} (hA : A.PosSemidef) :
    0 ≤ y A := by
  let Z : CMatrix (Sum (Prod a b) b) := Matrix.fromBlocks 0 0 0 A
  have hZpsd : Z.PosSemidef := by
    simpa [Z] using
      (cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) (b := b)
        (Matrix.PosSemidef.zero : (0 : CMatrix (Prod a b)).PosSemidef) hA)
  have hdual := hy Z (by
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZpsd)
  have hobj :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z = 0 := by
    change ρ.conditionalMinEntropyDualEffectObjectiveCLM Z = 0
    rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
    have h11 : Matrix.sumBlock11 Z = (0 : CMatrix (Prod a b)) := by
      ext i j
      simp [Z, Matrix.sumBlock11]
    rw [h11]
    simp
  have hAmap :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z = A := by
    change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z = A
    ext i j
    simp [conditionalMinEntropyDualEffectConstraintCLM, Z, Matrix.sumBlock11,
      Matrix.sumBlock22, partialTraceA]
  simpa [hobj, hAmap] using hdual

/-- Testing a conic dual functional on an effect-only block gives the
pointwise domination inequality. -/
theorem conditionalMinEntropyDualEffectProgram_dualFeasible_effect_le
    (ρ : State (Prod a b)) {y : CMatrix b →L[ℝ] ℝ}
    (hy : (ρ.conditionalMinEntropyDualEffectProgram (a := a)).IsDualFeasible y)
    {A : CMatrix (Prod a b)} (hA : A.PosSemidef) :
    ((ρ.matrix * A).trace).re ≤ y (partialTraceA (a := a) (b := b) A) := by
  let Z : CMatrix (Sum (Prod a b) b) := Matrix.fromBlocks A 0 0 0
  have hZpsd : Z.PosSemidef := by
    simpa [Z] using
      (cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) (b := b)
        hA (Matrix.PosSemidef.zero : (0 : CMatrix b).PosSemidef))
  have hdual := hy Z (by
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZpsd)
  have hobj :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z =
        ((ρ.matrix * A).trace).re := by
    change ρ.conditionalMinEntropyDualEffectObjectiveCLM Z =
      ((ρ.matrix * A).trace).re
    rw [conditionalMinEntropyDualEffectObjectiveCLM_apply]
    have h11 : Matrix.sumBlock11 Z = A := by
      ext i j
      simp [Z, Matrix.sumBlock11]
    rw [h11]
  have hAmap :
      (ρ.conditionalMinEntropyDualEffectProgram (a := a)).A Z =
        partialTraceA (a := a) (b := b) A := by
    change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z =
      partialTraceA (a := a) (b := b) A
    have h11 : Matrix.sumBlock11 Z = A := by
      ext i j
      simp [Z, Matrix.sumBlock11]
    ext i j
    simp [conditionalMinEntropyDualEffectConstraintCLM, Z, h11, Matrix.sumBlock22]
  simpa [hobj, hAmap] using hdual

/-- Every conic dual value is represented by a matrix-order min-entropy scale
feasible point. -/
theorem conditionalMinEntropyDualEffectProgram_dualValueSet_subset_scaleValueSet
    (ρ : State (Prod a b)) :
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
      have hK : (Matrix.kronecker (1 : CMatrix a) T.val).IsHermitian := by
        rw [Matrix.IsHermitian]
        calc
          (Matrix.kronecker (1 : CMatrix a) T.val)ᴴ =
              Matrix.kronecker ((1 : CMatrix a)ᴴ) (T.valᴴ) := by
            simpa [Matrix.kronecker] using
              (Matrix.conjTranspose_kronecker (1 : CMatrix a) T.val)
          _ = Matrix.kronecker (1 : CMatrix a) T.val := by
            rw [Matrix.conjTranspose_one, T.isHermitian.eq]
      have hHerm : (Matrix.kronecker (1 : CMatrix a) T.val - ρ.matrix).IsHermitian :=
        hK.sub ρ.pos.1
      refine (cMatrix_posSemidef_iff_trace_mul_posSemidef_re_nonneg hHerm).2 ?_
      intro A hA
      have heffect := conditionalMinEntropyDualEffectProgram_dualFeasible_effect_le
        (a := a) ρ hy hA
      have hrep := hrep_psd (partialTraceA (a := a) (b := b) A)
        (partialTraceA_posSemidef hA)
      have htrace :
          (((Matrix.kronecker (1 : CMatrix a) T.val - ρ.matrix) * A).trace).re =
            ((T.val * partialTraceA (a := a) (b := b) A).trace).re -
              ((ρ.matrix * A).trace).re := by
        calc
          (((Matrix.kronecker (1 : CMatrix a) T.val - ρ.matrix) * A).trace).re =
              (((Matrix.kronecker (1 : CMatrix a) T.val * A -
                  ρ.matrix * A)).trace).re := by
            simp [Matrix.sub_mul]
          _ = ((Matrix.kronecker (1 : CMatrix a) T.val * A).trace).re -
                ((ρ.matrix * A).trace).re := by
            simp [Matrix.trace_sub]
          _ = ((T.val * partialTraceA (a := a) (b := b) A).trace).re -
                ((ρ.matrix * A).trace).re := by
            rw [trace_kronecker_one_mul_eq_trace_mul_partialTraceA]
      have heffect' :
          ((ρ.matrix * A).trace).re ≤
            ((T.val * partialTraceA (a := a) (b := b) A).trace).re := by
        calc
          ((ρ.matrix * A).trace).re ≤
              y (partialTraceA (a := a) (b := b) A) := heffect
          _ = ((T.val * partialTraceA (a := a) (b := b) A).trace).re := hrep
      linarith
  · have hrep_one : y (1 : CMatrix b) = T.val.trace.re := by
      let X : HermitianMatrix b := ⟨1, Matrix.PosSemidef.one.1⟩
      have h := hTrep X
      simpa [yH, X, tracePairing] using h
    change y (1 : CMatrix b) = T.val.trace.re
    exact hrep_one

/-- The conic and matrix-order dual value sets coincide. -/
theorem conditionalMinEntropyDualEffectProgram_dualValueSet_eq_scaleValueSet
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).dualValueSet =
      ρ.conditionalMinEntropyScaleValueSet (a := a) :=
  Set.Subset.antisymm
    (conditionalMinEntropyDualEffectProgram_dualValueSet_subset_scaleValueSet (a := a) ρ)
    (conditionalMinEntropyScaleValueSet_subset_dualValueSet (a := a) ρ)

/-- The endpoint dual-effect conic primal is feasible. -/
theorem conditionalMinEntropyDualEffectProgram_primalValueSet_nonempty
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet.Nonempty := by
  classical
  let Z : CMatrix (Sum (Prod a b) b) :=
    Matrix.fromBlocks 0 0 0 (1 : CMatrix b)
  refine ⟨(ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValue Z, Z, ?_, rfl⟩
  constructor
  · have hZpsd : Z.PosSemidef := by
      simpa [Z] using
        (cMatrix_fromBlocks_diagonal_posSemidef (a := Prod a b) (b := b)
          (Matrix.PosSemidef.zero : (0 : CMatrix (Prod a b)).PosSemidef)
          (Matrix.PosSemidef.one : (1 : CMatrix b).PosSemidef))
    simpa [conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZpsd
  · change conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z =
      (1 : CMatrix b)
    ext i j
    simp [conditionalMinEntropyDualEffectConstraintCLM, Z, Matrix.sumBlock11,
      Matrix.sumBlock22, partialTraceA]

/-- A concrete scale-feasible point bounds the dual-effect primal value set
above. -/
theorem conditionalMinEntropyDualEffectProgram_primalValueSet_bddAbove
    [Nonempty b] (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet := by
  rcases ρ.conditionalMinEntropyScaleValueSet_nonempty (a := a) with ⟨v, hv⟩
  rcases hv with ⟨T, hT, rfl⟩
  exact (ρ.conditionalMinEntropyDualEffectProgram (a := a)).primalValueSet_bddAbove_of_dualFeasible
    (conditionalMinEntropyDualEffectProgram_dualFeasible_of_scaleFeasible (a := a) hT)

/-- The block SDP constraint preserves trace: `Tr(Tr_A Z₁₁ + Z₂₂) = Tr Z`. -/
theorem conditionalMinEntropyDualEffectConstraint_trace_re
    (Z : CMatrix (Sum (Prod a b) b)) :
    ((conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z).trace).re =
      Z.trace.re := by
  have hptr :
      (partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z)).trace =
        (Matrix.sumBlock11 Z).trace :=
    partialTraceA_trace (a := a) (b := b) (Matrix.sumBlock11 Z)
  have hsplit :
      Z.trace = (Matrix.sumBlock11 Z).trace + (Matrix.sumBlock22 Z).trace := by
    simp [Matrix.trace, Matrix.sumBlock11, Matrix.sumBlock22,
      Fintype.sum_sum_type, add_comm]
  calc
    ((conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) Z).trace).re =
        ((partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z) +
            Matrix.sumBlock22 Z).trace).re := rfl
    _ = ((partialTraceA (a := a) (b := b) (Matrix.sumBlock11 Z)).trace +
          (Matrix.sumBlock22 Z).trace).re := by
      rw [Matrix.trace_add]
    _ = ((Matrix.sumBlock11 Z).trace + (Matrix.sumBlock22 Z).trace).re := by
      rw [hptr]
    _ = Z.trace.re := by rw [hsplit]

set_option maxHeartbeats 900000 in
/-- The dual-effect primal hypograph is closed.  The key finite-dimensional
estimate is that PSD block variables are norm-bounded by the trace of their
constraint value. -/
theorem conditionalMinEntropyDualEffectProgram_hasClosedPrimalHypograph
    (ρ : State (Prod a b)) :
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
    conditionalMinEntropyTracePairingCLM (1 : CMatrix b)
  let oneZ : CMatrix (Sum (Prod a b) b) := 1
  have hZ_norm_le (n : ℕ) :
      ‖Z n‖ ≤ ((‖trCLM‖ * C) * ‖oneZ‖) := by
    have hZpsd : (Z n).PosSemidef := by
      simpa [P, conditionalMinEntropyDualEffectProgram, psdCone_mem] using hZK n
    have hnormZ :=
      norm_le_trace_re_mul_norm_one_of_posSemidef (a := Sum (Prod a b) b) hZpsd
    have htrace_eq :
        (Z n).trace.re = ((ztSeq n).1).trace.re := by
      have hconstraint :
          (ztSeq n).1 = conditionalMinEntropyDualEffectConstraintCLM (a := a) (b := b) (Z n) := by
        simpa [P, conditionalMinEntropyDualEffectProgram] using hA n
      rw [hconstraint]
      exact (conditionalMinEntropyDualEffectConstraint_trace_re (a := a) (b := b) (Z n)).symm
    have htrace_abs :
        ((ztSeq n).1).trace.re ≤ ‖trCLM ((ztSeq n).1)‖ := by
      change ((ztSeq n).1).trace.re ≤ ‖conditionalMinEntropyTracePairingCLM
        (1 : CMatrix b) ((ztSeq n).1)‖
      rw [conditionalMinEntropyTracePairingCLM_apply]
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
      ‖Z n‖ ≤ (Z n).trace.re * ‖(1 : CMatrix (Sum (Prod a b) b))‖ := hnormZ
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
    (ρ : State (Prod a b)) :
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
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    (Fintype.card a : ℝ)⁻¹ ≤ Real.rpow 2 (-lam) := by
  have htrace := trace_re_le_of_le h
  have hleft : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
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
    {ρ : State (Prod a b)} {σ : State b} {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    lam ≤ log2 (Fintype.card a : ℝ) := by
  classical
  haveI : Nonempty a := ⟨(Classical.choice ρ.nonempty).1⟩
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
    (ρ : State (Prod a b)) (σ : State b) (x : a) {lam : ℝ}
    (h : ConditionalMinEntropyFeasible (a := a) ρ σ lam) :
    Classical.block ρ.matrix x x ≤ (Real.rpow 2 (-lam) : ℂ) • σ.matrix := by
  let c : ℂ := (Real.rpow 2 (-lam) : ℂ)
  rw [Matrix.le_iff]
  have hdiff :
      (c • State.identityTensorStateMatrix (a := a) σ - ρ.matrix).PosSemidef := by
    simpa [c, ConditionalMinEntropyFeasible, Matrix.le_iff] using h
  have hblock := hdiff.submatrix (fun i : b => (x, i))
  have hblock_eq :
      Matrix.submatrix
          (c • State.identityTensorStateMatrix (a := a) σ - ρ.matrix)
          (fun i : b => (x, i)) (fun i : b => (x, i)) =
        c • σ.matrix - Classical.block ρ.matrix x x := by
    ext i j
    simp [Classical.block, State.identityTensorStateMatrix, Matrix.kronecker,
      Matrix.kroneckerMap_apply, c]
  rwa [hblock_eq] at hblock

theorem conditionalMinEntropyScaleFeasible_trace_lower_bound [Nonempty a]
    {ρ : State (Prod a b)} {T : CMatrix b}
    (h : ConditionalMinEntropyScaleFeasible (a := a) ρ T) :
    (Fintype.card a : ℝ)⁻¹ ≤ T.trace.re := by
  have htrace := trace_re_le_of_le h.2
  have hleft : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hright :
      (Matrix.kronecker (1 : CMatrix a) T).trace.re =
        (Fintype.card a : ℝ) * T.trace.re := by
    rw [show Matrix.kronecker (1 : CMatrix a) T =
        Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) T by rfl]
    rw [Matrix.trace_kronecker, Matrix.trace_one]
    simp [Complex.mul_re]
  rw [hleft, hright] at htrace
  have hcard_pos : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  rw [inv_le_iff_one_le_mul₀ hcard_pos]
  simpa [mul_comm] using htrace

/-- Feasible conditional-min exponents. -/
def conditionalMinEntropyFeasibleExponentValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {lam : ℝ | ∃ σ : State b, ConditionalMinEntropyFeasible (a := a) ρ σ lam}

/-- The normalized conditional-min feasible exponent set is bounded above. -/
theorem conditionalMinEntropyFeasibleExponentValueSet_bddAbove
    (ρ : State (Prod a b)) :
    BddAbove (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)) := by
  refine ⟨log2 (Fintype.card a : ℝ), ?_⟩
  intro lam hlam
  rcases hlam with ⟨σ, hσ⟩
  exact conditionalMinEntropyFeasible_le_log2_card_left (a := a) hσ

/-- A uniform classical register independent of the side information has
conditional min-entropy at least the logarithm of its alphabet size. -/
theorem conditionalMinEntropyFeasible_maximallyMixed_prod
    [Nonempty a] (σ : State b) :
    ConditionalMinEntropyFeasible (a := a)
      ((State.maximallyMixed a).prod σ) σ (log2 (Fintype.card a : ℝ)) := by
  rw [ConditionalMinEntropyFeasible]
  rw [State.identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod (a := a) σ]
  have hrpow :
      Real.rpow 2 (-(log2 (Fintype.card a : ℝ))) =
        (Fintype.card a : ℝ)⁻¹ := by
    calc
      Real.rpow 2 (-(log2 (Fintype.card a : ℝ))) =
          (Real.rpow 2 (log2 (Fintype.card a : ℝ)))⁻¹ := by
            exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _
      _ = (Fintype.card a : ℝ)⁻¹ := by
            rw [State.rpow_two_log2_card (b := a)]
  have hcard_ne : (Fintype.card a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [hrpow]
  simp [smul_smul, hcard_ne]

/-- The normalized scale values `2^{-λ}` coming from normalized
conditional-min feasible pairs. -/
def conditionalMinEntropyNormalizedScaleValueSet (ρ : State (Prod a b)) : Set ℝ :=
  {t : ℝ | ∃ σ : State b, ∃ lam : ℝ,
    ConditionalMinEntropyFeasible (a := a) ρ σ lam ∧ t = Real.rpow 2 (-lam)}

/-- The infimum of normalized conditional-min scale values. -/
def conditionalMinEntropyNormalizedScale (ρ : State (Prod a b)) : ℝ :=
  sInf (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a))

theorem conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet
    [Nonempty a] (ρ : State (Prod a b)) :
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
    let σ : State b := ofPosSemidefTracePos T hTfeas.1 htr_pos
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
            Matrix.kronecker (1 : CMatrix a) T := by
        rw [identityTensorStateMatrix]
        rw [show Matrix.kronecker (1 : CMatrix a) T =
            Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) T by rfl]
        change ((T.trace.re : ℂ) •
            Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) σ.matrix) =
          Matrix.kroneckerMap (fun x y => x * y) (1 : CMatrix a) T
        rw [← Matrix.kronecker_smul]
        rw [show ((T.trace.re : ℂ) • σ.matrix) = T by
          exact smul_ofPosSemidefTracePos_matrix T hTfeas.1 htr_pos]
      rw [hrpow, hside]
      exact hTfeas.2
    · dsimp [lam]
      rw [neg_neg]
      change T.trace.re = Real.rpow 2 (log2 T.trace.re)
      exact (rpow_two_log2_pos htr_pos).symm
  · rintro ⟨σ, lam, hfeas, rfl⟩
    refine ⟨((Real.rpow 2 (-lam) : ℂ) • σ.matrix), ?_, ?_⟩
    · exact conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible hfeas
    · exact (trace_conditionalMinEntropyScaleFeasible_of_conditionalMinEntropyFeasible hfeas).symm

theorem conditionalMinEntropyScale_eq_normalizedScale
    [Nonempty a] (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropyScale (a := a) =
      ρ.conditionalMinEntropyNormalizedScale (a := a) := by
  rw [conditionalMinEntropyScale_eq_sInf_scaleValueSet, conditionalMinEntropyNormalizedScale,
    conditionalMinEntropyScaleValueSet_eq_normalizedScaleValueSet (a := a)]

theorem conditionalMinEntropyFeasibleExponentValueSet_nonempty [Nonempty b]
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyFeasibleExponentValueSet (a := a)).Nonempty := by
  exact ⟨-log2 (Fintype.card b : ℝ), maximallyMixed b,
    ρ.conditionalMinEntropyFeasible_maximallyMixed (a := a)⟩

theorem conditionalMinEntropyNormalizedScaleValueSet_nonempty [Nonempty b]
    (ρ : State (Prod a b)) :
    (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)).Nonempty := by
  refine ⟨Real.rpow 2 (-(-log2 (Fintype.card b : ℝ))), maximallyMixed b,
    -log2 (Fintype.card b : ℝ), ?_, rfl⟩
  exact ρ.conditionalMinEntropyFeasible_maximallyMixed (a := a)

theorem conditionalMinEntropyNormalizedScaleValueSet_pos
    {ρ : State (Prod a b)} {t : ℝ}
    (ht : t ∈ ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)) :
    0 < t := by
  rcases ht with ⟨σ, lam, hfeas, rfl⟩
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-lam)

theorem conditionalMinEntropyNormalizedScaleValueSet_bddBelow
    (ρ : State (Prod a b)) :
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
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
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
    (ρ : State (Prod a b)) :
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
    {ρ : State (Prod a b)} {t : ℝ}
    (ht : t ∈ ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)) :
    (Fintype.card a : ℝ)⁻¹ ≤ t := by
  rcases ht with ⟨σ, lam, hfeas, rfl⟩
  exact conditionalMinEntropyFeasible_scale_lower_bound (a := a) hfeas

theorem conditionalMinEntropyNormalizedScale_inf_pos [Nonempty a] [Nonempty b]
    (ρ : State (Prod a b)) :
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
    (ρ : State (Prod a b)) :
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
    (ρ : State (Prod a b))
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
    (ρ : State (Prod a b))
    (hne : (ρ.conditionalMinEntropyNormalizedScaleValueSet (a := a)).Nonempty)
    (hinf_pos : 0 < ρ.conditionalMinEntropyNormalizedScale (a := a)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyNormalizedScale (a := a)) :=
  ρ.conditionalMinEntropy_eq_neg_log2_normalizedScale hne
    (ρ.conditionalMinEntropyNormalizedScaleValueSet_bddBelow (a := a)) hinf_pos

theorem conditionalMinEntropy_eq_neg_log2_normalizedScale_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyNormalizedScale (a := a)) :=
  ρ.conditionalMinEntropy_eq_neg_log2_normalizedScale_of_inf_pos
    (ρ.conditionalMinEntropyNormalizedScaleValueSet_nonempty (a := a))
    (ρ.conditionalMinEntropyNormalizedScale_inf_pos (a := a))

theorem conditionalMinEntropy_eq_neg_log2_scale_of_nonempty
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMinEntropy =
      -log2 (ρ.conditionalMinEntropyScale (a := a)) := by
  rw [ρ.conditionalMinEntropy_eq_neg_log2_normalizedScale_of_nonempty (a := a),
    ρ.conditionalMinEntropyScale_eq_normalizedScale (a := a)]

/-- A normalized finite-dimensional conditional min-entropy is bounded above by
the logarithm of the conditioned register dimension. -/
theorem conditionalMinEntropy_le_log2_card_left
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
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
theorem conditionalMinEntropy_maximallyMixed_prod
    [Nonempty a] (σ : State b) :
    ((State.maximallyMixed a).prod σ).conditionalMinEntropy =
      log2 (Fintype.card a : ℝ) := by
  classical
  letI : Nonempty b := σ.nonempty
  have hle :
      ((State.maximallyMixed a).prod σ).conditionalMinEntropy ≤
        log2 (Fintype.card a : ℝ) :=
    ((State.maximallyMixed a).prod σ).conditionalMinEntropy_le_log2_card_left
      (a := a) (b := b)
  have hbdd :
      BddAbove
        (((State.maximallyMixed a).prod σ).conditionalMinEntropyFeasibleExponentValueSet
          (a := a)) := by
    exact conditionalMinEntropyFeasibleExponentValueSet_bddAbove
      (a := a) ((State.maximallyMixed a).prod σ)
  have hmem :
      log2 (Fintype.card a : ℝ) ∈
        ((State.maximallyMixed a).prod σ).conditionalMinEntropyFeasibleExponentValueSet
          (a := a) := by
    exact ⟨σ, conditionalMinEntropyFeasible_maximallyMixed_prod (a := a) σ⟩
  have hge :
      log2 (Fintype.card a : ℝ) ≤
        ((State.maximallyMixed a).prod σ).conditionalMinEntropy := by
    rw [State.conditionalMinEntropy_eq]
    exact le_csSup hbdd hmem
  exact le_antisymm hle hge

/-- One entropy-level consequence of the scale pushforward: applying an
isometry to the conditioning register cannot decrease the conditional
min-entropy.  The reverse inequality requires compressing side operators back
to the isometry range, and is left as the remaining equality direction. -/
theorem conditionalMinEntropy_le_conditioningIsometryApply
    {bPlus : Type*} [Fintype bPlus] [DecidableEq bPlus]
    [Nonempty a] [Nonempty b] [Nonempty bPlus]
    (ρ : State (Prod a b)) (V : ReferenceIsometry b bPlus) :
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
    (ρ : State (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy ≤
      ρ.conditionalMinEntropy := by
  rw [(ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy_eq_neg_log2_scale_of_nonempty
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
    (ρ : State (Prod a b)) :
    (ρ.conditioningIsometryApply (ReferenceIsometry.sumInr extra b)).conditionalMinEntropy =
      ρ.conditionalMinEntropy := by
  exact le_antisymm
    (ρ.conditionalMinEntropy_conditioningIsometryApply_sumInr_le (a := a) (extra := extra))
    (ρ.conditionalMinEntropy_le_conditioningIsometryApply (a := a)
      (ReferenceIsometry.sumInr extra b))

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_exponent_eq_scale
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
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
    [Nonempty b] (ρ : State (Prod a b))
    (hpoint : ∀ σ : State b, ∀ T : CMatrix b,
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
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hpoint : ∀ σ : State b, ∀ T : CMatrix b,
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

This is deliberately only an order-theoretic assembly lemma.  The source-shaped
pure-state proof must still provide the pointwise matrix/SDP inequality used as
`hpoint`. -/
theorem conditionalMinEntropyScale_le_conditionalMaxEntropyExponent_of_feasible_le
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
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
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
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
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hforward : ∀ σ : State b, ∀ T : CMatrix b,
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
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b)) :
    ρ.conditionalMaxEntropyPositive =
      log2 ((Fintype.card a : ℝ) *
        sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a))) := by
  rw [ρ.conditionalMaxEntropyPositive_eq_log2_exponent_of_nonempty (a := a),
    ρ.conditionalMaxEntropyExponent_eq_card_mul_sSup_fidelityValueSet (a := a)]

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_card_mul_sSup_fidelity_eq_scale
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
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
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hscale :
      (Fintype.card a : ℝ) *
          sSup (ρ.conditionalMaxEntropyFidelityValueSet (a := a)) =
        ρ.conditionalMinEntropyScale (a := a)) :
    ρ.conditionalMaxEntropy = -ρ.conditionalMinEntropy := by
  rw [ρ.conditionalMaxEntropy_eq_positive (a := a)]
  exact ρ.conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_card_mul_sSup_fidelity_eq_scale
    (a := a) hscale

theorem conditionalMaxEntropyPositive_eq_neg_conditionalMinEntropy_of_fidelity_endpoint_bounds
    [Nonempty a] [Nonempty b] (ρ : State (Prod a b))
    (hforward : ∀ σ : State b, ∀ T : CMatrix b,
      ConditionalMinEntropyScaleFeasible (a := a) ρ T →
        (Fintype.card a : ℝ) *
          ρ.squaredFidelity ((maximallyMixed a).prod σ) ≤ T.trace.re)
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
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
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
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
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
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        (Fintype.card a : ℝ) *
          ρAB.squaredFidelity ((maximallyMixed a).prod σ) ≤ T.trace.re)
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

For complementary pure marginals, the missing SDP/fidelity proof is expected to
provide `hforward`.  This theorem packages only the order-theoretic
`sSup ≤ sInf` and logarithm transport, keeping the exact remaining proof
obligation visible. -/
theorem conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_cross_fidelity_forward_bound
    [Nonempty a] [Nonempty b] [Nonempty c]
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        (Fintype.card a : ℝ) *
          ρAB.squaredFidelity ((maximallyMixed a).prod σ) ≤ T.trace.re) :
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
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
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
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hdual : ∀ M : CMatrix (Prod a c),
      ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ρAC.matrix * M).trace).re ≤
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
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hdual : ∀ M : CMatrix (Prod a c),
      ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ρAC.matrix * M).trace).re ≤
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
    (ρAB : State (Prod a b)) (ρAC : State (Prod a c))
    (hforward : ∀ σ : State b, ∀ T : CMatrix c,
      ConditionalMinEntropyScaleFeasible (a := a) ρAC T →
        (Fintype.card a : ℝ) *
          ρAB.squaredFidelity ((maximallyMixed a).prod σ) ≤ T.trace.re)
    (hdual : ∀ M : CMatrix (Prod a c),
      ConditionalMinEntropyDualEffectFeasible (a := a) M →
        ((ρAC.matrix * M).trace).re ≤
          (Fintype.card a : ℝ) *
            sSup (ρAB.conditionalMaxEntropyFidelityValueSet (a := a))) :
    ρAB.conditionalMaxEntropyPositive = -ρAC.conditionalMinEntropy :=
  le_antisymm
    (ρAB.conditionalMaxEntropyPositive_le_neg_conditionalMinEntropy_of_cross_fidelity_forward_bound
      (a := a) ρAC hforward)
    (ρAB.neg_conditionalMinEntropy_le_conditionalMaxEntropyPositive_of_cross_dualEffect_bound
      (a := a) ρAC hdual)

end State
end

end QIT
