/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Channels.Diamond
public import QuantumLib.QIT.Measurements.OverlapDomination

/-!
# Coherent rank-one projective measurements

The Stinespring isometry of a rank-one projective measurement copies its
outcome coherently into two classical registers.  This is the finite matrix
form used in Tomamichel2015FiniteResources, `apps.tex:195-212`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker NNReal

namespace QIT

universe u v

noncomputable section

variable {y : Type u} {a : Type v}
variable [Fintype y] [DecidableEq y] [Fintype a] [DecidableEq a]

namespace ProjectiveMeasurement.IsRankOne

variable {P : ProjectiveMeasurement y a}

/-- The coherent measurement matrix sends `|psi>` to
`sum_y <theta_y|psi> |y,y>`. -/
def coherentMatrix (hP : P.IsRankOne) : Matrix (y × y) a ℂ :=
  fun yy i => if yy.1 = yy.2 then star ((hP.vector yy.1).vec i) else 0

/-- The coherent measurement matrix is an isometry. Its proof is derived from
the rank-one effect representation and PVM completeness. -/
def coherentIsometry (hP : P.IsRankOne) : ReferenceIsometry a (y × y) where
  matrix := hP.coherentMatrix
  isometry := by
    classical
    ext i j
    have hsum := congrFun (congrFun P.sum_eq_one i) j
    have hsum' :
        (∑ outcome, (hP.vector outcome).vec i * star ((hP.vector outcome).vec j)) =
          if i = j then (1 : ℂ) else 0 := by
      simpa [hP.effect_eq, Ket.state_matrix, rankOneMatrix_apply,
        Matrix.sum_apply, Matrix.one_apply] using hsum
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    rw [Fintype.sum_prod_type]
    simpa [coherentMatrix, Matrix.one_apply] using hsum'

@[simp]
theorem coherentIsometry_matrix (hP : P.IsRankOne) (yy : y × y) (i : a) :
    hP.coherentIsometry.matrix yy i =
      if yy.1 = yy.2 then star ((hP.vector yy.1).vec i) else 0 :=
  rfl

/-- The matrix element `<theta_y|X|theta_y'>` appearing in the coherent
measurement formula. -/
def coherentBracket (hP : P.IsRankOne) (X : CMatrix a) (i j : y) : ℂ :=
  ∑ k, ∑ l, star ((hP.vector i).vec k) * X k l * (hP.vector j).vec l

/-- The coherent rank-one measurement channel. -/
def coherentChannel (hP : P.IsRankOne) : CPTPMap a (y × y) :=
  CPTPOp.ofReferenceIsometry hP.coherentIsometry

/-- Entrywise form of the coherent measurement channel from `apps.tex:200`. -/
theorem coherentChannel_map_apply (hP : P.IsRankOne) (X : CMatrix a)
    (i j : y × y) :
    hP.coherentChannel.map X i j =
      if i.1 = i.2 ∧ j.1 = j.2 then hP.coherentBracket X i.1 j.1 else 0 := by
  classical
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  by_cases hi : i₁ = i₂
  · subst i₂
    by_cases hj : j₁ = j₂
    · subst j₂
      simp [coherentChannel, CPTPOp.ofReferenceIsometry_map,
        MatrixMap.ofReferenceIsometry_apply, coherentBracket, Matrix.mul_apply,
        Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    · simp [coherentChannel, CPTPOp.ofReferenceIsometry_map,
        MatrixMap.ofReferenceIsometry_apply, coherentIsometry_matrix, Matrix.mul_apply, hj]
  · simp [coherentChannel, CPTPOp.ofReferenceIsometry_map,
      MatrixMap.ofReferenceIsometry_apply, coherentIsometry_matrix, Matrix.mul_apply, hi]

/-- Matrix form of the coherent Stinespring channel in `apps.tex:200`. -/
theorem coherentChannel_map (hP : P.IsRankOne) (X : CMatrix a) :
    hP.coherentChannel.map X =
      ∑ i, ∑ j, Matrix.single (i, i) (j, j) (hP.coherentBracket X i j) := by
  classical
  apply Matrix.ext
  intro i j
  calc
    hP.coherentChannel.map X i j =
        if i.1 = i.2 ∧ j.1 = j.2 then hP.coherentBracket X i.1 j.1 else 0 :=
      hP.coherentChannel_map_apply X i j
    _ = (∑ k, ∑ l, Matrix.single (k, k) (l, l) (hP.coherentBracket X k l)) i j := by
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases hi : i₁ = i₂
      · subst i₂
        by_cases hj : j₁ = j₂
        · subst j₂
          simp only [true_and, if_true, Matrix.sum_apply]
          rw [Finset.sum_eq_single i₁]
          · rw [Finset.sum_eq_single j₁]
            · simp
            · intro j _ hj
              simp [hj]
            · simp
          · intro i _ hi
            simp [hi]
          · simp
        · simp only [true_and, hj, if_false, Matrix.sum_apply]
          symm
          apply Finset.sum_eq_zero
          intro i _
          apply Finset.sum_eq_zero
          intro j _
          by_cases hj₁ : j = j₁
          · subst j
            simp [hj]
          · simp [hj₁]
      · simp only [hi, false_and, if_false, Matrix.sum_apply]
        symm
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        by_cases hi₁ : i = i₁
        · subst i
          simp [hi]
        · simp [hi₁]

omit [DecidableEq y] in
private theorem coherentBracket_self (hP : P.IsRankOne) (X : CMatrix a) (i : y) :
    hP.coherentBracket X i i = (X * P.effects i).trace := by
  classical
  rw [hP.effect_eq]
  simp only [coherentBracket, Ket.state_matrix, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, rankOneMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Tracing out the copied outcome register recovers the ordinary measurement
channel. -/
theorem traceRight_coherentChannel_map (hP : P.IsRankOne) (X : CMatrix a) :
    Matrix.traceRight (hP.coherentChannel.map X) =
      (POVM.measureDiscard P.toPOVM).map X := by
  classical
  rw [POVM.measureDiscard_map]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.traceRight, hP.coherentChannel_map_apply, hP.coherentBracket_self,
      Matrix.sum_apply, Matrix.single_apply]
  · have hleft : ∀ k, ¬(i = k ∧ j = k) := by
      intro k h
      exact hij (h.1.trans h.2.symm)
    have hright : ∀ k, ¬(k = i ∧ k = j) := by
      intro k h
      exact hij (h.1.symm.trans h.2)
    simp [Matrix.traceRight, hP.coherentChannel_map_apply, Matrix.sum_apply,
      hleft, hright]

variable {b : Type*} [Fintype b] [DecidableEq b]

/-- The coherent measurement isometry tensored with the identity on side
information `B`. -/
def coherentSideIsometry (hP : P.IsRankOne) :
    ReferenceIsometry (a × b) ((y × y) × b) :=
  hP.coherentIsometry.prod
    (ReferenceIsometry.ofInjective (fun z : b => z) Function.injective_id)

@[simp]
theorem coherentSideIsometry_matrix (hP : P.IsRankOne)
    (out : (y × y) × b) (input : a × b) :
    hP.coherentSideIsometry.matrix out input =
      if out.1.1 = out.1.2 ∧ out.2 = input.2 then
        star ((hP.vector out.1.1).vec input.1) else 0 := by
  simp only [coherentSideIsometry, ReferenceIsometry.prod, Matrix.kroneckerMap_apply, ReferenceIsometry.ofInjective,
  coherentIsometry_matrix]
  by_cases hdiag : out.1.1 = out.1.2 <;>
    by_cases hside : out.2 = input.2 <;> simp [hdiag, hside]

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- Coherently measure `A` in a pure state `ABC`, retaining the copied outcome
registers and both side-information systems. -/
def coherentKet (hP : P.IsRankOne)
    (ψ : Ket ((a × b) × c)) :
    Ket (((y × y) × b) × c) :=
  hP.coherentSideIsometry.applyKet ψ

/-- Ket form of `|psi⟩ ↦ Σ_y ⟨theta_y|psi⟩ |y,y⟩`. -/
@[simp]
theorem coherentKet_vec (hP : P.IsRankOne)
    (ψ : Ket ((a × b) × c)) (outcome copy : y) (k : b) (l : c) :
    (hP.coherentKet ψ).vec (((outcome, copy), k), l) =
      if outcome = copy then
        ∑ i, star ((hP.vector outcome).vec i) * ψ.vec ((i, k), l)
      else 0 := by
  classical
  simp [coherentKet, ReferenceIsometry.applyKet_vec,
    ReferenceIsometry.applyAmp, Matrix.mulVec, dotProduct,
    coherentSideIsometry_matrix, Fintype.sum_prod_type]
  by_cases hdiag : outcome = copy
  · rw [if_pos hdiag]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single k]
    · simp [hdiag]
    · intro k' _ hk'
      have hne : k ≠ k' := Ne.symm hk'
      simp [hdiag, hne]
    · simp
  · simp [hdiag]

/-- The coherent pure state is the reference-isometry channel applied to the
`AB` side of the original pure state. -/
theorem coherentKet_state_matrix (hP : P.IsRankOne)
    (ψ : Ket ((a × b) × c)) :
    (hP.coherentKet ψ).state.m =
      hP.coherentSideIsometry.applyMatrix ψ.state.m := by
  rw [Ket.state_matrix, Ket.state_matrix]
  exact hP.coherentSideIsometry.rankOne_applyAmp ψ.vec

/-- The `YY'B` marginal is the coherent channel applied to `rho_AB`. -/
theorem coherentKet_marginalYYCopyB (hP : P.IsRankOne)
    (ψ : Ket ((a × b) × c)) :
    (hP.coherentKet ψ).state.traceRight =
      (CPTPOp.ofReferenceIsometry (hP.coherentSideIsometry (b := b)))
        ψ.state.traceRight := by
  apply MState.ext
  rw [MState.traceRight_m, hP.coherentKet_state_matrix]
  change Matrix.traceRight (hP.coherentSideIsometry.applyMatrix ψ.state.m) = _
  rw [ReferenceIsometry.traceRight_applyMatrix, CPTPOp.mat_coe_eq_apply_mat,
    MState.traceRight_m,
    CPTPOp.ofReferenceIsometry_map, MatrixMap.ofReferenceIsometry_apply]

/-- The same `YY'B` marginal in the source association `Y × (Y' × B)`. -/
theorem coherentKet_marginalYCopyB (hP : P.IsRankOne)
    (ψ : Ket ((a × b) × c)) :
    (hP.coherentKet ψ).state.traceRight.reindex (Equiv.prodAssoc y y b) =
      MState.reindex
        ((CPTPOp.ofReferenceIsometry (hP.coherentSideIsometry (b := b))) ψ.state.traceRight)
        (Equiv.prodAssoc y y b) := by
  rw [hP.coherentKet_marginalYYCopyB]

/-- Trace out `B` and the copied register `Y'`, retaining the `YC` marginal. -/
def coherentYCMarginal (hP : P.IsRankOne)
    (ψ : Ket ((a × b) × c)) : MState (y × c) :=
  (hP.coherentKet ψ).state.marginalAC.marginalAC

/-- The `YC` marginal of the coherent pure state is the ordinary `Y`
measurement of the original `AC` marginal. -/
theorem coherentYCMarginal_eq_measure (hP : P.IsRankOne)
    (ψ : Ket ((a × b) × c)) :
    hP.coherentYCMarginal ψ = measureSubsystemState P.toPOVM ψ.state.marginalAC := by
  classical
  apply MState.ext
  simp only [measureSubsystemState, CPTPOp.mat_coe_eq_apply_mat, CPTPOp.prod_map]
  ext ⟨i, l⟩ ⟨j, m⟩
  rw [MatrixMap.kron_idChannel_apply_slice, POVM.measureDiscard_map]
  simp [coherentYCMarginal, MState.marginalAC,
    Ket.state_matrix, rankOneMatrix_apply, coherentKet_vec,
    hP.effect_eq, Matrix.trace, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm]
  by_cases hij : j = i
  · subst j
    rw [Matrix.sum_apply, Finset.sum_eq_single i]
    · simp only [Matrix.single_apply, and_self, if_true]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun (p : a) _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun (k : b) _ => ?_
      rw [map_sum]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun (q : a) _ => ?_
      simp only [map_mul, starRingEnd_self_apply]
      ring
    · intro outcome _ houtcome
      simp [houtcome]
    · simp
  · simp only [hij, if_false, map_zero, mul_zero, Finset.sum_const_zero]
    symm
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro outcome _
    by_cases hi : outcome = i
    · subst outcome
      have hne : i ≠ j := Ne.symm hij
      simp [hne]
    · simp [hi]

/-- `I_Y tensor sigma_{Y'B}`, reindexed to the register order
`(Y tensor Y') tensor B`. -/
def copiedIdentityTensor (σ : CMatrix (y × b)) : CMatrix ((y × y) × b) :=
  Matrix.reindex (Equiv.prodAssoc y y b).symm (Equiv.prodAssoc y y b).symm
    ((1 : CMatrix y) ⊗ₖ σ)

omit [Fintype y] [Fintype b] [DecidableEq b] in
@[simp]
theorem copiedIdentityTensor_apply (σ : CMatrix (y × b))
    (i j : (y × y) × b) :
    copiedIdentityTensor σ i j =
      if i.1.1 = j.1.1 then σ (i.1.2, i.2) (j.1.2, j.2) else 0 := by
  simp [copiedIdentityTensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.one_apply]

omit [DecidableEq b] in
theorem copiedIdentityTensor_posSemidef {σ : CMatrix (y × b)}
    (hσ : σ.PosSemidef) : (copiedIdentityTensor σ).PosSemidef := by
  simpa [copiedIdentityTensor, Matrix.reindex_apply] using
    (Matrix.PosSemidef.one.kronecker hσ).submatrix (Equiv.prodAssoc y y b)

omit [DecidableEq b] in
theorem copiedIdentityTensor_posDef {σ : CMatrix (y × b)} (hσ : σ.PosDef) :
    (copiedIdentityTensor σ).PosDef := by
  simpa [copiedIdentityTensor, Matrix.reindex_apply] using
    (Matrix.PosDef.one.kronecker hσ).submatrix
      (Equiv.injective (Equiv.prodAssoc y y b))

/-- Pull back `I_Y tensor sigma_{Y'B}` through the coherent measurement
isometry `U tensor I_B`. -/
def coherentPullback (hP : P.IsRankOne) (σ : CMatrix (y × b)) :
    CMatrix (a × b) :=
  Matrix.conjTranspose (hP.coherentSideIsometry (b := b)).matrix * copiedIdentityTensor σ *
    (hP.coherentSideIsometry (b := b)).matrix

theorem coherentPullback_posSemidef (hP : P.IsRankOne) {σ : CMatrix (y × b)}
    (hσ : σ.PosSemidef) : (hP.coherentPullback σ).PosSemidef := by
  exact (copiedIdentityTensor_posSemidef hσ).conjTranspose_mul_mul_same
    hP.coherentSideIsometry.matrix

theorem coherentPullback_posDef (hP : P.IsRankOne) {σ : CMatrix (y × b)}
    (hσ : σ.PosDef) : (hP.coherentPullback σ).PosDef := by
  exact (copiedIdentityTensor_posDef hσ).conjTranspose_mul_mul_same
    hP.coherentSideIsometry.matrix_mulVec_injective

/-- The `Y'B` diagonal block of a matrix. -/
def copiedOutcomeBlock (σ : CMatrix (y × b)) (i : y) : CMatrix b :=
  Matrix.of fun k l => σ (i, k) (i, l)

/-- Block expansion of `U†(I_Y tensor sigma_{Y'B})U` from `apps.tex:208-210`. -/
theorem coherentPullback_apply (hP : P.IsRankOne) (σ : CMatrix (y × b))
    (i j : a × b) :
    hP.coherentPullback σ i j =
      ∑ outcome, P.effects outcome i.1 j.1 * (copiedOutcomeBlock σ outcome) i.2 j.2 := by
  classical
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  simp only [coherentPullback, copiedOutcomeBlock, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    coherentSideIsometry_matrix, copiedIdentityTensor_apply]
  simp_rw [hP.effect_eq]
  simp only [Ket.state_matrix, rankOneMatrix_apply]
  simp only [apply_ite, star_star, ite_mul, mul_zero, ite_and]
  simp
  refine Finset.sum_congr rfl fun outcome _ => ?_
  ring

variable {x : Type*} [Fintype x] [DecidableEq x]

omit [DecidableEq y] [DecidableEq x] in
/-- For rank-one effects, the complex trace product is the squared vector overlap. -/
theorem rankOneEffectTrace_eq_overlapSq (hP : P.IsRankOne)
    {R : ProjectiveMeasurement x a} (hR : R.IsRankOne) (i : x) (j : y) :
    (R.effects i * P.effects j).trace =
      ((hR.vector i).overlapSq (hP.vector j) : ℂ) := by
  rw [hR.effect_eq, hP.effect_eq]
  have htrace :
      (rankOneMatrix (hR.vector i).vec * rankOneMatrix (hP.vector j).vec).trace =
        (hR.vector i).overlap (hP.vector j) *
          star ((hR.vector i).overlap (hP.vector j)) := by
    let C : ℂ := (hR.vector i).overlap (hP.vector j)
    change (Matrix.vecMulVec (hR.vector i).vec (fun k => star ((hR.vector i).vec k)) *
        Matrix.vecMulVec (hP.vector j).vec (fun k => star ((hP.vector j).vec k))).trace = _
    rw [Matrix.vecMulVec_mul_vecMulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    change (∑ k, (hR.vector i).vec k * (C * star ((hP.vector j).vec k))) =
      C * star C
    calc
      (∑ k, (hR.vector i).vec k * (C * star ((hP.vector j).vec k))) =
          ∑ k, C * (star ((hP.vector j).vec k) * (hR.vector i).vec k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
      _ = C * (∑ k, star ((hP.vector j).vec k) * (hR.vector i).vec k) := by
            simp [Finset.mul_sum]
      _ = C * star C := by
            congr 1
            simp [C, Ket.overlap, mul_comm]
  simp only [Ket.state_matrix]
  change (rankOneMatrix (hR.vector i).vec * rankOneMatrix (hP.vector j).vec).trace = _
  rw [htrace, Ket.overlapSq_eq_normSq]
  apply Complex.ext
  · simp [Complex.normSq]
  · simp [Complex.mul_im]
    ring

omit [DecidableEq y] [DecidableEq x] in
/-- The source overlap constant is strictly positive on a nonempty quantum
system.  Completeness of the second PVM makes the overlaps against any
rank-one effect sum to one, so at least one pair has positive trace overlap.
This discharges the `c > 0` side condition used in `apps.tex:208-214` from
the measurement data rather than exposing it as a theorem hypothesis. -/
theorem rankOneTraceOverlap_pos [Nonempty a]
    {R : ProjectiveMeasurement x a} (hR : R.IsRankOne)
    (P : ProjectiveMeasurement y a) :
    0 < R.rankOneTraceOverlap P := by
  classical
  have hxcard : 0 < Fintype.card x := by
    by_contra h
    have hcard : Fintype.card x = 0 := Nat.eq_zero_of_not_pos h
    let _ : IsEmpty x := Fintype.card_eq_zero_iff.mp hcard
    have hzero_one : (0 : CMatrix a) = 1 := by
      simpa using R.sum_eq_one
    exact zero_ne_one hzero_one
  let i : x := Classical.choice (Fintype.card_pos_iff.mp hxcard)
  have hsum :
      (Finset.univ.sum fun j : y => ((R.effects i * P.effects j).trace).re) = 1 := by
    calc
      (Finset.univ.sum fun j : y => ((R.effects i * P.effects j).trace).re) =
          ((R.effects i * (Finset.univ.sum fun j : y => P.effects j)).trace).re := by
            rw [Finset.mul_sum, Matrix.trace_sum, ← Complex.re_sum]
      _ = (R.effects i).trace.re := by rw [P.sum_eq_one, mul_one]
      _ = 1 := by
        rw [hR.effect_eq, (hR.vector i).state.tr']
        norm_num
  have hexists : ∃ j : y, 0 < ((R.effects i * P.effects j).trace).re := by
    by_contra h
    push Not at h
    have hnonpos :
        (Finset.univ.sum fun j : y => ((R.effects i * P.effects j).trace).re) ≤ 0 :=
      Finset.sum_nonpos fun j _ => h j
    linarith
  obtain ⟨j, hj⟩ := hexists
  exact lt_of_lt_of_le hj (R.trace_re_le_rankOneTraceOverlap P i j)

/-- Applying a second projective measurement to the coherent pullback gives
the first double-sum form in `apps.tex:210`. -/
theorem measureCoherentPullback_apply (hP : P.IsRankOne)
    (R : ProjectiveMeasurement x a) (σ : CMatrix (y × b))
    (i j : x × b) :
    MatrixMap.kron (POVM.measureDiscard R.toPOVM).map (CPTPOp.id (dIn := b)).map
        (hP.coherentPullback σ) i j =
      if i.1 = j.1 then
        ∑ outcome, (R.effects i.1 * P.effects outcome).trace *
          (copiedOutcomeBlock σ outcome) i.2 j.2
      else 0 := by
  classical
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [POVM.measureDiscard_map]
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.smul_apply, Matrix.single_apply, ↓reduceIte, smul_eq_mul,
        mul_one, true_and]
      have hslice :
          (Matrix.of fun p q => hP.coherentPullback σ (p, k) (q, l)) =
            ∑ outcome, ((copiedOutcomeBlock σ outcome) k l) • P.effects outcome := by
        ext p q
        simp only [Matrix.of_apply]
        rw [hP.coherentPullback_apply]
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun outcome _ => ?_
        ring
      rw [hslice]
      simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul]
      refine Finset.sum_congr rfl fun outcome _ => ?_
      rw [Matrix.trace_mul_comm]
      change copiedOutcomeBlock σ outcome k l *
          (R.effects i * P.effects outcome).trace = _
      ring
    · intro outcome _ houtcome
      simp [houtcome]
    · simp
  · simp only [hij, if_false]
    apply Finset.sum_eq_zero
    intro outcome _
    by_cases hi : outcome = i
    · subst outcome
      simp [hij]
    · simp [hi]

/-- Rank-one specialization of `measureCoherentPullback_apply`, matching the
overlap coefficient in `apps.tex:211`. -/
theorem measureCoherentPullback_rankOne_apply (hP : P.IsRankOne)
    {R : ProjectiveMeasurement x a} (hR : R.IsRankOne) (σ : CMatrix (y × b))
    (i j : x × b) :
    MatrixMap.kron (POVM.measureDiscard R.toPOVM).map (CPTPOp.id (dIn := b)).map
        (hP.coherentPullback σ) i j =
      if i.1 = j.1 then
        ∑ outcome, ((hR.vector i.1).overlapSq (hP.vector outcome) : ℂ) *
          (copiedOutcomeBlock σ outcome) i.2 j.2
      else 0 := by
  rw [hP.measureCoherentPullback_apply]
  split
  · refine Finset.sum_congr rfl fun outcome _ => ?_
    rw [hP.rankOneEffectTrace_eq_overlapSq hR]
  · rfl

/-- The exact double-sum output of the second rank-one measurement from
`apps.tex:210-211`. -/
theorem measureCoherentPullback_rankOne (hP : P.IsRankOne)
    {R : ProjectiveMeasurement x a} (hR : R.IsRankOne) (σ : CMatrix (y × b)) :
    MatrixMap.kron (POVM.measureDiscard R.toPOVM).map (CPTPOp.id (dIn := b)).map
        (hP.coherentPullback σ) =
      ∑ measured, ∑ outcome,
        (hR.vector measured).overlapSq (hP.vector outcome) •
          ((Matrix.single measured measured (1 : ℂ)) ⊗ₖ
            (copiedOutcomeBlock σ outcome)) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [hP.measureCoherentPullback_rankOne_apply hR]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intro measured _ hmeasured
      simp [hmeasured]
    · simp
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro measured _
    by_cases hmeasured : measured = i
    · subst measured
      simp [hij]
    · simp [hmeasured]

end ProjectiveMeasurement.IsRankOne

end

end QIT
