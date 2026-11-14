/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Asymptotic.Typicality
public import QIT.Asymptotic.ClassicalTypicality
public import QIT.States.Product
public import QIT.Information.Entropy.Entropy
public import QIT.Symmetry.UnitaryTwirl
public import QIT.Classical.Bridge
public import QIT.Classical.CQState
public import QIT.Measurements.Projective

/-!
# Conditionally-typical subspace projector

Spectral conditionally-typical projector for a non-iid product state
`⊗_i ρ_i`, the HSW object. The eigenvalue predicate centers at the
per-sequence entropy sum `Σ_i S(ρ_i)`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Eigenvalue typicality for the non-iid product state `⊗_i ρ_i`: `-log₂ μ`
lies within `n δ` of `Σ_i S(ρ_i)`, zero eigenvalues excluded. -/
def conditionallyTypicalEigenvalue {n : ℕ} (states : Fin n → State a) (δ μ : ℝ) : Prop :=
  0 < μ ∧ |(-log2 μ) - ∑ i, (states i).vonNeumann| ≤ (n : ℝ) * δ

/-- Spectral conditionally-typical projector for `⊗_i ρ_i`; eigenvalue
predicate centered at `Σ_i S(ρ_i)`. Source: [Wilde2011Qst, qit-notes.tex:28649-28672]. -/
def conditionallyTypicalSubspaceProjector {n : ℕ} (states : Fin n → State a) (δ : ℝ) :
    CMatrix (TensorPower a n) := by
  classical
  let τ := productState states
  exact spectralPredicateProjector τ.matrix τ.pos.isHermitian
    (fun i => conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i))

/-- Number of selected spectral directions, expressed as a real trace count. -/
def conditionallyTypicalSubspaceDimension {n : ℕ} (states : Fin n → State a) (δ : ℝ) : ℝ := by
  classical
  let τ := productState states
  exact ∑ i : TensorPower a n,
    if conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
    then (1 : ℝ) else 0

/-- Spectral probability weight accepted by the conditionally-typical projector. -/
def conditionallyTypicalSpectralWeight {n : ℕ} (states : Fin n → State a) (δ : ℝ) : ℝ := by
  classical
  let τ := productState states
  exact ∑ i : TensorPower a n,
    if conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
    then τ.pos.isHermitian.eigenvalues i else 0

/-- Spectral probability weight rejected by the conditionally-typical projector. -/
def conditionallyAtypicalSpectralWeight {n : ℕ} (states : Fin n → State a) (δ : ℝ) : ℝ := by
  classical
  let τ := productState states
  exact ∑ i : TensorPower a n,
    if ¬ conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
    then τ.pos.isHermitian.eigenvalues i else 0

/-- Second moment of the centered log-eigenvalue random variable for the
product state `⊗_i ρ_i`, centered at `Σ_i S(ρ_i)`. It is the finite
spectral-distribution quantity that feeds Chebyshev-style concentration
estimates; separate product-spectrum lemmas are needed to turn it into an
explicit variance bound. -/
def conditionalLogDeviationSecondMoment {n : ℕ} (states : Fin n → State a) : ℝ := by
  classical
  let τ := productState states
  exact ∑ i : TensorPower a n,
    let μ := τ.pos.isHermitian.eigenvalues i
    μ * (((-log2 μ) - ∑ j, (states j).vonNeumann) ^ 2)

/-! ## Product-state spectrum bridges -/

/-- Spectrum multiset of a non-iid finite product state, written recursively as
the multiset of products of one-letter eigenvalues. -/
def productSpectrumMultiset : {n : ℕ} → (Fin n → State a) → Multiset ℝ
  | 0, _ => ({1} : Multiset ℝ)
  | n + 1, states =>
      (eigenvalueMultiset (states 0).pos.isHermitian).bind fun μ =>
        (productSpectrumMultiset (fun i : Fin n => states i.succ)).map fun ν => μ * ν

@[simp]
theorem productSpectrumMultiset_zero (states : Fin 0 → State a) :
    productSpectrumMultiset states = ({1} : Multiset ℝ) := rfl

@[simp]
theorem productSpectrumMultiset_succ {n : ℕ} (states : Fin (n + 1) → State a) :
    productSpectrumMultiset states =
      (eigenvalueMultiset (states 0).pos.isHermitian).bind fun μ =>
        (productSpectrumMultiset (fun i : Fin n => states i.succ)).map fun ν => μ * ν :=
  rfl

/-- Eigenvalues of a non-iid finite product state are exactly the products of
the one-letter eigenvalues, with multiplicity. -/
theorem eigenvalueMultiset_productState :
    {n : ℕ} → (states : Fin n → State a) →
      eigenvalueMultiset ((productState states).pos.isHermitian) =
        productSpectrumMultiset states
  | 0, states => by
      rw [productState_zero states, productSpectrumMultiset_zero]
      have hUnit : (State.unit.matrix : CMatrix (TensorPower a 0)).IsHermitian :=
        State.unit.pos.isHermitian
      have hTraceEq : (State.unit.matrix : CMatrix (TensorPower a 0)).trace =
          ∑ i : TensorPower a 0, (hUnit.eigenvalues i : ℂ) :=
        hUnit.trace_eq_sum_eigenvalues
      have hTraceOne : (State.unit.matrix : CMatrix (TensorPower a 0)).trace = 1 :=
        State.unit.trace_eq_one
      have hEig : hUnit.eigenvalues PUnit.unit = (1 : ℝ) := by
        have hSum : ∑ i : TensorPower a 0, (hUnit.eigenvalues i : ℂ) = 1 := by
          rw [← hTraceEq, hTraceOne]
        have hSum' : ((hUnit.eigenvalues PUnit.unit : ℝ) : ℂ) = 1 := by
          simpa [TensorPower] using hSum
        exact Complex.ofReal_injective hSum'
      show eigenvalueMultiset hUnit = ({1} : Multiset ℝ)
      rw [eigenvalueMultiset]
      simp [hEig]
  | n + 1, states => by
      rw [productState_succ, productSpectrumMultiset_succ]
      have hKron : eigenvalueMultiset
          (kronecker_isHermitian (states 0).matrix
            (productState fun i : Fin n => states i.succ).matrix
            (states 0).pos.isHermitian
            (productState fun i : Fin n => states i.succ).pos.isHermitian) =
          (eigenvalueMultiset (states 0).pos.isHermitian).bind fun μ =>
            (eigenvalueMultiset
              (productState fun i : Fin n => states i.succ).pos.isHermitian).map
              fun ν => μ * ν :=
        eigenvalueMultiset_kronecker (states 0).matrix
          (productState fun i : Fin n => states i.succ).matrix
          (states 0).pos.isHermitian
          (productState fun i : Fin n => states i.succ).pos.isHermitian
      show eigenvalueMultiset
          (kronecker_isHermitian (states 0).matrix
            (productState fun i : Fin n => states i.succ).matrix
            (states 0).pos.isHermitian
            (productState fun i : Fin n => states i.succ).pos.isHermitian) = _
      rw [hKron, eigenvalueMultiset_productState (fun i : Fin n => states i.succ)]

/-- The spectral definition of the product centered log-deviation second moment,
rewritten over the recursive product-spectrum multiset. -/
theorem conditionalLogDeviationSecondMoment_eq_productSpectrum {n : ℕ}
    (states : Fin n → State a) :
    conditionalLogDeviationSecondMoment states =
      (Multiset.map
        (fun μ => μ * (((-log2 μ) - ∑ j, (states j).vonNeumann) ^ 2))
        (productSpectrumMultiset states)).sum := by
  classical
  unfold conditionalLogDeviationSecondMoment
  rw [Finset.sum_eq_multiset_sum]
  conv_lhs =>
    rw [show (fun i : TensorPower a n =>
        let μ := (productState states).pos.isHermitian.eigenvalues i
        μ * ((-log2 μ - ∑ j, (states j).vonNeumann) ^ 2)) =
          (fun μ => μ * ((-log2 μ - ∑ j, (states j).vonNeumann) ^ 2)) ∘
            (productState states).pos.isHermitian.eigenvalues from rfl]
  rw [← Multiset.map_map]
  rw [show Multiset.map (productState states).pos.isHermitian.eigenvalues
        Finset.univ.val =
      eigenvalueMultiset ((productState states).pos.isHermitian) from rfl]
  rw [eigenvalueMultiset_productState states]

/-- One-letter centered log-eigenvalue second moment, over the actual spectrum
of a state rather than over a tensor power. -/
def stateLogDeviationSecondMoment (ρ : State a) : ℝ := by
  classical
  exact ∑ i : a,
    let μ := ρ.pos.isHermitian.eigenvalues i
    μ * (((-log2 μ) - ρ.vonNeumann) ^ 2)

/-- Multiset form of the one-letter centered log-eigenvalue second moment. -/
theorem stateLogDeviationSecondMoment_eq_eigenvalueMultiset (ρ : State a) :
    stateLogDeviationSecondMoment ρ =
      (Multiset.map (fun μ => μ * (((-log2 μ) - ρ.vonNeumann) ^ 2))
        (eigenvalueMultiset ρ.pos.isHermitian)).sum := by
  classical
  unfold stateLogDeviationSecondMoment
  rw [Finset.sum_eq_multiset_sum]
  conv_lhs =>
    rw [show (fun i : a =>
        let μ := ρ.pos.isHermitian.eigenvalues i
        μ * ((-log2 μ - ρ.vonNeumann) ^ 2)) =
          (fun μ => μ * ((-log2 μ - ρ.vonNeumann) ^ 2)) ∘
            ρ.pos.isHermitian.eigenvalues from rfl]
  rw [← Multiset.map_map]
  rfl

/-- The one-letter centered log-eigenvalue second moment is nonnegative. -/
theorem stateLogDeviationSecondMoment_nonneg (ρ : State a) :
    0 ≤ stateLogDeviationSecondMoment ρ := by
  classical
  unfold stateLogDeviationSecondMoment
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (ρ.pos.eigenvalues_nonneg i) (sq_nonneg _)

/-- Product-spectrum multisets are probability multisets: their entries sum to
one. -/
theorem productSpectrumMultiset_sum :
    {n : ℕ} → (states : Fin n → State a) → (productSpectrumMultiset states).sum = 1
  | 0, states => by simp
  | n + 1, states => by
      rw [productSpectrumMultiset_succ, multiset_sum_bind]
      have ih : (productSpectrumMultiset (fun i : Fin n => states i.succ)).sum = 1 :=
        productSpectrumMultiset_sum (fun i : Fin n => states i.succ)
      have hinner : ∀ μ,
          ((productSpectrumMultiset (fun i : Fin n => states i.succ)).map
              fun ν => μ * ν).sum =
            μ := by
        intro μ
        rw [Multiset.map_congr rfl (fun ν _ => (mul_comm μ ν))]
        rw [multiset_sum_mul_const, Multiset.map_id', ih, one_mul]
      rw [Multiset.map_congr rfl (fun μ _ => hinner μ)]
      rw [Multiset.map_id']
      exact State.eigenvalueMultiset_sum (states 0)

/-- Entries in a product-spectrum multiset are nonnegative. -/
theorem productSpectrumMultiset_nonneg :
    {n : ℕ} → (states : Fin n → State a) → ∀ μ ∈ productSpectrumMultiset states, 0 ≤ μ
  | 0, states, μ, hμ => by
      simp at hμ
      rw [hμ]
      norm_num
  | n + 1, states, μ, hμ => by
      rw [productSpectrumMultiset_succ] at hμ
      simp only [Multiset.mem_bind, Multiset.mem_map] at hμ
      obtain ⟨x, hx, y, hy, rfl⟩ := hμ
      exact mul_nonneg (State.eigenvalueMultiset_nonneg (states 0) x hx)
        (productSpectrumMultiset_nonneg (fun i : Fin n => states i.succ) y hy)

/-- The per-element centered log deviation `cd(S, μ) = -log₂ μ − S`. -/
private def conditionalCenteredLogDev (S μ : ℝ) : ℝ := -log2 μ - S

private lemma conditionalCenteredLogDev_prod {x y Sx Sy : ℝ}
    (hxnn : 0 ≤ x) (hynn : 0 ≤ y) (hxy : 0 < x * y) :
    conditionalCenteredLogDev (Sx + Sy) (x * y) =
      conditionalCenteredLogDev Sx x + conditionalCenteredLogDev Sy y := by
  have hxp : 0 < x := by
    rcases lt_or_eq_of_le hxnn with h | h
    · exact h
    · nlinarith
  have hyp : 0 < y := by
    rcases lt_or_eq_of_le hynn with h | h
    · exact h
    · nlinarith
  have hlog2 : log2 (x * y) = log2 x + log2 y := by
    simp only [log2, log2]
    rw [Real.log_mul (ne_of_gt hxp) (ne_of_gt hyp)]
    ring
  simp only [conditionalCenteredLogDev]
  rw [hlog2]
  ring

/-- The spectrum of a state has zero mean centered log deviation. -/
private lemma eigenvalueMultiset_conditionalCentered_sum (ρ : State a) :
    (Multiset.map (fun μ => μ * conditionalCenteredLogDev ρ.vonNeumann μ)
      (eigenvalueMultiset ρ.pos.isHermitian)).sum = 0 := by
  have hS : ρ.vonNeumann = -((eigenvalueMultiset ρ.pos.isHermitian).map xlog2).sum :=
    State.vonNeumann_eq_neg_sum_eigenvalueMultiset ρ
  have hSum : (eigenvalueMultiset ρ.pos.isHermitian).sum = 1 :=
    State.eigenvalueMultiset_sum ρ
  rw [Multiset.map_congr rfl (fun μ _ => by
      show μ * conditionalCenteredLogDev ρ.vonNeumann μ =
        -(μ * log2 μ) + -(μ * ρ.vonNeumann)
      simp only [conditionalCenteredLogDev]
      ring)]
  rw [multiset_sum_add_distrib]
  have hxl : ∀ μ : ℝ, μ * log2 μ = xlog2 μ := fun μ => by
    by_cases hμ : μ = 0 <;> simp [xlog2, hμ]
  simp only [Multiset.sum_map_neg, Multiset.map_congr rfl (fun μ _ => hxl μ),
    Multiset.map_congr rfl (fun μ _ =>
      (show -(μ * ρ.vonNeumann) = μ * (-ρ.vonNeumann) from by ring))]
  rw [multiset_sum_mul_const, Multiset.map_id', hSum, ← hS]
  ring

/-- The conditionally-typical projector is positive semidefinite. -/
theorem conditionallyTypicalSubspaceProjector_posSemidef {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    (conditionallyTypicalSubspaceProjector states δ).PosSemidef := by
  classical
  unfold conditionallyTypicalSubspaceProjector
  exact spectralPredicateProjector_posSemidef _ _ _

/-- The conditionally-typical projector is Hermitian. -/
theorem conditionallyTypicalSubspaceProjector_isHermitian {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    (conditionallyTypicalSubspaceProjector states δ).IsHermitian :=
  (conditionallyTypicalSubspaceProjector_posSemidef states δ).1

/-- The conditionally-typical projector is idempotent. -/
theorem conditionallyTypicalSubspaceProjector_idempotent {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    conditionallyTypicalSubspaceProjector states δ *
      conditionallyTypicalSubspaceProjector states δ =
      conditionallyTypicalSubspaceProjector states δ := by
  classical
  unfold conditionallyTypicalSubspaceProjector
  exact spectralPredicateProjector_idempotent _ _ _

/-- The conditionally-typical projector is bounded by the identity effect. -/
theorem conditionallyTypicalSubspaceProjector_le_one {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    conditionallyTypicalSubspaceProjector states δ ≤ 1 := by
  classical
  unfold conditionallyTypicalSubspaceProjector
  exact spectralPredicateProjector_le_one _ _ _

/-- Eigenvalues of a non-iid product density matrix sum to one. -/
theorem productState_eigenvalue_sum {n : ℕ} (states : Fin n → State a) :
    ∑ i : TensorPower a n, (productState states).pos.isHermitian.eigenvalues i = 1 := by
  have hc :
      (∑ i : TensorPower a n,
          (((productState states).pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 :=
    (productState states).pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans
      (productState states).trace_eq_one
  rw [← Complex.ofReal_sum] at hc
  exact Complex.ofReal_injective hc

/-- Von Neumann entropy is additive over a non-iid finite product state:
`S(⊗ᵢ ρᵢ) = Σᵢ S(ρᵢ)`.  This is the entropy-center bridge used by the
conditionarly-typical HSW projector. -/
theorem productState_vonNeumann_eq_sum :
    {n : ℕ} → (states : Fin n → State a) →
      (productState states).vonNeumann = ∑ i : Fin n, (states i).vonNeumann
  | 0, states => by
      have hunit : (State.unit : State (TensorPower a 0)).vonNeumann = 0 := by
        have hUnitH : ((State.unit : State (TensorPower a 0)).matrix).IsHermitian :=
          State.unit.pos.isHermitian
        have hTraceEq :
            (State.unit.matrix : CMatrix (TensorPower a 0)).trace =
              ∑ i : TensorPower a 0, (hUnitH.eigenvalues i : ℂ) :=
          hUnitH.trace_eq_sum_eigenvalues
        have hTraceOne : (State.unit.matrix : CMatrix (TensorPower a 0)).trace = 1 :=
          State.unit.trace_eq_one
        have hEig : hUnitH.eigenvalues PUnit.unit = (1 : ℝ) := by
          have hSum : ∑ i : TensorPower a 0, (hUnitH.eigenvalues i : ℂ) = 1 := by
            rw [← hTraceEq, hTraceOne]
          have hSum' : ((hUnitH.eigenvalues PUnit.unit : ℝ) : ℂ) = 1 := by
            simpa [TensorPower] using hSum
          exact Complex.ofReal_injective hSum'
        rw [State.vonNeumann]
        simp [hEig, xlog2, log2]
      simpa [productState_zero states] using hunit
  | n + 1, states => by
      rw [productState_succ]
      change State.vonNeumann ((states 0).prod (productState fun x => states x.succ)) =
        ∑ i : Fin (n + 1), (states i).vonNeumann
      rw [State.vonNeumann_prod (states 0) (productState fun x => states x.succ)]
      rw [productState_vonNeumann_eq_sum (fun i : Fin n => states i.succ)]
      rw [Fin.sum_univ_succ]

/-- Product spectra have zero mean centered log deviation around the sum of
the component entropies. -/
private lemma productSpectrumMultiset_conditionalCentered_sum {n : ℕ}
    (states : Fin n → State a) :
    (Multiset.map (fun μ => μ *
        conditionalCenteredLogDev (∑ i, (states i).vonNeumann) μ)
      (productSpectrumMultiset states)).sum = 0 := by
  have h := eigenvalueMultiset_conditionalCentered_sum (productState states)
  rw [productState_vonNeumann_eq_sum states] at h
  rw [eigenvalueMultiset_productState states] at h
  exact h

private lemma conditional_inner_variance_sum
    (t : Multiset ℝ) (x px : ℝ) (g : ℝ → ℝ) :
    (t.map fun y => x * y * (px + g y) ^ 2).sum =
      x * px ^ 2 * t.sum +
        2 * (x * px) * (t.map fun y => y * g y).sum +
        x * (t.map fun y => y * g y ^ 2).sum := by
  classical
  induction t using Multiset.induction_on with
  | empty => simp
  | cons y t ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      simp only [Multiset.map_cons, Multiset.sum_cons]
      ring

private lemma conditional_kronecker_second_moment_step
    (s t : Multiset ℝ) (q : ℝ → ℝ) (pxOf : ℝ → ℝ) (gyOf : ℝ → ℝ)
    (hsplit : ∀ x ∈ s, ∀ y ∈ t,
      x * y * q (x * y) ^ 2 = x * y * (pxOf x + gyOf y) ^ 2) :
    (Multiset.map (fun μ => μ * q μ ^ 2)
      (s.bind fun x => t.map fun y => x * y)).sum =
      t.sum * (s.map fun x => x * pxOf x ^ 2).sum +
        2 * (s.map fun x => x * pxOf x).sum * (t.map fun y => y * gyOf y).sum +
        s.sum * (t.map fun y => y * gyOf y ^ 2).sum := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons x s ih =>
      have hsplit_tail : ∀ x' ∈ s, ∀ y ∈ t,
          x' * y * q (x' * y) ^ 2 = x' * y * (pxOf x' + gyOf y) ^ 2 := by
        intro x' hx' y hy
        exact hsplit x' (Multiset.mem_cons.mpr (Or.inr hx')) y hy
      rw [Multiset.cons_bind, Multiset.map_add, Multiset.sum_add, ih hsplit_tail]
      have hinner : (t.map fun y => x * y * q (x * y) ^ 2).sum =
          x * (pxOf x) ^ 2 * t.sum +
            2 * (x * pxOf x) * (t.map fun y => y * gyOf y).sum +
            x * (t.map fun y => y * gyOf y ^ 2).sum := by
        have hsp : ∀ y ∈ t,
            x * y * q (x * y) ^ 2 = x * y * (pxOf x + gyOf y) ^ 2 :=
          fun y hy => hsplit x (Multiset.mem_cons.mpr (Or.inl rfl)) y hy
        rw [Multiset.map_congr rfl hsp]
        exact conditional_inner_variance_sum t x (pxOf x) gyOf
      rw [Multiset.map_map,
        show (fun μ => μ * q μ ^ 2) ∘ (fun y => x * y) =
          (fun y => x * y * q (x * y) ^ 2) from rfl]
      rw [hinner]
      simp only [Multiset.map_cons, Multiset.sum_cons]
      ring

private lemma productSpectrum_secondMoment_scaled :
    {n : ℕ} → (states : Fin n → State a) →
      (Multiset.map (fun μ => μ *
          (Real.log 2 *
            conditionalCenteredLogDev (∑ i, (states i).vonNeumann) μ) ^ 2)
        (productSpectrumMultiset states)).sum =
        ∑ i : Fin n,
          (Multiset.map (fun μ => μ *
            (Real.log 2 *
              conditionalCenteredLogDev (states i).vonNeumann μ) ^ 2)
            (eigenvalueMultiset (states i).pos.isHermitian)).sum
  | 0, states => by
      rw [productSpectrumMultiset_zero]
      simp [conditionalCenteredLogDev, log2, Real.log_one]
  | n + 1, states => by
      rw [productSpectrumMultiset_succ]
      have ih := productSpectrum_secondMoment_scaled (fun i : Fin n => states i.succ)
      have hsum_s : (eigenvalueMultiset (states 0).pos.isHermitian).sum = 1 :=
        State.eigenvalueMultiset_sum (states 0)
      have hsum_t :
          (productSpectrumMultiset (fun i : Fin n => states i.succ)).sum = 1 :=
        productSpectrumMultiset_sum (fun i : Fin n => states i.succ)
      have hcenter_s :
          (Multiset.map (fun μ => μ *
              (Real.log 2 * conditionalCenteredLogDev (states 0).vonNeumann μ))
            (eigenvalueMultiset (states 0).pos.isHermitian)).sum = 0 := by
        have h := eigenvalueMultiset_conditionalCentered_sum (states 0)
        rw [Multiset.map_congr rfl (fun μ _ =>
          (show μ * (Real.log 2 * conditionalCenteredLogDev (states 0).vonNeumann μ) =
            Real.log 2 * (μ * conditionalCenteredLogDev (states 0).vonNeumann μ)
            from by ring))]
        rw [Multiset.sum_map_mul_left, h]
        ring
      have hcenter_t :
          (Multiset.map (fun μ => μ *
              (Real.log 2 *
                conditionalCenteredLogDev (∑ i : Fin n, (states i.succ).vonNeumann) μ))
            (productSpectrumMultiset (fun i : Fin n => states i.succ))).sum = 0 := by
        have h := productSpectrumMultiset_conditionalCentered_sum
          (fun i : Fin n => states i.succ)
        rw [Multiset.map_congr rfl (fun μ _ =>
          (show μ *
              (Real.log 2 *
                conditionalCenteredLogDev (∑ i : Fin n, (states i.succ).vonNeumann) μ) =
            Real.log 2 *
              (μ * conditionalCenteredLogDev
                (∑ i : Fin n, (states i.succ).vonNeumann) μ) from by ring))]
        rw [Multiset.sum_map_mul_left, h]
        ring
      have hsplit :
          ∀ x ∈ eigenvalueMultiset (states 0).pos.isHermitian,
            ∀ y ∈ productSpectrumMultiset (fun i : Fin n => states i.succ),
              x * y *
                  (Real.log 2 *
                    conditionalCenteredLogDev
                      (∑ i : Fin (n + 1), (states i).vonNeumann) (x * y)) ^ 2 =
                x * y *
                  (Real.log 2 * conditionalCenteredLogDev (states 0).vonNeumann x +
                    Real.log 2 *
                      conditionalCenteredLogDev
                        (∑ i : Fin n, (states i.succ).vonNeumann) y) ^ 2 := by
        intro x hx y hy
        have hxnn : 0 ≤ x := State.eigenvalueMultiset_nonneg (states 0) x hx
        have hynn : 0 ≤ y :=
          productSpectrumMultiset_nonneg (fun i : Fin n => states i.succ) y hy
        by_cases hxy : 0 < x * y
        · have hcenter :
              conditionalCenteredLogDev
                  (∑ i : Fin (n + 1), (states i).vonNeumann) (x * y) =
                conditionalCenteredLogDev (states 0).vonNeumann x +
                  conditionalCenteredLogDev
                    (∑ i : Fin n, (states i.succ).vonNeumann) y := by
            rw [show (∑ i : Fin (n + 1), (states i).vonNeumann) =
                (states 0).vonNeumann +
                  ∑ i : Fin n, (states i.succ).vonNeumann from by
                  rw [Fin.sum_univ_succ]]
            exact conditionalCenteredLogDev_prod hxnn hynn hxy
          rw [hcenter]
          ring
        · have hzero : x * y = 0 := le_antisymm (not_lt.mp hxy) (mul_nonneg hxnn hynn)
          rw [hzero]
          ring
      rw [conditional_kronecker_second_moment_step
        (eigenvalueMultiset (states 0).pos.isHermitian)
        (productSpectrumMultiset (fun i : Fin n => states i.succ))
        (fun μ => Real.log 2 *
          conditionalCenteredLogDev (∑ i : Fin (n + 1), (states i).vonNeumann) μ)
        (fun μ => Real.log 2 * conditionalCenteredLogDev (states 0).vonNeumann μ)
        (fun μ => Real.log 2 *
          conditionalCenteredLogDev (∑ i : Fin n, (states i.succ).vonNeumann) μ)
        hsplit]
      rw [hsum_t, hsum_s, hcenter_s, hcenter_t]
      rw [ih]
      rw [Fin.sum_univ_succ]
      ring

private lemma conditional_scaledSecondMoment_factor (s : Multiset ℝ) (C : ℝ) :
    (s.map fun μ => μ * (Real.log 2 * conditionalCenteredLogDev C μ) ^ 2).sum =
      (Real.log 2) ^ 2 *
        (s.map fun μ => μ * (conditionalCenteredLogDev C μ) ^ 2).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons μ s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih,
        Multiset.map_cons, Multiset.sum_cons]
      ring

/-- The non-iid product-state centered log-eigenvalue second moment is the sum
of the one-letter centered log-eigenvalue second moments.  This is the
variance-of-a-sum identity needed for HSW conditional typicality; cross terms
vanish because each one-letter centered log-eigenvalue has mean zero. -/
theorem conditionalLogDeviationSecondMoment_eq_sum_stateLogDeviationSecondMoment :
    {n : ℕ} → (states : Fin n → State a) →
      conditionalLogDeviationSecondMoment states =
        ∑ i : Fin n, stateLogDeviationSecondMoment (states i)
  | n, states => by
      have hlog2_ne : (Real.log 2) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (Real.log_pos one_lt_two).ne'
      apply mul_left_cancel₀ hlog2_ne
      calc
        (Real.log 2) ^ 2 * conditionalLogDeviationSecondMoment states
            =
          (Real.log 2) ^ 2 *
            (Multiset.map
              (fun μ => μ *
                (conditionalCenteredLogDev (∑ j : Fin n, (states j).vonNeumann) μ) ^ 2)
              (productSpectrumMultiset states)).sum := by
              rw [conditionalLogDeviationSecondMoment_eq_productSpectrum]
              simp [conditionalCenteredLogDev]
        _ =
          (Multiset.map
            (fun μ => μ *
              (Real.log 2 *
                conditionalCenteredLogDev (∑ j : Fin n, (states j).vonNeumann) μ) ^ 2)
            (productSpectrumMultiset states)).sum := by
              rw [conditional_scaledSecondMoment_factor]
        _ =
          ∑ i : Fin n,
            (Multiset.map (fun μ => μ *
              (Real.log 2 *
                conditionalCenteredLogDev (states i).vonNeumann μ) ^ 2)
              (eigenvalueMultiset (states i).pos.isHermitian)).sum :=
              productSpectrum_secondMoment_scaled states
        _ =
          ∑ i : Fin n, (Real.log 2) ^ 2 * stateLogDeviationSecondMoment (states i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [stateLogDeviationSecondMoment_eq_eigenvalueMultiset,
                conditional_scaledSecondMoment_factor]
              simp [conditionalCenteredLogDev]
        _ =
          (Real.log 2) ^ 2 * ∑ i : Fin n, stateLogDeviationSecondMoment (states i) := by
              rw [Finset.mul_sum]

/-- The conditionally-typical spectral weight is nonnegative. -/
theorem conditionallyTypicalSpectralWeight_nonneg {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    0 ≤ conditionallyTypicalSpectralWeight states δ := by
  classical
  set τ := productState states
  unfold conditionallyTypicalSpectralWeight
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
  · simp only [hi]; exact τ.pos.eigenvalues_nonneg i
  · simp only [hi]; exact le_refl _

/-- The conditionally-atypical spectral weight is nonnegative. -/
theorem conditionallyAtypicalSpectralWeight_nonneg {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    0 ≤ conditionallyAtypicalSpectralWeight states δ := by
  classical
  set τ := productState states
  unfold conditionallyAtypicalSpectralWeight
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
  · simp only [hi]; exact le_refl _
  · simp only [hi]; exact τ.pos.eigenvalues_nonneg i

/-- The centered log-eigenvalue second moment of the product state is nonnegative. -/
theorem conditionalLogDeviationSecondMoment_nonneg {n : ℕ}
    (states : Fin n → State a) :
    0 ≤ conditionalLogDeviationSecondMoment states := by
  classical
  set τ := productState states
  unfold conditionalLogDeviationSecondMoment
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (τ.pos.eigenvalues_nonneg i) (sq_nonneg _)

/-- The conditionally-typical and conditionally-atypical spectral weights
partition the product state's total spectral weight. -/
theorem conditionallyTypicalSpectralWeight_add_atypical {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    conditionallyTypicalSpectralWeight states δ +
      conditionallyAtypicalSpectralWeight states δ = 1 := by
  classical
  set τ := productState states
  unfold conditionallyTypicalSpectralWeight conditionallyAtypicalSpectralWeight
  rw [← Finset.sum_add_distrib]
  have hsum : ∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i = 1 := by
    have hc :
        (∑ i : TensorPower a n,
            ((τ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 :=
      τ.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans τ.trace_eq_one
    rw [← Complex.ofReal_sum] at hc
    exact Complex.ofReal_injective hc
  calc
    (∑ i : TensorPower a n,
        ((if conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
          then τ.pos.isHermitian.eigenvalues i else 0) +
        if ¬ conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
          then τ.pos.isHermitian.eigenvalues i else 0)) =
        ∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i := by
          apply Finset.sum_congr rfl
          intro i _
          split
          · rw [add_zero]
          · rw [zero_add]
    _ = 1 := hsum

/-- Finite spectral Chebyshev bridge for the conditionally-typical projector.

This is a genuine concentration-form estimate at the spectral-distribution
level: the conditionally-atypical spectral weight times `(n δ)^2` is controlled
by the centered second moment of the log-eigenvalues of the product state
`⊗_i ρ_i`, centered at `Σ_i S(ρ_i)`. -/
theorem conditionallyAtypicalSpectralWeight_mul_sq_le_logDeviationSecondMoment
    {n : ℕ} (states : Fin n → State a) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    conditionallyAtypicalSpectralWeight states δ * (((n : ℝ) * δ) ^ 2) ≤
      conditionalLogDeviationSecondMoment states := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  set τ := productState states
  unfold conditionallyAtypicalSpectralWeight conditionalLogDeviationSecondMoment
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  set μ := τ.pos.isHermitian.eigenvalues i with hμ_def
  set d := (-log2 μ) - ∑ j, (states j).vonNeumann with hd_def
  have hμ_nonneg : 0 ≤ μ := τ.pos.eigenvalues_nonneg i
  by_cases htyp : conditionallyTypicalEigenvalue states δ μ
  · -- typical: atypical contribution is 0; RHS μ*d^2 ≥ 0
    have h_rhs_nonneg : 0 ≤ μ * d ^ 2 := mul_nonneg hμ_nonneg (sq_nonneg d)
    have h_lhs : (if ¬ conditionallyTypicalEigenvalue states δ μ then μ else 0)
        * ((n : ℝ) * δ) ^ 2 = 0 := by
      have hnn : ¬ (¬ conditionallyTypicalEigenvalue states δ μ) := fun h => h htyp
      rw [if_neg hnn, zero_mul]
    rw [h_lhs]
    exact h_rhs_nonneg
  · by_cases hμ_pos : 0 < μ
    · -- atypical and μ > 0: |d| > n*δ, so (n*δ)^2 ≤ d^2, multiply by μ ≥ 0
      have hnotle : ¬ |d| ≤ (n : ℝ) * δ := by
        intro hle
        exact htyp ⟨hμ_pos, by simpa [d, μ] using hle⟩
      have hclt : (n : ℝ) * δ < |d| := lt_of_not_ge hnotle
      have hcabs : |(n : ℝ) * δ| ≤ |d| := by
        rw [abs_of_nonneg (le_of_lt hcpos)]
        exact le_of_lt hclt
      have hsq : ((n : ℝ) * δ) ^ 2 ≤ d ^ 2 := by
        have hs := sq_le_sq.mpr hcabs
        simpa [sq_abs] using hs
      have hmul := mul_le_mul_of_nonneg_left hsq hμ_nonneg
      have h_lhs : (if ¬ conditionallyTypicalEigenvalue states δ μ then μ else 0)
          * ((n : ℝ) * δ) ^ 2 = μ * ((n : ℝ) * δ) ^ 2 := by
        rw [if_pos htyp]
      rw [h_lhs]
      exact hmul
    · -- μ = 0: both sides 0 (μ * anything = 0)
      have hμ_zero : μ = 0 := le_antisymm (not_lt.mp hμ_pos) hμ_nonneg
      have h_lhs : (if ¬ conditionallyTypicalEigenvalue states δ μ then μ else 0)
          * ((n : ℝ) * δ) ^ 2 = 0 := by
        rw [if_pos htyp, hμ_zero, zero_mul]
      have h_rhs : μ * d ^ 2 = 0 := by rw [hμ_zero, zero_mul]
      rw [h_lhs, h_rhs]

/-- Division form of the finite spectral Chebyshev bridge. -/
theorem conditionallyAtypicalSpectralWeight_le_logDeviationSecondMoment_div_sq
    {n : ℕ} (states : Fin n → State a) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    conditionallyAtypicalSpectralWeight states δ ≤
      conditionalLogDeviationSecondMoment states / (((n : ℝ) * δ) ^ 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  have hc2pos : 0 < (((n : ℝ) * δ) ^ 2) := sq_pos_of_pos hcpos
  rw [le_div_iff₀ hc2pos]
  exact conditionallyAtypicalSpectralWeight_mul_sq_le_logDeviationSecondMoment
    states hn hδ

/-- pack-2: the conditionally-typical projector captures its own product state.
`Tr{Π_cond · (⊗_i ρ_i)} ≥ 1 − (secondMoment / (nδ)²)`.
Source: [Wilde2011Qst, qit-notes.tex:28704-28713]. -/
theorem conditionallyTypicalSubspaceProjector_ownCapture {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) (hn : 0 < n) (hδ : 0 < δ) :
    1 - conditionalLogDeviationSecondMoment states / ((n : ℝ) * δ) ^ 2
      ≤ conditionallyTypicalSpectralWeight states δ := by
  have hle := conditionallyAtypicalSpectralWeight_le_logDeviationSecondMoment_div_sq
    states hn hδ
  have hadd := conditionallyTypicalSpectralWeight_add_atypical states δ
  linarith

/-! ## pack-3: dimension bound

Each accepted eigenvalue `μ` of the product state `⊗_i ρ_i` satisfies the
typicality predicate, whose upper bound on `-log₂ μ` gives the eigenvalue
lower bound `μ ≥ 2^{-(Σ_i S(ρ_i) + n δ)}`. Since the accepted spectral weight
`Σ_{accepted} μ` is at most the total spectral weight `1`, the number of
accepted directions is bounded by `2^{Σ_i S(ρ_i) + n δ}`. This mirrors the
iid dimension argument: an eigenvalue lower bound together with a total
spectral weight of one bounds the count of selected directions. -/

/-- pack-3 (core): the conditionally-typical-subspace dimension satisfies
`Tr{Π_cond} ≤ 2^{Σ_i S(ρ_i) + n δ}`. This is a pure finite-spectral
estimate: it uses only the eigenvalue lower bound implied by the
typicality predicate and the fact that the product state's eigenvalues
sum to one. No entropy-additivity interface is required (the per-symbol
entropy sum `Σ_i S(ρ_i)` is already the center of the predicate).
Source: [Wilde2011Qst, qit-notes.tex:28715-28734]. -/
theorem conditionallyTypicalSubspaceProjector_dim_le {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) (_hδ : 0 < δ) :
    conditionallyTypicalSubspaceDimension states δ
      ≤ Real.rpow 2 (∑ i, (states i).vonNeumann + (n : ℝ) * δ) := by
  classical
  set τ := productState states
  set S := ∑ i, (states i).vonNeumann
  -- The product state's eigenvalues sum to one (total spectral weight).
  have hsum : ∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i = 1 :=
    productState_eigenvalue_sum states
  -- The base 2^(ΣS + nδ) is strictly positive.
  have hbase_pos : 0 < Real.rpow 2 (S + (n : ℝ) * δ) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hl2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- For each accepted eigenvalue μ: μ ≥ 2^{-(ΣS + nδ)}, equivalently
  -- 1 ≤ μ * 2^{ΣS + nδ}.
  have hkey : ∀ i : TensorPower a n,
      conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i) →
        (1 : ℝ) ≤ τ.pos.isHermitian.eigenvalues i *
          Real.rpow 2 (S + (n : ℝ) * δ) := by
    intro i htyp
    obtain ⟨hμ_pos, habs⟩ := htyp
    set μ := τ.pos.isHermitian.eigenvalues i
    -- From the predicate: -log2 μ - S ≤ nδ, hence -log2 μ ≤ S + nδ.
    have hnegle : -log2 μ - S ≤ (n : ℝ) * δ := (abs_le.mp habs).2
    have hlog_le : -log2 μ ≤ S + (n : ℝ) * δ := by linarith
    -- Convert the log2 bound into a Real.log bound:
    -- Real.log μ ≥ -(S + nδ) · Real.log 2.
    have hlogμ_ge : -(S + (n : ℝ) * δ) * Real.log 2 ≤ Real.log μ := by
      -- hlog_le : -log2 μ ≤ S + nδ, with log2 μ · Real.log 2 = Real.log μ.
      -- Multiply through by Real.log 2 > 0 and use the identity.
      have hid : log2 μ * Real.log 2 = Real.log μ := by
        unfold log2; field_simp
      nlinarith [hlog_le, hl2_pos, hid,
        mul_le_mul_of_nonneg_right hlog_le hl2_pos.le]
    -- μ · 2^{S + nδ} ≥ 1  ⟺  Real.log(μ · 2^{S+nδ}) ≥ 0.
    have hlog_prod : 0 ≤ Real.log (μ * Real.rpow 2 (S + (n : ℝ) * δ)) := by
      rw [Real.log_mul hμ_pos.ne' hbase_pos.ne']
      have : Real.log (Real.rpow 2 (S + (n : ℝ) * δ)) =
          (S + (n : ℝ) * δ) * Real.log 2 :=
        Real.log_rpow (by norm_num : (0 : ℝ) < 2) _
      rw [this]
      linarith
    exact (Real.log_nonneg_iff (mul_pos hμ_pos hbase_pos)).mp hlog_prod
  -- The count is Σ_{accepted} 1; bound each accepted 1 by μ · 2^{ΣS+nδ},
  -- and each rejected term (which is 0) trivially.
  unfold conditionallyTypicalSubspaceDimension
  calc (∑ i : TensorPower a n,
        if conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
        then (1 : ℝ) else 0)
      ≤ ∑ i : TensorPower a n,
          τ.pos.isHermitian.eigenvalues i * Real.rpow 2 (S + (n : ℝ) * δ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi :
          conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
        · rw [if_pos hi]; exact hkey i hi
        · rw [if_neg hi]
          exact mul_nonneg (τ.pos.eigenvalues_nonneg i) hbase_pos.le
    _ = Real.rpow 2 (S + (n : ℝ) * δ) *
          ∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i := by
          rw [show (∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i *
                Real.rpow 2 (S + (n : ℝ) * δ)) =
                ∑ i : TensorPower a n,
                  Real.rpow 2 (S + (n : ℝ) * δ) *
                    τ.pos.isHermitian.eigenvalues i from
            Finset.sum_congr rfl fun i _ => mul_comm _ _,
            Finset.mul_sum]
    _ = Real.rpow 2 (S + (n : ℝ) * δ) * 1 := by rw [hsum]
    _ = Real.rpow 2 (S + (n : ℝ) * δ) := by ring

/-! ## pack-3 HSW form

This form connects the per-symbol entropy sum `Σ_i S(σ^{x_i})` for a
`p_X`-typical codeword `x^n` to the ensemble's per-symbol entropy
average `Σ_x p_x S(σ^x)` (the classical-quantum conditional entropy
`H(B|X)` of the channel's output ensemble). It is stated concretely,
directly over the ensemble's `probs` and `states` fields; no
entropy-additivity or conditional-entropy identity is taken as a
hypothesis. The identity `H(B|X) = Σ_x p_x S(σ^x)` — equivalently
`conditionalEntropy (cqState E) = Σ_x p_x S(σ^x)` — is formalized in the
entropy category and is referenced only in prose. -/

namespace Ensemble

/-- The classical distribution carried by an ensemble's index weights. -/
def indexDistribution {ι : Type u} {out : Type v}
    [Fintype ι] [Fintype out] [DecidableEq out] (E : Ensemble ι out) :
    QIT.FiniteDistribution ι where
  prob := E.probs
  sum_eq_one := E.weights_sum

@[simp]
theorem indexDistribution_prob {ι : Type u} {out : Type v}
    [Fintype ι] [Fintype out] [DecidableEq out] (E : Ensemble ι out) (x : ι) :
    E.indexDistribution.prob x = E.probs x :=
  rfl

/-- Dimension envelope obtained from strong typicality of the entropy observable. -/
noncomputable def strongTypicalDimensionEnvelope {ι : Type u} {out : Type v}
    [Fintype ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (n : ℕ) (δx δc : ℝ) : ℝ :=
  Real.rpow 2
    ((n : ℝ) *
      (∑ x, ↑(E.probs x) * (E.states x).vonNeumann + δc +
        δx * ∑ x, |(E.states x).vonNeumann|))

/-- Finite envelope for the one-letter centered log-eigenvalue second moments
of an ensemble's member states.  For a codeword product state, the
non-iid variance identity bounds the product second moment by
`n * logDeviationSecondMomentEnvelope`. -/
noncomputable def logDeviationSecondMomentEnvelope {ι : Type u} {out : Type v}
    [Fintype ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) : ℝ :=
  ∑ x, |stateLogDeviationSecondMoment (E.states x)|

theorem logDeviationSecondMomentEnvelope_nonneg {ι : Type u} {out : Type v}
    [Fintype ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) :
    0 ≤ E.logDeviationSecondMomentEnvelope := by
  classical
  dsimp [logDeviationSecondMomentEnvelope]
  exact Finset.sum_nonneg fun x _ => abs_nonneg _

theorem conditionalLogDeviationSecondMoment_codeword_le_envelope
    {n : ℕ} {ι : Type u} {out : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (codeword : Fin n → ι) :
    conditionalLogDeviationSecondMoment (fun i => E.states (codeword i))
      ≤ (n : ℝ) * E.logDeviationSecondMomentEnvelope := by
  classical
  rw [conditionalLogDeviationSecondMoment_eq_sum_stateLogDeviationSecondMoment]
  have hterm : ∀ i : Fin n,
      stateLogDeviationSecondMoment (E.states (codeword i)) ≤
        E.logDeviationSecondMomentEnvelope := by
    intro i
    dsimp [logDeviationSecondMomentEnvelope]
    exact le_trans (le_abs_self _)
      (Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun x => |stateLogDeviationSecondMoment (E.states x)|)
        (fun x _ => abs_nonneg _)
        (Finset.mem_univ (codeword i)))
  calc
    ∑ i : Fin n, stateLogDeviationSecondMoment (E.states (codeword i))
        ≤ ∑ _i : Fin n, E.logDeviationSecondMomentEnvelope :=
          Finset.sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) * E.logDeviationSecondMomentEnvelope := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num

theorem conditionalLogDeviationSecondMoment_codeword_ratio_le_of_envelope
    {n : ℕ} {ι : Type u} {out : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (codeword : Fin n → ι)
    {δ ε : ℝ} (hn : 0 < n) (hδ : 0 < δ)
    (hlarge : E.logDeviationSecondMomentEnvelope / ((n : ℝ) * δ ^ 2) ≤ ε) :
    conditionalLogDeviationSecondMoment (fun i => E.states (codeword i)) /
        ((n : ℝ) * δ) ^ 2 ≤ ε := by
  have hbound := E.conditionalLogDeviationSecondMoment_codeword_le_envelope codeword
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hden : 0 < ((n : ℝ) * δ) ^ 2 := sq_pos_of_pos (mul_pos hnR hδ)
  have hdiv :
      conditionalLogDeviationSecondMoment (fun i => E.states (codeword i)) /
          ((n : ℝ) * δ) ^ 2
        ≤ ((n : ℝ) * E.logDeviationSecondMomentEnvelope) / ((n : ℝ) * δ) ^ 2 :=
    div_le_div_of_nonneg_right hbound (le_of_lt hden)
  have hred :
      ((n : ℝ) * E.logDeviationSecondMomentEnvelope) / ((n : ℝ) * δ) ^ 2 =
        E.logDeviationSecondMomentEnvelope / ((n : ℝ) * δ ^ 2) := by
    field_simp [ne_of_gt hnR]
  exact le_trans (by simpa [hred] using hdiv) hlarge

end Ensemble

/-- A codeword `x^n : Fin n → ι` is `p_X`-typical when its per-symbol
entropy sum `Σ_i S(σ^{x_i})` differs from the ensemble entropy-rate
`n · Σ_x p_x S(σ^x)` by at most `n δ`. The center
`Σ_x p_x S(σ^x)` is the concrete per-symbol entropy average of the
ensemble's output states (the classical-quantum conditional entropy
`H(B|X)`); it is written directly over the ensemble fields rather than
as an opaque `conditionalEntropy`. This is the per-sequence
entropy-typicality condition that feeds the HSW dimension bound. -/
def CodewordIsTypical {n : ℕ} {ι : Type u} {out : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (codeword : Fin n → ι) (δ : ℝ) : Prop :=
  |∑ i, (E.states (codeword i)).vonNeumann -
      (n : ℝ) * ∑ x, ↑(E.probs x) * (E.states x).vonNeumann| ≤ (n : ℝ) * δ

/-- pack-3 (HSW form): for a `p_X`-typical codeword into the ensemble's
output states, `Tr{Π_cond} ≤ 2^{n(H(B|X) + c · δ)}` with `c = 2`, where
`H(B|X) = Σ_x p_x S(σ^x)` is the ensemble's per-symbol entropy average
(equal to `conditionalEntropy (cqState E)` by the cq-conditional-entropy
identity formalized in the entropy category). The constant `c = 2` arises
as `1` (from the typicality predicate's own `n δ` slack) plus `1` (from
the codeword's per-symbol-entropy slack `n δ` versus the rate
`n · Σ_x p_x S(σ^x)`). This form is interface-free: it assumes no
entropy-additivity or conditional-entropy identity as a hypothesis. -/
theorem conditionallyTypicalSubspaceProjector_dim_le_hsw
    {n : ℕ} {ι : Type u} {out : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (codeword : Fin n → ι) (δ : ℝ) (hδ : 0 < δ)
    (hTyp : CodewordIsTypical E codeword δ) :
    conditionallyTypicalSubspaceDimension (fun i => E.states (codeword i)) δ
      ≤ Real.rpow 2
        ((n : ℝ) * (∑ x, ↑(E.probs x) * (E.states x).vonNeumann + 2 * δ)) := by
  -- Step 1: the core dimension bound at the per-symbol entropy sum.
  have hcore := conditionallyTypicalSubspaceProjector_dim_le
    (fun i => E.states (codeword i)) δ hδ
  -- Step 2: codeword typicality bounds the per-symbol entropy sum.
  -- hTyp_ge : ∑ i S(σ^{x_i}) - n·Σ_x p_x S(σ^x) ≤ n δ,
  -- so ∑ i S(σ^{x_i}) ≤ n·Σ_x p_x S(σ^x) + n δ.
  obtain ⟨_hTyp_le, hTyp_ge⟩ := abs_le.mp hTyp
  -- Combine: Σ S(σ^{x_i}) + nδ ≤ n·Σ_x p_x S(σ^x) + nδ + nδ
  --        = n·(Σ_x p_x S(σ^x) + 2δ).
  have hsum_bound : ∑ i, (E.states (codeword i)).vonNeumann + (n : ℝ) * δ
      ≤ (n : ℝ) * (∑ x, ↑(E.probs x) * (E.states x).vonNeumann + 2 * δ) := by
    nlinarith [hTyp_ge]
  -- Exponentiate: 2^{ΣS + nδ} ≤ 2^{n·(Σ_x p_x S(σ^x) + 2δ)}.
  refine le_trans hcore ?_
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hsum_bound

/-- Strong classical typicality of the codeword implies the HSW entropy
typicality predicate, with the observable chosen as the member-state entropy. -/
theorem CodewordIsTypical.of_strongTypical_indexDistribution
    {n : ℕ} {ι : Type u} {out : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (codeword : Fin n → ι) {δ : ℝ}
    (hn : 0 < n) (hδ : 0 ≤ δ)
    (hstrong : ClassicalTypicality.StrongTypical E.indexDistribution codeword δ) :
    CodewordIsTypical E codeword
      (δ * ∑ x : ι, |(E.states x).vonNeumann|) := by
  have hobs := ClassicalTypicality.strongTypical_sum_observable_deviation_le
    E.indexDistribution codeword hn hδ hstrong (fun x => (E.states x).vonNeumann)
  simpa [CodewordIsTypical, mul_assoc] using hobs

/-- Strong classical typicality gives the source-shaped HSW pack-3 dimension
bound with separate input-typicality and conditionally-typical projector slacks.

The exponent is `n(Σ_x p_x S(σ_x) + δc + δx Σ_x |S(σ_x)|)`: the `δc` term comes
from the conditionally-typical projector and the `δx` term comes from empirical
typicality of the entropy observable along the codeword. -/
theorem conditionallyTypicalSubspaceProjector_dim_le_hsw_of_strongTypical
    {n : ℕ} {ι : Type u} {out : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (codeword : Fin n → ι) {δx δc : ℝ}
    (hn : 0 < n) (hδx : 0 ≤ δx) (hδc : 0 < δc)
    (hstrong : ClassicalTypicality.StrongTypical E.indexDistribution codeword δx) :
    conditionallyTypicalSubspaceDimension (fun i => E.states (codeword i)) δc
      ≤ Real.rpow 2
        ((n : ℝ) *
          (∑ x, ↑(E.probs x) * (E.states x).vonNeumann + δc +
            δx * ∑ x, |(E.states x).vonNeumann|)) := by
  have hcore := conditionallyTypicalSubspaceProjector_dim_le
    (fun i => E.states (codeword i)) δc hδc
  have hobs := ClassicalTypicality.strongTypical_sum_observable_deviation_le
    E.indexDistribution codeword hn hδx hstrong (fun x => (E.states x).vonNeumann)
  obtain ⟨_hlower, hupper⟩ := abs_le.mp hobs
  have hupper' :
      ∑ i, (E.states (codeword i)).vonNeumann -
          (n : ℝ) * ∑ x, ↑(E.probs x) * (E.states x).vonNeumann
        ≤ (n : ℝ) * δx * ∑ x, |(E.states x).vonNeumann| := by
    simpa using hupper
  have hsum_bound :
      ∑ i, (E.states (codeword i)).vonNeumann + (n : ℝ) * δc
        ≤ (n : ℝ) *
          (∑ x, ↑(E.probs x) * (E.states x).vonNeumann + δc +
            δx * ∑ x, |(E.states x).vonNeumann|) := by
    nlinarith [hupper']
  exact le_trans hcore
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hsum_bound)

/-- Named-envelope form of
`conditionallyTypicalSubspaceProjector_dim_le_hsw_of_strongTypical`. -/
theorem conditionallyTypicalSubspaceProjector_dim_le_strongTypicalDimensionEnvelope
    {n : ℕ} {ι : Type u} {out : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype out] [DecidableEq out]
    (E : Ensemble ι out) (codeword : Fin n → ι) {δx δc : ℝ}
    (hn : 0 < n) (hδx : 0 ≤ δx) (hδc : 0 < δc)
    (hstrong : ClassicalTypicality.StrongTypical E.indexDistribution codeword δx) :
    conditionallyTypicalSubspaceDimension (fun i => E.states (codeword i)) δc
      ≤ E.strongTypicalDimensionEnvelope n δx δc := by
  simpa [Ensemble.strongTypicalDimensionEnvelope] using
    conditionallyTypicalSubspaceProjector_dim_le_hsw_of_strongTypical
      E codeword hn hδx hδc hstrong

/-- The HSW diagonal-output dimension envelope for a classical channel `K`.

This is the named value used when codeword strong typicality supplies pack-3:
`2^{n(Σ_x p_x S(diag K_x) + δc + δx Σ_x |S(diag K_x)|)}`. -/
noncomputable def hswConditionalDiagonalDimensionEnvelope
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (n : ℕ) (δx δc : ℝ) : ℝ :=
  let Ediag : Ensemble α β :=
    { probs := p.prob
      weights_sum := p.sum_eq_one
      states := fun x => Classical.diagonalState (K.prob x) (K.sum_eq_one x) }
  Ediag.strongTypicalDimensionEnvelope n δx δc

/-- Strong typicality supplies the named diagonal-output pack-3 dimension
envelope for the conditional product states generated by `K`. -/
theorem conditionallyTypicalSubspaceProjector_dim_le_hswConditionalDiagonalDimensionEnvelope
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {n : ℕ} (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (codeword : Fin n → α) {δx δc : ℝ}
    (hn : 0 < n) (hδx : 0 ≤ δx) (hδc : 0 < δc)
    (hstrong : ClassicalTypicality.StrongTypical p codeword δx) :
    conditionallyTypicalSubspaceDimension
        (fun i : Fin n => Classical.diagonalState (K.prob (codeword i))
          (K.sum_eq_one (codeword i))) δc
      ≤ hswConditionalDiagonalDimensionEnvelope p K n δx δc := by
  let Ediag : Ensemble α β :=
    { probs := p.prob
      weights_sum := p.sum_eq_one
      states := fun x => Classical.diagonalState (K.prob x) (K.sum_eq_one x) }
  have hstrong' : ClassicalTypicality.StrongTypical Ediag.indexDistribution codeword δx := by
    simpa [Ediag, Ensemble.indexDistribution] using hstrong
  have hdim :=
    conditionallyTypicalSubspaceProjector_dim_le_strongTypicalDimensionEnvelope
      Ediag codeword hn hδx hδc hstrong'
  simpa [hswConditionalDiagonalDimensionEnvelope, Ediag] using hdim

/-! ## pack-4: projected average-state upper bound

Each accepted eigenvalue `μ` of `σ̄^{⊗ n}` satisfies the typicality predicate,
whose centered-log upper half gives the eigenvalue upper bound
`μ ≤ 2^{-n(S(σ̄) − δ)}` (the `typicalEigenvalue_le_eigenvalueUpperBound`
consequence, proved in `Typicality.lean`). In the eigenbasis of `σ̄^{⊗ n}`,
the typical projector `Π` is the `0/1` diagonal mask selecting the accepted
directions, so `Π · σ̄^{⊗ n} · Π` is the diagonal matrix carrying `μ_i` on
accepted directions and `0` elsewhere. Comparing entrywise against
`2^{-n(S(σ̄) − δ)} · Π` (which carries the scalar on accepted directions and
`0` elsewhere) gives the Loewner inequality
`Π · σ̄^{⊗ n} · Π ≤ 2^{-n(S(σ̄) − δ)} · Π`.

This is the packing-lemma `Π σ Π ≤ (1/D) Π` condition with
`D = 2^{n(S(σ̄) − δ)}`, stated for the HSW output ensemble's average state
`σ̄ = E.averageState` directly over `σ̄^{⊗ n}`. Wilde's HSW form additionally
carries a `[1 − ε]^{-1}` prefactor coming from the pruned-distribution
reduction `𝔼[σ^{X'^n}] ≤ [1 − ε]^{-1} σ̄^{⊗ n}`; that reduction is a
separate step and is not folded in here, so this is the concrete `σ̄^{⊗ n}`
form of pack-4. The proof is interface-free: it derives the eigenvalue upper
bound from the `typicalEigenvalue` predicate (no equipartition hypothesis) and
diagonalizes via the spectral theorem, the same unitary-conjugation pattern
used by `spectralPredicateProjector_le_one`. -/

/-- pack-4: the projected average state is bounded above by the scalar
`2^{-n(S(σ̄) − δ)}` times the typical projector, with
`σ̄ = E.averageState`. Concretely, for the ensemble's average state's
`n`-fold tensor power and its typical subspace projector,
`Π · σ̄^{⊗ n} · Π ≤ 2^{-n(S(σ̄) − δ)} · Π` (the packing-lemma
`Π σ Π ≤ (1/D) Π` condition with `D = 2^{n(S(σ̄) − δ)}`). The scalar is
written as a complex number so the inequality lives in the `CMatrix`
Loewner order directly. Source: [Wilde2011Qst, qit-notes.tex:28736-28747]. -/
theorem averageState_typicalProjector_projectedAvgState_le
    {n : ℕ} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι a) (δ : ℝ) :
    E.averageState.typicalSubspaceProjector n δ *
      (E.averageState.tensorPower n).matrix *
      E.averageState.typicalSubspaceProjector n δ
      ≤ (↑((2 : ℝ) ^ (-((n : ℝ) * E.averageState.vonNeumann - (n : ℝ) * δ))) : ℂ) •
        E.averageState.typicalSubspaceProjector n δ := by
  classical
  let σbar := E.averageState
  let τ := σbar.tensorPower n
  let hτ : τ.matrix.IsHermitian := τ.pos.isHermitian
  let U : CMatrix (TensorPower a n) := hτ.eigenvectorUnitary
  -- Eigenvalue diagonal Λ and projector mask D in the eigenbasis.
  let Λ : CMatrix (TensorPower a n) :=
    Matrix.diagonal (fun i => (hτ.eigenvalues i : ℂ))
  let D : CMatrix (TensorPower a n) :=
    Matrix.diagonal (fun i =>
      if σbar.typicalEigenvalue n δ (hτ.eigenvalues i) then (1 : ℂ) else 0)
  -- Spectral-theorem decompositions of `τ.matrix` and `Π`.
  have hspec : τ.matrix = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hτ.spectral_theorem
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hτ.eigenvectorUnitary]
  -- The scalar `c = 2^{-n(S(σ̄) − δ)}` (real-valued, then cast to ℂ).
  set c : ℝ := 2 ^ (-((n : ℝ) * σbar.vonNeumann - (n : ℝ) * δ))
  -- Typical projector `P` (kept in `set` so the goal's projector resolves to it).
  set P : CMatrix (TensorPower a n) :=
    σbar.typicalSubspaceProjector n δ with hPi_def
  -- Unfold `P` to its `spectralPredicateProjector` form `U · D · U*`.
  have hPi : P = U * D * star U := by
    have hPi_spec : P =
      spectralPredicateProjector τ.matrix hτ
        (fun i => σbar.typicalEigenvalue n δ (hτ.eigenvalues i)) := by
      rfl
    rw [hPi_spec]
    rfl
  -- Step (i): `P · τ.matrix · P = U · (D · Λ · D) · U*`,
  -- using `star U · U = 1` twice and 0/1 idempotence of `D`.
  have hPiPiM :
      P * τ.matrix * P = U * (D * Λ * D) * star U := by
    conv_lhs => rw [hPi, hspec]
    -- Bring the adjacent `star U, U` factors together so `hU` applies, then
    -- collapse and reassociate. Use `simp only [hU]` (rather than `rw [hU]`)
    -- so the unitary-column-orthonormality fact is applied as a rewrite
    -- without the surrounding simp-normalization that pre-collapses `star U * U`.
    conv_lhs =>
      rw [show (U * D * star U) * (U * Λ * star U) =
            U * D * (star U * U) * Λ * star U by noncomm_ring]
      rw [show U * D * (star U * U) * Λ * star U * (U * D * star U) =
            U * D * (star U * U) * Λ * (star U * U) * D * star U by noncomm_ring]
      simp only [hU, one_mul, mul_one]
    noncomm_ring
  -- Step (ii): `c • P = U · (c • D) · U*`. Scalar multiplication distributes
  -- over the matrix product: `U · (c • D) = c • (U · D)`, and
  -- `(c • (U · D)) · U* = c • (U · D · U*)`.
  have hcPi : (↑c : ℂ) • P = U * ((↑c : ℂ) • D) * star U := by
    rw [hPi]
    calc (↑c : ℂ) • (U * D * star U)
          = ((↑c : ℂ) • (U * D)) * star U := by rw [← Matrix.smul_mul]
      _ = (U * ((↑c : ℂ) • D)) * star U := by rw [← Matrix.mul_smul]
      _ = U * ((↑c : ℂ) • D) * star U := rfl
  -- Step (iii): reduce the Loewner inequality to a diagonal comparison in the
  -- eigenbasis. Both sides are `U · (·) · U*`, so
  -- `(c • P) − (P · τ.matrix · P) = U · ((c • D) − (D · Λ · D)) · U*`,
  -- and the conjugation by the unitary `U` preserves positive semidefiniteness.
  rw [Matrix.le_iff]
  rw [show (↑c : ℂ) • P - P * τ.matrix * P =
        U * ((↑c : ℂ) • D - D * Λ * D) * star U by
        rw [hcPi, hPiPiM]; noncomm_ring]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (Unitary.isUnit_coe : IsUnit (hτ.eigenvectorUnitary : CMatrix (TensorPower a n)))]
  -- Step (iv): the inner matrix is diagonal; reduce to its diagonal entries.
  have hdiag_inner :
      ((↑c : ℂ) • D - D * Λ * D : CMatrix (TensorPower a n)) =
        Matrix.diagonal (fun i =>
          if σbar.typicalEigenvalue n δ (hτ.eigenvalues i)
          then (↑c : ℂ) - hτ.eigenvalues i else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      -- Diagonal entry i = i.  D_ii = (if typical then 1 else 0),
      -- Λ_ii = eigenvalues_i, and (↑c • D)_ii = ↑c · D_ii.
      by_cases hi : σbar.typicalEigenvalue n δ (hτ.eigenvalues i)
      all_goals simp [hi, D, Λ, Matrix.diagonal_apply_eq,
        Matrix.diagonal_mul_diagonal]
    · -- Off-diagonal: all three pieces are zero (every factor is diagonal).
      have hne : ∀ (f : TensorPower a n → ℂ), Matrix.diagonal f i j = 0 :=
        fun f => Matrix.diagonal_apply_ne f hij
      simp only [D, Λ, ← Matrix.diagonal_smul, Matrix.diagonal_mul_diagonal]
      -- Split the pointwise subtraction, then every `Matrix.diagonal f i j`
      -- is zero off-diagonal. Both sides reduce to `0`.
      conv_lhs => rw [show ∀ (A B : CMatrix (TensorPower a n)),
        (A - B) i j = A i j - B i j from fun _ _ => rfl]
      simp only [hne, sub_zero]
  rw [hdiag_inner]
  rw [Matrix.posSemidef_diagonal_iff]
  -- Step (v): each accepted diagonal entry `c − eigenvalues_i` is nonnegative
  -- by `typicalEigenvalue_le_eigenvalueUpperBound`; rejected entries are 0.
  intro i
  by_cases hi : σbar.typicalEigenvalue n δ (hτ.eigenvalues i)
  · simp only [hi, if_true]
    -- `eigenvalues_i ≤ c = 2^{-n(S(σ̄) − δ)}`, equivalently `0 ≤ c − eigenvalues_i`.
    have hle := σbar.typicalEigenvalue_le_eigenvalueUpperBound n δ
      (hτ.eigenvalues i) hi
    exact_mod_cast (sub_nonneg.mpr hle)
  · simp only [hi, if_false]
    exact le_refl _

end

/-! ## HSW spectral packing-hypotheses bundle

This section packages the proved spectral estimates `pack-2`, `pack-3`, `pack-4`
(own-capture, dimension, projected-average-state) into the exact 4-hypothesis
shape consumed by `PackingLemma.packingLemma_avgError`, leaving the
cross-capture hypothesis `pack-1` (`h1`) as an explicit open field.

The packing lemma operates on a generic ensemble `E : Ensemble 𝒳 sys` of output
states, a typical-subspace projector `P`, codeword projectors `Px : 𝒳 → CMatrix
sys`, and scalars `d D ε`. In the HSW direct route the system is the `n`-fold
output `sys = TensorPower b n`, the typical projector `P` is the
single-symbol-average `σ̄`-typical projector `Π(σ̄^{⊗ n}, δ)`, and the codeword
projectors `Px x` are the conditionally-typical projectors of the codeword
product states `⊗_i σ^{x_i}`. The bundle records exactly these choices and the
proved `pack-2/3/4` instantiations, so that the only remaining input to
`packingLemma_avgError` is the open cross-capture hypothesis `pack-1`
(`Re Tr(Π σ_x) ≥ 1 − ε`), discharged by the source-shaped diagonal route below.

The spectral tolerance `ε` is a uniform scalar upper bound on the per-codeword
second-moment ratios `conditionalLogDeviationSecondMoment/(nδ)²` (the finite
spectral Chebyshev form in which `pack-2` is delivered); the constructor
requires this uniform bound as a hypothesis, so `pack-2` instantiates as
`1 − ε ≤ Re Tr(Π_x σ_x)`. The dimension bound `d` is a caller-supplied upper
bound on `Re Tr(Π_x) = conditionallyTypicalSubspaceDimension` (e.g.
`2^{n(H(B|X)+2δ)}` from `conditionallyTypicalSubspaceProjector_dim_le_hsw`). The
inverse-typical-weight `D` is `2^{n(S(σ̄) − δ)}` (from `pack-4`).
[Wilde2011Qst, qit-notes.tex:33634-33808] -/

/-- The conditionally-typical spectral weight equals the real trace of the
codeword product state against the conditionally-typical projector:
`Re Tr{(⊗_i ρ_i) · Π_cond} = conditionallyTypicalSpectralWeight`. This is the
trace-form bridge that turns `conditionallyTypicalSubspaceProjector_ownCapture`
(a bound on the spectral weight) into the packing-lemma `pack-2` trace form. It
follows from `spectralPredicateProjector_trace_mul_re` on the product state.
[Wilde2011Qst, qit-notes.tex:28704-28713] -/
theorem conditionallyTypicalSubspaceProjector_trace_mul_re {a : Type u} [Fintype a]
    [DecidableEq a] {n : ℕ} (states : Fin n → State a) (δ : ℝ) :
    ((productState states).matrix *
        conditionallyTypicalSubspaceProjector states δ).trace.re =
      conditionallyTypicalSpectralWeight states δ := by
  classical
  have hτ : (productState states).matrix.IsHermitian :=
    (productState states).pos.isHermitian
  unfold conditionallyTypicalSubspaceProjector conditionallyTypicalSpectralWeight
  exact spectralPredicateProjector_trace_mul_re _ hτ _

/-- The `pack-2` hypothesis in the trace form consumed by the packing lemma:
`Re Tr(Π_cond · (⊗_i ρ_i)) ≥ 1 − secondMoment/(nδ)²`. This is
`conditionallyTypicalSubspaceProjector_ownCapture` rewritten through the
trace-form bridge `conditionallyTypicalSubspaceProjector_trace_mul_re`, with the
projector commuted to the leading position by trace cyclicity.
[Wilde2011Qst, qit-notes.tex:28704-28713] -/
theorem conditionallyTypicalSubspaceProjector_ownCapture_trace {a : Type u} [Fintype a]
    [DecidableEq a] {n : ℕ} (states : Fin n → State a) {δ : ℝ} (hn : 0 < n)
    (hδ : 0 < δ) :
    1 - conditionalLogDeviationSecondMoment states / ((n : ℝ) * δ) ^ 2 ≤
      ((conditionallyTypicalSubspaceProjector states δ *
          (productState states).matrix).trace).re := by
  have hown := conditionallyTypicalSubspaceProjector_ownCapture states δ hn hδ
  have htr := conditionallyTypicalSubspaceProjector_trace_mul_re states δ
  have hcomm : ((conditionallyTypicalSubspaceProjector states δ *
        (productState states).matrix).trace).re =
      ((productState states).matrix *
        conditionallyTypicalSubspaceProjector states δ).trace.re :=
    congrArg Complex.re (Matrix.trace_mul_comm _ _)
  rw [hcomm, htr]
  exact hown

/-- The conditionally-typical-subspace dimension equals the real trace of the
conditionally-typical projector: `Re Tr(Π_cond) = conditionallyTypicalSubspaceDimension`.
This is the trace-form bridge that turns the `pack-3` dimension estimate into
the packing-lemma form `Re Tr(Π_x) ≤ d`. -/
theorem conditionallyTypicalSubspaceProjector_trace_re_eq_dimension {a : Type u}
    [Fintype a] [DecidableEq a] {n : ℕ} (states : Fin n → State a) (δ : ℝ) :
    (conditionallyTypicalSubspaceProjector states δ).trace.re =
      conditionallyTypicalSubspaceDimension states δ := by
  classical
  unfold conditionallyTypicalSubspaceProjector conditionallyTypicalSubspaceDimension
  exact spectralPredicateProjector_trace_re _ _ _

/-- **HSW spectral packing-hypotheses bundle.** For an `n`-block output
ensemble `E : Ensemble 𝒳 (TensorPower a n)` (the channel-output ensemble lifted
to `n` uses, with each `E.states x` a codeword product state `⊗_i σ^{x_i}`),
this structure bundles the typical projector `P` (the single-symbol-average
`σ̄`-typical projector `Π(σ̄^{⊗ n}, δ)`), the codeword projectors `Px` (the
conditionally-typical projectors), the scalars `d D ε`, the projector-side
hypotheses on `P` and `Px`, and the proved packing hypotheses `pack-2`/`pack-3`/
`pack-4`, in the exact shape consumed by `PackingLemma.packingLemma_avgError`.

The cross-capture hypothesis `pack-1` (`h1 : ∀ x, 1 − ε ≤ Re Tr(P · σ_x)`) is
left as an **open field with no default proof**: it is the only remaining input
that `packingLemma_avgError` requires beyond this bundle, and it is discharged
by a separate proof leaf (the unconditional-typical-subspace capture of each
codeword's product state, i.e. the pack-1 cross-capture estimate). Do not
supply a placeholder proof of `h1`; consumers must discharge it explicitly.

The fields are ordered to match `PackingLemma.packingLemma_avgError`'s argument
list (ensemble `E`, then `P`/`P`-facts, then `Px`/`Px`-facts, then
`d D ε`/sign-hypotheses, then `h1 h2 h3 h4`), so that the derandomized packing
step can feed a value of this structure straight into the packing lemma by
projection.
[Wilde2011Qst, qit-notes.tex:33634-33808] -/
structure HSWPackingHypothesesSpectral
    {a : Type u} {𝒳 : Type*} {n : ℕ}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (E : Ensemble 𝒳 (TensorPower a n)) (δ : ℝ) where
  /-- The single-symbol-average typical projector `Π = Π(σ̄^{⊗ n}, δ)`. -/
  P : CMatrix (TensorPower a n)
  /-- The codeword conditionally-typical projectors `Π_x`. -/
  Px : 𝒳 → CMatrix (TensorPower a n)
  /-- Dimension bound `d` (an upper bound on `Re Tr(Π_x)`). -/
  d : ℝ
  /-- Inverse typical weight `D = 2^{n(S(σ̄) − δ)}` (strictly positive). -/
  D : ℝ
  /-- Spectral tolerance `ε ≥ 0`, a uniform upper bound on the per-codeword
  second-moment ratios `conditionalLogDeviationSecondMoment/(nδ)²`. -/
  ε : ℝ
  /-- Nonnegativity of the spectral tolerance. -/
  hε_nonneg : 0 ≤ ε
  /-- Strict positivity of the inverse typical weight `D`. -/
  hD_pos : 0 < D
  /-- The typical projector `P` is positive semidefinite. -/
  P_posSemidef : P.PosSemidef
  /-- The typical projector `P` is idempotent. -/
  P_idempotent : P * P = P
  /-- The typical projector `P` is bounded by the identity effect. -/
  P_le_one : P ≤ 1
  /-- Each codeword projector `Px x` is positive semidefinite, idempotent, and
  bounded by the identity effect (the projector-side hypothesis bundle required
  by `packingLemma_avgError`). -/
  Px_projector : ∀ x, (Px x).PosSemidef ∧ Px x * Px x = Px x ∧ Px x ≤ 1
  /-- **pack-1 (OPEN).** Cross-capture: the typical projector captures each
  codeword product state, `Re Tr(P · σ_x) ≥ 1 − ε`. This field has no default
  proof; it is the remaining input discharged separately by the
  source-shaped diagonal cross-capture route. -/
  h1 : ∀ x, 1 - ε ≤ ((P * (E.states x).matrix).trace).re
  /-- **pack-2.** Own-capture: each codeword's conditionally-typical projector
  captures its own product state, `Re Tr(Π_x · σ_x) ≥ 1 − ε`. -/
  h2 : ∀ x, 1 - ε ≤ ((Px x * (E.states x).matrix).trace).re
  /-- **pack-3.** Dimension: the codeword-projector trace is bounded by `d`. -/
  h3 : ∀ x, ((Px x).trace).re ≤ d
  /-- **pack-4.** Projected average state: `Π · σ̄ · Π ≤ D⁻¹ · Π`, where
  `σ̄ = E.averageState` is the ensemble's `n`-block average state. -/
  h4 : P * E.averageState.matrix * P ≤ ((D : ℝ)⁻¹) • P

namespace FiniteDistribution

variable {β : Type v} [Fintype β]

/-- Shannon entropy of a finite classical distribution, in bits. -/
noncomputable def shannonEntropy (p : QIT.FiniteDistribution β) : ℝ :=
  -∑ z : β, xlog2 (p.prob z : ℝ)

/-- The finite log-slack constant controlling strong-typical product-mass
envelopes.  For a strongly typical word, the i.i.d. product mass is bounded by
`2^{-n H(p) + n δ L(p)}`, where `L(p)` is this sum of absolute log weights.
Zero-probability symbols contribute `0` because `Real.log 0 = 0` and the
`xlog2` convention is `0 log 0 = 0`. -/
noncomputable def logTypicalitySlack (p : QIT.FiniteDistribution β) : ℝ :=
  ∑ z : β, |log2 (p.prob z : ℝ)|

theorem logTypicalitySlack_nonneg (p : QIT.FiniteDistribution β) :
    0 ≤ p.logTypicalitySlack := by
  classical
  dsimp [logTypicalitySlack]
  exact Finset.sum_nonneg fun z _ => abs_nonneg _

/-- The inverse mass scale used for a strongly typical marginal type class:
`D = 2^{nH(p)-nδL(p)}`. -/
noncomputable def strongTypicalMassScale (p : QIT.FiniteDistribution β) (n : ℕ) (δ : ℝ) :
    ℝ :=
  Real.rpow 2 ((n : ℝ) * p.shannonEntropy - (n : ℝ) * δ * p.logTypicalitySlack)

theorem strongTypicalMassScale_pos (p : QIT.FiniteDistribution β) (n : ℕ) (δ : ℝ) :
    0 < p.strongTypicalMassScale n δ :=
  Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _

theorem rpow_entropy_slack_eq_strongTypicalMassScale_inv
    (p : QIT.FiniteDistribution β) (n : ℕ) (δ : ℝ) :
    Real.rpow 2 (- (n : ℝ) * p.shannonEntropy + (n : ℝ) * δ * p.logTypicalitySlack) =
      (p.strongTypicalMassScale n δ)⁻¹ := by
  unfold strongTypicalMassScale
  have hexp :
      - (n : ℝ) * p.shannonEntropy + (n : ℝ) * δ * p.logTypicalitySlack =
        -((n : ℝ) * p.shannonEntropy - (n : ℝ) * δ * p.logTypicalitySlack) := by
    ring
  rw [hexp]
  exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)
    ((n : ℝ) * p.shannonEntropy - (n : ℝ) * δ * p.logTypicalitySlack)

end FiniteDistribution

namespace HSWPackingHypothesesSpectral

variable {a : Type u} {𝒳 : Type*} {n : ℕ}
  [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
variable {E : Ensemble 𝒳 (TensorPower a n)} {δ : ℝ}

/-! ### pack-1 cross-capture estimates

The full per-codeword cross-capture of Wilde's conditional-typical-subspace
analysis (`prop-qt:cond-state-with-uncond-proj`: a codeword product state
`⊗_i σ^{x_i}` captured by the AVERAGE state's typical projector
`Π(σ̄^{⊗ n}, δ)`) is not available from the older spectral helper alone: the
codeword product state is not diagonal in the average state's eigenbasis, so
the clean spectral argument used in `pack-2` (own-capture) does not transfer.
The source-shaped strong-typical block below supplies the pinched/diagonal
kernel used in Wilde's proof.

Three small, cleanly-provable pieces are delivered here:

* **Piece A** — the AVERAGE state captures itself under its own typical
  projector (the iid self-capture; the codeword product state coincides with
  `σ̄^{⊗ n}`, which IS diagonal in its own eigenbasis, so the spectral argument
  applies). This is the same route as `pack-2`'s `ownCapture_trace` but routed
  through the high-probability typical-subspace form rather than the per-codeword
  second-moment bound.
* **Discharge helper** — the open `h1` field is recovered pointwise from a
  hypothesis that bounds the *deficit* `1 − Re Tr(Π σ_x)` by `ε` (mechanical
  rearrangement, no content).
* **Legacy spectral statement** — the per-codeword unconditional-capture shape
  for `State.typicalSubspaceProjector` is recorded as a `Prop` only, so later
  code can keep the old packing-lemma field visible without pretending that
  this spectral-vs-strong projector bridge has already been identified.

[Wilde2011Qst, qit-notes.tex:33634-33808] -/

/-- **Piece A.** The average state captures itself under its own typical
projector in the high-probability regime: for `σ̄ = E₀.averageState` and `n`
past the threshold `C / (ε δ²)` (with `C = typicalLogDeviationSecondMoment σ̄ 1`,
the same threshold form as the high-probability typical-subspace theorem),
`Re Tr(Π · σ̄^{⊗ n}) ≥ 1 − ε`. The codeword product state coincides with
`σ̄^{⊗ n}`, which is diagonal in its own eigenbasis, so the spectral argument
applies; this is the iid self-capture, NOT the per-codeword cross-capture.

Route: `Re Tr(Π · σ̄^{⊗ n})` equals `typicalSubspaceSpectralWeight σ̄ n δ` by
`typicalSubspaceProjector_trace_mul_re` (with the projector commuted to the
leading position by trace cyclicity), then apply
`typicalSubspaceSpectralWeight_high_probability`. Source:
[Wilde2011Qst, qit-notes.tex:33634-33808]. -/
theorem reTrace_averageStateTypicalProjector_self {a : Type u} [Fintype a]
    [DecidableEq a] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a) {n : ℕ} {δ ε : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hε : 0 < ε)
    (hthresh :
      (E₀.averageState.typicalLogDeviationSecondMoment 1 / (ε * δ ^ 2)) ≤ n) :
    1 - ε ≤
      ((E₀.averageState.typicalSubspaceProjector n δ *
          (E₀.averageState.tensorPower n).matrix).trace).re := by
  -- Trace cyclicity commutes the leading projector to the trailing position,
  -- matching `typicalSubspaceProjector_trace_mul_re`'s `(τ.matrix * P)` form.
  have hcomm :
      ((E₀.averageState.typicalSubspaceProjector n δ *
          (E₀.averageState.tensorPower n).matrix).trace).re =
        (((E₀.averageState.tensorPower n).matrix *
            E₀.averageState.typicalSubspaceProjector n δ).trace).re :=
    congrArg Complex.re (Matrix.trace_mul_comm _ _)
  rw [hcomm,
    E₀.averageState.typicalSubspaceProjector_trace_mul_re n δ]
  exact E₀.averageState.typicalSubspaceSpectralWeight_high_probability
    hn hδ hε hthresh

/-- **Discharge helper.** Recover the open `h1` field pointwise from a hypothesis
bounding the *deficit* `1 − Re Tr(Π σ_x)` by `ε`. This is a mechanical
rearrangement: `1 − Re Tr(Π σ_x) ≤ ε` iff `1 − ε ≤ Re Tr(Π σ_x)` over the reals.
It does not prove cross-capture; it just re-presents an atypical-deficit bound
in the `h1` shape consumed by the packing lemma. -/
abbrev h1_of_perCodewordAtypical
    {a : Type u} {𝒳 : Type*} {n : ℕ}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (_E₀ : Ensemble 𝒳 a) -- unused at this signature level; kept for symmetry
        -- with the constructor's single-symbol-ensemble framing
    (E : Ensemble 𝒳 (TensorPower a n)) (P : CMatrix (TensorPower a n))
    (ε : ℝ)
    (hatypical : ∀ x,
      1 - ((P * (E.states x).matrix).trace).re ≤ ε) :
    ∀ x, 1 - ε ≤ ((P * (E.states x).matrix).trace).re := fun x =>
  by linarith [hatypical x]

/-- Matrix entries of a non-i.i.d. product state factor coordinatewise under
the repository's `TensorPower a n ≃ (Fin n → a)` convention. -/
theorem productState_matrix_apply {a : Type u} [Fintype a] [DecidableEq a] :
    ∀ {n : ℕ} (states : Fin n → State a) (x y : TensorPower a n),
      (productState states).matrix x y =
        ∏ i : Fin n, (states i).matrix ((tensorPowerEquiv n x) i)
          ((tensorPowerEquiv n y) i)
  | 0, _states, x, y => by
      cases x
      cases y
      simp [productState, State.unit]
  | n + 1, states, (x0, xs), (y0, ys) => by
      rw [productState_succ, State.prod]
      change (states 0).matrix x0 y0 * (productState fun i => states i.succ).matrix xs ys =
        ∏ i : Fin (n + 1),
          (states i).matrix ((tensorPowerEquiv (n + 1) (x0, xs)) i)
            ((tensorPowerEquiv (n + 1) (y0, ys)) i)
      rw [productState_matrix_apply (fun i : Fin n => states i.succ) xs ys]
      rw [Fin.prod_univ_succ]
      simp

/-- **Legacy spectral statement.** The per-codeword UNCONDITIONAL
typical-subspace capture statement — the codeword product state `⊗_i σ^{x_i}`
captured by the AVERAGE state's typical projector `Π(σ̄^{⊗ n}, δ)`:
`Re Tr(Π · σ_x) ≥ 1 − ε` for every codeword `x`.

This is the old spectral-projector interface for HSW pack-1 cross-capture.  It
is recorded here as a `Prop` only: the proved source-shaped theorem below uses
Wilde's pinching reduction and strong-typical diagonal projector, while this
legacy `State.typicalSubspaceProjector` statement would additionally require a
spectral-vs-strong projector identification if retained as the packing object.
Source: [Wilde2011Qst, qit-notes.tex:33634-33808]. -/
def pack1_crossCapture_unconditional_statement {a : Type u} {𝒳 : Type*} {n : ℕ}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (E₀ : Ensemble 𝒳 a) (E : Ensemble 𝒳 (TensorPower a n)) (δ ε : ℝ) : Prop :=
  ∀ x, 1 - ε ≤
    ((E₀.averageState.typicalSubspaceProjector n δ * (E.states x).matrix).trace).re

/-! #### Source-shaped strong-typical pack-1 bridge

Wilde's proof of `prop-qt:cond-state-with-uncond-proj` first pinches every
conditional output state in an eigenbasis of the average state.  After that
pinching step, the projector is a diagonal strong-typical projector and the
conditional product state is a diagonal classical conditional product law.
The theorem below proves exactly this diagonal/pinched pack-1 kernel from the
finite classical conditional-typicality theorem in
`QIT.Asymptotic.ClassicalTypicality`.

It intentionally does not identify this source-shaped strong-typical
projector with the older spectral `State.typicalSubspaceProjector`; that
spectral-vs-strong projector bridge is a separate statement if a later API
chooses to keep the spectral projector as the packing-lemma object.
[Wilde2011Qst, qit-notes.tex:28892-28904] -/

/-- Strong-typical diagonal projector for a finite classical distribution on
`β^n`, written on the repository's tensor-power basis.  This is the
source-shaped projector obtained after choosing the average state's eigenbasis
in Wilde's pinching reduction. -/
noncomputable def strongTypicalDiagonalProjector {β : Type v} [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution β) (n : ℕ) (δ : ℝ) :
    CMatrix (TensorPower β n) := by
  classical
  exact Matrix.diagonal fun z =>
    if ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
    then (1 : ℂ) else 0

/-- The source-shaped strong-typical diagonal projector is positive
semidefinite. -/
theorem strongTypicalDiagonalProjector_posSemidef {β : Type v} [Fintype β]
    [DecidableEq β] (p : QIT.FiniteDistribution β) (n : ℕ) (δ : ℝ) :
    (strongTypicalDiagonalProjector p n δ).PosSemidef := by
  classical
  unfold strongTypicalDiagonalProjector
  rw [Matrix.posSemidef_diagonal_iff]
  intro z
  by_cases hz : ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
  · simp [hz]
  · simp [hz]

/-- The source-shaped strong-typical diagonal projector is idempotent. -/
theorem strongTypicalDiagonalProjector_idempotent {β : Type v} [Fintype β]
    [DecidableEq β] (p : QIT.FiniteDistribution β) (n : ℕ) (δ : ℝ) :
    strongTypicalDiagonalProjector p n δ * strongTypicalDiagonalProjector p n δ =
      strongTypicalDiagonalProjector p n δ := by
  classical
  unfold strongTypicalDiagonalProjector
  rw [Matrix.diagonal_mul_diagonal]
  ext z z'
  by_cases hzz' : z = z'
  · subst z'
    by_cases hz : ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
    · simp [hz]
    · simp [hz]
  · simp [Matrix.diagonal, hzz']

/-- The source-shaped strong-typical diagonal projector is bounded by the
identity effect. -/
theorem strongTypicalDiagonalProjector_le_one {β : Type v} [Fintype β]
    [DecidableEq β] (p : QIT.FiniteDistribution β) (n : ℕ) (δ : ℝ) :
    strongTypicalDiagonalProjector p n δ ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  unfold strongTypicalDiagonalProjector
  have hdiag :
      (1 - Matrix.diagonal (fun z : TensorPower β n =>
        if ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
        then (1 : ℂ) else 0) : CMatrix (TensorPower β n)) =
        Matrix.diagonal (fun z : TensorPower β n =>
          1 - if ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
          then (1 : ℂ) else 0) := by
    ext z z'
    by_cases hzz' : z = z'
    · subst z'
      simp
    · simp [Matrix.diagonal, hzz']
  rw [hdiag, Matrix.posSemidef_diagonal_iff]
  intro z
  by_cases hz : ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
  · simp [hz]
  · simp [hz]

/-! #### Source-shaped total typical projector

The textbook typical projector `Π_{ρ,δ}^n` is built from the one-copy
eigenbasis of `ρ` and then tensored across `n` positions.  This differs from
the older local `State.typicalSubspaceProjector`, which diagonalizes the whole
matrix `ρ^{⊗ n}` and therefore may choose an arbitrary basis inside degenerate
eigenspaces.  The following definitions expose the source-shaped projector
directly, so HSW pack-1 can be connected to the post-pinching classical
strong-typicality kernel without silently changing projector semantics. -/

/-- The one-symbol eigenvalue distribution of a density state, as a finite
classical distribution. -/
noncomputable def stateEigenvalueDistribution {a : Type u} [Fintype a] [DecidableEq a]
    (ρ : State a) : QIT.FiniteDistribution a where
  prob := ProjectiveMeasurement.stateEigenvalueProb ρ
  sum_eq_one := ProjectiveMeasurement.stateEigenvalueProb_sum ρ

/-- The Shannon entropy of a state's eigenvalue distribution is the state's
von Neumann entropy, in the common log-base-two convention. -/
theorem stateEigenvalueDistribution_shannonEntropy {a : Type u} [Fintype a] [DecidableEq a]
    (ρ : State a) :
    (stateEigenvalueDistribution ρ).shannonEntropy = ρ.vonNeumann := by
  dsimp [stateEigenvalueDistribution, FiniteDistribution.shannonEntropy, State.vonNeumann,
    ProjectiveMeasurement.stateEigenvalueProb]
  congr 1

/-- Conjugating a state by its eigenvector unitary gives the diagonal matrix of
its eigenvalue distribution. -/
theorem stateEigenbasis_conj_matrix_eq_diagonalEigenvalueProb
    {a : Type u} [Fintype a] [DecidableEq a] (ρ : State a) :
    star (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
        ρ.matrix *
        (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a) =
      Matrix.diagonal (fun i => (((stateEigenvalueDistribution ρ).prob i : ℝ≥0) : ℂ)) := by
  let U : CMatrix a := ρ.pos.isHermitian.eigenvectorUnitary
  let D : CMatrix a :=
    Matrix.diagonal (fun i => (((stateEigenvalueDistribution ρ).prob i : ℝ≥0) : ℂ))
  have hρ : ρ.matrix = U * D * star U := by
    dsimp [U, D, stateEigenvalueDistribution]
    exact ProjectiveMeasurement.state_matrix_eq_unitary_diagonalEigenvalueProb ρ
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self ρ.pos.isHermitian.eigenvectorUnitary]
  calc
    star U * ρ.matrix * U = star U * (U * D * star U) * U := by rw [hρ]
    _ = (star U * U) * D * (star U * U) := by noncomm_ring
    _ = D := by simp [hU]

/-- Source-shaped tensor-product-eigenbasis typical projector.

If `U` diagonalizes `ρ`, this projector is
`U^{⊗ n} Π_typ(p_ρ) (U^{⊗ n})†`, where `Π_typ(p_ρ)` is the classical
strong-typical diagonal projector for the eigenvalue distribution of `ρ`.
This is the projector used in Wilde's statement
`Π_{ρ,δ}^n`, not the arbitrary spectral projector of `ρ^{⊗ n}`. -/
noncomputable def sourceTypicalSubspaceProjector
    {a : Type u} [Fintype a] [DecidableEq a] (ρ : State a) (n : ℕ) (δ : ℝ) :
    CMatrix (TensorPower a n) :=
  let U := unitaryTensorPowerMatrix ρ.pos.isHermitian.eigenvectorUnitary n
  (U : CMatrix (TensorPower a n)) *
    strongTypicalDiagonalProjector (stateEigenvalueDistribution ρ) n δ *
      star (U : CMatrix (TensorPower a n))

/-- The source-shaped typical projector is positive semidefinite. -/
theorem sourceTypicalSubspaceProjector_posSemidef
    {a : Type u} [Fintype a] [DecidableEq a] (ρ : State a) (n : ℕ) (δ : ℝ) :
    (sourceTypicalSubspaceProjector ρ n δ).PosSemidef := by
  classical
  unfold sourceTypicalSubspaceProjector
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (Unitary.isUnit_coe :
      IsUnit (unitaryTensorPowerMatrix ρ.pos.isHermitian.eigenvectorUnitary n :
        CMatrix (TensorPower a n)))]
  exact strongTypicalDiagonalProjector_posSemidef (stateEigenvalueDistribution ρ) n δ

/-- The source-shaped typical projector is idempotent. -/
theorem sourceTypicalSubspaceProjector_idempotent
    {a : Type u} [Fintype a] [DecidableEq a] (ρ : State a) (n : ℕ) (δ : ℝ) :
    sourceTypicalSubspaceProjector ρ n δ *
        sourceTypicalSubspaceProjector ρ n δ =
      sourceTypicalSubspaceProjector ρ n δ := by
  classical
  unfold sourceTypicalSubspaceProjector
  let U := unitaryTensorPowerMatrix ρ.pos.isHermitian.eigenvectorUnitary n
  let D := strongTypicalDiagonalProjector (stateEigenvalueDistribution ρ) n δ
  have hU : star (U : CMatrix (TensorPower a n)) * (U : CMatrix (TensorPower a n)) = 1 :=
    Unitary.coe_star_mul_self U
  have hD : D * D = D :=
    strongTypicalDiagonalProjector_idempotent (stateEigenvalueDistribution ρ) n δ
  change ((U : CMatrix (TensorPower a n)) * D * star (U : CMatrix (TensorPower a n))) *
      ((U : CMatrix (TensorPower a n)) * D * star (U : CMatrix (TensorPower a n))) =
    (U : CMatrix (TensorPower a n)) * D * star (U : CMatrix (TensorPower a n))
  calc
    ((U : CMatrix (TensorPower a n)) * D * star (U : CMatrix (TensorPower a n))) *
        ((U : CMatrix (TensorPower a n)) * D * star (U : CMatrix (TensorPower a n))) =
      (U : CMatrix (TensorPower a n)) * D *
        (star (U : CMatrix (TensorPower a n)) * (U : CMatrix (TensorPower a n))) *
        D * star (U : CMatrix (TensorPower a n)) := by
        noncomm_ring
    _ = (U : CMatrix (TensorPower a n)) * D * 1 * D *
        star (U : CMatrix (TensorPower a n)) := by rw [hU]
    _ = (U : CMatrix (TensorPower a n)) * (D * D) *
        star (U : CMatrix (TensorPower a n)) := by
        noncomm_ring
    _ = (U : CMatrix (TensorPower a n)) * D *
        star (U : CMatrix (TensorPower a n)) := by rw [hD]

/-- The source-shaped typical projector is bounded by the identity effect. -/
theorem sourceTypicalSubspaceProjector_le_one
    {a : Type u} [Fintype a] [DecidableEq a] (ρ : State a) (n : ℕ) (δ : ℝ) :
    sourceTypicalSubspaceProjector ρ n δ ≤ 1 := by
  classical
  unfold sourceTypicalSubspaceProjector
  let U := unitaryTensorPowerMatrix ρ.pos.isHermitian.eigenvectorUnitary n
  let D := strongTypicalDiagonalProjector (stateEigenvalueDistribution ρ) n δ
  have hUU : (U : CMatrix (TensorPower a n)) * star (U : CMatrix (TensorPower a n)) = 1 :=
    Unitary.coe_mul_star_self U
  have hU1 : (U : CMatrix (TensorPower a n)) * 1 *
        star (U : CMatrix (TensorPower a n)) = 1 := by
    simp
  rw [Matrix.le_iff]
  have hsub :
      (1 : CMatrix (TensorPower a n)) -
          (U : CMatrix (TensorPower a n)) * D * star (U : CMatrix (TensorPower a n)) =
        (U : CMatrix (TensorPower a n)) * (1 - D) *
          star (U : CMatrix (TensorPower a n)) := by
    calc
      (1 : CMatrix (TensorPower a n)) -
          (U : CMatrix (TensorPower a n)) * D * star (U : CMatrix (TensorPower a n)) =
          (U : CMatrix (TensorPower a n)) * 1 *
            star (U : CMatrix (TensorPower a n)) -
          (U : CMatrix (TensorPower a n)) * D *
            star (U : CMatrix (TensorPower a n)) := by
          rw [hU1]
      _ = (U : CMatrix (TensorPower a n)) * (1 - D) *
          star (U : CMatrix (TensorPower a n)) := by
          noncomm_ring
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (Unitary.isUnit_coe :
      IsUnit (unitaryTensorPowerMatrix ρ.pos.isHermitian.eigenvectorUnitary n :
        CMatrix (TensorPower a n)))]
  rw [← Matrix.le_iff]
  exact strongTypicalDiagonalProjector_le_one (stateEigenvalueDistribution ρ) n δ

/-- Diagonal entries of a product state after a tensor-power unitary conjugation
factor as products of the one-symbol conjugated diagonal entries. -/
theorem unitaryTensorPowerMatrix_conj_productState_diag
    {a : Type u} [Fintype a] [DecidableEq a] (U : Matrix.unitaryGroup a ℂ) :
    ∀ {n : ℕ} (states : Fin n → State a) (z : TensorPower a n),
      (star (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n)) *
          (productState states).matrix *
          (unitaryTensorPowerMatrix U n : CMatrix (TensorPower a n))) z z =
        ∏ i : Fin n,
          (star (U : CMatrix a) * (states i).matrix * (U : CMatrix a))
            ((tensorPowerEquiv n z) i) ((tensorPowerEquiv n z) i)
  | 0, _states, z => by
      cases z
      simp [unitaryTensorPowerMatrix, productState, State.unit]
  | n + 1, states, (z0, zs) => by
      let Un := unitaryTensorPowerMatrix U n
      have hstar :
          star (Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n))) =
            Matrix.kronecker (star (U : CMatrix a)) (star (Un : CMatrix (TensorPower a n))) := by
        simpa [Matrix.star_eq_conjTranspose] using
          Matrix.conjTranspose_kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n))
      change
        (star (Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n))) *
              Matrix.kronecker (states 0).matrix (productState (states ·.succ)).matrix *
              Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)))
            (z0, zs) (z0, zs) =
          ∏ i : Fin (n + 1),
            (star (U : CMatrix a) * (states i).matrix * (U : CMatrix a))
              ((tensorPowerEquiv (n + 1) (z0, zs)) i)
              ((tensorPowerEquiv (n + 1) (z0, zs)) i)
      rw [hstar]
      let A : CMatrix a := star (U : CMatrix a) * (states 0).matrix * (U : CMatrix a)
      let B : CMatrix (TensorPower a n) :=
        star (Un : CMatrix (TensorPower a n)) *
          (productState (states ·.succ)).matrix *
          (Un : CMatrix (TensorPower a n))
      have hkr :
          Matrix.kronecker (star (U : CMatrix a)) (star (Un : CMatrix (TensorPower a n))) *
                Matrix.kronecker (states 0).matrix (productState (states ·.succ)).matrix *
                Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)) =
            Matrix.kronecker A B := by
        calc
          Matrix.kronecker (star (U : CMatrix a)) (star (Un : CMatrix (TensorPower a n))) *
                Matrix.kronecker (states 0).matrix (productState (states ·.succ)).matrix *
                Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)) =
            Matrix.kronecker (star (U : CMatrix a) * (states 0).matrix)
                (star (Un : CMatrix (TensorPower a n)) *
                  (productState (states ·.succ)).matrix) *
                Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)) := by
              exact congrArg
                (fun M : CMatrix (Prod a (TensorPower a n)) =>
                  M * Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)))
                (Matrix.mul_kronecker_mul
                  (star (U : CMatrix a)) (states 0).matrix
                  (star (Un : CMatrix (TensorPower a n)))
                  (productState (states ·.succ)).matrix).symm
          _ = Matrix.kronecker ((star (U : CMatrix a) * (states 0).matrix) * (U : CMatrix a))
                ((star (Un : CMatrix (TensorPower a n)) *
                    (productState (states ·.succ)).matrix) *
                  (Un : CMatrix (TensorPower a n))) := by
              exact (Matrix.mul_kronecker_mul
                (star (U : CMatrix a) * (states 0).matrix) (U : CMatrix a)
                (star (Un : CMatrix (TensorPower a n)) *
                  (productState (states ·.succ)).matrix)
                (Un : CMatrix (TensorPower a n))).symm
          _ = Matrix.kronecker A B := by
              rfl
      rw [hkr]
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      have hBdiag :
          B zs zs =
            ∏ i : Fin n,
              (star (U : CMatrix a) * (states i.succ).matrix * (U : CMatrix a))
                ((tensorPowerEquiv n zs) i) ((tensorPowerEquiv n zs) i) := by
        dsimp [B, Un]
        exact unitaryTensorPowerMatrix_conj_productState_diag U (states ·.succ) zs
      rw [hBdiag]
      rw [Fin.prod_univ_succ]
      simp [A]

/-- Product mass of an output word under an i.i.d. finite distribution. -/
def marginalProductMass {β : Type v} [Fintype β] {n : ℕ}
    (p : QIT.FiniteDistribution β) (zseq : Fin n → β) : ℝ≥0 :=
  ∏ i : Fin n, p.prob (zseq i)

/-- The i.i.d. product mass of a finite distribution sums to one. -/
theorem marginalProductMass_sum_eq_one {β : Type v} [Fintype β] [DecidableEq β]
    {n : ℕ} (p : QIT.FiniteDistribution β) :
    ∑ zseq : Fin n → β, marginalProductMass p zseq = 1 := by
  classical
  unfold marginalProductMass
  calc
    ∑ zseq : Fin n → β, ∏ i : Fin n, p.prob (zseq i)
        = ∑ zseq ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset β)),
            ∏ i : Fin n, p.prob (zseq i) := by
              rw [Fintype.piFinset_univ]
      _ = ∏ i : Fin n, ∑ z ∈ (Finset.univ : Finset β), p.prob z := by
              rw [Finset.sum_prod_piFinset]
      _ = ∏ _i : Fin n, (1 : ℝ≥0) := by
              refine Finset.prod_congr rfl fun _i _ => ?_
              simpa using p.sum_eq_one
      _ = 1 := by simp

/-- The diagonal i.i.d. product state for a finite classical distribution. -/
def marginalProductDiagonalState {β : Type v} [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution β) (n : ℕ) : State (TensorPower β n) :=
  Classical.diagonalState
    (fun z : TensorPower β n => marginalProductMass p (tensorPowerEquiv n z))
    (by
      classical
      have hsum :
          (∑ z : TensorPower β n, marginalProductMass p (tensorPowerEquiv n z)) =
            ∑ zseq : Fin n → β, marginalProductMass p zseq := by
        exact Fintype.sum_equiv (tensorPowerEquiv n)
          (fun z : TensorPower β n => marginalProductMass p (tensorPowerEquiv n z))
          (fun zseq : Fin n → β => marginalProductMass p zseq)
          (by intro z; rfl)
      rw [hsum]
      exact marginalProductMass_sum_eq_one p)

@[simp]
theorem marginalProductDiagonalState_matrix {β : Type v} [Fintype β]
    [DecidableEq β] (p : QIT.FiniteDistribution β) (n : ℕ) :
    (marginalProductDiagonalState p n).matrix =
      Matrix.diagonal (fun z : TensorPower β n =>
        ((marginalProductMass p (tensorPowerEquiv n z) : ℝ) : ℂ)) := by
  rfl

/-- The tensor power of a density matrix is diagonalized by the tensor power of
the one-symbol eigenvector unitary, with diagonal entries given by the
eigenvalue-product distribution. -/
theorem unitaryTensorPowerMatrix_conj_tensorPower_eq_marginalProductDiagonalState
    {a : Type u} [Fintype a] [DecidableEq a] (ρ : State a) :
    ∀ n : ℕ,
      star (unitaryTensorPowerMatrix ρ.pos.isHermitian.eigenvectorUnitary n :
          CMatrix (TensorPower a n)) *
          (ρ.tensorPower n).matrix *
          (unitaryTensorPowerMatrix ρ.pos.isHermitian.eigenvectorUnitary n :
            CMatrix (TensorPower a n)) =
        (marginalProductDiagonalState (stateEigenvalueDistribution ρ) n).matrix
  | 0 => by
      ext x y
      cases x
      cases y
      simp [unitaryTensorPowerMatrix, State.tensorPower, marginalProductDiagonalState,
        marginalProductMass, State.unit]
  | n + 1 => by
      let U := ρ.pos.isHermitian.eigenvectorUnitary
      let Un := unitaryTensorPowerMatrix U n
      have hstar :
          star (Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n))) =
            Matrix.kronecker (star (U : CMatrix a)) (star (Un : CMatrix (TensorPower a n))) := by
        simpa [Matrix.star_eq_conjTranspose] using
          Matrix.conjTranspose_kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n))
      change
        star (Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n))) *
              Matrix.kronecker ρ.matrix (ρ.tensorPower n).matrix *
              Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)) =
          (marginalProductDiagonalState (stateEigenvalueDistribution ρ) (n + 1)).matrix
      rw [hstar]
      let A : CMatrix a := star (U : CMatrix a) * ρ.matrix * (U : CMatrix a)
      let B : CMatrix (TensorPower a n) :=
        star (Un : CMatrix (TensorPower a n)) *
          (ρ.tensorPower n).matrix *
          (Un : CMatrix (TensorPower a n))
      have hkr :
          Matrix.kronecker (star (U : CMatrix a)) (star (Un : CMatrix (TensorPower a n))) *
                Matrix.kronecker ρ.matrix (ρ.tensorPower n).matrix *
                Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)) =
            Matrix.kronecker A B := by
        calc
          Matrix.kronecker (star (U : CMatrix a)) (star (Un : CMatrix (TensorPower a n))) *
                Matrix.kronecker ρ.matrix (ρ.tensorPower n).matrix *
                Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)) =
            Matrix.kronecker (star (U : CMatrix a) * ρ.matrix)
                (star (Un : CMatrix (TensorPower a n)) * (ρ.tensorPower n).matrix) *
                Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)) := by
              exact congrArg
                (fun M : CMatrix (Prod a (TensorPower a n)) =>
                  M * Matrix.kronecker (U : CMatrix a) (Un : CMatrix (TensorPower a n)))
                (Matrix.mul_kronecker_mul
                  (star (U : CMatrix a)) ρ.matrix
                  (star (Un : CMatrix (TensorPower a n)))
                  (ρ.tensorPower n).matrix).symm
          _ = Matrix.kronecker ((star (U : CMatrix a) * ρ.matrix) * (U : CMatrix a))
                ((star (Un : CMatrix (TensorPower a n)) * (ρ.tensorPower n).matrix) *
                  (Un : CMatrix (TensorPower a n))) := by
              exact (Matrix.mul_kronecker_mul
                (star (U : CMatrix a) * ρ.matrix) (U : CMatrix a)
                (star (Un : CMatrix (TensorPower a n)) * (ρ.tensorPower n).matrix)
                (Un : CMatrix (TensorPower a n))).symm
          _ = Matrix.kronecker A B := by rfl
      rw [hkr]
      have hA : A =
          Matrix.diagonal
            (fun i => (((stateEigenvalueDistribution ρ).prob i : ℝ≥0) : ℂ)) := by
        dsimp [A, U]
        exact stateEigenbasis_conj_matrix_eq_diagonalEigenvalueProb ρ
      have hB : B = (marginalProductDiagonalState (stateEigenvalueDistribution ρ) n).matrix := by
        dsimp [B, Un, U]
        exact unitaryTensorPowerMatrix_conj_tensorPower_eq_marginalProductDiagonalState ρ n
      rw [hA, hB]
      ext x y
      cases x with
      | mk x0 xs =>
      cases y with
      | mk y0 ys =>
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      by_cases h0 : x0 = y0
      · subst y0
        by_cases hs : xs = ys
        · subst ys
          rw [marginalProductDiagonalState_matrix (stateEigenvalueDistribution ρ) n,
            marginalProductDiagonalState_matrix (stateEigenvalueDistribution ρ) (n + 1)]
          simp [marginalProductMass, Fin.prod_univ_succ]
        · have hpair : (x0, xs) ≠ (x0, ys) := by
            intro h
            exact hs (Prod.mk.inj h).2
          rw [marginalProductDiagonalState_matrix (stateEigenvalueDistribution ρ) n,
            marginalProductDiagonalState_matrix (stateEigenvalueDistribution ρ) (n + 1)]
          by_cases hp : (x0, xs) = (x0, ys)
          · exact False.elim (hpair hp)
          · simp [Matrix.diagonal_apply, hs]
            intro h
            exact False.elim (hp h)
      · have hpair : (x0, xs) ≠ (y0, ys) := by
          intro h
          exact h0 (Prod.mk.inj h).1
        rw [marginalProductDiagonalState_matrix (stateEigenvalueDistribution ρ) n,
          marginalProductDiagonalState_matrix (stateEigenvalueDistribution ρ) (n + 1)]
        by_cases hp : (x0, xs) = (y0, ys)
        · exact False.elim (hpair hp)
        · simp [Matrix.diagonal_apply, h0]
          intro h
          exact False.elim (hp h)

/-- Tensor powers of a one-symbol classical diagonal state are the diagonal
i.i.d. product states used by the source-shaped HSW strong-typical route. -/
theorem diagonalState_tensorPower_matrix_eq_marginalProductDiagonalState
    {β : Type v} [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution β) (n : ℕ) :
    ((Classical.diagonalState p.prob p.sum_eq_one).tensorPower n).matrix =
      (marginalProductDiagonalState p n).matrix := by
  ext x y
  rw [State.tensorPower_matrix_apply]
  rw [marginalProductDiagonalState_matrix]
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq]
    simp [marginalProductMass, Classical.diagonalState_apply_self]
  · have hseq_ne : tensorPowerEquiv n x ≠ tensorPowerEquiv n y := by
      intro hseq
      exact hxy ((tensorPowerEquiv n).injective hseq)
    have hidx : ∃ i : Fin n, tensorPowerEquiv n x i ≠ tensorPowerEquiv n y i := by
      by_contra hnone
      apply hseq_ne
      funext i
      by_contra hne
      exact hnone ⟨i, hne⟩
    obtain ⟨i, hi⟩ := hidx
    have hfactor_zero :
        (Classical.diagonalState p.prob p.sum_eq_one).matrix
          ((tensorPowerEquiv n x) i) ((tensorPowerEquiv n y) i) = 0 :=
      Classical.diagonalState_apply_ne p.prob p.sum_eq_one hi
    have hprod_zero :
        (∏ j : Fin n,
          (Classical.diagonalState p.prob p.sum_eq_one).matrix
            ((tensorPowerEquiv n x) j) ((tensorPowerEquiv n y) j)) = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hfactor_zero]
    rw [hprod_zero]
    rw [Matrix.diagonal_apply_ne _ hxy]

/-- Projected-average pack-4 kernel for the source-shaped diagonal route.

If every strong-typical output word has i.i.d. marginal product mass at most
`D⁻¹`, then the strong-typical diagonal projector satisfies the packing
lemma's projected-average inequality against the diagonal i.i.d. product
state.  Later source-specific rate lemmas discharge `hmass_bound` with the
usual entropy exponent; this lemma isolates the matrix-order step and keeps
that numerical envelope explicit. -/
theorem strongTypicalDiagonalProjector_projectedMarginalProduct_le_of_mass_bound
    {β : Type v} [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution β) {n : ℕ} {δ D : ℝ}
    (hmass_bound : ∀ zseq : Fin n → β,
      ClassicalTypicality.StrongTypical p zseq δ →
        (marginalProductMass p zseq : ℝ) ≤ D⁻¹) :
    strongTypicalDiagonalProjector p n δ *
        (marginalProductDiagonalState p n).matrix *
        strongTypicalDiagonalProjector p n δ
      ≤ ((D : ℝ)⁻¹) • strongTypicalDiagonalProjector p n δ := by
  classical
  rw [Matrix.le_iff]
  rw [marginalProductDiagonalState_matrix]
  unfold strongTypicalDiagonalProjector
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have hdiag :
      (((D : ℝ)⁻¹) •
          Matrix.diagonal (fun z : TensorPower β n =>
            if ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
            then (1 : ℂ) else 0) -
        Matrix.diagonal (fun z : TensorPower β n =>
          (if ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
            then (1 : ℂ) else 0) *
          ((marginalProductMass p (tensorPowerEquiv n z) : ℝ) : ℂ) *
          (if ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
            then (1 : ℂ) else 0)) : CMatrix (TensorPower β n)) =
        Matrix.diagonal (fun z : TensorPower β n =>
          ((D : ℝ)⁻¹ : ℂ) *
            (if ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
              then (1 : ℂ) else 0) -
          (if ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
            then (1 : ℂ) else 0) *
          ((marginalProductMass p (tensorPowerEquiv n z) : ℝ) : ℂ) *
          (if ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
            then (1 : ℂ) else 0)) := by
    ext z z'
    by_cases hzz' : z = z'
    · subst z'
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hzz']
  rw [hdiag, Matrix.posSemidef_diagonal_iff]
  intro z
  by_cases hz : ClassicalTypicality.StrongTypical p (tensorPowerEquiv n z) δ
  · have hbound := hmass_bound (tensorPowerEquiv n z) hz
    have hboundC :
        (((marginalProductMass p (tensorPowerEquiv n z) : ℝ) : ℂ)) ≤
          (((D : ℝ)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast hbound
    simpa [hz, sub_nonneg] using hboundC
  · simp [hz]

/-- Unitary conjugation preserves Loewner order. -/
theorem cMatrix_unitary_conjugate_le {a : Type u} [Fintype a] [DecidableEq a]
    (U : Matrix.unitaryGroup a ℂ) {A B : CMatrix a} (hAB : A ≤ B) :
    (U : CMatrix a) * A * star (U : CMatrix a) ≤
      (U : CMatrix a) * B * star (U : CMatrix a) := by
  rw [Matrix.le_iff] at hAB ⊢
  have hpsd :
      ((U : CMatrix a) * (B - A) * star (U : CMatrix a)).PosSemidef := by
    simpa [Matrix.star_eq_conjTranspose] using
      hAB.conjTranspose_mul_mul_same (star (U : CMatrix a))
  have hdiff :
      (U : CMatrix a) * B * star (U : CMatrix a) -
          (U : CMatrix a) * A * star (U : CMatrix a) =
        (U : CMatrix a) * (B - A) * star (U : CMatrix a) := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  simpa [hdiff] using hpsd

/-- Source-shaped projected-average pack-4 kernel.

This is the unitary-conjugated version of
`strongTypicalDiagonalProjector_projectedMarginalProduct_le_of_mass_bound`: the
source projector `U^{⊗n} Π_typ U^{⊗n†}` compresses `ρ^{⊗n}` exactly as the
classical diagonal projector compresses the i.i.d. eigenvalue-product law. -/
theorem sourceTypicalSubspaceProjector_projectedTensorPower_le_of_mass_bound
    {a : Type u} [Fintype a] [DecidableEq a] (ρ : State a)
    {n : ℕ} {δ D : ℝ}
    (hmass_bound : ∀ zseq : Fin n → a,
      ClassicalTypicality.StrongTypical (stateEigenvalueDistribution ρ) zseq δ →
        (marginalProductMass (stateEigenvalueDistribution ρ) zseq : ℝ) ≤ D⁻¹) :
    sourceTypicalSubspaceProjector ρ n δ *
        (ρ.tensorPower n).matrix *
        sourceTypicalSubspaceProjector ρ n δ
      ≤ ((D : ℝ)⁻¹) • sourceTypicalSubspaceProjector ρ n δ := by
  classical
  let U := unitaryTensorPowerMatrix ρ.pos.isHermitian.eigenvectorUnitary n
  let P : CMatrix (TensorPower a n) :=
    strongTypicalDiagonalProjector (stateEigenvalueDistribution ρ) n δ
  let M : CMatrix (TensorPower a n) :=
    (marginalProductDiagonalState (stateEigenvalueDistribution ρ) n).matrix
  have hdiag :
      star (U : CMatrix (TensorPower a n)) * (ρ.tensorPower n).matrix *
          (U : CMatrix (TensorPower a n)) =
        M := by
    dsimp [U, M]
    exact unitaryTensorPowerMatrix_conj_tensorPower_eq_marginalProductDiagonalState ρ n
  have hUUstar : (U : CMatrix (TensorPower a n)) *
        star (U : CMatrix (TensorPower a n)) = 1 :=
    Unitary.coe_mul_star_self U
  have hstarUU : star (U : CMatrix (TensorPower a n)) *
        (U : CMatrix (TensorPower a n)) = 1 :=
    Unitary.coe_star_mul_self U
  have hρ :
      (ρ.tensorPower n).matrix =
        (U : CMatrix (TensorPower a n)) * M * star (U : CMatrix (TensorPower a n)) := by
    calc
      (ρ.tensorPower n).matrix =
          1 * (ρ.tensorPower n).matrix * 1 := by simp
      _ = ((U : CMatrix (TensorPower a n)) * star (U : CMatrix (TensorPower a n))) *
            (ρ.tensorPower n).matrix *
            ((U : CMatrix (TensorPower a n)) * star (U : CMatrix (TensorPower a n))) := by
          rw [hUUstar]
      _ = (U : CMatrix (TensorPower a n)) *
            (star (U : CMatrix (TensorPower a n)) * (ρ.tensorPower n).matrix *
              (U : CMatrix (TensorPower a n))) *
            star (U : CMatrix (TensorPower a n)) := by
          noncomm_ring
      _ = (U : CMatrix (TensorPower a n)) * M *
            star (U : CMatrix (TensorPower a n)) := by rw [hdiag]
  have hdiag_bound :
      P * M * P ≤ ((D : ℝ)⁻¹) • P := by
    dsimp [P, M]
    exact strongTypicalDiagonalProjector_projectedMarginalProduct_le_of_mass_bound
      (stateEigenvalueDistribution ρ) (n := n) (δ := δ) (D := D) hmass_bound
  have hconj :
      (U : CMatrix (TensorPower a n)) * (P * M * P) *
          star (U : CMatrix (TensorPower a n)) ≤
        (U : CMatrix (TensorPower a n)) * (((D : ℝ)⁻¹) • P) *
          star (U : CMatrix (TensorPower a n)) :=
    cMatrix_unitary_conjugate_le U hdiag_bound
  have hleft :
      sourceTypicalSubspaceProjector ρ n δ *
          (ρ.tensorPower n).matrix *
          sourceTypicalSubspaceProjector ρ n δ =
        (U : CMatrix (TensorPower a n)) * (P * M * P) *
          star (U : CMatrix (TensorPower a n)) := by
    have hsrc :
        sourceTypicalSubspaceProjector ρ n δ =
          (U : CMatrix (TensorPower a n)) * P * star (U : CMatrix (TensorPower a n)) := by
      rfl
    rw [hsrc, hρ]
    calc
      ((U : CMatrix (TensorPower a n)) * P * star (U : CMatrix (TensorPower a n))) *
            ((U : CMatrix (TensorPower a n)) * M * star (U : CMatrix (TensorPower a n))) *
            ((U : CMatrix (TensorPower a n)) * P * star (U : CMatrix (TensorPower a n))) =
          (U : CMatrix (TensorPower a n)) * P *
            (star (U : CMatrix (TensorPower a n)) * (U : CMatrix (TensorPower a n))) *
            M *
            (star (U : CMatrix (TensorPower a n)) * (U : CMatrix (TensorPower a n))) *
            P * star (U : CMatrix (TensorPower a n)) := by
            noncomm_ring
      _ = (U : CMatrix (TensorPower a n)) * P * 1 * M * 1 * P *
            star (U : CMatrix (TensorPower a n)) := by
            rw [hstarUU]
      _ = (U : CMatrix (TensorPower a n)) * (P * M * P) *
            star (U : CMatrix (TensorPower a n)) := by
            noncomm_ring
  have hright :
      (U : CMatrix (TensorPower a n)) * (((D : ℝ)⁻¹) • P) *
          star (U : CMatrix (TensorPower a n)) =
        ((D : ℝ)⁻¹) • sourceTypicalSubspaceProjector ρ n δ := by
    dsimp [sourceTypicalSubspaceProjector, U, P]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  simpa [hleft, hright] using hconj

/-- Every finite i.i.d. product mass is bounded by one. -/
theorem marginalProductMass_le_one {β : Type v} [Fintype β] {n : ℕ}
    (p : QIT.FiniteDistribution β) (zseq : Fin n → β) :
    marginalProductMass p zseq ≤ 1 := by
  classical
  unfold marginalProductMass
  refine Finset.prod_le_one ?_ ?_
  · intro i _
    positivity
  · intro i _
    exact p.prob_le_one (zseq i)

private theorem x_mul_log2_eq_xlog2 (x : ℝ) :
    x * log2 x = xlog2 x := by
  by_cases hz : x = 0
  · simp [xlog2, hz]
  · simp [xlog2, hz]

private theorem log2_nonpos_of_prob {β : Type v} [Fintype β]
    (p : QIT.FiniteDistribution β) (z : β) :
    log2 (p.prob z : ℝ) ≤ 0 := by
  unfold log2
  have hlog_nonpos :
      Real.log (p.prob z : ℝ) ≤ 0 := by
    exact Real.log_nonpos (by positivity) (by exact_mod_cast p.prob_le_one z)
  exact div_nonpos_of_nonpos_of_nonneg hlog_nonpos
    (le_of_lt (Real.log_pos one_lt_two))

private theorem wordCount_real_eq_length_mul_wordFreq {β : Type v} [DecidableEq β]
    {n : ℕ} (zseq : Fin n → β) (z : β) (hn : 0 < n) :
    (ClassicalTypicality.wordCount zseq z : ℝ) =
      (n : ℝ) * ClassicalTypicality.wordFreq zseq z := by
  unfold ClassicalTypicality.wordFreq
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [hnR]

/-- Positive-mass log-product identity for the i.i.d. marginal product mass. -/
theorem log2_marginalProductMass_eq_sum_log2_of_pos {β : Type v} [Fintype β]
    {n : ℕ} (p : QIT.FiniteDistribution β) (zseq : Fin n → β)
    (hpos : 0 < (marginalProductMass p zseq : ℝ)) :
    log2 (marginalProductMass p zseq : ℝ) =
      ∑ i : Fin n, log2 (p.prob (zseq i) : ℝ) := by
  have hfactor_ne : ∀ i : Fin n, (p.prob (zseq i) : ℝ) ≠ 0 := by
    intro i hi
    have hprod_zero : (∏ j : Fin n, (p.prob (zseq j) : ℝ)) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hmass_zero : (marginalProductMass p zseq : ℝ) = 0 := by
      unfold marginalProductMass
      simp [hprod_zero]
    linarith
  unfold marginalProductMass log2
  rw [NNReal.coe_prod]
  change Real.log (∏ i : Fin n, (p.prob (zseq i) : ℝ)) / Real.log 2 =
    ∑ i : Fin n, Real.log (p.prob (zseq i) : ℝ) / Real.log 2
  rw [Real.log_prod]
  · rw [Finset.sum_div]
  · intro i _hi
    exact hfactor_ne i

/-- Strong typicality implies the usual finite classical product-mass
envelope, with an explicit log-slack constant:
`p^n(z^n) ≤ 2^{-n H(p) + n δ L(p)}`.

The statement deliberately exposes the `L(p)` slack instead of hiding support
assumptions.  If the product mass is zero, the bound is trivial; otherwise the
proof takes logs, groups coordinates by symbol counts, and uses
`|freq(z)-p(z)|≤δ` with `log₂ p(z)≤0`. -/
theorem marginalProductMass_le_rpow_entropy_slack {β : Type v} [Fintype β]
    [DecidableEq β] {n : ℕ}
    (p : QIT.FiniteDistribution β) (zseq : Fin n → β) {δ : ℝ}
    (hn : 0 < n) (hδ : 0 ≤ δ)
    (hz : ClassicalTypicality.StrongTypical p zseq δ) :
    (marginalProductMass p zseq : ℝ) ≤
      Real.rpow 2
        (- (n : ℝ) * p.shannonEntropy + (n : ℝ) * δ * p.logTypicalitySlack) := by
  by_cases hzero : (marginalProductMass p zseq : ℝ) = 0
  · rw [hzero]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  · have hmass_nonneg : 0 ≤ (marginalProductMass p zseq : ℝ) := by positivity
    have hmass_pos : 0 < (marginalProductMass p zseq : ℝ) :=
      lt_of_le_of_ne hmass_nonneg (Ne.symm hzero)
    let e : ℝ := - (n : ℝ) * p.shannonEntropy + (n : ℝ) * δ * p.logTypicalitySlack
    have hlogprod := log2_marginalProductMass_eq_sum_log2_of_pos p zseq hmass_pos
    have hlog2_le : log2 (marginalProductMass p zseq : ℝ) ≤ e := by
      rw [hlogprod]
      rw [ClassicalTypicality.sum_eq_sum_wordCount_mul
        (xseq := zseq) (f := fun z : β => log2 (p.prob z : ℝ))]
      have hrewrite :
          (∑ z : β, (ClassicalTypicality.wordCount zseq z : ℝ) *
              log2 (p.prob z : ℝ)) =
            (n : ℝ) * ∑ z : β, ClassicalTypicality.wordFreq zseq z *
              log2 (p.prob z : ℝ) := by
        calc
          (∑ z : β, (ClassicalTypicality.wordCount zseq z : ℝ) *
              log2 (p.prob z : ℝ)) =
              ∑ z : β, ((n : ℝ) * ClassicalTypicality.wordFreq zseq z) *
                log2 (p.prob z : ℝ) := by
                refine Finset.sum_congr rfl fun z _ => ?_
                rw [wordCount_real_eq_length_mul_wordFreq zseq z hn]
          _ = (n : ℝ) * ∑ z : β, ClassicalTypicality.wordFreq zseq z *
                log2 (p.prob z : ℝ) := by
                rw [Finset.mul_sum]
                ring_nf
      rw [hrewrite]
      have hinner :
          (∑ z : β, ClassicalTypicality.wordFreq zseq z * log2 (p.prob z : ℝ)) ≤
            (∑ z : β, xlog2 (p.prob z : ℝ)) +
              δ * p.logTypicalitySlack := by
        calc
          (∑ z : β, ClassicalTypicality.wordFreq zseq z * log2 (p.prob z : ℝ))
              ≤ ∑ z : β, ((p.prob z : ℝ) - δ) * log2 (p.prob z : ℝ) := by
                refine Finset.sum_le_sum fun z _ => ?_
                have hz_lower : (p.prob z : ℝ) - δ ≤
                    ClassicalTypicality.wordFreq zseq z := by
                  have hle := (abs_le.mp (hz z)).1
                  linarith
                exact mul_le_mul_of_nonpos_right hz_lower (log2_nonpos_of_prob p z)
          _ = (∑ z : β, xlog2 (p.prob z : ℝ)) -
                δ * ∑ z : β, log2 (p.prob z : ℝ) := by
                calc
                  (∑ z : β, ((p.prob z : ℝ) - δ) * log2 (p.prob z : ℝ)) =
                      ∑ z : β,
                        (xlog2 (p.prob z : ℝ) - δ * log2 (p.prob z : ℝ)) := by
                        refine Finset.sum_congr rfl fun z _ => ?_
                        rw [sub_mul]
                        rw [x_mul_log2_eq_xlog2 (p.prob z : ℝ)]
                  _ = (∑ z : β, xlog2 (p.prob z : ℝ)) -
                        ∑ z : β, δ * log2 (p.prob z : ℝ) := by
                        rw [Finset.sum_sub_distrib]
                  _ = (∑ z : β, xlog2 (p.prob z : ℝ)) -
                        δ * ∑ z : β, log2 (p.prob z : ℝ) := by
                        rw [Finset.mul_sum]
          _ ≤ (∑ z : β, xlog2 (p.prob z : ℝ)) +
                δ * p.logTypicalitySlack := by
                unfold FiniteDistribution.logTypicalitySlack
                have hsum_neg_le_abs :
                    -∑ z : β, log2 (p.prob z : ℝ) ≤
                      ∑ z : β, |log2 (p.prob z : ℝ)| := by
                  calc
                    -∑ z : β, log2 (p.prob z : ℝ)
                        = ∑ z : β, -log2 (p.prob z : ℝ) := by
                            rw [Finset.sum_neg_distrib]
                    _ ≤ ∑ z : β, |log2 (p.prob z : ℝ)| := by
                            refine Finset.sum_le_sum fun z _ => ?_
                            exact neg_le_abs _
                have hmul := mul_le_mul_of_nonneg_left hsum_neg_le_abs hδ
                linarith
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hmul := mul_le_mul_of_nonneg_left hinner hn_nonneg
      have he :
          e =
            (n : ℝ) *
              ((∑ z : β, xlog2 (p.prob z : ℝ)) +
                δ * ∑ z : β, |log2 (p.prob z : ℝ)|) := by
        dsimp [e, FiniteDistribution.shannonEntropy, FiniteDistribution.logTypicalitySlack]
        ring
      rw [he]
      exact hmul
    have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlog_le : Real.log (marginalProductMass p zseq : ℝ) ≤ e * Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hlog2_le (le_of_lt hlog2pos)
      unfold log2 at hmul
      field_simp [ne_of_gt hlog2pos] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have htarget_pos : 0 < Real.rpow 2 e :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) e
    have htarget_log : Real.log (Real.rpow 2 e) = e * Real.log 2 :=
      Real.log_rpow (by norm_num : (0 : ℝ) < 2) e
    have hlog_le_target :
        Real.log (marginalProductMass p zseq : ℝ) ≤ Real.log (Real.rpow 2 e) := by
      rw [htarget_log]
      exact hlog_le
    exact (Real.log_le_log_iff hmass_pos htarget_pos).mp hlog_le_target

/-- Strong-typical product-mass envelope in the exact `D⁻¹` form consumed by
the HSW pack-4 hypothesis.

The side condition states the explicit source exponent choice for `D`: if the
usual bound `2^{-n H(p) + n δ L(p)}` is at most `D⁻¹`, then every strongly
typical word has i.i.d. product mass at most `D⁻¹`. -/
theorem marginalProductMass_le_D_inv_of_entropy_slack {β : Type v} [Fintype β]
    [DecidableEq β] {n : ℕ}
    (p : QIT.FiniteDistribution β) (zseq : Fin n → β) {δ D : ℝ}
    (hn : 0 < n) (hδ : 0 ≤ δ)
    (hD :
      Real.rpow 2
        (- (n : ℝ) * p.shannonEntropy + (n : ℝ) * δ * p.logTypicalitySlack)
        ≤ D⁻¹)
    (hz : ClassicalTypicality.StrongTypical p zseq δ) :
    (marginalProductMass p zseq : ℝ) ≤ D⁻¹ :=
  le_trans (marginalProductMass_le_rpow_entropy_slack p zseq hn hδ hz) hD

/-- Strong-typical product-mass envelope with the canonical HSW mass scale
`D = 2^{nH(p)-nδL(p)}`. -/
theorem marginalProductMass_le_strongTypicalMassScale_inv
    {β : Type v} [Fintype β] [DecidableEq β] {n : ℕ}
    (p : QIT.FiniteDistribution β) (zseq : Fin n → β) {δ : ℝ}
    (hn : 0 < n) (hδ : 0 ≤ δ)
    (hz : ClassicalTypicality.StrongTypical p zseq δ) :
    (marginalProductMass p zseq : ℝ) ≤ (p.strongTypicalMassScale n δ)⁻¹ := by
  refine marginalProductMass_le_D_inv_of_entropy_slack p zseq hn hδ ?_ hz
  exact le_of_eq (p.rpow_entropy_slack_eq_strongTypicalMassScale_inv n δ)

/-- Source-shaped projected-average pack-4 envelope in entropy-scale form.

This packages
`sourceTypicalSubspaceProjector_projectedTensorPower_le_of_mass_bound` with the
standard strong-typical product-mass estimate. The numerical side condition is
kept explicit: callers may instantiate `D` either with the canonical
`strongTypicalMassScale` or with any smaller denominator justified by a
separate asymptotic estimate. -/
theorem sourceTypicalSubspaceProjector_projectedTensorPower_le_of_entropy_slack
    {a : Type u} [Fintype a] [DecidableEq a] (ρ : State a)
    {n : ℕ} {δ D : ℝ} (hn : 0 < n) (hδ : 0 ≤ δ)
    (hD :
      Real.rpow 2
        (- (n : ℝ) * (stateEigenvalueDistribution ρ).shannonEntropy +
          (n : ℝ) * δ * (stateEigenvalueDistribution ρ).logTypicalitySlack)
        ≤ D⁻¹) :
    sourceTypicalSubspaceProjector ρ n δ *
        (ρ.tensorPower n).matrix *
        sourceTypicalSubspaceProjector ρ n δ
      ≤ ((D : ℝ)⁻¹) • sourceTypicalSubspaceProjector ρ n δ := by
  refine sourceTypicalSubspaceProjector_projectedTensorPower_le_of_mass_bound
    ρ ?_
  intro zseq hz
  exact marginalProductMass_le_D_inv_of_entropy_slack
    (stateEigenvalueDistribution ρ) zseq hn hδ hD hz

/-- Source-shaped projected-average pack-4 envelope at the canonical
strong-typical mass scale of the average state's eigenvalue distribution. -/
theorem sourceTypicalSubspaceProjector_projectedTensorPower_le_strongTypicalMassScale
    {a : Type u} [Fintype a] [DecidableEq a] (ρ : State a)
    {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 ≤ δ) :
    sourceTypicalSubspaceProjector ρ n δ *
        (ρ.tensorPower n).matrix *
        sourceTypicalSubspaceProjector ρ n δ
      ≤ (((stateEigenvalueDistribution ρ).strongTypicalMassScale n δ : ℝ)⁻¹) •
          sourceTypicalSubspaceProjector ρ n δ := by
  refine sourceTypicalSubspaceProjector_projectedTensorPower_le_of_entropy_slack
    ρ hn hδ ?_
  exact le_of_eq
    ((stateEigenvalueDistribution ρ).rpow_entropy_slack_eq_strongTypicalMassScale_inv
      n δ)

/-- Weak fully-closed projected-average pack-4 kernel for the diagonal route:
with `D = 1`, the strong-typical diagonal projector always satisfies
`P σ P ≤ P` against the i.i.d. diagonal product state.  This is not the
entropy-exponent estimate needed for the final HSW rate; it is the
placeholder-free matrix bridge that the source-shaped diagonal route can use
before the sharper entropy envelope is supplied. -/
theorem strongTypicalDiagonalProjector_projectedMarginalProduct_le_one
    {β : Type v} [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution β) (n : ℕ) (δ : ℝ) :
    strongTypicalDiagonalProjector p n δ *
        (marginalProductDiagonalState p n).matrix *
        strongTypicalDiagonalProjector p n δ
      ≤ ((1 : ℝ)⁻¹) • strongTypicalDiagonalProjector p n δ := by
  refine strongTypicalDiagonalProjector_projectedMarginalProduct_le_of_mass_bound
    p (n := n) (δ := δ) (D := 1) ?_
  intro zseq _hz
  simpa using marginalProductMass_le_one p zseq

/-- The diagonal matrix of the conditional product law
`p_{Z^n|X^n}(.|x^n)` on the tensor-power output basis. -/
def conditionalProductDiagonalMatrix {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) :
    CMatrix (TensorPower β n) :=
  Matrix.diagonal fun z =>
    ((ClassicalTypicality.conditionalProductMass K xseq (tensorPowerEquiv n z) : ℝ) : ℂ)

/-- The pinched conditional product law is a normalized diagonal state. -/
def conditionalProductDiagonalState {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) :
    State (TensorPower β n) :=
  Classical.diagonalState
    (fun z : TensorPower β n =>
      ClassicalTypicality.conditionalProductMass K xseq (tensorPowerEquiv n z))
    (by
      classical
      have hsum :
          (∑ z : TensorPower β n,
              ClassicalTypicality.conditionalProductMass K xseq (tensorPowerEquiv n z)) =
            ∑ zseq : Fin n → β,
              ClassicalTypicality.conditionalProductMass K xseq zseq := by
        exact Fintype.sum_equiv (tensorPowerEquiv n)
          (fun z : TensorPower β n =>
            ClassicalTypicality.conditionalProductMass K xseq (tensorPowerEquiv n z))
          (fun zseq : Fin n → β =>
            ClassicalTypicality.conditionalProductMass K xseq zseq)
          (by intro z; rfl)
      rw [hsum]
      exact ClassicalTypicality.conditionalProductMass_sum_eq_one K xseq)

@[simp]
theorem conditionalProductDiagonalState_matrix {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) :
    (conditionalProductDiagonalState K xseq).matrix =
      conditionalProductDiagonalMatrix K xseq := by
  rfl

/-- The diagonal conditional product law is the product of the one-symbol
classical diagonal states `diag(K(.|x_i))`. -/
theorem conditionalProductDiagonalState_matrix_eq_productState_diagonal
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (K : QIT.StochasticKernel α β) (xseq : Fin n → α) :
    (conditionalProductDiagonalState K xseq).matrix =
      (productState fun i : Fin n =>
        Classical.diagonalState (K.prob (xseq i)) (K.sum_eq_one (xseq i))).matrix := by
  ext x y
  rw [productState_matrix_apply]
  rw [conditionalProductDiagonalState_matrix]
  unfold conditionalProductDiagonalMatrix
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq]
    simp [ClassicalTypicality.conditionalProductMass, Classical.diagonalState_apply_self]
  · have hseq_ne : tensorPowerEquiv n x ≠ tensorPowerEquiv n y := by
      intro hseq
      exact hxy ((tensorPowerEquiv n).injective hseq)
    have hidx : ∃ i : Fin n, tensorPowerEquiv n x i ≠ tensorPowerEquiv n y i := by
      by_contra hnone
      apply hseq_ne
      funext i
      by_contra hne
      exact hnone ⟨i, hne⟩
    obtain ⟨i, hi⟩ := hidx
    have hfactor_zero :
        (Classical.diagonalState (K.prob (xseq i)) (K.sum_eq_one (xseq i))).matrix
          ((tensorPowerEquiv n x) i) ((tensorPowerEquiv n y) i) = 0 :=
      Classical.diagonalState_apply_ne (K.prob (xseq i)) (K.sum_eq_one (xseq i)) hi
    have hprod_zero :
        (∏ j : Fin n,
          (Classical.diagonalState (K.prob (xseq j)) (K.sum_eq_one (xseq j))).matrix
            ((tensorPowerEquiv n x) j) ((tensorPowerEquiv n y) j)) = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hfactor_zero]
    rw [hprod_zero]
    rw [Matrix.diagonal_apply_ne _ hxy]

/-- The diagonal state of the induced output law is the average of the
one-symbol conditional diagonal states. -/
theorem diagonalState_inducedMarginal_matrix_eq_average_conditionalDiagonalStates
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β) :
    (Classical.diagonalState (ClassicalTypicality.inducedMarginal p K).prob
        (ClassicalTypicality.inducedMarginal p K).sum_eq_one).matrix =
      ∑ x : α, (p.prob x) •
        (Classical.diagonalState (K.prob x) (K.sum_eq_one x)).matrix := by
  ext z z'
  by_cases hzz : z = z'
  · subst z'
    rw [Matrix.sum_apply]
    simp only [Classical.diagonalState_apply_self, ClassicalTypicality.inducedMarginal_prob,
      NNReal.coe_sum, NNReal.coe_mul]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.smul_apply]
    simp only [Classical.diagonalState_apply_self, Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ, NNReal.algebraMap_eq_coe,
      Complex.coe_algebraMap]
  · simp [Classical.diagonalState_apply_ne, hzz, Matrix.sum_apply]

/-- The classical channel obtained by measuring each ensemble state in the
average state's eigenbasis.  This is the stochastic kernel used in Wilde's
pinching reduction for `prop-qt:cond-state-with-uncond-proj`. -/
noncomputable def eigenbasisStochasticKernel
    {α : Type u} {β : Type v} [Fintype α] [Fintype β] [DecidableEq β]
    (E : Ensemble α β) : QIT.StochasticKernel α β where
  prob x z := ProjectiveMeasurement.eigenbasisDiagonalProb (E.states x) E.averageState z
  sum_eq_one x := ProjectiveMeasurement.eigenbasisDiagonalProb_sum
    (E.states x) E.averageState

/-- The eigenbasis stochastic kernel is exactly the diagonal of the ensemble
state in the average state's eigenbasis. -/
theorem eigenbasisStochasticKernel_prob_coe_eq_diag
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Ensemble α β) (x : α) (z : β) :
    (((eigenbasisStochasticKernel E).prob x z : ℝ≥0) : ℂ) =
      (star (E.averageState.pos.isHermitian.eigenvectorUnitary : CMatrix β) *
          (E.states x).matrix *
          (E.averageState.pos.isHermitian.eigenvectorUnitary : CMatrix β)) z z := by
  classical
  let U : Matrix.unitaryGroup β ℂ := E.averageState.pos.isHermitian.eigenvectorUnitary
  let Y : CMatrix β := star (U : CMatrix β) * (E.states x).matrix * (U : CMatrix β)
  have hstar : Matrix.conjTranspose (star (U : CMatrix β)) = (U : CMatrix β) := by
    rw [← Matrix.star_eq_conjTranspose, star_star]
  have hpsd : Y.PosSemidef := by
    simpa [Y, hstar] using (E.states x).pos.mul_mul_conjTranspose_same (star (U : CMatrix β))
  have hreal_fun : (fun i => (((Y i i).re : ℝ) : ℂ)) = fun i => Y i i := by
    simpa [Matrix.diag] using hpsd.isHermitian.coe_re_diag
  change (((ProjectiveMeasurement.eigenbasisDiagonalProb (E.states x) E.averageState z :
      ℝ≥0) : ℝ) : ℂ) = Y z z
  rw [← congrFun hreal_fun z]
  rfl

/-- Tensoring the average-state eigenbasis measurement over a product output
state gives the conditional product diagonal law of `eigenbasisStochasticKernel`.

Only diagonal entries are asserted: this is the exact information consumed by
the source-shaped strong-typical projector trace. -/
theorem unitaryTensorPowerMatrix_conj_productState_diag_eq_conditionalProduct
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {n : ℕ} (E : Ensemble α β) (xseq : Fin n → α) (z : TensorPower β n) :
    (star (unitaryTensorPowerMatrix E.averageState.pos.isHermitian.eigenvectorUnitary n :
          CMatrix (TensorPower β n)) *
        (productState fun i : Fin n => E.states (xseq i)).matrix *
        (unitaryTensorPowerMatrix E.averageState.pos.isHermitian.eigenvectorUnitary n :
          CMatrix (TensorPower β n))) z z =
      (conditionalProductDiagonalState (eigenbasisStochasticKernel E) xseq).matrix z z := by
  classical
  rw [unitaryTensorPowerMatrix_conj_productState_diag]
  rw [conditionalProductDiagonalState_matrix]
  unfold conditionalProductDiagonalMatrix ClassicalTypicality.conditionalProductMass
  rw [Matrix.diagonal_apply_eq]
  simp_rw [← eigenbasisStochasticKernel_prob_coe_eq_diag E]
  simp

/-- The marginal law induced by measuring an ensemble in its average state's
eigenbasis is exactly the average state's eigenvalue distribution.  This is the
one-symbol probability identity behind the pinching reduction in Wilde's HSW
pack-1 route. -/
theorem inducedMarginal_eigenbasisStochasticKernel_eq_stateEigenvalueProb
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Ensemble α β) (z : β) :
    (ClassicalTypicality.inducedMarginal E.indexDistribution
        (eigenbasisStochasticKernel E)).prob z =
      ProjectiveMeasurement.stateEigenvalueProb E.averageState z := by
  classical
  apply NNReal.coe_injective
  let σbar := E.averageState
  let U : Matrix.unitaryGroup β ℂ := σbar.pos.isHermitian.eigenvectorUnitary
  let Y : CMatrix β := star (U : CMatrix β) * σbar.matrix * (U : CMatrix β)
  have hspecY :
      Y =
        Matrix.diagonal
          (fun i : β => ((ProjectiveMeasurement.stateEigenvalueProb σbar i : ℝ≥0) : ℂ)) := by
    have hσ :
        σbar.matrix =
          (U : CMatrix β) *
            Matrix.diagonal
              (fun i : β => ((ProjectiveMeasurement.stateEigenvalueProb σbar i : ℝ≥0) : ℂ)) *
            star (U : CMatrix β) := by
      simpa [σbar, U] using ProjectiveMeasurement.state_matrix_eq_unitary_diagonalEigenvalueProb
        σbar
    have hstarU : star (U : CMatrix β) * (U : CMatrix β) = 1 :=
      Unitary.coe_star_mul_self U
    change star (U : CMatrix β) * σbar.matrix * (U : CMatrix β) =
      Matrix.diagonal
        (fun i : β => ((ProjectiveMeasurement.stateEigenvalueProb σbar i : ℝ≥0) : ℂ))
    rw [hσ]
    calc
      star (U : CMatrix β) *
          ((U : CMatrix β) *
            Matrix.diagonal
              (fun i : β => ((ProjectiveMeasurement.stateEigenvalueProb σbar i : ℝ≥0) : ℂ)) *
            star (U : CMatrix β)) *
          (U : CMatrix β)
          =
        (star (U : CMatrix β) * (U : CMatrix β)) *
          Matrix.diagonal
            (fun i : β => ((ProjectiveMeasurement.stateEigenvalueProb σbar i : ℝ≥0) : ℂ)) *
          (star (U : CMatrix β) * (U : CMatrix β)) := by
          noncomm_ring
      _ = Matrix.diagonal
            (fun i : β => ((ProjectiveMeasurement.stateEigenvalueProb σbar i : ℝ≥0) : ℂ)) := by
          rw [hstarU]
          simp
  have hdiagY :
      (Y z z).re =
        (ProjectiveMeasurement.stateEigenvalueProb σbar z : ℝ) := by
    rw [hspecY]
    simp [Matrix.diagonal]
  calc
    (((ClassicalTypicality.inducedMarginal E.indexDistribution
        (eigenbasisStochasticKernel E)).prob z : ℝ≥0) : ℝ)
        =
          ∑ x : α,
            (E.probs x : ℝ) *
              (ProjectiveMeasurement.eigenbasisDiagonalProb (E.states x) σbar z : ℝ) := by
          simp [ClassicalTypicality.inducedMarginal_prob, eigenbasisStochasticKernel,
            Ensemble.indexDistribution, NNReal.coe_sum, NNReal.coe_mul, σbar]
    _ =
          (∑ x : α,
            (E.probs x : ℂ) *
              ((star (U : CMatrix β) * (E.states x).matrix * (U : CMatrix β)) z z)).re := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          change
            (E.probs x : ℝ) *
                ((star (U : CMatrix β) * (E.states x).matrix * (U : CMatrix β)) z z).re =
              (((E.probs x : ℝ) : ℂ) *
                ((star (U : CMatrix β) * (E.states x).matrix * (U : CMatrix β)) z z)).re
          simp [Complex.mul_re]
    _ = (Y z z).re := by
          have hmatrix :
              (∑ x : α,
                  (E.probs x : ℂ) •
                    (star (U : CMatrix β) * (E.states x).matrix * (U : CMatrix β))) = Y := by
            dsimp [Y, σbar]
            rw [Ensemble.averageState_matrix]
            ext i j
            simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
              Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x _ => ?_
            simp only [Algebra.smul_def]
            rw [show (algebraMap ℝ≥0 ℂ) (E.probs x) = (E.probs x : ℂ) by rfl]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y' _ => ?_
            change
              (E.probs x : ℂ) *
                  ((star (U : CMatrix β)) i y' * (E.states x).matrix y' y *
                    (U : CMatrix β) y j) =
                (star (U : CMatrix β)) i y' * ((E.probs x : ℂ) *
                  (E.states x).matrix y' y) * (U : CMatrix β) y j
            ring_nf
          have happly := congrFun (congrFun hmatrix z) z
          rw [← happly]
          simp [Matrix.sum_apply, Matrix.smul_apply]
    _ = (ProjectiveMeasurement.stateEigenvalueProb σbar z : ℝ) := hdiagY
    _ = (ProjectiveMeasurement.stateEigenvalueProb E.averageState z : ℝ) := by rfl

/-- The strong-typical diagonal projector built from the induced post-pinching
output marginal is the same as the one built from the average state's eigenvalue
distribution. -/
theorem strongTypicalDiagonalProjector_inducedMarginal_eigenbasis_eq_stateEigenvalueDistribution
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Ensemble α β) (n : ℕ) (δ : ℝ) :
    strongTypicalDiagonalProjector
        (ClassicalTypicality.inducedMarginal E.indexDistribution
          (eigenbasisStochasticKernel E)) n δ =
      strongTypicalDiagonalProjector (stateEigenvalueDistribution E.averageState) n δ := by
  classical
  unfold strongTypicalDiagonalProjector
  ext z z'
  by_cases hzz : z = z'
  · subst z'
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    have hind : ∀ x : β,
        (ClassicalTypicality.inducedMarginal E.indexDistribution
            (eigenbasisStochasticKernel E)).prob x =
          (stateEigenvalueDistribution E.averageState).prob x := by
      intro x
      exact inducedMarginal_eigenbasisStochasticKernel_eq_stateEigenvalueProb E x
    have hind_sum : ∀ x : β,
        (∑ x_1 : α, (E.probs x_1 : ℝ) *
            ((eigenbasisStochasticKernel E).prob x_1 x : ℝ)) =
          ((stateEigenvalueDistribution E.averageState).prob x : ℝ) := by
      intro x
      have h := congrArg (fun q : ℝ≥0 => (q : ℝ)) (hind x)
      simpa [ClassicalTypicality.inducedMarginal_prob, Ensemble.indexDistribution,
        NNReal.coe_sum, NNReal.coe_mul] using h
    have hprop :
        ClassicalTypicality.StrongTypical
            (ClassicalTypicality.inducedMarginal E.indexDistribution
              (eigenbasisStochasticKernel E)) (tensorPowerEquiv n z) δ ↔
          ClassicalTypicality.StrongTypical
            (stateEigenvalueDistribution E.averageState) (tensorPowerEquiv n z) δ := by
      constructor
      · intro h x
        simpa [ClassicalTypicality.StrongTypical, hind_sum x] using h x
      · intro h x
        simpa [ClassicalTypicality.StrongTypical, hind_sum x] using h x
    by_cases hleft :
        ClassicalTypicality.StrongTypical
          (ClassicalTypicality.inducedMarginal E.indexDistribution
            (eigenbasisStochasticKernel E)) (tensorPowerEquiv n z) δ
    · have hright := hprop.mp hleft
      simp [hleft, hright]
    · have hright :
          ¬ ClassicalTypicality.StrongTypical
            (stateEigenvalueDistribution E.averageState) (tensorPowerEquiv n z) δ := by
        intro hr
        exact hleft (hprop.mpr hr)
      simp [hleft, hright]
  · rw [Matrix.diagonal_apply_ne _ hzz, Matrix.diagonal_apply_ne _ hzz]

/-- Event mass of the strong-typical output set under the conditional product
law, with classical decidability kept internal to the finite definition. -/
noncomputable def strongTypicalEventMass {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (pZ : QIT.FiniteDistribution β) (K : QIT.StochasticKernel α β)
    (xseq : Fin n → α) (δ : ℝ) : ℝ≥0 := by
  classical
  exact ClassicalTypicality.conditionalEventMass K xseq
    (fun zseq => ClassicalTypicality.StrongTypical pZ zseq δ)

/-- Trace of the strong-typical diagonal projector against the pinched
conditional product state is exactly the classical marginal-typical event
mass. -/
theorem strongTypicalDiagonalProjector_trace_mul_conditionalProduct
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (pZ : QIT.FiniteDistribution β) (K : QIT.StochasticKernel α β)
    (xseq : Fin n → α) (δ : ℝ) :
    ((strongTypicalDiagonalProjector pZ n δ *
        (conditionalProductDiagonalState K xseq).matrix).trace).re =
      (strongTypicalEventMass pZ K xseq δ : ℝ) := by
  classical
  rw [conditionalProductDiagonalState_matrix]
  unfold strongTypicalDiagonalProjector conditionalProductDiagonalMatrix
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  have hsum :
      (∑ z : TensorPower β n,
          (((if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
              then (1 : ℂ) else 0) *
            ((ClassicalTypicality.conditionalProductMass K xseq
              (tensorPowerEquiv n z) : ℝ) : ℂ))).re) =
        ∑ zseq : Fin n → β,
          (if ClassicalTypicality.StrongTypical pZ zseq δ
            then (ClassicalTypicality.conditionalProductMass K xseq zseq : ℝ)
            else 0) := by
    calc
      (∑ z : TensorPower β n,
          (((if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
              then (1 : ℂ) else 0) *
            ((ClassicalTypicality.conditionalProductMass K xseq
              (tensorPowerEquiv n z) : ℝ) : ℂ))).re)
          =
        ∑ z : TensorPower β n,
          (if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
            then (ClassicalTypicality.conditionalProductMass K xseq
              (tensorPowerEquiv n z) : ℝ)
            else 0) := by
            refine Finset.sum_congr rfl fun z _ => ?_
            by_cases hz :
                ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
            · simp [hz]
            · simp [hz]
      _ =
        ∑ zseq : Fin n → β,
          (if ClassicalTypicality.StrongTypical pZ zseq δ
            then (ClassicalTypicality.conditionalProductMass K xseq zseq : ℝ)
            else 0) := by
            exact Fintype.sum_equiv (tensorPowerEquiv n)
              (fun z : TensorPower β n =>
                if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
                then (ClassicalTypicality.conditionalProductMass K xseq
                  (tensorPowerEquiv n z) : ℝ)
                else 0)
              (fun zseq : Fin n → β =>
                if ClassicalTypicality.StrongTypical pZ zseq δ
                then (ClassicalTypicality.conditionalProductMass K xseq zseq : ℝ)
                else 0)
              (by intro z; rfl)
  rw [hsum]
  unfold strongTypicalEventMass ClassicalTypicality.conditionalEventMass
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl fun zseq _ => ?_
  by_cases hz : ClassicalTypicality.StrongTypical pZ zseq δ
  · simp [hz]
  · simp [hz]

/-- Multiplying by a strong-typical diagonal projector and taking the trace only
depends on the diagonal entries of the right-hand matrix. -/
theorem strongTypicalDiagonalProjector_trace_mul_eq_of_diag_eq
    {β : Type v} [Fintype β] [DecidableEq β] {n : ℕ}
    (pZ : QIT.FiniteDistribution β) (δ : ℝ) {A B : CMatrix (TensorPower β n)}
    (hdiag : ∀ z : TensorPower β n, A z z = B z z) :
    ((strongTypicalDiagonalProjector pZ n δ * A).trace).re =
      ((strongTypicalDiagonalProjector pZ n δ * B).trace).re := by
  classical
  unfold strongTypicalDiagonalProjector
  rw [Matrix.trace, Matrix.trace, Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  change
    ((Matrix.diagonal (fun z : TensorPower β n =>
        if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
        then (1 : ℂ) else 0) * A) z z).re =
      ((Matrix.diagonal (fun z : TensorPower β n =>
        if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
        then (1 : ℂ) else 0) * B) z z).re
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hsum :
      (∑ x : TensorPower β n,
          (Matrix.diagonal (fun z : TensorPower β n =>
              if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
              then (1 : ℂ) else 0) z x) * A x z) =
        (if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
          then (1 : ℂ) else 0) * A z z := by
    rw [Finset.sum_eq_single z]
    · simp
    · intro x _ hx
      rw [Matrix.diagonal_apply_ne _ hx.symm]
      simp
    · intro hz
      exact False.elim (hz (Finset.mem_univ z))
  have hsum' :
      (∑ x : TensorPower β n,
          (Matrix.diagonal (fun z : TensorPower β n =>
              if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
              then (1 : ℂ) else 0) z x) * B x z) =
        (if ClassicalTypicality.StrongTypical pZ (tensorPowerEquiv n z) δ
          then (1 : ℂ) else 0) * B z z := by
    rw [Finset.sum_eq_single z]
    · simp
    · intro x _ hx
      rw [Matrix.diagonal_apply_ne _ hx.symm]
      simp
    · intro hz
      exact False.elim (hz (Finset.mem_univ z))
  rw [hsum, hsum', hdiag z]

/-- Source-shaped pack-1 trace bridge: the tensor-product eigenbasis typical
projector against an actual product output state has the same trace as the
strong-typical diagonal projector against the post-pinching classical
conditional product law. -/
theorem sourceTypicalSubspaceProjector_trace_mul_productState_eq_conditionalProduct
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {n : ℕ} (E : Ensemble α β) (xseq : Fin n → α) (δ : ℝ) :
    ((sourceTypicalSubspaceProjector E.averageState n δ *
        (productState fun i : Fin n => E.states (xseq i)).matrix).trace).re =
      ((strongTypicalDiagonalProjector (stateEigenvalueDistribution E.averageState) n δ *
        (conditionalProductDiagonalState (eigenbasisStochasticKernel E) xseq).matrix).trace).re := by
  classical
  let U := unitaryTensorPowerMatrix E.averageState.pos.isHermitian.eigenvectorUnitary n
  let D := strongTypicalDiagonalProjector (stateEigenvalueDistribution E.averageState) n δ
  let S : CMatrix (TensorPower β n) :=
    (productState fun i : Fin n => E.states (xseq i)).matrix
  let C : CMatrix (TensorPower β n) :=
    (conditionalProductDiagonalState (eigenbasisStochasticKernel E) xseq).matrix
  have hcyc :
      ((sourceTypicalSubspaceProjector E.averageState n δ * S).trace).re =
        ((D * (star (U : CMatrix (TensorPower β n)) * S *
            (U : CMatrix (TensorPower β n)))).trace).re := by
    have hcomplex :
        (((U : CMatrix (TensorPower β n)) * D *
              star (U : CMatrix (TensorPower β n))) * S).trace =
          (D * (star (U : CMatrix (TensorPower β n)) * S *
              (U : CMatrix (TensorPower β n)))).trace := by
      calc
        (((U : CMatrix (TensorPower β n)) * D *
              star (U : CMatrix (TensorPower β n))) * S).trace =
            ((U : CMatrix (TensorPower β n)) *
              (D * star (U : CMatrix (TensorPower β n)) * S)).trace := by
              congr 1
              noncomm_ring
        _ = ((D * star (U : CMatrix (TensorPower β n)) * S) *
              (U : CMatrix (TensorPower β n))).trace := by
              rw [Matrix.trace_mul_comm]
        _ = (D * (star (U : CMatrix (TensorPower β n)) * S *
              (U : CMatrix (TensorPower β n)))).trace := by
              congr 1
              noncomm_ring
    unfold sourceTypicalSubspaceProjector
    dsimp [U, D, S] at hcomplex ⊢
    exact congrArg Complex.re hcomplex
  have hdiag : ∀ z : TensorPower β n,
      (star (U : CMatrix (TensorPower β n)) * S * (U : CMatrix (TensorPower β n))) z z =
        C z z := by
    intro z
    dsimp [U, S, C]
    exact unitaryTensorPowerMatrix_conj_productState_diag_eq_conditionalProduct E xseq z
  calc
    ((sourceTypicalSubspaceProjector E.averageState n δ * S).trace).re =
        ((D * (star (U : CMatrix (TensorPower β n)) * S *
          (U : CMatrix (TensorPower β n)))).trace).re := hcyc
    _ = ((D * C).trace).re :=
        strongTypicalDiagonalProjector_trace_mul_eq_of_diag_eq
          (stateEigenvalueDistribution E.averageState) δ hdiag

/-- Pinched/diagonal pack-1 capture.  If the input word is strongly typical
and the conditional typicality Chebyshev/union-bound threshold holds, then the
strong-typical projector for the induced marginal output distribution captures
the pinched conditional product state with probability at least `1 - ε`.

This is the fully proved classical reduction kernel in Wilde's
`prop-qt:cond-state-with-uncond-proj`; it is the part that follows after
pinching the conditional states in the average state's eigenbasis. -/
theorem strongTypicalDiagonalProjector_conditionalProduct_capture
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ}
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (xseq : Fin n → α) {δx δc ε : ℝ}
    (hn : 0 < n) (hδx : 0 ≤ δx) (hδc : 0 < δc)
    (hx : ClassicalTypicality.StrongTypical p xseq δx)
    (hlarge :
      (Fintype.card α : ℝ) * (Fintype.card β : ℝ) /
          ((n : ℝ) * δc ^ 2) ≤ ε) :
    1 - ε ≤
      ((strongTypicalDiagonalProjector (ClassicalTypicality.inducedMarginal p K) n
          ((Fintype.card α : ℝ) * (δx + δc)) *
        (conditionalProductDiagonalState K xseq).matrix).trace).re := by
  rw [strongTypicalDiagonalProjector_trace_mul_conditionalProduct]
  change 1 - ε ≤
    (ClassicalTypicality.marginalTypicalMass p K xseq
      ((Fintype.card α : ℝ) * (δx + δc)) : ℝ)
  exact ClassicalTypicality.marginalTypicalMass_ge_one_sub_epsilon_of_conditionalTypicality
    p K xseq hn hδx hδc hx hlarge

/-- Source-shaped pack-1 capture for actual product output states.

This is the quantum version of `strongTypicalDiagonalProjector_conditionalProduct_capture`:
the projector is the tensor-product eigenbasis typical projector of the average
state, and the state being captured is the physical product
`⊗ᵢ E.states (xseq i)`.  The proof explicitly conjugates into the average-state
eigenbasis and applies the classical conditional-typicality estimate, rather
than identifying this projector with the legacy spectral typical projector. -/
theorem sourceTypicalSubspaceProjector_product_capture_of_strongTypical
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {n : ℕ} (E : Ensemble α β) (xseq : Fin n → α) {δx δc ε : ℝ}
    (hn : 0 < n) (hδx : 0 ≤ δx) (hδc : 0 < δc)
    (hx : ClassicalTypicality.StrongTypical E.indexDistribution xseq δx)
    (hlarge :
      (Fintype.card α : ℝ) * (Fintype.card β : ℝ) /
          ((n : ℝ) * δc ^ 2) ≤ ε) :
    1 - ε ≤
      ((sourceTypicalSubspaceProjector E.averageState n
          ((Fintype.card α : ℝ) * (δx + δc)) *
        (productState fun i : Fin n => E.states (xseq i)).matrix).trace).re := by
  classical
  let δz := (Fintype.card α : ℝ) * (δx + δc)
  rw [sourceTypicalSubspaceProjector_trace_mul_productState_eq_conditionalProduct E xseq δz]
  rw [← strongTypicalDiagonalProjector_inducedMarginal_eigenbasis_eq_stateEigenvalueDistribution
    E n δz]
  exact strongTypicalDiagonalProjector_conditionalProduct_capture
    E.indexDistribution (eigenbasisStochasticKernel E) xseq hn hδx hδc hx hlarge

/-- Diagonal-route pack-1 bridge.  If an n-block output ensemble's states are
exactly the pinched conditional product laws associated to a finite classical
channel `K` and codeword map `codewordOf`, then the source-shaped
strong-typical diagonal projector gives the packing-lemma cross-capture
hypothesis `h1`.

This theorem does not identify the diagonal strong-typical projector with the
legacy spectral `State.typicalSubspaceProjector`; it records the alternative
source-shaped route explicitly, so consumers cannot silently swap projector
semantics. -/
theorem hsw_diagonal_pack1_of_pinched_strong_typical
    {α : Type u} {β : Type v} {𝒳 : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype 𝒳] [DecidableEq 𝒳] {n : ℕ}
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (E : Ensemble 𝒳 (TensorPower β n)) (codewordOf : 𝒳 → Fin n → α)
    {δx δc ε : ℝ}
    (hn : 0 < n) (hδx : 0 ≤ δx) (hδc : 0 < δc)
    (hstates : ∀ x,
      (E.states x).matrix = (conditionalProductDiagonalState K (codewordOf x)).matrix)
    (hx : ∀ x, ClassicalTypicality.StrongTypical p (codewordOf x) δx)
    (hlarge :
      (Fintype.card α : ℝ) * (Fintype.card β : ℝ) /
          ((n : ℝ) * δc ^ 2) ≤ ε) :
    ∀ x, 1 - ε ≤
      ((strongTypicalDiagonalProjector (ClassicalTypicality.inducedMarginal p K) n
          ((Fintype.card α : ℝ) * (δx + δc)) *
        (E.states x).matrix).trace).re := by
  intro x
  rw [hstates x]
  exact strongTypicalDiagonalProjector_conditionalProduct_capture
    p K (codewordOf x) hn hδx hδc (hx x) hlarge

/-- Source-shaped diagonal packing constructor.  This constructor packages the
diagonal route into the same generic packing-hypotheses structure used by the
packing lemma.

It proves the total-projector side and pack-1 from the strong-typical capture
theorem.  The remaining codeword-projector estimates `h2`, `h3`, and
the projected-average estimate `h4` are explicit inputs, so no spectral/strong
projector identification is smuggled in.  In the full HSW direct route these
inputs are supplied by the conditionally-typical projector estimates and the
pruned-distribution pack-4 bound. -/
@[expose]
noncomputable def hswPackingHypothesesDiagonal_of_pinchedStrongTypical
    {α : Type u} {β : Type v} {𝒳 : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype 𝒳] [DecidableEq 𝒳] {n : ℕ}
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    (E : Ensemble 𝒳 (TensorPower β n)) (codewordOf : 𝒳 → Fin n → α)
    {δx δc ε d D : ℝ}
    (hn : 0 < n) (hδx : 0 ≤ δx) (hδc : 0 < δc)
    (hε_nonneg : 0 ≤ ε) (hD_pos : 0 < D)
    (hstates : ∀ x,
      (E.states x).matrix = (conditionalProductDiagonalState K (codewordOf x)).matrix)
    (hx : ∀ x, ClassicalTypicality.StrongTypical p (codewordOf x) δx)
    (hlarge :
      (Fintype.card α : ℝ) * (Fintype.card β : ℝ) /
          ((n : ℝ) * δc ^ 2) ≤ ε)
    (Px : 𝒳 → CMatrix (TensorPower β n))
    (hPx : ∀ x, (Px x).PosSemidef ∧ Px x * Px x = Px x ∧ Px x ≤ 1)
    (h2 : ∀ x, 1 - ε ≤ ((Px x * (E.states x).matrix).trace).re)
    (h3 : ∀ x, ((Px x).trace).re ≤ d)
    (h4 :
      strongTypicalDiagonalProjector (ClassicalTypicality.inducedMarginal p K) n
          ((Fintype.card α : ℝ) * (δx + δc)) *
        E.averageState.matrix *
        strongTypicalDiagonalProjector (ClassicalTypicality.inducedMarginal p K) n
          ((Fintype.card α : ℝ) * (δx + δc))
        ≤ ((D : ℝ)⁻¹) •
          strongTypicalDiagonalProjector (ClassicalTypicality.inducedMarginal p K) n
            ((Fintype.card α : ℝ) * (δx + δc))) :
    HSWPackingHypothesesSpectral E ((Fintype.card α : ℝ) * (δx + δc)) where
  P := strongTypicalDiagonalProjector (ClassicalTypicality.inducedMarginal p K) n
    ((Fintype.card α : ℝ) * (δx + δc))
  Px := Px
  d := d
  D := D
  ε := ε
  hε_nonneg := hε_nonneg
  hD_pos := hD_pos
  P_posSemidef := strongTypicalDiagonalProjector_posSemidef
    (ClassicalTypicality.inducedMarginal p K) n
      ((Fintype.card α : ℝ) * (δx + δc))
  P_idempotent := strongTypicalDiagonalProjector_idempotent
    (ClassicalTypicality.inducedMarginal p K) n
      ((Fintype.card α : ℝ) * (δx + δc))
  P_le_one := strongTypicalDiagonalProjector_le_one
    (ClassicalTypicality.inducedMarginal p K) n
      ((Fintype.card α : ℝ) * (δx + δc))
  Px_projector := hPx
  h1 := hsw_diagonal_pack1_of_pinched_strong_typical
    p K E codewordOf hn hδx hδc hstates hx hlarge
  h2 := h2
  h3 := h3
  h4 := h4

/-- The codeword-product-state family `fun i => σ^{(codeword i)}` built from a
length-`n` symbol sequence into an abstract per-symbol state family. This is the
per-codeword product state whose conditionally-typical projector is `Px x`.

In the HSW channel-output setup, `symStates j = N.applyState (inputState j)`
for the channel `N` and the chosen input distribution's per-symbol states. -/
abbrev codewordStates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (symStates : ι → State a) (codeword : Fin n → ι) :
    Fin n → State a := fun i => symStates (codeword i)

end HSWPackingHypothesesSpectral

/-! ### Constructor: proved fields from the spectral estimates

The constructor `hswPackingHypothesesSpectral_of_estimates` builds the proved
fields (`P`, `Px`, `d`, `D`, `ε`, the projector facts, and
`pack-2`/`pack-3`/`pack-4`) directly from the spectral estimates in this
module, leaving `pack-1` (`h1`) as the sole open input.

The constructor is stated over a **single-symbol** ensemble `E₀ : Ensemble ι a`
(the one-use channel-output ensemble), whose average state is
`σ̄ = E₀.averageState`. The `n`-block ensemble `E : Ensemble 𝒳 (TensorPower a n)`
is required to have codeword-product states (`hstates`) and average state
`σ̄.tensorPower n` (`hσbar`), so the spectral `pack-2/3` estimates (stated for
`productState`) and the proved `pack-4` estimate
`averageState_typicalProjector_projectedAvgState_le E₀ δ` (stated for the
single-symbol average tensored to `n` copies) instantiate against `E.states x`
and `E.averageState` verbatim. -/


/-- **Constructor.** Build an `HSWPackingHypothesesSpectral` from the proved
spectral estimates, leaving `pack-1` (`h1`) as the sole open input.

The instantiated objects are:
* `P = E₀.averageState.typicalSubspaceProjector n δ` (the `σ̄^{⊗ n}` typical
  projector, with its PSD/idempotent/`≤ 1` facts from `Typicality.lean`);
* `Px x = conditionallyTypicalSubspaceProjector (codewordStates symStates (codewordOf x)) δ`
  (the codeword conditionally-typical projectors, with their projector facts);
* `D = 2^{n(S(σ̄) − δ)}` (the inverse typical weight, from `pack-4`);
* `d` and `ε` supplied by the caller (`d` a `pack-3` upper bound on the
  conditionally-typical-subspace dimension; `ε` a nonnegative uniform upper
  bound on the per-codeword second-moment ratios `secondMoment/(nδ)²`).

The hypothesis `hstates` identifies each `n`-block ensemble state matrix with
its codeword product-state matrix, so the spectral `pack-2/3` estimates
instantiate against `E.states x`. The hypothesis `hσbar` identifies the
`n`-block ensemble's average state with `σ̄.tensorPower n`, so the proved
`pack-4` estimate `averageState_typicalProjector_projectedAvgState_le E₀ δ`
instantiates against `E.averageState`. The `h1` argument is the open
cross-capture hypothesis, passed through unchanged.
[Wilde2011Qst, qit-notes.tex:33634-33808] -/
@[expose]
noncomputable def hswPackingHypothesesSpectral_of_estimates
    {a : Type u} {ι : Type u} {𝒳 : Type*} {n : ℕ}
    [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    [Fintype 𝒳] [DecidableEq 𝒳]
    (E₀ : Ensemble ι a) (E : Ensemble 𝒳 (TensorPower a n)) (δ : ℝ)
    (symStates : ι → State a) (codewordOf : 𝒳 → Fin n → ι)
    (hn : 0 < n) (hδ : 0 < δ)
    (d ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hstates : ∀ x, (E.states x).matrix =
      (productState <|
        HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)).matrix)
    (hε_bound : ∀ x,
      conditionalLogDeviationSecondMoment
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) /
        ((n : ℝ) * δ) ^ 2 ≤ ε)
    (hpack3 : ∀ x, conditionallyTypicalSubspaceDimension
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ ≤ d)
    (hσbar : E.averageState = E₀.averageState.tensorPower n)
    (h1 : ∀ x, 1 - ε ≤
        ((E₀.averageState.typicalSubspaceProjector n δ * (E.states x).matrix).trace).re) :
    HSWPackingHypothesesSpectral E δ where
  P := E₀.averageState.typicalSubspaceProjector n δ
  Px := fun x => conditionallyTypicalSubspaceProjector
    (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ
  d := d
  D := (2 : ℝ) ^ ((n : ℝ) * E₀.averageState.vonNeumann - (n : ℝ) * δ)
  ε := ε
  hε_nonneg := hε_nonneg
  hD_pos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  P_posSemidef := E₀.averageState.typicalSubspaceProjector_posSemidef n δ
  P_idempotent := E₀.averageState.typicalSubspaceProjector_idempotent n δ
  P_le_one := E₀.averageState.typicalSubspaceProjector_le_one n δ
  Px_projector := fun x =>
    ⟨conditionallyTypicalSubspaceProjector_posSemidef
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ,
      conditionallyTypicalSubspaceProjector_idempotent
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ,
      conditionallyTypicalSubspaceProjector_le_one
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ⟩
  h1 := h1
  h2 := fun x => by
    -- Identify the ensemble state matrix with the codeword product-state matrix.
    rw [hstates x]
    -- Spectral `pack-2` trace form: `1 − sm_x/(nδ)² ≤ Re Tr(Π_x · ⊗ρ_i)`.
    have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
      (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) hn hδ
    -- `hε_bound` gives `sm_x/(nδ)² ≤ ε`, hence `1 − ε ≤ 1 − sm_x/(nδ)²`.
    have hkey : 1 - ε ≤
        1 - conditionalLogDeviationSecondMoment
          (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) /
          ((n : ℝ) * δ) ^ 2 := by linarith [hε_bound x]
    exact le_trans hkey hown
  h3 := fun x => by
    -- `Re Tr(Π_x) = conditionallyTypicalSubspaceDimension` (trace-counts bridge).
    rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension
      (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ]
    exact hpack3 x
  h4 := by
    -- Proved `pack-4` for the single-symbol ensemble `E₀`: in the eigenbasis
    -- of `σ̄^{⊗ n}`, `Π · σ̄^{⊗ n} · Π ≤ ↑(2^{−n(S(σ̄)−δ)}) · Π`.
    have hpack4 := averageState_typicalProjector_projectedAvgState_le (n := n) E₀ δ
    -- Align the average-state matrix via `hσbar`: `E.averageState.matrix`
    -- equals `(σ̄.tensorPower n).matrix`, the middle factor in `hpack4`.
    rw [show E.averageState.matrix = (E₀.averageState.tensorPower n).matrix from by
        rw [hσbar]]
    -- Align the goal's real scalar `(2^{a})⁻¹` (`a = n(S(σ̄)−δ)`) to `2^{−a}`
    -- via `Real.rpow_neg` (`b^{-x} = (b^x)⁻¹`), matching `hpack4`'s real base
    -- `2^{−a}` before its `ℝ → ℂ` coercion.
    rw [show ((2 : ℝ) ^ ((n : ℝ) * E₀.averageState.vonNeumann - (n : ℝ) * δ))⁻¹ =
        (2 : ℝ) ^ (-((n : ℝ) * E₀.averageState.vonNeumann - (n : ℝ) * δ)) by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]]
    -- The goal's real-smul `(2^{−a} : ℝ) • P` and `hpack4`'s complex-smul
    -- `↑(2^{−a}) • P` agree elementwise via the `ℝ → ℂ` smul coercion.
    exact_mod_cast hpack4

/-! ## pack-4 pruned-distribution `(1 − ε)⁻¹` prefactor

Wilde's HSW form of `pack-4` carries a `[1 − ε]⁻¹` prefactor coming from the
pruned-distribution reduction. Codewords are drawn from the law `p'` obtained by
restricting the i.i.d. law `p^{⊗ n}` to the typical set (atypical mass `≤ ε`)
and renormalizing; then `p'(x^n) ≤ p^{⊗ n}(x^n) / (1 − ε)` pointwise, and
because each codeword output `σ^{x^n}` is positive semidefinite the Loewner
order of the weighted sums inherits the coefficient domination:

`𝔼_{p'}[σ^{X'^n}] = Σ_{x^n} p'(x^n) σ^{x^n} ≤ (1 − ε)⁻¹ Σ_{x^n} p^{⊗ n}(x^n) σ^{x^n}
                  = (1 − ε)⁻¹ σ̄^{⊗ n}`.

This section delivers both the Loewner-order coefficient-domination kernel for
two ensembles sharing their state family and the n-block pruned-output
reduction used by the HSW packing estimates. Source:
[Wilde2011Qst, qit-notes.tex:33634-33808]. -/

/-- Hermitian congruence preserves Loewner order for complex matrices.

This is the matrix-order kernel needed in HSW pack-4: after the pruned average
state is dominated by a scalar multiple of the i.i.d. average state, one may
compress both sides by the same Hermitian projector. -/
theorem cMatrix_projector_mul_mul_le_of_le {a : Type u} [Fintype a] [DecidableEq a]
    {A B P : CMatrix a} (hP : P.IsHermitian) (hAB : A ≤ B) :
    P * A * P ≤ P * B * P := by
  rw [Matrix.le_iff]
  have hpsd :
      (Matrix.conjTranspose P * (B - A) * P).PosSemidef :=
    (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same P
  have hdiff : P * B * P - P * A * P = Matrix.conjTranspose P * (B - A) * P := by
    rw [show Matrix.conjTranspose P = P by simpa [Matrix.IsHermitian] using hP]
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hdiff]
  exact hpsd

/-- Combine a scalar Loewner domination bound with a projected Loewner bound.

If `A ≤ c • B` and the Hermitian projector/compressor `P` satisfies
`P B P ≤ d • P`, then `P A P ≤ (c*d) • P`.  This is the exact algebraic shape
of the HSW pruned-distribution pack-4 step. -/
theorem cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
    {a : Type u} [Fintype a] [DecidableEq a] {A B P : CMatrix a}
    {c d : ℝ} (hP : P.IsHermitian) (hc : 0 ≤ c)
    (hAB : A ≤ c • B) (hPB : P * B * P ≤ d • P) :
    P * A * P ≤ (c * d) • P := by
  have hcongr : P * A * P ≤ P * (c • B) * P :=
    cMatrix_projector_mul_mul_le_of_le hP hAB
  have hscale : P * (c • B) * P = c • (P * B * P) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hscaled : c • (P * B * P) ≤ c • (d • P) :=
    cMatrix_real_smul_le_smul hc hPB
  calc
    P * A * P ≤ P * (c • B) * P := hcongr
    _ = c • (P * B * P) := hscale
    _ ≤ c • (d • P) := hscaled
    _ = (c * d) • P := by
      ext i j
      simp [Complex.real_smul, mul_assoc]

/-- **Coefficient-domination kernel (proved).** If two ensembles `E E'` over the
same index type share their state family and `E'`'s weights are pointwise
dominated by a nonnegative real multiple of `E`'s weights —
`(E'.probs x : ℝ) ≤ c * (E.probs x : ℝ)` for every `x`, for some `0 ≤ c` — then
the average states satisfy the Loewner inequality
`E'.averageState.matrix ≤ c • E.averageState.matrix` (the scalar `c` acting on
the complex matrix through the `ℝ → ℂ` algebra map).

Route: write `c • E.averageState.matrix − E'.averageState.matrix` as the single
sum `Σ_x (c * (E.probs x : ℝ) − (E'.probs x : ℝ)) • (E.states x).matrix` (the two
`averageState_matrix` sums coincide entry-by-entry after distributing the outer
real scalar, using ring-subtraction of the real-valued coefficients). Each
summand is positive semidefinite because the real coefficient
`c * (E.probs x) − (E'.probs x)` is nonnegative (pointwise domination) and
`(E.states x).matrix` is a density matrix; `Matrix.posSemidef_sum` lifts the
pointwise PSD fact to the sum, and `Matrix.le_iff` converts PSD-of-the-difference
back to the Loewner order. This is the kernel of the pruned-distribution
`(1 − ε)⁻¹` prefactor for `pack-4`; the n-block HSW instantiation is proved
below. -/
theorem averageState_le_of_probDomination {a : Type u} {ι : Type u}
    [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    (E E' : Ensemble ι a) {c : ℝ} (hc : 0 ≤ c)
    (hstates : ∀ x, E.states x = E'.states x)
    (hdom : ∀ x, (E'.probs x : ℝ) ≤ c * (E.probs x : ℝ)) :
    E'.averageState.matrix ≤ c • E.averageState.matrix := by
  -- Unfold both Loewner order and `averageState` into the PSD-of-difference form.
  rw [Matrix.le_iff]
  -- Symmetrize the state families: rewrite `E'.states` as `E.states` throughout.
  have hstates' : ∀ x, E'.states x = E.states x := fun x => (hstates x).symm
  -- Express the difference as a single sum of per-index PSD summands. The real
  -- scalar distributes over the `averageState_matrix` sum; ring-subtraction of
  -- the real coefficients then factors each summand as a single real smul.
  have hkey : (c • E.averageState.matrix : CMatrix a) - E'.averageState.matrix =
      ∑ x, ((c * (E.probs x : ℝ) - (E'.probs x : ℝ)) : ℝ) • (E.states x).matrix := by
    ext i j
    simp only [Ensemble.averageState_matrix, Matrix.sub_apply, Finset.smul_sum,
      Matrix.smul_apply, Matrix.sum_apply]
    -- Rewrite both the outer `ℝ` smul and the per-index `ℝ≥0` smul to the
    -- common `algebraMap … * _` form, then normalize every algebraMap to the
    -- `ℝ≥0 → ℝ → ℂ` coercion so `push_cast` + `ring` can close over `ℂ`.
    simp only [Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
      NNReal.algebraMap_eq_coe, Complex.coe_algebraMap]
    have hseq : ∀ x, (E'.states x).matrix i j = (E.states x).matrix i j :=
      fun x => by rw [hstates']
    simp only [hseq]
    -- Combine the two LHS sums into a single sum via `sum_sub_distrib`, then
    -- close per-index by `ring` (the only structural difference is the
    -- scalar/matrix-entry multiplication order, which `ring` reorders).
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    ring
  rw [hkey]
  -- Each summand `(c * E.probs x − E'.probs x) • (E.states x).matrix` is PSD:
  -- the real coefficient is nonnegative — `hc` makes `c * ↑p ≥ 0`, and `hdom`
  -- gives `↑p' ≤ c * ↑p`, so `0 ≤ c * ↑p − ↑p'` — and the density matrix
  -- `(E.states x).matrix` is PSD; `PosSemidef.smul` lifts.
  refine Matrix.posSemidef_sum Finset.univ fun x _ => ?_
  have hp_nonneg : 0 ≤ (E.probs x : ℝ) := NNReal.coe_nonneg _
  have hcoeff_nonneg : 0 ≤ c * (E.probs x : ℝ) - (E'.probs x : ℝ) := by
    have : 0 ≤ c * (E.probs x : ℝ) := mul_nonneg hc hp_nonneg
    linarith [hdom x, this]
  exact (E.states x).pos.smul hcoeff_nonneg

/-- **n-block product-of-expectations identity.** The expectation of the
codeword product state under the i.i.d. product law equals the tensor power
of the average state:

`Σ_{x : Fin n → ι} (∏ i, probs (x i)) • (⊗_i σ^{x_i}).matrix = σ̄^{⊗ n}.matrix`

where `σ̄` has matrix `Σ_j (probs j) • (symStates j).matrix`. This is the
crux of the pruned-distribution reduction: the i.i.d. law's expected codeword
output is exactly the tensor power of the per-symbol average, so any
Loewner-order bound on `σ̄^{⊗ n}` transfers to the expected pruned output.

The proof inducts on `n` at the matrix-entry level. In the successor step
the sum over `Fin (n + 1) → ι` is split head/tail via `Fin.consEquiv`, the
probability product splits via `Fin.prod_univ_succ`, the head sum collapses
to `σ̄.matrix` by hypothesis, and the tail sum is the induction hypothesis. -/
theorem averageState_eq_tensorPower_of_iid {a ι : Type*} [Fintype a] [DecidableEq a]
    [Fintype ι] [DecidableEq ι] (symStates : ι → State a) (probs : ι → ℝ≥0)
    (σbar : State a) (hσbar : σbar.matrix = ∑ j, (probs j) • (symStates j).matrix) :
    ∀ (n : ℕ) (X Y : TensorPower a n),
      (∑ x : Fin n → ι,
          (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix) X Y =
        (σbar.tensorPower n).matrix X Y
  | 0, X, Y => by
    -- n = 0: there is a unique empty codeword, the empty probability product
    -- is 1, and `productState` / `σbar.tensorPower 0` are both `State.unit`.
    let e : Fin 0 → ι := fun i => i.elim0
    have hsub : ∀ x : Fin 0 → ι, x = e := fun x => by funext i; exact i.elim0
    have huniv : (Finset.univ : Finset (Fin 0 → ι)) = {e} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_singleton]
      exact ⟨fun _ => hsub x, fun hx => trivial⟩
    -- The sum over the singleton index set equals its single summand.
    rw [huniv, Finset.sum_singleton]
    -- Empty probability product is 1 (`Fin.prod_univ_zero`).
    rw [Fin.prod_univ_zero, one_smul, productState_zero, State.tensorPower_zero]
  | n + 1, (X0, Xs), (Y0, Ys) => by
    -- n + 1: unfold both sides into head/tail Kronecker factors. The codeword
    -- sum is transported through the head/tail bijection
    -- `ι × (Fin n → ι) ≃ Fin (n+1) → ι` (`Fin.cons`); after splitting the
    -- probability product and the Kronecker entry, the double sum factors via
    -- `Fintype.sum_mul_sum` into `(σbar.matrix X0 Y0) * ((σbar.tensorPower n).matrix Xs Ys)`,
    -- matching the RHS Kronecker expansion.
    -- Define the head/tail entry functions we will sum.
    let head : ι → ℂ := fun x0 => (probs x0 : ℂ) * (symStates x0).matrix X0 Y0
    let tail : (Fin n → ι) → ℂ := fun xs =>
      (∏ i, probs (xs i)) • (productState (fun i => symStates (xs i))).matrix Xs Ys
    -- Pointwise summand identity: under `Fin.cons`, the codeword summand at
    -- entry `(X0,Xs),(Y0,Ys)` equals `head x0 * tail xs`.
    have hsummand : ∀ (x0 : ι) (xs : Fin n → ι),
        (∏ i, probs ((Fin.cons x0 xs : Fin (n + 1) → ι) i)) •
          (productState (fun i => symStates ((Fin.cons x0 xs : Fin (n + 1) → ι) i))).matrix
            (X0, Xs) (Y0, Ys) =
        head x0 * tail xs := by
      intro x0 xs
      -- Split the probability product (head * tail).
      have hprod : ∏ i, probs ((Fin.cons x0 xs : Fin (n + 1) → ι) i) =
          probs x0 * ∏ i, probs (xs i) := by
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
      -- Unfold the productState matrix entry to its head/tail Kronecker product.
      have hentry :
          (productState fun i => symStates ((Fin.cons x0 xs : Fin (n + 1) → ι) i)).matrix
            (X0, Xs) (Y0, Ys) =
            (symStates x0).matrix X0 Y0 *
              (productState fun i => symStates (xs i)).matrix Xs Ys := by
        -- Reduce `productState (cons head/tail)` to `(symStates head).prod (productState tail)`
        -- by `productState_succ` and `Fin.cons_zero`/`Fin.cons_succ`, then read off the
        -- matrix entry via `prod_matrix_kronecker` + `kronecker_apply`.
        have htail_eq : (fun j : Fin n =>
            symStates ((Fin.cons x0 xs : Fin (n + 1) → ι) j.succ)) =
            (fun j : Fin n => symStates (xs j)) := by
          funext j; simp only [Fin.cons_succ]
        conv_lhs => rw [productState_succ, htail_eq]
        rw [State.prod_matrix_kronecker]
        simp only [Fin.cons_zero]
        rfl
      -- Split the `ℝ≥0 → ℂ` smul across the `ℂ` product.
      rw [hprod, hentry]
      -- Coerce both scalars to `ℂ` explicitly so the only remaining algebra is
      -- commutativity of `ℂ` (no opaque `∏` of coerced elements for `ring`).
      have hkey : ((probs x0 * ∏ i, probs (xs i) : ℝ≥0) •
            ((symStates x0).matrix X0 Y0 * (productState fun i => symStates (xs i)).matrix Xs Ys : ℂ)) =
          ((probs x0 : ℂ) * (symStates x0).matrix X0 Y0) *
            ((∏ i, probs (xs i)) • (productState fun i => symStates (xs i)).matrix Xs Ys) := by
        rw [Algebra.smul_def, Algebra.smul_def]
        -- Split the product-scalar cast without unfolding the `∏`.
        rw [show ((algebraMap ℝ≥0 ℂ) (probs x0 * ∏ i, probs (xs i))) =
              (algebraMap ℝ≥0 ℂ) (probs x0) * (algebraMap ℝ≥0 ℂ) (∏ i, probs (xs i)) from
            map_mul _ _ _]
        rw [IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ, NNReal.algebraMap_eq_coe,
          Complex.coe_algebraMap, IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
          NNReal.algebraMap_eq_coe, Complex.coe_algebraMap]
        ring
      rw [hkey]
    -- The head-sum is `σbar.matrix X0 Y0` by `hσbar` (entrywise).
    have hhead_sum : ∑ x0, head x0 = σbar.matrix X0 Y0 := by
      rw [hσbar]
      simp only [Matrix.sum_apply, Matrix.smul_apply, head]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
        NNReal.algebraMap_eq_coe, Complex.coe_algebraMap]
    -- The tail-sum is `(σbar.tensorPower n).matrix Xs Ys` by the IH.
    have htail_sum : ∑ xs, tail xs = (σbar.tensorPower n).matrix Xs Ys := by
      have key : (∑ xs : Fin n → ι,
          (∏ i, probs (xs i)) • (productState (fun i => symStates (xs i))).matrix) Xs Ys
          = (σbar.tensorPower n).matrix Xs Ys :=
        averageState_eq_tensorPower_of_iid symStates probs σbar hσbar n Xs Ys
      simp only [Matrix.sum_apply, Matrix.smul_apply, tail] at key ⊢
      exact key
    -- RHS: `(σbar.tensorPower (n+1)).matrix (X0,Xs) (Y0,Ys)` is the head/tail
    -- Kronecker product `σbar.matrix X0 Y0 * (σbar.tensorPower n).matrix Xs Ys`.
    rw [show (σbar.tensorPower (n + 1)).matrix (X0, Xs) (Y0, Ys) =
        σbar.matrix X0 Y0 * (σbar.tensorPower n).matrix Xs Ys from by
        rw [State.tensorPower_succ, State.prod_matrix_kronecker]
        rfl]
    -- Combine: RHS = head-sum * tail-sum.
    rw [← hhead_sum, ← htail_sum]
    -- Push the LHS entry application into the sum, factor via `sum_mul_sum`,
    -- then transport the `(x0,xs)`-product-type sum back to the codeword sum.
    rw [Matrix.sum_apply]
    rw [Fintype.sum_mul_sum head tail]
    rw [← Fintype.sum_prod_type (f := fun p : ι × (Fin n → ι) => head p.1 * tail p.2)]
    exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => ι))
      (fun p => head p.1 * tail p.2)
      (fun x => (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix (X0, Xs) (Y0, Ys))
      (fun p => (hsummand p.1 p.2).symm)).symm


/-- **pack-4 pruned-distribution reduction.** The HSW `(1 − ε)⁻¹` prefactor on
the expected pruned-distribution codeword output. Let `symStates : ι → State a`
be the per-symbol channel outputs, `probs : ι → ℝ≥0` the input law, and
`σbar` the per-symbol average output state with matrix
`σbar.matrix = Σ_j (probs j) • (symStates j).matrix`. If a pruned ensemble
`E_pruned : Ensemble (Fin n → ι) (TensorPower a n)` has

* codeword-product outputs `E_pruned.states x = productState (fun i => symStates (x i))`
  (same family as the i.i.d. law), and
* pruned weights pointwise dominated by `(1 − ε)⁻¹` times the i.i.d. product
  law, `(E_pruned.probs x : ℝ) ≤ (1 − ε)⁻¹ * ∏ i, (probs (x i) : ℝ)`,

then the expected pruned codeword output is Loewner-bounded by the renormalized
tensor power:

`E_pruned.averageState.matrix ≤ ((1 − ε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix`.

This is the `(1 − ε)⁻¹` renormalization step of the HSW packing argument: the
typical-set restriction discards atypical mass `≤ ε` and renormalizes the
surviving mass by `(1 − ε)⁻¹`, so the expected pruned output is dominated by the
renormalized i.i.d. average `σ̄^{⊗ n}`. The hypothesis `ε < 1` keeps the inverse
well-defined and nonneg.

Proof route: unfold `E_pruned.averageState.matrix` and `(σbar.tensorPower n).matrix`
into their per-codeword sums (the latter via `averageState_eq_tensorPower_of_iid`),
rewrite the pruned states via `hstates`, and reduce to positive-semidefiniteness
of the single difference sum
`Σ_x ((1 − ε)⁻¹ * ∏_i probs (x_i) − E_pruned.probs x) • (productState ...).matrix`,
which follows from `Matrix.posSemidef_sum` plus each coefficient nonneg
(pointwise domination `hdom`, with `ε < 1` giving `(1 − ε)⁻¹ ≥ 0`) and each
`productState.matrix` positive semidefinite. This mirrors
`averageState_le_of_probDomination` with the i.i.d. law substituted for the
dominating ensemble's weights. Source: [Wilde2011Qst, qit-notes.tex:33634-33808]. -/
theorem pack4_prunedReduction {a : Type v} {ι : Type u}
    [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    (symStates : ι → State a) (probs : ι → ℝ≥0) (σbar : State a)
    (hσbar : σbar.matrix = ∑ j, (probs j) • (symStates j).matrix)
    {n : ℕ} {ε : ℝ} (hε : ε < 1)
    (E_pruned : Ensemble (Fin n → ι) (TensorPower a n))
    (hstates : ∀ x : Fin n → ι,
      E_pruned.states x = productState (fun i => symStates (x i)))
    (hdom : ∀ x : Fin n → ι,
      (E_pruned.probs x : ℝ) ≤ (1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ)) :
    E_pruned.averageState.matrix ≤ ((1 - ε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
  -- `(1 − ε)⁻¹` is nonneg because `ε < 1` gives `0 < 1 − ε`.
  have hε_pos : 0 < 1 - ε := by linarith
  have hinv_nonneg : 0 ≤ (1 - ε)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hε_pos)
  -- Replace the RHS tensor-power matrix by the i.i.d. product sum (entrywise).
  have hiid : ∀ X Y,
      (∑ x : Fin n → ι,
          (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix) X Y =
        (σbar.tensorPower n).matrix X Y :=
    averageState_eq_tensorPower_of_iid symStates probs σbar hσbar n
  -- Lift the entrywise identity to a matrix equality.
  have hiid_matrix :
      (∑ x : Fin n → ι,
          (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix) =
        (σbar.tensorPower n).matrix := by
    ext X Y; exact hiid X Y
  rw [Matrix.le_iff]
  -- Reduce to positive-semidefiniteness of the difference, with the RHS
  -- rewritten as the i.i.d. product sum.
  rw [← hiid_matrix]
  have hkey :
      ((1 - ε)⁻¹ •
          (∑ x : Fin n → ι,
              (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix)
          : CMatrix (TensorPower a n)) -
        E_pruned.averageState.matrix =
      ∑ x : Fin n → ι,
        (((1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ) - (E_pruned.probs x : ℝ)) : ℝ) •
          (productState (fun i => symStates (x i))).matrix := by
    -- First rewrite the pruned average state's member states via `hstates`.
    have hpruned_sum :
        E_pruned.averageState.matrix =
          ∑ x : Fin n → ι,
            (E_pruned.probs x) • (productState (fun i => symStates (x i))).matrix := by
      rw [Ensemble.averageState_matrix]
      exact Finset.sum_congr rfl fun x _ => by rw [hstates x]
    rw [hpruned_sum]
    ext i j
    simp only [Matrix.sub_apply, Finset.smul_sum, Matrix.smul_apply, Matrix.sum_apply]
    -- Coerce both the outer `ℝ` smul and the per-codeword `ℝ≥0` smul to the
    -- common `algebraMap … * _` form, then normalize via `push_cast` + `ring`.
    simp only [Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
      NNReal.algebraMap_eq_coe, Complex.coe_algebraMap]
    -- Combine the two sums into one via `sum_sub_distrib`, then close per-index.
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    ring
  rw [hkey]
  -- Each summand is PSD: the real coefficient is nonneg (`hdom` + `(1−ε)⁻¹ ≥ 0`
  -- and each `probs` coerces nonneg), and `productState.matrix` is PSD.
  refine Matrix.posSemidef_sum Finset.univ fun x _ => ?_
  have hprod_nonneg : 0 ≤ ∏ i, (probs (x i) : ℝ) := by
    apply Finset.prod_nonneg
    intro i _
    exact NNReal.coe_nonneg _
  have hcoeff_nonneg :
      0 ≤ ((1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ) - (E_pruned.probs x : ℝ) : ℝ) := by
    have hlhs_nonneg : 0 ≤ (1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ) :=
      mul_nonneg hinv_nonneg hprod_nonneg
    have hpr_nonneg : 0 ≤ (E_pruned.probs x : ℝ) := NNReal.coe_nonneg _
    linarith [hdom x, hlhs_nonneg, hpr_nonneg]
  exact (productState (fun i => symStates (x i))).pos.smul hcoeff_nonneg

/-- Pruned-distribution reduction for the strongly-typical subtype.

This is the canonical HSW pruning step: the codebook index type is the
strongly-typical subtype and the codeword law is the normalized i.i.d. law on
that subtype.  The lower bound on the typical mass gives the `(1 - ε)⁻¹`
renormalization factor, and the subtype inclusion into all words compares the
pruned average with the full i.i.d. product average.

The statement is deliberately more rigid than `pack4_prunedReduction`: it
removes a caller-supplied pointwise-domination hypothesis by deriving it from
`ClassicalTypicality.prunedStrongTypicalDistribution_prob_le_inv_one_sub`. -/
theorem pack4_prunedStrongTypicalReduction {a : Type v} {ι : Type u}
    [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    (symStates : ι → State a) (p : QIT.FiniteDistribution ι) (σbar : State a)
    (hσbar : σbar.matrix = ∑ j, (p.prob j) • (symStates j).matrix)
    {n : ℕ} {δ pruneε : ℝ}
    (hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δ)
    (hmass_lower : (1 - pruneε : ℝ) ≤
      (ClassicalTypicality.strongTypicalMass (n := n) p δ : ℝ))
    (hprune : pruneε < 1)
    (E_pruned : Ensemble (ClassicalTypicality.StrongTypicalWord p n δ) (TensorPower a n))
    (hprobs : ∀ x,
      E_pruned.probs x =
        (ClassicalTypicality.prunedStrongTypicalDistribution p δ hmass_pos).prob x)
    (hstates : ∀ x,
      E_pruned.states x =
        productState (fun i => symStates
          (ClassicalTypicality.StrongTypicalWord.codeword p δ x i))) :
    E_pruned.averageState.matrix ≤
      ((1 - pruneε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
  classical
  let c : ℝ := (1 - pruneε)⁻¹
  let codewordOf : ClassicalTypicality.StrongTypicalWord p n δ → Fin n → ι :=
    fun x => ClassicalTypicality.StrongTypicalWord.codeword p δ x
  have hprune_pos : 0 < 1 - pruneε := by linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr hprune_pos.le
  have hdom : ∀ x,
      (E_pruned.probs x : ℝ) ≤ c * ∏ i : Fin n, (p.prob (codewordOf x i) : ℝ) := by
    intro x
    rw [hprobs x]
    dsimp [c, codewordOf]
    exact ClassicalTypicality.prunedStrongTypicalDistribution_prob_le_inv_one_sub
      p hmass_pos hmass_lower hprune x
  have hiid : ∀ X Y,
      (∑ x : Fin n → ι,
          (∏ i, p.prob (x i)) • (productState (fun i => symStates (x i))).matrix) X Y =
        (σbar.tensorPower n).matrix X Y :=
    averageState_eq_tensorPower_of_iid symStates p.prob σbar hσbar n
  have hiid_matrix :
      (∑ x : Fin n → ι,
          (∏ i, p.prob (x i)) • (productState (fun i => symStates (x i))).matrix) =
        (σbar.tensorPower n).matrix := by
    ext X Y
    exact hiid X Y
  have hsplit :
      (∑ x : Fin n → ι,
          (∏ i, p.prob (x i)) • (productState (fun i => symStates (x i))).matrix) =
        (∑ x : ClassicalTypicality.StrongTypicalWord p n δ,
            (∏ i, p.prob (codewordOf x i)) •
              (productState (fun i => symStates (codewordOf x i))).matrix) +
          ∑ x : {w : Fin n → ι // ¬ ClassicalTypicality.StrongTypical p w δ},
            (∏ i, p.prob (x.1 i)) • (productState (fun i => symStates (x.1 i))).matrix := by
    change
      (∑ x : Fin n → ι,
          (∏ i, p.prob (x i)) • (productState (fun i => symStates (x i))).matrix) =
        (∑ x : {w : Fin n → ι // ClassicalTypicality.StrongTypical p w δ},
            (∏ i, p.prob (x.1 i)) • (productState (fun i => symStates (x.1 i))).matrix) +
          ∑ x : {w : Fin n → ι // ¬ ClassicalTypicality.StrongTypical p w δ},
            (∏ i, p.prob (x.1 i)) • (productState (fun i => symStates (x.1 i))).matrix
    exact
      (Fintype.sum_subtype_add_sum_subtype
        (fun w : Fin n → ι => ClassicalTypicality.StrongTypical p w δ)
        (fun w : Fin n → ι =>
          (∏ i, p.prob (w i)) • (productState (fun i => symStates (w i))).matrix)).symm
  rw [Matrix.le_iff]
  rw [← hiid_matrix]
  rw [hsplit]
  have hkey :
      (c •
          ((∑ x : ClassicalTypicality.StrongTypicalWord p n δ,
              (∏ i, p.prob (codewordOf x i)) •
                (productState (fun i => symStates (codewordOf x i))).matrix) +
            ∑ x : {w : Fin n → ι // ¬ ClassicalTypicality.StrongTypical p w δ},
              (∏ i, p.prob (x.1 i)) •
                (productState (fun i => symStates (x.1 i))).matrix) : CMatrix (TensorPower a n)) -
          E_pruned.averageState.matrix =
        (∑ x : ClassicalTypicality.StrongTypicalWord p n δ,
            ((c * ∏ i, (p.prob (codewordOf x i) : ℝ) -
                (E_pruned.probs x : ℝ)) : ℝ) •
              (productState (fun i => symStates (codewordOf x i))).matrix) +
          c •
            (∑ x : {w : Fin n → ι // ¬ ClassicalTypicality.StrongTypical p w δ},
              (∏ i, p.prob (x.1 i)) •
                (productState (fun i => symStates (x.1 i))).matrix) := by
    have hpruned_sum :
        E_pruned.averageState.matrix =
          ∑ x : ClassicalTypicality.StrongTypicalWord p n δ,
            (E_pruned.probs x) •
              (productState (fun i => symStates (codewordOf x i))).matrix := by
      rw [Ensemble.averageState_matrix]
      exact Finset.sum_congr rfl fun x _ => by rw [hstates x]
    have htyp :
        (c •
            (∑ x : ClassicalTypicality.StrongTypicalWord p n δ,
              (∏ i, p.prob (codewordOf x i)) •
                (productState (fun i => symStates (codewordOf x i))).matrix) :
            CMatrix (TensorPower a n)) -
          E_pruned.averageState.matrix =
        ∑ x : ClassicalTypicality.StrongTypicalWord p n δ,
          ((c * ∏ i, (p.prob (codewordOf x i) : ℝ) -
              (E_pruned.probs x : ℝ)) : ℝ) •
            (productState (fun i => symStates (codewordOf x i))).matrix := by
      rw [hpruned_sum]
      ext i j
      simp only [Matrix.sub_apply, Finset.smul_sum, Matrix.smul_apply, Matrix.sum_apply]
      simp only [Algebra.smul_def,
        IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
        NNReal.algebraMap_eq_coe, Complex.coe_algebraMap]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      push_cast
      ring
    calc
      (c •
          ((∑ x : ClassicalTypicality.StrongTypicalWord p n δ,
              (∏ i, p.prob (codewordOf x i)) •
                (productState (fun i => symStates (codewordOf x i))).matrix) +
            ∑ x : {w : Fin n → ι // ¬ ClassicalTypicality.StrongTypical p w δ},
              (∏ i, p.prob (x.1 i)) •
                (productState (fun i => symStates (x.1 i))).matrix) :
          CMatrix (TensorPower a n)) -
          E_pruned.averageState.matrix
          =
        ((c •
            (∑ x : ClassicalTypicality.StrongTypicalWord p n δ,
              (∏ i, p.prob (codewordOf x i)) •
                (productState (fun i => symStates (codewordOf x i))).matrix) :
            CMatrix (TensorPower a n)) -
          E_pruned.averageState.matrix) +
          c •
            (∑ x : {w : Fin n → ι // ¬ ClassicalTypicality.StrongTypical p w δ},
              (∏ i, p.prob (x.1 i)) •
                (productState (fun i => symStates (x.1 i))).matrix) := by
          ext i j
          simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_add]
          abel
      _ =
        (∑ x : ClassicalTypicality.StrongTypicalWord p n δ,
            ((c * ∏ i, (p.prob (codewordOf x i) : ℝ) -
                (E_pruned.probs x : ℝ)) : ℝ) •
              (productState (fun i => symStates (codewordOf x i))).matrix) +
          c •
            (∑ x : {w : Fin n → ι // ¬ ClassicalTypicality.StrongTypical p w δ},
              (∏ i, p.prob (x.1 i)) •
                (productState (fun i => symStates (x.1 i))).matrix) := by
          rw [htyp]
  rw [hkey]
  refine Matrix.PosSemidef.add ?_ ?_
  · refine Matrix.posSemidef_sum Finset.univ fun x _ => ?_
    have hprod_nonneg : 0 ≤ ∏ i : Fin n, (p.prob (codewordOf x i) : ℝ) := by
      refine Finset.prod_nonneg fun i _ => ?_
      exact NNReal.coe_nonneg _
    have hcoeff_nonneg :
        0 ≤ c * ∏ i, (p.prob (codewordOf x i) : ℝ) -
            (E_pruned.probs x : ℝ) := by
      have hleft_nonneg : 0 ≤ c * ∏ i, (p.prob (codewordOf x i) : ℝ) :=
        mul_nonneg hc_nonneg hprod_nonneg
      linarith [hdom x, hleft_nonneg]
    exact (productState (fun i => symStates (codewordOf x i))).pos.smul hcoeff_nonneg
  · refine Matrix.PosSemidef.smul ?_ hc_nonneg
    refine Matrix.posSemidef_sum Finset.univ fun x _ => ?_
    have hprod_nonneg : 0 ≤ (∏ i, p.prob (x.1 i) : ℝ≥0) := by
      exact bot_le
    exact (productState (fun i => symStates (x.1 i))).pos.smul hprod_nonneg

/-- Projected pack-4 bound for a pruned ensemble, assembled from the pruned
coefficient-domination reduction and a diagonal marginal-product mass envelope.

The bridge between the per-symbol average `σbar` and the diagonal marginal
state is deliberately explicit as `hσbar_tensor`: this theorem does not hide
the eigenbasis/pinching identification needed to instantiate it in the full
HSW proof. -/
theorem strongTypicalDiagonalProjector_projectedPrunedAverage_le_of_mass_bound
    {β : Type v} {ι : Type u} [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (pZ : QIT.FiniteDistribution β)
    (symStates : ι → State β) (probs : ι → ℝ≥0) (σbar : State β)
    (hσbar : σbar.matrix = ∑ j, (probs j) • (symStates j).matrix)
    {n : ℕ} {ε δ D : ℝ} (hε : ε < 1)
    (hσbar_tensor :
      (σbar.tensorPower n).matrix =
        (HSWPackingHypothesesSpectral.marginalProductDiagonalState pZ n).matrix)
    (E_pruned : Ensemble (Fin n → ι) (TensorPower β n))
    (hstates : ∀ x : Fin n → ι,
      E_pruned.states x = productState (fun i => symStates (x i)))
    (hdom : ∀ x : Fin n → ι,
      (E_pruned.probs x : ℝ) ≤ (1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ))
    (hmass_bound : ∀ zseq : Fin n → β,
      ClassicalTypicality.StrongTypical pZ zseq δ →
        (HSWPackingHypothesesSpectral.marginalProductMass pZ zseq : ℝ) ≤ D⁻¹) :
    HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector pZ n δ *
        E_pruned.averageState.matrix *
        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector pZ n δ
      ≤ (((1 - ε)⁻¹ : ℝ) * ((D : ℝ)⁻¹)) •
          HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector pZ n δ := by
  let P : CMatrix (TensorPower β n) :=
    HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector pZ n δ
  have hpruned :
      E_pruned.averageState.matrix ≤ ((1 - ε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix :=
    pack4_prunedReduction (a := β) (ι := ι)
      symStates probs σbar hσbar hε E_pruned hstates hdom
  have hprojected :
      P * (σbar.tensorPower n).matrix * P ≤ ((D : ℝ)⁻¹) • P := by
    dsimp [P]
    rw [hσbar_tensor]
    exact HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector_projectedMarginalProduct_le_of_mass_bound
      pZ (n := n) (δ := δ) (D := D) hmass_bound
  have hP_herm : P.IsHermitian := by
    dsimp [P]
    exact (HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector_posSemidef
      pZ n δ).isHermitian
  have hinv_nonneg : 0 ≤ (1 - ε)⁻¹ := by
    have hpos : 0 < 1 - ε := by linarith
    exact inv_nonneg.mpr hpos.le
  exact cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
    hP_herm hinv_nonneg hpruned hprojected

/-- Projected pruned-average pack-4 bound specialized to the diagonal classical
average state `diag(pZ)`.

This removes the explicit tensor-power diagonalization bridge from
`strongTypicalDiagonalProjector_projectedPrunedAverage_le_of_mass_bound` in the
common post-pinching HSW case: the per-symbol average is already the diagonal
state of the induced output law `pZ`. -/
theorem strongTypicalDiagonalProjector_projectedPrunedAverage_le_of_diagonal_average_mass_bound
    {β : Type v} {ι : Type u} [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (pZ : QIT.FiniteDistribution β)
    (symStates : ι → State β) (probs : ι → ℝ≥0)
    (hσbar : (Classical.diagonalState pZ.prob pZ.sum_eq_one).matrix =
      ∑ j, (probs j) • (symStates j).matrix)
    {n : ℕ} {ε δ D : ℝ} (hε : ε < 1)
    (E_pruned : Ensemble (Fin n → ι) (TensorPower β n))
    (hstates : ∀ x : Fin n → ι,
      E_pruned.states x = productState (fun i => symStates (x i)))
    (hdom : ∀ x : Fin n → ι,
      (E_pruned.probs x : ℝ) ≤ (1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ))
    (hmass_bound : ∀ zseq : Fin n → β,
      ClassicalTypicality.StrongTypical pZ zseq δ →
        (HSWPackingHypothesesSpectral.marginalProductMass pZ zseq : ℝ) ≤ D⁻¹) :
    HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector pZ n δ *
        E_pruned.averageState.matrix *
        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector pZ n δ
      ≤ (((1 - ε)⁻¹ : ℝ) * ((D : ℝ)⁻¹)) •
          HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector pZ n δ := by
  refine strongTypicalDiagonalProjector_projectedPrunedAverage_le_of_mass_bound
    pZ symStates probs (Classical.diagonalState pZ.prob pZ.sum_eq_one) hσbar hε ?_
    E_pruned hstates hdom hmass_bound
  exact HSWPackingHypothesesSpectral.diagonalState_tensorPower_matrix_eq_marginalProductDiagonalState
    pZ n

/-- Projected pruned-average pack-4 bound for conditional product diagonal
states.

This is the HSW post-pinching pack-4 interface: the pruned codeword ensemble is
indexed by length-`n` input words, its state for `xⁿ` is the diagonal
conditional product law `K^n(.|xⁿ)`, and its probability is pointwise dominated
by `(1 - ε)⁻¹ p^n(xⁿ)`. The conclusion is exactly the projected average-state
Loewner bound used by the packing lemma, with the entropy exponent still
isolated as the explicit `hmass_bound`. -/
theorem strongTypicalDiagonalProjector_projectedPrunedConditionalProductAverage_le_of_mass_bound
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    {n : ℕ} {ε δ D : ℝ} (hε : ε < 1)
    (E_pruned : Ensemble (Fin n → α) (TensorPower β n))
    (hstates : ∀ x : Fin n → α,
      E_pruned.states x = HSWPackingHypothesesSpectral.conditionalProductDiagonalState K x)
    (hdom : ∀ x : Fin n → α,
      (E_pruned.probs x : ℝ) ≤ (1 - ε)⁻¹ * ∏ i, (p.prob (x i) : ℝ))
    (hmass_bound : ∀ zseq : Fin n → β,
      ClassicalTypicality.StrongTypical (ClassicalTypicality.inducedMarginal p K) zseq δ →
        (HSWPackingHypothesesSpectral.marginalProductMass
          (ClassicalTypicality.inducedMarginal p K) zseq : ℝ) ≤ D⁻¹) :
    HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
          (ClassicalTypicality.inducedMarginal p K) n δ *
        E_pruned.averageState.matrix *
        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
          (ClassicalTypicality.inducedMarginal p K) n δ
      ≤ (((1 - ε)⁻¹ : ℝ) * ((D : ℝ)⁻¹)) •
          HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
            (ClassicalTypicality.inducedMarginal p K) n δ := by
  let symStates : α → State β := fun x =>
    Classical.diagonalState (K.prob x) (K.sum_eq_one x)
  have hstates_product : ∀ x : Fin n → α,
      E_pruned.states x = productState (fun i => symStates (x i)) := by
    intro x
    apply State.ext
    rw [hstates x]
    exact HSWPackingHypothesesSpectral.conditionalProductDiagonalState_matrix_eq_productState_diagonal
      K x
  refine strongTypicalDiagonalProjector_projectedPrunedAverage_le_of_diagonal_average_mass_bound
    (ClassicalTypicality.inducedMarginal p K) symStates p.prob ?_ hε E_pruned
    hstates_product hdom hmass_bound
  simpa [symStates] using
    HSWPackingHypothesesSpectral.diagonalState_inducedMarginal_matrix_eq_average_conditionalDiagonalStates
      p K

/-- Effective-`D` form of
`strongTypicalDiagonalProjector_projectedPrunedConditionalProductAverage_le_of_mass_bound`.

The pruned-distribution prefactor is absorbed into the packing lemma's
dimension parameter as `D_eff = (1 - ε) * D`. -/
theorem strongTypicalDiagonalProjector_projectedPrunedConditionalProductAverage_le_effectiveD
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    {n : ℕ} {ε δ D : ℝ} (hε : ε < 1) (hD : 0 < D)
    (E_pruned : Ensemble (Fin n → α) (TensorPower β n))
    (hstates : ∀ x : Fin n → α,
      E_pruned.states x = HSWPackingHypothesesSpectral.conditionalProductDiagonalState K x)
    (hdom : ∀ x : Fin n → α,
      (E_pruned.probs x : ℝ) ≤ (1 - ε)⁻¹ * ∏ i, (p.prob (x i) : ℝ))
    (hmass_bound : ∀ zseq : Fin n → β,
      ClassicalTypicality.StrongTypical (ClassicalTypicality.inducedMarginal p K) zseq δ →
        (HSWPackingHypothesesSpectral.marginalProductMass
          (ClassicalTypicality.inducedMarginal p K) zseq : ℝ) ≤ D⁻¹) :
    HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
          (ClassicalTypicality.inducedMarginal p K) n δ *
        E_pruned.averageState.matrix *
        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
          (ClassicalTypicality.inducedMarginal p K) n δ
      ≤ (((1 - ε) * D : ℝ)⁻¹) •
          HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
            (ClassicalTypicality.inducedMarginal p K) n δ := by
  have hbase :=
    strongTypicalDiagonalProjector_projectedPrunedConditionalProductAverage_le_of_mass_bound
      p K hε E_pruned hstates hdom hmass_bound
  have hscalar :
      (((1 - ε)⁻¹ : ℝ) * ((D : ℝ)⁻¹)) = (((1 - ε) * D : ℝ)⁻¹) := by
    have hpos : 0 < 1 - ε := by linarith
    field_simp [ne_of_gt hpos, ne_of_gt hD]
  simpa [hscalar] using hbase

/-- Entropy-envelope form of the projected pruned-average pack-4 bound for
conditional product diagonal states.

This discharges the explicit word-by-word `hmass_bound` of
`strongTypicalDiagonalProjector_projectedPrunedConditionalProductAverage_le_effectiveD`
from the finite strong-typical product-mass theorem.  The only remaining
numerical input is the source-shaped choice of `D`:
`2^{-n H(Z) + n δ L(Z)} ≤ D⁻¹` for the induced output distribution. -/
theorem strongTypicalDiagonalProjector_projectedPrunedConditionalProductAverage_le_entropyD
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    {n : ℕ} {ε δ D : ℝ} (hn : 0 < n) (hε : ε < 1) (hD : 0 < D)
    (hδ : 0 ≤ δ)
    (hD_entropy :
      Real.rpow 2
        (- (n : ℝ) * (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
          (n : ℝ) * δ *
            (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
        ≤ D⁻¹)
    (E_pruned : Ensemble (Fin n → α) (TensorPower β n))
    (hstates : ∀ x : Fin n → α,
      E_pruned.states x = HSWPackingHypothesesSpectral.conditionalProductDiagonalState K x)
    (hdom : ∀ x : Fin n → α,
      (E_pruned.probs x : ℝ) ≤ (1 - ε)⁻¹ * ∏ i, (p.prob (x i) : ℝ)) :
    HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
          (ClassicalTypicality.inducedMarginal p K) n δ *
        E_pruned.averageState.matrix *
        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
          (ClassicalTypicality.inducedMarginal p K) n δ
      ≤ (((1 - ε) * D : ℝ)⁻¹) •
          HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
            (ClassicalTypicality.inducedMarginal p K) n δ := by
  refine strongTypicalDiagonalProjector_projectedPrunedConditionalProductAverage_le_effectiveD
    p K hε hD E_pruned hstates hdom ?_
  intro zseq hz
  exact HSWPackingHypothesesSpectral.marginalProductMass_le_D_inv_of_entropy_slack
    (ClassicalTypicality.inducedMarginal p K) zseq hn hδ hD_entropy hz

/-- Projected pack-4 bound for the canonical pruned strongly-typical codebook.

This is the source-shaped HSW pruning interface used by the direct theorem:
the random-coding alphabet is the strongly-typical subtype, its law is the
normalized i.i.d. law on that subtype, and its output states are the conditional
product diagonal states generated by `K`.  The theorem derives the projected
average-state Loewner bound, including the `(1 - pruneε)⁻¹` pruning prefactor
and the strong-typical marginal-product mass envelope. -/
theorem strongTypicalDiagonalProjector_projectedPrunedStrongTypicalConditionalProductAverage_le_entropyD
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (p : QIT.FiniteDistribution α) (K : QIT.StochasticKernel α β)
    {n : ℕ} {pruneε δx δ D : ℝ} (hn : 0 < n) (hprune : pruneε < 1)
    (hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx)
    (hmass_lower : (1 - pruneε : ℝ) ≤
      (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ))
    (hD : 0 < D) (hδ : 0 ≤ δ)
    (hD_entropy :
      Real.rpow 2
        (- (n : ℝ) * (ClassicalTypicality.inducedMarginal p K).shannonEntropy +
          (n : ℝ) * δ *
            (ClassicalTypicality.inducedMarginal p K).logTypicalitySlack)
        ≤ D⁻¹)
    (E_pruned :
      Ensemble (ClassicalTypicality.StrongTypicalWord p n δx) (TensorPower β n))
    (hprobs : ∀ x,
      E_pruned.probs x =
        (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob x)
    (hstates : ∀ x,
      E_pruned.states x =
        HSWPackingHypothesesSpectral.conditionalProductDiagonalState K
          (ClassicalTypicality.StrongTypicalWord.codeword p δx x)) :
    HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
          (ClassicalTypicality.inducedMarginal p K) n δ *
        E_pruned.averageState.matrix *
        HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
          (ClassicalTypicality.inducedMarginal p K) n δ
      ≤ (((1 - pruneε) * D : ℝ)⁻¹) •
          HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
            (ClassicalTypicality.inducedMarginal p K) n δ := by
  let symStates : α → State β := fun x =>
    Classical.diagonalState (K.prob x) (K.sum_eq_one x)
  let σbar : State β :=
    Classical.diagonalState
      (ClassicalTypicality.inducedMarginal p K).prob
      (ClassicalTypicality.inducedMarginal p K).sum_eq_one
  let P : CMatrix (TensorPower β n) :=
    HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector
      (ClassicalTypicality.inducedMarginal p K) n δ
  have hstates_product : ∀ x,
      E_pruned.states x =
        productState (fun i => symStates
          (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) := by
    intro x
    apply State.ext
    rw [hstates x]
    exact HSWPackingHypothesesSpectral.conditionalProductDiagonalState_matrix_eq_productState_diagonal
      K (ClassicalTypicality.StrongTypicalWord.codeword p δx x)
  have hσbar :
      σbar.matrix = ∑ j, (p.prob j) • (symStates j).matrix := by
    dsimp [σbar, symStates]
    simpa using
      HSWPackingHypothesesSpectral.diagonalState_inducedMarginal_matrix_eq_average_conditionalDiagonalStates
        p K
  have hpruned :
      E_pruned.averageState.matrix ≤ ((1 - pruneε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix :=
    pack4_prunedStrongTypicalReduction
      symStates p σbar hσbar hmass_pos hmass_lower hprune E_pruned hprobs hstates_product
  have hprojected :
      P * (σbar.tensorPower n).matrix * P ≤ ((D : ℝ)⁻¹) • P := by
    dsimp [P, σbar]
    rw [HSWPackingHypothesesSpectral.diagonalState_tensorPower_matrix_eq_marginalProductDiagonalState]
    exact HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector_projectedMarginalProduct_le_of_mass_bound
      (ClassicalTypicality.inducedMarginal p K) (n := n) (δ := δ) (D := D)
      (fun zseq hz =>
        HSWPackingHypothesesSpectral.marginalProductMass_le_D_inv_of_entropy_slack
          (ClassicalTypicality.inducedMarginal p K) zseq hn hδ hD_entropy hz)
  have hP_herm : P.IsHermitian := by
    dsimp [P]
    exact (HSWPackingHypothesesSpectral.strongTypicalDiagonalProjector_posSemidef
      (ClassicalTypicality.inducedMarginal p K) n δ).isHermitian
  have hinv_nonneg : 0 ≤ (1 - pruneε)⁻¹ := by
    have hpos : 0 < 1 - pruneε := by linarith
    exact inv_nonneg.mpr hpos.le
  have hbase :
      P * E_pruned.averageState.matrix * P ≤
        (((1 - pruneε)⁻¹ : ℝ) * ((D : ℝ)⁻¹)) • P :=
    cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
      hP_herm hinv_nonneg hpruned hprojected
  have hscalar :
      (((1 - pruneε)⁻¹ : ℝ) * ((D : ℝ)⁻¹)) = (((1 - pruneε) * D : ℝ)⁻¹) := by
    have hpos : 0 < 1 - pruneε := by linarith
    field_simp [ne_of_gt hpos, ne_of_gt hD]
  simpa [P, hscalar] using hbase

end QIT
