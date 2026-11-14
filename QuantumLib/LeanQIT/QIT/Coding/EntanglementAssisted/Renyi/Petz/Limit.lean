/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.Lower.Petz
public import QIT.Coding.EntanglementAssisted.Basic
public import QIT.Information.BinaryHypothesisTest
public import QIT.Information.Renyi.RenyiLimit
public import QIT.Util.Order.EReal

/-!
# Petz--Renyi alpha-to-one limit for entanglement-assisted information

This module proves the source-shaped `alpha -> 1^-` bridge for the PSD-domain
barred Petz--Renyi mutual information used in the asymptotic
entanglement-assisted achievability step
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:894-982] and the channel
mutual-information definition
[KhatriWilde2024Principles, Chapters/entropies.tex:8132-8144].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology
open Filter

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace BinaryHypothesisTest


/-- KL summand for the product-marginal Nussbaum--Szkola model, with the
overlap factor cancelling in the `p ≠ 0` branch. -/
private theorem relativeEntropySummandReal_productMarginalNussbaumSzkolaModel
    (rhoAB : State (Prod a b)) (xy : (Prod a b) × (Prod a b)) :
    relativeEntropySummandReal
        (productMarginalNussbaumSzkolaModel rhoAB).pDistribution
        (productMarginalNussbaumSzkolaModel rhoAB).qDistribution xy =
      (((stateSpectralWeight rhoAB xy.1 : NNReal) : ℝ) *
        ((productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2 : NNReal) : ℝ)) *
        (Real.log ((stateSpectralWeight rhoAB xy.1 : NNReal) : ℝ) -
          Real.log ((productMarginalSpectralWeight rhoAB xy.2 : NNReal) : ℝ)) := by
  classical
  rcases xy with ⟨x, y⟩
  let M := productMarginalNussbaumSzkolaModel rhoAB
  by_cases hp : M.p (x, y) = 0
  · have hfactor :
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) = 0 := by
      have hpR : ((M.p (x, y) : NNReal) : ℝ) = 0 := by
        rw [hp]
        norm_num
      simpa [M, productMarginalNussbaumSzkolaModel, NNReal.coe_mul] using hpR
    simp [relativeEntropySummandReal, ClassicalBinaryModel.pDistribution,
      productMarginalNussbaumSzkolaModel, hfactor]
  · have hq : M.q (x, y) ≠ 0 :=
      productMarginalNussbaumSzkolaModel_p_supportedBy_q rhoAB (x, y) (by
        simpa [M, ClassicalBinaryModel.pDistribution] using hp)
    have hp_prod :
        stateSpectralWeight rhoAB x *
            productMarginalNussbaumSzkolaOverlap rhoAB x y ≠ 0 := by
      simpa [M, productMarginalNussbaumSzkolaModel] using hp
    have hq_prod :
        productMarginalSpectralWeight rhoAB y *
            productMarginalNussbaumSzkolaOverlap rhoAB x y ≠ 0 := by
      simpa [M, productMarginalNussbaumSzkolaModel] using hq
    have hlam_ne : stateSpectralWeight rhoAB x ≠ 0 :=
      (mul_ne_zero_iff.mp hp_prod).1
    have ho_ne : productMarginalNussbaumSzkolaOverlap rhoAB x y ≠ 0 :=
      (mul_ne_zero_iff.mp hp_prod).2
    have hmu_ne : productMarginalSpectralWeight rhoAB y ≠ 0 :=
      (mul_ne_zero_iff.mp hq_prod).1
    have hlam_pos : 0 < ((stateSpectralWeight rhoAB x : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < stateSpectralWeight rhoAB x :=
        lt_of_le_of_ne (show (0 : NNReal) ≤ stateSpectralWeight rhoAB x from zero_le)
          (Ne.symm hlam_ne)
      exact_mod_cast hnn
    have ho_pos : 0 < ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < productMarginalNussbaumSzkolaOverlap rhoAB x y :=
        lt_of_le_of_ne
          (show (0 : NNReal) ≤ productMarginalNussbaumSzkolaOverlap rhoAB x y from zero_le)
          (Ne.symm ho_ne)
      exact_mod_cast hnn
    have hmu_pos : 0 < ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) := by
      have hnn : (0 : NNReal) < productMarginalSpectralWeight rhoAB y :=
        lt_of_le_of_ne
          (show (0 : NNReal) ≤ productMarginalSpectralWeight rhoAB y from zero_le)
          (Ne.symm hmu_ne)
      exact_mod_cast hnn
    have hlog :
        Real.log
            ((((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
                ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) /
              (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) *
                ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ))) =
          Real.log ((stateSpectralWeight rhoAB x : NNReal) : ℝ) -
            Real.log ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) := by
      have hoR_ne :
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) ≠ 0 :=
        ne_of_gt ho_pos
      rw [show
          (((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
              ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) /
            (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) *
              ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) =
            ((stateSpectralWeight rhoAB x : NNReal) : ℝ) /
              ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) by
            field_simp [hoR_ne]]
      exact Real.log_div hlam_pos.ne' hmu_pos.ne'
    rw [relativeEntropySummandReal]
    simp only [ClassicalBinaryModel.pDistribution, ClassicalBinaryModel.qDistribution]
    rw [if_neg (by simpa [M] using hp)]
    simp [productMarginalNussbaumSzkolaModel, NNReal.coe_mul, hlog]


/-- Product-marginal Nussbaum--Szkola classical relative entropy is the
entropy-form mutual-information log numerator. -/
private theorem productMarginalNussbaumSzkolaModel_relativeEntropyReal_eq_log_sums
    (rhoAB : State (Prod a b)) :
    relativeEntropyReal
        (productMarginalNussbaumSzkolaModel rhoAB).pDistribution
        (productMarginalNussbaumSzkolaModel rhoAB).qDistribution =
      (∑ x : Prod a b,
        ((stateSpectralWeight rhoAB x : NNReal) : ℝ) *
          Real.log ((stateSpectralWeight rhoAB x : NNReal) : ℝ)) -
        ((∑ i : a,
          ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) *
            Real.log ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ)) +
          (∑ j : b,
            ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) *
              Real.log ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ))) := by
  classical
  let lam : Prod a b → ℝ := fun x =>
    ((stateSpectralWeight rhoAB x : NNReal) : ℝ)
  let ov : Prod a b → Prod a b → ℝ := fun x y =>
    ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)
  let mu : Prod a b → ℝ := fun y =>
    ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ)
  let muA : a → ℝ := fun i =>
    ((stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ)
  let muB : b → ℝ := fun j =>
    ((stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ)
  have hrow : ∀ x : Prod a b, ∑ y : Prod a b, ov x y = 1 := by
    intro x
    have h :
        ∑ y : Prod a b,
          ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ) = 1 := by
      exact_mod_cast productMarginalNussbaumSzkolaOverlap_row_sum rhoAB x
    simpa [ov] using h
  have hfst : ∀ i : a, ∑ j : b, ∑ x : Prod a b, lam x * ov x (i, j) = muA i := by
    intro i
    rw [Finset.sum_comm]
    simpa [lam, ov, muA] using
      productMarginalNussbaumSzkolaOverlap_weighted_fst_sum rhoAB i
  have hsnd : ∀ j : b, ∑ i : a, ∑ x : Prod a b, lam x * ov x (i, j) = muB j := by
    intro j
    rw [Finset.sum_comm]
    simpa [lam, ov, muB] using
      productMarginalNussbaumSzkolaOverlap_weighted_snd_sum rhoAB j
  have hfirst :
      ∑ xy : (Prod a b) × (Prod a b),
          (lam xy.1 * ov xy.1 xy.2) * Real.log (lam xy.1) =
        ∑ x : Prod a b, lam x * Real.log (lam x) := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ x : Prod a b, ∑ y : Prod a b,
          (lam x * ov x y) * Real.log (lam x)
          =
        ∑ x : Prod a b, ∑ y : Prod a b,
          ov x y * (lam x * Real.log (lam x)) := by
          simp [mul_assoc, mul_comm]
      _ = ∑ x : Prod a b,
          (∑ y : Prod a b, ov x y) * (lam x * Real.log (lam x)) := by
          simp [Finset.sum_mul]
      _ = ∑ x : Prod a b, lam x * Real.log (lam x) := by
          simp [hrow]
  have hsecond :
      ∑ xy : (Prod a b) × (Prod a b),
          (lam xy.1 * ov xy.1 xy.2) * Real.log (mu xy.2) =
        (∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j)) := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ x : Prod a b, ∑ y : Prod a b,
          (lam x * ov x y) * Real.log (mu y)
          =
        ∑ y : Prod a b, (∑ x : Prod a b, lam x * ov x y) * Real.log (mu y) := by
          rw [Finset.sum_comm]
          simp [Finset.sum_mul]
      _ =
        ∑ y : Prod a b, (∑ x : Prod a b, lam x * ov x y) *
          (Real.log (muA y.1) + Real.log (muB y.2)) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          simpa [lam, ov, mu, muA, muB] using
            productMarginalNussbaumSzkolaModel_weighted_log_product rhoAB y
      _ =
        (∑ i : a, ∑ j : b,
          (∑ x : Prod a b, lam x * ov x (i, j)) * Real.log (muA i)) +
          (∑ i : a, ∑ j : b,
            (∑ x : Prod a b, lam x * ov x (i, j)) * Real.log (muB j)) := by
          rw [Fintype.sum_prod_type]
          simp [mul_add, Finset.sum_add_distrib]
      _ =
        (∑ i : a, (∑ j : b, ∑ x : Prod a b, lam x * ov x (i, j)) *
          Real.log (muA i)) +
          (∑ j : b, (∑ i : a, ∑ x : Prod a b, lam x * ov x (i, j)) *
            Real.log (muB j)) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [Finset.sum_mul]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            simp [Finset.sum_mul]
      _ =
        (∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j)) := by
          simp [hfst, hsnd]
  calc
    relativeEntropyReal
        (productMarginalNussbaumSzkolaModel rhoAB).pDistribution
        (productMarginalNussbaumSzkolaModel rhoAB).qDistribution
        =
      ∑ xy : (Prod a b) × (Prod a b),
        (lam xy.1 * ov xy.1 xy.2) *
          (Real.log (lam xy.1) - Real.log (mu xy.2)) := by
        unfold relativeEntropyReal
        refine Finset.sum_congr rfl ?_
        intro xy _hxy
        simpa [lam, ov, mu] using
          relativeEntropySummandReal_productMarginalNussbaumSzkolaModel rhoAB xy
    _ =
      (∑ xy : (Prod a b) × (Prod a b),
          (lam xy.1 * ov xy.1 xy.2) * Real.log (lam xy.1)) -
        (∑ xy : (Prod a b) × (Prod a b),
          (lam xy.1 * ov xy.1 xy.2) * Real.log (mu xy.2)) := by
        simp [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ x : Prod a b, lam x * Real.log (lam x)) -
        ((∑ i : a, muA i * Real.log (muA i)) +
          (∑ j : b, muB j * Real.log (muB j))) := by
        rw [hfirst, hsecond]

private theorem productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_term
    (p q r : NNReal) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (p * r) ^ s * (q * r) ^ (1 - s) =
      p ^ s * q ^ (1 - s) * r := by
  have hs1' : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  calc
    (p * r) ^ s * (q * r) ^ (1 - s) =
        (p ^ s * r ^ s) * (q ^ (1 - s) * r ^ (1 - s)) := by
          rw [NNReal.mul_rpow, NNReal.mul_rpow]
    _ = p ^ s * q ^ (1 - s) * (r ^ s * r ^ (1 - s)) := by
          ac_rfl
    _ = p ^ s * q ^ (1 - s) * r ^ (s + (1 - s)) := by
          rw [NNReal.rpow_add_of_nonneg r hs0 hs1']
    _ = p ^ s * q ^ (1 - s) * r := by
          have hsum : s + (1 - s) = 1 := by ring
          rw [hsum, NNReal.rpow_one]

/-- The product-marginal classical Chernoff coefficient is the Petz
coefficient for the barred product-marginal pair. -/
theorem productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_eq
    (rhoAB : State (Prod a b)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (productMarginalNussbaumSzkolaModel rhoAB).petzChernoffCoefficient s =
      rhoAB.petzRenyiCoefficient
        (rhoAB.marginalA.prod rhoAB.marginalB) s := by
  classical
  let Urho : Matrix.unitaryGroup (Prod a b) ℂ :=
    rhoAB.pos.isHermitian.eigenvectorUnitary
  let Uprod : Matrix.unitaryGroup (Prod a b) ℂ :=
    productMarginalEigenvectorUnitary rhoAB
  let sigma : State (Prod a b) := rhoAB.marginalA.prod rhoAB.marginalB
  have hrho :
      CFC.rpow rhoAB.matrix s =
        (Urho : CMatrix (Prod a b)) *
          Matrix.diagonal
            (fun x : Prod a b =>
              (((((stateSpectralWeight rhoAB x : NNReal) : ℝ) ^ s : ℝ) : ℂ))) *
          star (Urho : CMatrix (Prod a b)) := by
    simpa [Urho, stateSpectralWeight] using
      cMatrix_rpow_eq_eigenbasis_diagonal rhoAB.pos s
  have hw_nonneg :
      ∀ y : Prod a b, 0 ≤ ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) := by
    intro y
    positivity
  have hsigma_spec :
      sigma.matrix =
        (Uprod : CMatrix (Prod a b)) *
          Matrix.diagonal
            (fun y : Prod a b =>
              (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) : ℂ)) *
          star (Uprod : CMatrix (Prod a b)) := by
    simpa [sigma, Uprod] using
      productMarginal_matrix_eq_productEigenbasis_diagonal rhoAB
  have hsigma :
      CFC.rpow sigma.matrix (1 - s) =
        (Uprod : CMatrix (Prod a b)) *
          Matrix.diagonal
            (fun y : Prod a b =>
              ((((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) ^ (1 - s) : ℝ) : ℂ)) *
          star (Uprod : CMatrix (Prod a b)) := by
    rw [hsigma_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal
      Uprod (fun y : Prod a b => ((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ))
      hw_nonneg (1 - s)
  have htrace :
      (rhoAB.petzRenyiCoefficient sigma s : ℝ) =
        ∑ x : Prod a b, ∑ y : Prod a b,
          (((stateSpectralWeight rhoAB x : NNReal) : ℝ) ^ s) *
            ((((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) ^ (1 - s)) *
              ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) := by
    change ((CFC.rpow rhoAB.matrix s * CFC.rpow sigma.matrix (1 - s)).trace).re = _
    rw [hrho, hsigma]
    simpa [Urho, Uprod, productMarginalNussbaumSzkolaOverlap,
      productMarginalNussbaumSzkolaTransitionUnitary, Matrix.star_eq_conjTranspose,
      mul_assoc, mul_left_comm, mul_comm] using
      trace_mul_two_unitary_conj_diagonal_ofReal_re
        Urho Uprod
        (fun x : Prod a b => (((stateSpectralWeight rhoAB x : NNReal) : ℝ) ^ s : ℝ))
        (fun y : Prod a b =>
          (((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) ^ (1 - s) : ℝ))
  apply NNReal.eq
  calc
    ((productMarginalNussbaumSzkolaModel rhoAB).petzChernoffCoefficient s : ℝ) =
        ∑ xy : (Prod a b) × (Prod a b),
          (((stateSpectralWeight rhoAB xy.1) ^ s *
            (productMarginalSpectralWeight rhoAB xy.2) ^ (1 - s) *
              productMarginalNussbaumSzkolaOverlap rhoAB xy.1 xy.2 : NNReal) : ℝ) := by
          simp [ClassicalBinaryModel.petzChernoffCoefficient,
            productMarginalNussbaumSzkolaModel,
            productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_term _ _ _ hs0 hs1,
            mul_assoc]
    _ = ∑ x : Prod a b, ∑ y : Prod a b,
          (((stateSpectralWeight rhoAB x : NNReal) : ℝ) ^ s) *
            ((((productMarginalSpectralWeight rhoAB y : NNReal) : ℝ) ^ (1 - s)) *
              ((productMarginalNussbaumSzkolaOverlap rhoAB x y : NNReal) : ℝ)) := by
          rw [Fintype.sum_prod_type]
          simp [NNReal.coe_rpow, mul_assoc]
    _ = (rhoAB.petzRenyiCoefficient sigma s : ℝ) := htrace.symm

end BinaryHypothesisTest

namespace State


/-- The product-marginal Nussbaum--Szkola endpoint is the entropy-form mutual
information, not the full-rank relative-entropy API. -/
theorem productMarginalNussbaumSzkolaModel_relativeEntropyReal_div_log_two_eq_mutualInformation
    (rhoAB : State (Prod a b)) :
    BinaryHypothesisTest.relativeEntropyReal
        (BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).pDistribution
        (BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).qDistribution /
      Real.log 2 =
        mutualInformation rhoAB := by
  classical
  let sAB : ℝ := ∑ x : Prod a b,
    ((BinaryHypothesisTest.stateSpectralWeight rhoAB x : NNReal) : ℝ) *
      Real.log ((BinaryHypothesisTest.stateSpectralWeight rhoAB x : NNReal) : ℝ)
  let sA : ℝ := ∑ i : a,
    ((BinaryHypothesisTest.stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ) *
      Real.log ((BinaryHypothesisTest.stateSpectralWeight rhoAB.marginalA i : NNReal) : ℝ)
  let sB : ℝ := ∑ j : b,
    ((BinaryHypothesisTest.stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ) *
      Real.log ((BinaryHypothesisTest.stateSpectralWeight rhoAB.marginalB j : NNReal) : ℝ)
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hAB : sAB / Real.log 2 = -rhoAB.vonNeumann := by
    simpa [sAB] using
      spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann rhoAB
  have hA : sA / Real.log 2 = -rhoAB.marginalA.vonNeumann := by
    simpa [sA] using
      spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann rhoAB.marginalA
  have hB : sB / Real.log 2 = -rhoAB.marginalB.vonNeumann := by
    simpa [sB] using
      spectralWeight_mul_log_div_log_two_eq_neg_vonNeumann rhoAB.marginalB
  rw [BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_relativeEntropyReal_eq_log_sums]
  change (sAB - (sA + sB)) / Real.log 2 = mutualInformation rhoAB
  calc
    (sAB - (sA + sB)) / Real.log 2 =
        sAB / Real.log 2 - (sA / Real.log 2 + sB / Real.log 2) := by
          field_simp [hlog_ne]
    _ = mutualInformation rhoAB := by
          rw [hAB, hA, hB]
          unfold mutualInformation
          ring

/-- In the PSD source branch, barred Petz--Renyi mutual information is the
base-2 Chernoff log partition of the product-marginal Nussbaum--Szkola model. -/
theorem barPetzRenyiMutualInformationPSDFinite_eq_productMarginal_chernoffLog2
    (rhoAB : State (Prod a b)) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    rhoAB.barPetzRenyiMutualInformationPSDFinite alpha halpha0 (ne_of_lt halpha1) =
      (1 / (alpha - 1)) *
        log2 ((BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).chernoffPartition alpha) := by
  classical
  let sigma : State (Prod a b) := rhoAB.marginalA.prod rhoAB.marginalB
  let M := BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB
  have htrace :
      ((CFC.rpow rhoAB.matrix alpha *
        CFC.rpow sigma.matrix (1 - alpha)).trace).re =
        (rhoAB.petzRenyiCoefficient sigma alpha : ℝ) := by
    have h := State.petzRenyiCoefficient_trace_eq rhoAB sigma alpha
    have hre := congrArg Complex.re h
    simpa using hre.symm
  have hpart :
      M.chernoffPartition alpha =
        (rhoAB.petzRenyiCoefficient sigma alpha : ℝ) := by
    have hnn :
        M.chernoffPartitionNNReal alpha = M.petzChernoffCoefficient alpha :=
      BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
        (M := M) halpha0 halpha1
    have hns :
        M.petzChernoffCoefficient alpha =
          rhoAB.petzRenyiCoefficient sigma alpha := by
      simpa [sigma, M] using
        BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_petzChernoffCoefficient_eq
          rhoAB (le_of_lt halpha0) (le_of_lt halpha1)
    calc
      M.chernoffPartition alpha =
          (M.chernoffPartitionNNReal alpha : ℝ) := by
            exact (BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_coe
              M alpha).symm
      _ = (M.petzChernoffCoefficient alpha : ℝ) := by rw [hnn]
      _ = (rhoAB.petzRenyiCoefficient sigma alpha : ℝ) := by rw [hns]
  have hpart' :
      (BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).chernoffPartition alpha =
        (rhoAB.petzRenyiCoefficient (rhoAB.marginalA.prod rhoAB.marginalB) alpha : ℝ) := by
    simpa [M, sigma] using hpart
  unfold State.barPetzRenyiMutualInformationPSDFinite State.petzRenyiPSDFinite
  change
    (1 / (alpha - 1)) *
        log2 ((CFC.rpow rhoAB.matrix alpha *
          CFC.rpow (rhoAB.marginalA.prod rhoAB.marginalB).matrix (1 - alpha)).trace).re =
      (1 / (alpha - 1)) *
        log2 ((BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB).chernoffPartition alpha)
  rw [htrace, ← hpart']

/-- State-level barred PSD Petz--Renyi mutual information converges to the
entropy-form mutual information as `alpha -> 1^-`. -/
theorem barPetzRenyiMutualInformationPSDFinite_tendsto_mutualInformation_left
    (rhoAB : State (Prod a b)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        rhoAB.barPetzRenyiMutualInformationPSDFinite
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds (mutualInformation rhoAB)) := by
  classical
  let M := BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB
  have hpq : M.pDistribution.SupportedBy M.q := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_p_supportedBy_q rhoAB
  have hendpoint :
      BinaryHypothesisTest.relativeEntropyReal M.pDistribution M.qDistribution /
        Real.log 2 = mutualInformation rhoAB := by
    simpa [M] using
      productMarginalNussbaumSzkolaModel_relativeEntropyReal_div_log_two_eq_mutualInformation rhoAB
  have hclassical :
      Tendsto
        (fun alpha : PetzRenyiAlpha =>
          (1 / (alpha.1 - 1)) * log2 (M.chernoffPartition alpha.1))
        PetzRenyiAlpha.leftToOne
        (nhds (mutualInformation rhoAB)) := by
    simpa [hendpoint] using
      BinaryHypothesisTest.ClassicalBinaryModel.petzChernoffLog2_tendsto_relativeEntropyReal_subtype_left
        (M := M) hpq
  refine hclassical.congr' ?_
  filter_upwards with alpha
  exact (barPetzRenyiMutualInformationPSDFinite_eq_productMarginal_chernoffLog2
    (rhoAB := rhoAB) (alpha := alpha.1) alpha.2.1 alpha.2.2).symm

/-- The canonical extended-real barred Petz quantity has the same left
endpoint as its finite representative. -/
theorem barPetzRenyiMutualInformationPSD_tendsto_mutualInformation_left
    (rhoAB : State (Prod a b)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        rhoAB.barPetzRenyiMutualInformationPSD
          alpha.1 alpha.2.1 alpha.2.2)
      PetzRenyiAlpha.leftToOne
      (nhds (mutualInformation rhoAB : EReal)) := by
  refine (EReal.tendsto_coe.mpr
    (barPetzRenyiMutualInformationPSDFinite_tendsto_mutualInformation_left rhoAB)).congr' ?_
  filter_upwards with alpha
  exact (rhoAB.barPetzRenyiMutualInformationPSD_eq_coe_finite
    alpha.1 alpha.2.1 alpha.2.2).symm

/-- Source-range comparison needed for the channel-level `sSup` upper bound:
barred PSD Petz--Renyi mutual information is bounded by entropy-form mutual
information. -/
theorem barPetzRenyiMutualInformationPSDFinite_le_mutualInformation
    (rhoAB : State (Prod a b)) (alpha : PetzRenyiAlpha) :
    rhoAB.barPetzRenyiMutualInformationPSDFinite
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
      mutualInformation rhoAB := by
  classical
  let M := BinaryHypothesisTest.productMarginalNussbaumSzkolaModel rhoAB
  have hpq : M.pDistribution.SupportedBy M.q := by
    simpa [M] using
      BinaryHypothesisTest.productMarginalNussbaumSzkolaModel_p_supportedBy_q rhoAB
  have hendpoint :
      BinaryHypothesisTest.relativeEntropyReal M.pDistribution M.qDistribution /
        Real.log 2 = mutualInformation rhoAB := by
    simpa [M] using
      productMarginalNussbaumSzkolaModel_relativeEntropyReal_div_log_two_eq_mutualInformation rhoAB
  calc
    rhoAB.barPetzRenyiMutualInformationPSDFinite
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) =
      (1 / (alpha.1 - 1)) * log2 (M.chernoffPartition alpha.1) := by
        simpa [M] using
          barPetzRenyiMutualInformationPSDFinite_eq_productMarginal_chernoffLog2
            (rhoAB := rhoAB) (alpha := alpha.1) alpha.2.1 alpha.2.2
    _ ≤ BinaryHypothesisTest.relativeEntropyReal M.pDistribution M.qDistribution /
        Real.log 2 :=
        BinaryHypothesisTest.ClassicalBinaryModel.petzChernoffLog2_le_relativeEntropyReal
          (M := M) hpq alpha.2.1 alpha.2.2
    _ = mutualInformation rhoAB := hendpoint

/-- Canonical extended-real source-range comparison with entropy-form mutual
information. -/
theorem barPetzRenyiMutualInformationPSD_le_mutualInformation
    (rhoAB : State (Prod a b)) (alpha : PetzRenyiAlpha) :
    rhoAB.barPetzRenyiMutualInformationPSD
        alpha.1 alpha.2.1 alpha.2.2 ≤
      (mutualInformation rhoAB : EReal) := by
  rw [rhoAB.barPetzRenyiMutualInformationPSD_eq_coe_finite]
  exact_mod_cast
    barPetzRenyiMutualInformationPSDFinite_le_mutualInformation rhoAB alpha

/-- State-level barred PSD Petz--Renyi mutual information converges to the
Nussbaum--Szkola classical relative entropy for the product-marginal pair. -/
theorem barPetzRenyiMutualInformationPSDFinite_tendsto_nussbaumSzkola_relativeEntropyReal_left
    (rhoAB : State (Prod a b)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        rhoAB.barPetzRenyiMutualInformationPSDFinite
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds
        (BinaryHypothesisTest.relativeEntropyReal
          (BinaryHypothesisTest.nussbaumSzkolaModel rhoAB
            (rhoAB.marginalA.prod rhoAB.marginalB)).pDistribution
          (BinaryHypothesisTest.nussbaumSzkolaModel rhoAB
            (rhoAB.marginalA.prod rhoAB.marginalB)).qDistribution /
            Real.log 2)) := by
  simpa [State.barPetzRenyiMutualInformationPSDFinite] using
    State.petzRenyiPSDFinite_tendsto_nussbaumSzkola_relativeEntropyReal_left
      rhoAB (rhoAB.marginalA.prod rhoAB.marginalB)
      rhoAB.matrix_supports_prod_marginals

end State

namespace Channel

variable (N : Channel a b)

/-- The hypothesis-testing and entanglement-assisted output-state APIs use the
same channel-output state. -/
theorem hypothesisTestingOutputState_eq_entanglementAssistedOutputState
    (psi : PureVector (Prod a a)) :
    N.hypothesisTestingOutputState psi = N.entanglementAssistedOutputState psi := by
  rfl

/-- Fixed-input channel bridge for the PSD barred Petz--Renyi endpoint, with
the endpoint still expressed as the Nussbaum--Szkola classical relative
entropy of the output/product-marginal pair. -/
theorem inputBarPetzRenyiMutualInformationPSDFinite_tendsto_nussbaumSzkola_relativeEntropyReal_left
    (psi : PureVector (Prod a a)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        N.inputBarPetzRenyiMutualInformationPSDFinite
          psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds
        (BinaryHypothesisTest.relativeEntropyReal
          (BinaryHypothesisTest.nussbaumSzkolaModel
            (N.hypothesisTestingOutputState psi)
            ((N.hypothesisTestingOutputState psi).marginalA.prod
              (N.hypothesisTestingOutputState psi).marginalB)).pDistribution
          (BinaryHypothesisTest.nussbaumSzkolaModel
            (N.hypothesisTestingOutputState psi)
            ((N.hypothesisTestingOutputState psi).marginalA.prod
              (N.hypothesisTestingOutputState psi).marginalB)).qDistribution /
            Real.log 2)) := by
  simpa [Channel.inputBarPetzRenyiMutualInformationPSDFinite] using
    State.barPetzRenyiMutualInformationPSDFinite_tendsto_nussbaumSzkola_relativeEntropyReal_left
      (N.hypothesisTestingOutputState psi)

/-- Fixed-input channel bridge for the PSD barred Petz--Renyi endpoint, with
the endpoint expressed as entropy-form entanglement-assisted mutual
information. -/
theorem inputBarPetzRenyiMutualInformationPSDFinite_tendsto_entanglementAssistedMutualInformation_left
    (psi : PureVector (Prod a a)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        N.inputBarPetzRenyiMutualInformationPSDFinite
          psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds (N.entanglementAssistedMutualInformation psi)) := by
  simpa [Channel.inputBarPetzRenyiMutualInformationPSDFinite,
    Channel.entanglementAssistedMutualInformation,
    N.hypothesisTestingOutputState_eq_entanglementAssistedOutputState psi] using
    State.barPetzRenyiMutualInformationPSDFinite_tendsto_mutualInformation_left
      (N.hypothesisTestingOutputState psi)

/-- Canonical extended-real fixed-input barred Petz information converges to
the ordinary entanglement-assisted mutual information. -/
theorem inputBarPetzRenyiMutualInformationPSD_tendsto_entanglementAssistedMutualInformation_left
    (psi : PureVector (Prod a a)) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        N.inputBarPetzRenyiMutualInformationPSD
          psi alpha.1 alpha.2.1 alpha.2.2)
      PetzRenyiAlpha.leftToOne
      (nhds (N.entanglementAssistedMutualInformation psi : EReal)) := by
  refine (EReal.tendsto_coe.mpr
    (N.inputBarPetzRenyiMutualInformationPSDFinite_tendsto_entanglementAssistedMutualInformation_left
      psi)).congr' ?_
  filter_upwards with alpha
  exact (N.inputBarPetzRenyiMutualInformationPSD_eq_coe_finite
    psi alpha.1 alpha.2.1 alpha.2.2).symm

/-- Fixed-input source-range comparison against the channel's ordinary
entanglement-assisted information. -/
theorem inputBarPetzRenyiMutualInformationPSDFinite_le_entanglementAssistedInformation
    [Nonempty a] (psi : PureVector (Prod a a)) (alpha : PetzRenyiAlpha) :
    N.inputBarPetzRenyiMutualInformationPSDFinite
        psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
      N.entanglementAssistedInformation := by
  calc
    N.inputBarPetzRenyiMutualInformationPSDFinite
        psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) =
      (N.hypothesisTestingOutputState psi).barPetzRenyiMutualInformationPSDFinite
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) := rfl
    _ ≤ mutualInformation (N.hypothesisTestingOutputState psi) :=
        State.barPetzRenyiMutualInformationPSDFinite_le_mutualInformation
          (N.hypothesisTestingOutputState psi) alpha
    _ = N.entanglementAssistedMutualInformation psi := by
        simp [Channel.entanglementAssistedMutualInformation,
          N.hypothesisTestingOutputState_eq_entanglementAssistedOutputState psi]
    _ ≤ N.entanglementAssistedInformation :=
        N.entanglementAssistedMutualInformation_le_information psi

/-- Canonical fixed-input source-range comparison against the channel's
ordinary entanglement-assisted information. -/
theorem inputBarPetzRenyiMutualInformationPSD_le_entanglementAssistedInformation
    [Nonempty a] (psi : PureVector (Prod a a)) (alpha : PetzRenyiAlpha) :
    N.inputBarPetzRenyiMutualInformationPSD
        psi alpha.1 alpha.2.1 alpha.2.2 ≤
      (N.entanglementAssistedInformation : EReal) := by
  rw [N.inputBarPetzRenyiMutualInformationPSD_eq_coe_finite]
  exact_mod_cast
    N.inputBarPetzRenyiMutualInformationPSDFinite_le_entanglementAssistedInformation
      psi alpha

/-- The PSD barred channel Petz value set is bounded above by `I(N)` in the
source range. -/
theorem barPetzRenyiMutualInformationPSDFiniteValueSet_bddAbove
    [Nonempty a] (alpha : PetzRenyiAlpha) :
    BddAbove
      (N.barPetzRenyiMutualInformationPSDFiniteValueSet
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)) := by
  refine ⟨N.entanglementAssistedInformation, ?_⟩
  intro value hvalue
  rcases hvalue with ⟨psi, rfl⟩
  exact N.inputBarPetzRenyiMutualInformationPSDFinite_le_entanglementAssistedInformation
    psi alpha

/-- The optimized canonical PSD quantity is the coercion of the optimized
finite real quantity throughout the source range. -/
theorem barPetzRenyiMutualInformationPSD_eq_coe_finite
    [Nonempty a] (alpha : PetzRenyiAlpha) :
    N.barPetzRenyiMutualInformationPSD alpha.1 alpha.2.1 alpha.2.2 =
      (N.barPetzRenyiMutualInformationPSDFinite
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) : EReal) := by
  classical
  letI : Nonempty (PureVector (Prod a a)) := ⟨PureVector.basisPureVector⟩
  let f : PureVector (Prod a a) → ℝ := fun psi =>
    N.inputBarPetzRenyiMutualInformationPSDFinite
      psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)
  have hfiniteSet :
      N.barPetzRenyiMutualInformationPSDFiniteValueSet
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) = Set.range f := by
    ext value
    simp only [barPetzRenyiMutualInformationPSDFiniteValueSet, Set.mem_setOf_eq,
      Set.mem_range, f]
    constructor <;> rintro ⟨psi, rfl⟩ <;> exact ⟨psi, rfl⟩
  have hcanonicalSet :
      N.barPetzRenyiMutualInformationPSDValueSet
          alpha.1 alpha.2.1 alpha.2.2 =
        Set.range fun psi => (f psi : EReal) := by
    ext value
    simp only [barPetzRenyiMutualInformationPSDValueSet, Set.mem_setOf_eq,
      Set.mem_range]
    constructor
    · rintro ⟨psi, rfl⟩
      refine ⟨psi, ?_⟩
      exact (N.inputBarPetzRenyiMutualInformationPSD_eq_coe_finite
        psi alpha.1 alpha.2.1 alpha.2.2).symm
    · rintro ⟨psi, rfl⟩
      refine ⟨psi, ?_⟩
      exact (N.inputBarPetzRenyiMutualInformationPSD_eq_coe_finite
        psi alpha.1 alpha.2.1 alpha.2.2).symm
  have hf : BddAbove (Set.range f) := by
    rw [← hfiniteSet]
    exact N.barPetzRenyiMutualInformationPSDFiniteValueSet_bddAbove alpha
  rw [N.barPetzRenyiMutualInformationPSD_eq_sSup,
    N.barPetzRenyiMutualInformationPSDFinite_eq_sSup, hcanonicalSet, hfiniteSet]
  exact ereal_sSup_range_coe_eq_coe_real_sSup f hf

/-- Channel-level source-range upper bound for PSD barred Petz--Renyi mutual
information. -/
theorem barPetzRenyiMutualInformationPSDFinite_le_entanglementAssistedInformation
    [Nonempty a] (alpha : PetzRenyiAlpha) :
    N.barPetzRenyiMutualInformationPSDFinite
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
      N.entanglementAssistedInformation := by
  classical
  rw [N.barPetzRenyiMutualInformationPSDFinite_eq_sSup
    alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)]
  have hne :
      (N.barPetzRenyiMutualInformationPSDFiniteValueSet
        alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)).Nonempty := by
    let psi0 : PureVector (Prod a a) := PureVector.basisPureVector
    refine ⟨N.inputBarPetzRenyiMutualInformationPSDFinite
      psi0 alpha.1 alpha.2.1 (ne_of_lt alpha.2.2), ?_⟩
    exact ⟨psi0, rfl⟩
  refine csSup_le hne ?_
  intro value hvalue
  rcases hvalue with ⟨psi, rfl⟩
  exact N.inputBarPetzRenyiMutualInformationPSDFinite_le_entanglementAssistedInformation
    psi alpha

/-- Channel-level canonical source-range upper bound for PSD barred
Petz--Renyi mutual information. -/
theorem barPetzRenyiMutualInformationPSD_le_entanglementAssistedInformation
    [Nonempty a] (alpha : PetzRenyiAlpha) :
    N.barPetzRenyiMutualInformationPSD
        alpha.1 alpha.2.1 alpha.2.2 ≤
      (N.entanglementAssistedInformation : EReal) := by
  rw [N.barPetzRenyiMutualInformationPSD_eq_coe_finite alpha]
  exact_mod_cast
    N.barPetzRenyiMutualInformationPSDFinite_le_entanglementAssistedInformation alpha

/-- Source-shaped alpha-to-one theorem for the PSD-domain barred
Petz--Renyi channel mutual information:
`lim_{alpha -> 1^-} \bar I_alpha^{Petz,PSD}(N) = I(N)`. -/
theorem barPetzRenyiMutualInformationPSDFinite_tendsto_entanglementAssistedInformation_left
    [Nonempty a] :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        N.barPetzRenyiMutualInformationPSDFinite
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds N.entanglementAssistedInformation) := by
  classical
  obtain ⟨psi, hpsi⟩ := N.exists_entanglementAssistedInformation_maximizer
  have hfixed :
      Tendsto
        (fun alpha : PetzRenyiAlpha =>
          N.inputBarPetzRenyiMutualInformationPSDFinite
            psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
        PetzRenyiAlpha.leftToOne
        (nhds N.entanglementAssistedInformation) := by
    simpa [hpsi] using
      N.inputBarPetzRenyiMutualInformationPSDFinite_tendsto_entanglementAssistedMutualInformation_left
        psi
  have hconst :
      Tendsto
        (fun _alpha : PetzRenyiAlpha => N.entanglementAssistedInformation)
        PetzRenyiAlpha.leftToOne
        (nhds N.entanglementAssistedInformation) := tendsto_const_nhds
  have hlower :
      (fun alpha : PetzRenyiAlpha =>
        N.inputBarPetzRenyiMutualInformationPSDFinite
          psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)) ≤
      (fun alpha : PetzRenyiAlpha =>
        N.barPetzRenyiMutualInformationPSDFinite
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)) := by
    intro alpha
    change
      N.inputBarPetzRenyiMutualInformationPSDFinite
          psi alpha.1 alpha.2.1 (ne_of_lt alpha.2.2) ≤
        N.barPetzRenyiMutualInformationPSDFinite
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)
    rw [N.barPetzRenyiMutualInformationPSDFinite_eq_sSup
      alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)]
    exact le_csSup
      (N.barPetzRenyiMutualInformationPSDFiniteValueSet_bddAbove alpha)
      ⟨psi, rfl⟩
  have hupper :
      (fun alpha : PetzRenyiAlpha =>
        N.barPetzRenyiMutualInformationPSDFinite
          alpha.1 alpha.2.1 (ne_of_lt alpha.2.2)) ≤
      (fun _alpha : PetzRenyiAlpha => N.entanglementAssistedInformation) := by
    intro alpha
    exact N.barPetzRenyiMutualInformationPSDFinite_le_entanglementAssistedInformation alpha
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hfixed hconst hlower hupper

/-- Source-shaped canonical alpha-to-one theorem for PSD barred Petz--Renyi
channel mutual information. -/
theorem barPetzRenyiMutualInformationPSD_tendsto_entanglementAssistedInformation_left
    [Nonempty a] :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        N.barPetzRenyiMutualInformationPSD
          alpha.1 alpha.2.1 alpha.2.2)
      PetzRenyiAlpha.leftToOne
      (nhds (N.entanglementAssistedInformation : EReal)) := by
  refine (EReal.tendsto_coe.mpr
    N.barPetzRenyiMutualInformationPSDFinite_tendsto_entanglementAssistedInformation_left).congr' ?_
  filter_upwards with alpha
  exact (N.barPetzRenyiMutualInformationPSD_eq_coe_finite alpha).symm

end Channel

end

end QIT