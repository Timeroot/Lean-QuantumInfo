/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.PosSqrt
public import QIT.States.Purification.Gram
public import QIT.States.TraceNorm.Distance
public import QIT.States.Topology
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Quantum entropy

Von Neumann entropy (spectral-sum), quantum relative entropy, conditional
entropy, and conditional mutual information. The trace norm is defined in
`QIT.States.TraceNorm.Distance`. Entropy is defined via the
eigenvalue sum (0 log 0 := 0 convention), avoiding the CFC.log eigenvalue-0
boundary. Relative entropy is exposed in bits, matching the base-2 entropy
convention used by conditional entropy and conditional mutual information.
The source definitions are registered from [Tomamichel2015FiniteResources,
renyi.tex:679-693], [Tomamichel2015FiniteResources, cond.tex:28-39], and
[SutterFawziRenner2015Recovery, universalRecMap.tex:166-169].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

noncomputable local instance matrixCStarAlgebra {n : Type u} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) where

noncomputable local instance matrixNormalCFC {n : Type u} [Fintype n] [DecidableEq n] :
    ContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance matrixNormalIsometricCFC {n : Type u} [Fintype n] [DecidableEq n] :
    IsometricContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instIsometricContinuousFunctionalCalculus

/-- log base 2. -/
def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- x log_2 x with the 0 log 0 := 0 convention. -/
def xlog2 (x : ℝ) : ℝ := if x = 0 then 0 else x * log2 x

/-! ## Order-theoretic logarithm transport

Supremum/infimum transport lemmas for `log2` and positive scaling on the
real line, consumed by the smooth-entropy endpoint characterizations. -/

section Log2OrderTransport

open Set

/-- On a nonempty positive bounded-above set, `log₂` sends the supremum to the
supremum of the image. -/
theorem log2_sSup_image_eq {s : Set ℝ}
    (hne : s.Nonempty) (hbdd : BddAbove s) (hpos : ∀ x ∈ s, 0 < x) :
    sSup (log2 '' s) = log2 (sSup s) := by
  unfold log2
  have hsup_pos : 0 < sSup s := by
    rcases hne with ⟨x, hx⟩
    exact lt_of_lt_of_le (hpos x hx) (le_csSup hbdd hx)
  have hcont : ContinuousWithinAt (fun x : ℝ => Real.log x / Real.log 2) s (sSup s) := by
    exact (Real.continuousAt_log hsup_pos.ne').div_const _ |>.continuousWithinAt
  have hmono : MonotoneOn (fun x : ℝ => Real.log x / Real.log 2) s := by
    intro x hx y hy hxy
    exact div_le_div_of_nonneg_right (Real.log_le_log (hpos x hx) hxy)
      (le_of_lt (Real.log_pos one_lt_two))
  have hmap := MonotoneOn.map_csSup_of_continuousWithinAt
    (f := fun x : ℝ => Real.log x / Real.log 2) (A := s) hcont hmono hne hbdd
  simpa using hmap.symm

/-- On a nonempty bounded-below set whose infimum is strictly positive,
`-log₂` sends the infimum to the supremum of the image. -/
theorem neg_log2_sInf_image_eq {s : Set ℝ}
    (hne : s.Nonempty) (hbdd : BddBelow s) (hinf_pos : 0 < sInf s) :
    sSup ((fun x : ℝ => -log2 x) '' s) = -log2 (sInf s) := by
  unfold log2
  have hcont : ContinuousWithinAt
      (fun x : ℝ => -(Real.log x / Real.log 2)) s (sInf s) := by
    exact (Real.continuousAt_log hinf_pos.ne').div_const _ |>.neg |>.continuousWithinAt
  have hanti : AntitoneOn (fun x : ℝ => -(Real.log x / Real.log 2)) s := by
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_of_lt_of_le hinf_pos (csInf_le hbdd hx)
    exact neg_le_neg (div_le_div_of_nonneg_right (Real.log_le_log hxpos hxy)
      (le_of_lt (Real.log_pos one_lt_two)))
  have hmap := AntitoneOn.map_csInf_of_continuousWithinAt
    (f := fun x : ℝ => -(Real.log x / Real.log 2)) (A := s) hcont hanti hne hbdd
  simpa using hmap.symm

theorem neg_log2_rpow_two_neg (lam : ℝ) :
    -log2 (Real.rpow 2 (-lam)) = lam := by
  unfold log2
  rw [show Real.log (Real.rpow 2 (-lam)) = -lam * Real.log 2 by
    exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) (-lam)]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

theorem rpow_two_log2_pos {x : ℝ} (hx : 0 < x) :
    Real.rpow 2 (log2 x) = x := by
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hx
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  unfold log2
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

theorem mul_sSup_image_eq {s : Set ℝ} {c : ℝ}
    (hne : s.Nonempty) (hbdd : BddAbove s) (hc : 0 < c) :
    sSup ((fun x : ℝ => c * x) '' s) = c * sSup s := by
  have hcont : ContinuousWithinAt (fun x : ℝ => c * x) s (sSup s) :=
    (continuous_const.mul continuous_id).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun x : ℝ => c * x) s := by
    intro x _ y _ hxy
    exact mul_le_mul_of_nonneg_left hxy (le_of_lt hc)
  have hmap := MonotoneOn.map_csSup_of_continuousWithinAt
    (f := fun x : ℝ => c * x) (A := s) hcont hmono hne hbdd
  simpa using hmap.symm

end Log2OrderTransport

/-- The eigenvalues of a Hermitian matrix, packaged as a real multiset
(indexed by the underlying finite label type, multiplicities included). -/
def eigenvalueMultiset {n : Type u} [Fintype n] [DecidableEq n]
    {M : CMatrix n} (hM : M.IsHermitian) : Multiset ℝ :=
  Multiset.map hM.eigenvalues Finset.univ.val

namespace State

/-- Von Neumann entropy S(ρ) = -Σ λᵢ log₂ λᵢ over the eigenvalues of ρ,
with 0 log 0 := 0. -/
def vonNeumann (ρ : State a) : ℝ :=
  -(Finset.univ.sum fun i => xlog2 ((ρ.pos.isHermitian).eigenvalues i))

/-- The von Neumann entropy, rewritten as a multiset sum over the
eigenvalue multiset: `S(ρ) = -∑_{λ ∈ spec(ρ)} xlog2 λ`. -/
lemma vonNeumann_eq_neg_sum_eigenvalueMultiset (ρ : State a) :
    vonNeumann ρ = -((eigenvalueMultiset ρ.pos.isHermitian).map xlog2).sum := by
  show -(Finset.univ.sum fun i => xlog2 (ρ.pos.isHermitian.eigenvalues i)) = _
  rw [eigenvalueMultiset, Finset.sum_eq_multiset_sum, Multiset.map_map]
  rfl

private noncomputable def entropyCfcScalar (x : ℝ) : ℝ :=
  -(x * Real.log x / Real.log 2)

private noncomputable def entropyCfcComplex (z : ℂ) : ℂ :=
  (entropyCfcScalar z.re : ℂ)

private theorem entropyCfcScalar_eq_neg_xlog2 (x : ℝ) :
    entropyCfcScalar x = -xlog2 x := by
  unfold entropyCfcScalar xlog2 log2
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]
    ring

private theorem continuous_entropyCfcScalar : Continuous entropyCfcScalar := by
  unfold entropyCfcScalar
  exact (Real.continuous_mul_log.div_const _).neg

private theorem continuous_entropyCfcComplex : Continuous entropyCfcComplex := by
  unfold entropyCfcComplex
  exact Complex.continuous_ofReal.comp (continuous_entropyCfcScalar.comp Complex.continuous_re)

private theorem vonNeumann_eq_cfc_trace (ρ : State a) :
    ρ.vonNeumann = ((cfc entropyCfcComplex ρ.matrix).trace).re := by
  rw [State.vonNeumann]
  have hreal :
      cfc entropyCfcScalar ρ.matrix = cfc entropyCfcComplex ρ.matrix := by
    simpa [entropyCfcComplex] using
      (cfc_real_eq_complex (a := ρ.matrix) entropyCfcScalar
        (ha := ρ.pos.isHermitian.isSelfAdjoint))
  rw [← hreal]
  have hcfc :
      cfc entropyCfcScalar ρ.matrix =
        ρ.pos.isHermitian.cfc entropyCfcScalar :=
    Matrix.IsHermitian.cfc_eq (𝕜 := ℂ) ρ.pos.isHermitian entropyCfcScalar
  rw [hcfc]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  rw [Matrix.trace_diagonal]
  simp only [Function.comp_apply, entropyCfcScalar_eq_neg_xlog2]
  simp [Finset.sum_neg_distrib]

/-- Eigenvalues of a state sum to one. -/
private lemma eigenvalue_sum (ρ : State a) :
    ∑ i, ρ.pos.isHermitian.eigenvalues i = 1 := by
  have hc : (∑ i, ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 := by
    exact ρ.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
  exact Complex.ofReal_injective (by simpa using hc)

/-- Eigenvalues of a state are bounded above by one. -/
private lemma eigenvalue_le_one (ρ : State a) (i : a) :
    ρ.pos.isHermitian.eigenvalues i ≤ 1 := by
  have hnonneg (j : a) : 0 ≤ ρ.pos.isHermitian.eigenvalues j :=
    ρ.pos.eigenvalues_nonneg j
  have hsum : ∑ j, ρ.pos.isHermitian.eigenvalues j = 1 :=
    eigenvalue_sum ρ
  calc ρ.pos.isHermitian.eigenvalues i
      ≤ ρ.pos.isHermitian.eigenvalues i
        + ∑ j ∈ Finset.univ.erase i, ρ.pos.isHermitian.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
    _ = ∑ j, ρ.pos.isHermitian.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => ρ.pos.isHermitian.eigenvalues j) (Finset.mem_univ i)
    _ = 1 := hsum

private theorem spectrum_subset_stateInterval (ρ : State a) :
    spectrum ℂ ρ.matrix ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
  intro z hz
  rw [ρ.pos.isHermitian.spectrum_eq_image_range] at hz
  rcases hz with ⟨x, ⟨i, rfl⟩, rfl⟩
  exact ⟨ρ.pos.isHermitian.eigenvalues i,
    ⟨ρ.pos.eigenvalues_nonneg i, eigenvalue_le_one ρ i⟩, rfl⟩

/-- Von Neumann entropy is continuous on finite-dimensional density states. -/
theorem vonNeumann_continuous : Continuous (fun ρ : State a => ρ.vonNeumann) := by
  let K : Set ℂ := Complex.ofReal '' Set.Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    CompactIccSpace.isCompact_Icc.image Complex.continuous_ofReal
  have hcfc : Continuous fun ρ : State a =>
      (cfc entropyCfcComplex (ρ.matrix : Matrix a a ℂ) : Matrix a a ℂ) := by
    exact Continuous.cfc' (A := Matrix a a ℂ) (p := IsStarNormal)
      (s := K) hK entropyCfcComplex State.continuous_matrix
      (fun ρ => spectrum_subset_stateInterval ρ)
      (continuous_entropyCfcComplex.continuousOn)
      (fun ρ => ρ.pos.isHermitian.isSelfAdjoint.isStarNormal)
  have htrace : Continuous fun ρ : State a =>
      ((cfc entropyCfcComplex ρ.matrix).trace).re :=
    Complex.continuous_re.comp (Continuous.matrix_trace hcfc)
  exact htrace.congr fun ρ => (vonNeumann_eq_cfc_trace ρ).symm

/-- Von Neumann entropy is nonnegative: S(rho) >= 0. -/
theorem vonNeumann_nonneg (ρ : State a) : 0 ≤ vonNeumann ρ := by
  let hH : ρ.matrix.IsHermitian := ρ.pos.isHermitian
  have hnonneg (i : a) : 0 ≤ hH.eigenvalues i := ρ.pos.eigenvalues_nonneg i
  have hle1 (i : a) : hH.eigenvalues i ≤ 1 := eigenvalue_le_one ρ i
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i _
  by_cases hl : hH.eigenvalues i = 0
  · simp only [xlog2, if_pos hl]
    exact le_rfl
  · simp only [xlog2, if_neg hl]
    have hpos : 0 < hH.eigenvalues i := lt_of_le_of_ne (hnonneg i) (Ne.symm hl)
    have hlog2le : log2 (hH.eigenvalues i) ≤ 0 := by
      unfold log2
      exact div_nonpos_of_nonpos_of_nonneg
        (Real.log_nonpos (hnonneg i) (hle1 i)) (le_of_lt (Real.log_pos one_lt_two))
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) hlog2le

/-- For x >= 0, x * Real.log x >= x - 1. -/
private lemma xlog_self_ge_sub_one {x : ℝ} (hx : 0 ≤ x) :
    x * Real.log x ≥ x - 1 := by
  rcases lt_or_eq_of_le hx with h | h
  · have hl := Real.one_sub_inv_le_log_of_pos h
    nlinarith [hl, mul_inv_cancel₀ (ne_of_gt h)]
  · rw [← h]
    norm_num

/-- Von Neumann entropy is bounded by log2(dim).

S(rho) <= log2(Fintype.card a).
-/
theorem vonNeumann_le_log_card (ρ : State a) :
    vonNeumann ρ ≤ log2 (Fintype.card a) := by
  let hH : ρ.matrix.IsHermitian := ρ.pos.isHermitian
  have hnonneg (i : a) : 0 ≤ hH.eigenvalues i := ρ.pos.eigenvalues_nonneg i
  have hsum : ∑ i, hH.eigenvalues i = 1 := eigenvalue_sum ρ
  have hcard_pos : 0 < Fintype.card a := by
    by_contra hcard
    have hcard_zero : Fintype.card a = 0 := Nat.eq_zero_of_not_pos hcard
    haveI : IsEmpty a := Fintype.card_eq_zero_iff.mp hcard_zero
    have hsum_zero : ∑ i, hH.eigenvalues i = 0 := by simp
    have : (0 : ℝ) = 1 := hsum_zero.symm.trans hsum
    norm_num at this
  have hnreal : (0 : ℝ) < Fintype.card a := Nat.cast_pos.mpr hcard_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- Key identity: xlog2(x) * Real.log 2 = x * Real.log x for x >= 0
  have hxlog2_mul (x : ℝ) (hx : 0 ≤ x) : xlog2 x * Real.log 2 = x * Real.log x := by
    by_cases h : x = 0
    · simp [xlog2, h]
    · simp only [xlog2, if_neg h, log2]
      field_simp [ne_of_gt hlog2_pos]
  -- Suffices: vonNeumann ρ * Real.log 2 ≤ Real.log n
  -- Because: vonNeumann ≤ log2 n = Real.log n / Real.log 2
  --   iff (le_div_iff₀ hlog2_pos): vonNeumann * Real.log 2 ≤ Real.log n
  rw [show log2 (Fintype.card a) = Real.log (Fintype.card a) / Real.log 2 from rfl]
  rw [le_div_iff₀ hlog2_pos]
  -- Goal: vonNeumann ρ * Real.log 2 ≤ Real.log (Fintype.card a)
  -- vonNeumann = -(∑ xlog2(λᵢ))
  -- So vonNeumann * Real.log 2 = -(∑ xlog2(λᵢ)) * Real.log 2 = -(∑ xlog2(λᵢ) * Real.log 2)
  have hvn_mul : vonNeumann ρ * Real.log 2 =
      -∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i) := by
    rw [vonNeumann]
    calc
      (-(∑ i, xlog2 (hH.eigenvalues i))) * Real.log 2
          = -((∑ i, xlog2 (hH.eigenvalues i)) * Real.log 2) := by ring
      _ = -(∑ i, xlog2 (hH.eigenvalues i) * Real.log 2) := by
        rw [Finset.sum_mul]
      _ = -∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact hxlog2_mul _ (hnonneg i)
  rw [hvn_mul]
  -- Now: -(∑ λᵢ ln λᵢ) ≤ Real.log n
  -- KL divergence: ∑ λᵢ * ln(λᵢ * n) ≥ 0, which expands to ∑ λᵢ ln λᵢ ≥ -ln n
  -- So -(∑ λᵢ ln λᵢ) ≤ ln n
  -- Prove KL ≥ 0 via: λᵢ * ln(λᵢ * n) ≥ λᵢ - 1/n for each i
  have hKL : 0 ≤ ∑ i, hH.eigenvalues i
      * Real.log (hH.eigenvalues i * ↑(Fintype.card a)) := by
    have hbound : ∀ i, hH.eigenvalues i
        * Real.log (hH.eigenvalues i * ↑(Fintype.card a))
        ≥ hH.eigenvalues i - 1 / ↑(Fintype.card a) := by
      intro i
      by_cases hl : hH.eigenvalues i = 0
      · simp [hl, Real.log_zero]
      · have hlpos : 0 < hH.eigenvalues i := lt_of_le_of_ne (hnonneg i) (Ne.symm hl)
        have hprod : 0 < hH.eigenvalues i * ↑(Fintype.card a) :=
          mul_pos hlpos hnreal
        have hxi := xlog_self_ge_sub_one (le_of_lt hprod)
        have : hH.eigenvalues i * Real.log (hH.eigenvalues i * ↑(Fintype.card a))
            ≥ hH.eigenvalues i - 1 / ↑(Fintype.card a) := by
          have hdiv :
              (hH.eigenvalues i * ↑(Fintype.card a) - 1) / ↑(Fintype.card a)
                ≤ (hH.eigenvalues i * ↑(Fintype.card a)
                    * Real.log (hH.eigenvalues i * ↑(Fintype.card a)))
                    / ↑(Fintype.card a) :=
            div_le_div_of_nonneg_right hxi (le_of_lt hnreal)
          calc
            hH.eigenvalues i - 1 / ↑(Fintype.card a)
                = (hH.eigenvalues i * ↑(Fintype.card a) - 1)
                    / ↑(Fintype.card a) := by
                    field_simp [ne_of_gt hnreal]
            _ ≤ (hH.eigenvalues i * ↑(Fintype.card a)
                    * Real.log (hH.eigenvalues i * ↑(Fintype.card a)))
                    / ↑(Fintype.card a) := hdiv
            _ = hH.eigenvalues i
                    * Real.log (hH.eigenvalues i * ↑(Fintype.card a)) := by
                    field_simp [ne_of_gt hnreal]
        exact this
    calc (0 : ℝ)
        = ∑ i, (hH.eigenvalues i - 1 / ↑(Fintype.card a)) := by
          rw [Finset.sum_sub_distrib]
          rw [hsum, Finset.sum_const]
          simp
          field_simp [ne_of_gt hnreal]
          ring
      _ ≤ ∑ i, hH.eigenvalues i
          * Real.log (hH.eigenvalues i * ↑(Fintype.card a)) :=
        Finset.sum_le_sum (fun i _ => hbound i)
  have hexpand_KL : ∑ i, hH.eigenvalues i
      * Real.log (hH.eigenvalues i * ↑(Fintype.card a))
    = ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i)
      + Real.log ↑(Fintype.card a) := by
    calc
      ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i * ↑(Fintype.card a))
          = ∑ i, (hH.eigenvalues i * Real.log (hH.eigenvalues i)
              + hH.eigenvalues i * Real.log ↑(Fintype.card a)) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hl : hH.eigenvalues i = 0
            · simp [hl, Real.log_zero]
            · have hlpos : 0 < hH.eigenvalues i :=
                lt_of_le_of_ne (hnonneg i) (Ne.symm hl)
              rw [Real.log_mul (ne_of_gt hlpos) (ne_of_gt hnreal)]
              ring
      _ = ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i)
          + ∑ i, hH.eigenvalues i * Real.log ↑(Fintype.card a) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i)
          + (∑ i, hH.eigenvalues i) * Real.log ↑(Fintype.card a) := by
            rw [Finset.sum_mul]
      _ = ∑ i, hH.eigenvalues i * Real.log (hH.eigenvalues i)
          + Real.log ↑(Fintype.card a) := by
            rw [hsum]
            ring
  -- From KL: sum λᵢ ln λᵢ ≥ -ln n
  linarith [hKL, hexpand_KL]

/-- The natural log of a positive-definite matrix via continuous functional
calculus. Requires `PosDef` (invertible, strictly positive spectrum) so that
`Real.log` is continuous on the spectrum. -/
def psdLog (M : CMatrix a) (_hM : M.PosDef) : CMatrix a :=
  cfc Real.log M

/-- Positive-definite finite compatibility API for quantum relative entropy
D(ρ‖σ) in bits.

Both states must be positive-definite (full-rank) for CFC.log to apply. The
CFC logarithm is the natural logarithm, so the trace expression is divided by
`Real.log 2` to match the base-2 entropy convention. -/
def relativeEntropyPosDefFinite (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) : ℝ :=
  ((ρ.matrix * psdLog ρ.matrix hρ).trace.re
    - (ρ.matrix * psdLog σ.matrix hσ).trace.re) / Real.log 2

/-- The matrix-log trace expression for a positive-definite state expands to
the spectral `λ log λ` sum. -/
theorem trace_mul_psdLog_eq_sum_eigenvalues_mul_log
    (ρ : State a) (hρ : ρ.matrix.PosDef) :
    ((ρ.matrix * psdLog ρ.matrix hρ).trace).re =
      ∑ i, hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hρ.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ)
  let L : CMatrix a := Matrix.diagonal fun i => ((Real.log (hρ.1.eigenvalues i) : ℝ) : ℂ)
  have hmat : ρ.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hρ.1.spectral_theorem
  have hlog : psdLog ρ.matrix hρ = (U : CMatrix a) * L * star (U : CMatrix a) := by
    rw [psdLog, hρ.1.cfc_eq]
    simp [U, L, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def]
  calc
    ((ρ.matrix * psdLog ρ.matrix hρ).trace).re =
        ((ρ.matrix * ((U : CMatrix a) * L * star (U : CMatrix a))).trace).re := by
      rw [hlog]
    _ = ((((U : CMatrix a) * D * star (U : CMatrix a)) *
          ((U : CMatrix a) * L * star (U : CMatrix a))).trace).re := by
      rw [hmat]
    _ = ((D * L).trace).re := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (U : CMatrix a)) (U : CMatrix a)
        (L * star (U : CMatrix a))]
      rw [Unitary.coe_star_mul_self]
      simp only [one_mul]
      rw [Matrix.trace_mul_comm (U : CMatrix a) (D * (L * star (U : CMatrix a)))]
      rw [← Matrix.mul_assoc D L (star (U : CMatrix a))]
      rw [Matrix.mul_assoc (D * L) (star (U : CMatrix a)) (U : CMatrix a)]
      rw [Unitary.coe_star_mul_self]
      simp
    _ = (∑ i, ((hρ.1.eigenvalues i : ℝ) : ℂ) *
          ((Real.log (hρ.1.eigenvalues i) : ℝ) : ℂ)).re := by
      simp [D, L, Matrix.diagonal_mul_diagonal]
    _ = ∑ i, hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i) := by
      simp

/-- Positive-definite states have the expected matrix-log trace formula for
von Neumann entropy. -/
theorem vonNeumann_eq_neg_trace_mul_psdLog_div_log_two
    (ρ : State a) (hρ : ρ.matrix.PosDef) :
    ρ.vonNeumann =
      -((ρ.matrix * psdLog ρ.matrix hρ).trace.re) / Real.log 2 := by
  classical
  have htrace := trace_mul_psdLog_eq_sum_eigenvalues_mul_log ρ hρ
  have hHerm : hρ.1 = ρ.pos.isHermitian := Subsingleton.elim _ _
  have hxlog (i : a) :
      xlog2 (ρ.pos.isHermitian.eigenvalues i) =
        hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i) / Real.log 2 := by
    rw [← hHerm]
    unfold xlog2 log2
    have hpos : 0 < hρ.1.eigenvalues i := Matrix.PosDef.eigenvalues_pos hρ i
    simp [ne_of_gt hpos]
    ring
  rw [htrace]
  unfold vonNeumann
  simp_rw [hxlog]
  rw [← Finset.sum_div]
  ring

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- Conditional von Neumann entropy `H(A|B)_ρ = H(AB)_ρ - H(B)_ρ`. -/
def conditionalEntropy (ρ : State (Prod a b)) : ℝ :=
  vonNeumann ρ - vonNeumann ρ.marginalB

@[simp]
theorem conditionalEntropy_eq (ρ : State (Prod a b)) :
    ρ.conditionalEntropy = vonNeumann ρ - vonNeumann ρ.marginalB := rfl

/-- Conditional entropy is continuous on finite-dimensional bipartite states. -/
theorem conditionalEntropy_continuous :
    Continuous (fun ρ : State (Prod a b) => ρ.conditionalEntropy) := by
  unfold conditionalEntropy
  exact State.vonNeumann_continuous.sub
    (State.vonNeumann_continuous.comp State.marginalB_continuous)

variable {c : Type w} [Fintype c] [DecidableEq c]

/-- Conditional mutual information
`I(A:C|B)_ρ = H(AB)_ρ + H(BC)_ρ - H(B)_ρ - H(ABC)_ρ`
for a left-associated tripartite state `ρ : State ((A × B) × C)`. -/
def condMutualInfo (ρ : State (Prod (Prod a b) c)) : ℝ :=
  vonNeumann ρ.marginalAB + vonNeumann ρ.marginalBC
    - vonNeumann ρ.marginalBOfABC - vonNeumann ρ

@[simp]
theorem condMutualInfo_eq (ρ : State (Prod (Prod a b) c)) :
    ρ.condMutualInfo =
      vonNeumann ρ.marginalAB + vonNeumann ρ.marginalBC
        - vonNeumann ρ.marginalBOfABC - vonNeumann ρ := rfl

private theorem roots_X_pow_map_re_xlog2_sum_zero (n : ℕ) :
    ((Polynomial.X ^ n : Polynomial ℂ).roots.map fun z : ℂ => xlog2 z.re).sum = 0 := by
  rw [Polynomial.roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton]
  simp [xlog2]

private theorem roots_re_xlog2_sum_eq_of_X_pow_mul_eq
    {P Q : Polynomial ℂ} (m n : ℕ) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : Polynomial.X ^ m * P = Polynomial.X ^ n * Q) :
    (P.roots.map fun z : ℂ => xlog2 z.re).sum =
      (Q.roots.map fun z : ℂ => xlog2 z.re).sum := by
  have hXm : (Polynomial.X ^ m : Polynomial ℂ) ≠ 0 := by simp
  have hXn : (Polynomial.X ^ n : Polynomial ℂ) ≠ 0 := by simp
  have hleft_ne : (Polynomial.X ^ m : Polynomial ℂ) * P ≠ 0 := mul_ne_zero hXm hP
  have hright_ne : (Polynomial.X ^ n : Polynomial ℂ) * Q ≠ 0 := mul_ne_zero hXn hQ
  have hroots := congrArg Polynomial.roots h
  rw [Polynomial.roots_mul hleft_ne, Polynomial.roots_mul hright_ne] at hroots
  have hsum :=
    congrArg (fun s : Multiset ℂ => (s.map fun z : ℂ => xlog2 z.re).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add] at hsum
  rw [roots_X_pow_map_re_xlog2_sum_zero m,
    roots_X_pow_map_re_xlog2_sum_zero n] at hsum
  simpa using hsum

private theorem pureVector_marginalA_matrix_eq_conjTranspose_mul_amplitudeMatrix
    {r : Type u} {α : Type v} [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (Ψ : PureVector (Prod r α)) :
    Ψ.state.marginalA.matrix =
      Matrix.transpose Ψ.amplitudeMatrix *
        Matrix.conjTranspose (Matrix.transpose Ψ.amplitudeMatrix) := by
  ext i j
  simp [PureVector.amplitudeMatrix, State.marginalA, QIT.partialTraceB,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    PureVector.state_matrix, rankOneMatrix_apply]

/-- Complementary marginals of a finite-dimensional pure bipartite state have
the same von Neumann entropy. -/
theorem pureVector_marginalA_vonNeumann_eq_marginalB
    {r : Type u} {α : Type v} [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (Ψ : PureVector (Prod r α)) :
    Ψ.state.marginalA.vonNeumann = Ψ.state.marginalB.vonNeumann := by
  let A : Matrix α r ℂ := Ψ.amplitudeMatrix
  let AT : Matrix r α ℂ := Matrix.transpose A
  have hA :
      Ψ.state.marginalA.matrix = AT * Matrix.conjTranspose AT := by
    simpa [A, AT] using pureVector_marginalA_matrix_eq_conjTranspose_mul_amplitudeMatrix Ψ
  have hB :
      Ψ.state.marginalB.matrix = A * Matrix.conjTranspose A := by
    rw [State.marginalB_matrix, PureVector.state_matrix]
    simpa [A] using
      PureVector.partialTraceA_rankOneMatrix_eq_amplitudeMatrix_mul_conjTranspose Ψ
  have hright_matrix :
      Matrix.conjTranspose AT * AT =
        Matrix.transpose (A * Matrix.conjTranspose A) := by
    ext i j
    simp [A, AT, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      mul_comm]
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset,
    vonNeumann_eq_neg_sum_eigenvalueMultiset]
  congr 1
  have hchar :
      Polynomial.X ^ Fintype.card α * Ψ.state.marginalA.matrix.charpoly =
        Polynomial.X ^ Fintype.card r * Ψ.state.marginalB.matrix.charpoly := by
    rw [hA, hB]
    have hcomm :=
      Matrix.charpoly_mul_comm' (A := AT) (B := Matrix.conjTranspose AT)
    rw [hright_matrix, Matrix.charpoly_transpose] at hcomm
    simpa [A, AT, Matrix.mul_assoc] using hcomm
  have hP : Ψ.state.marginalA.matrix.charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hQ : Ψ.state.marginalB.matrix.charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hroot :=
    roots_re_xlog2_sum_eq_of_X_pow_mul_eq
      (P := Ψ.state.marginalA.matrix.charpoly)
      (Q := Ψ.state.marginalB.matrix.charpoly)
      (Fintype.card α) (Fintype.card r) hP hQ hchar
  have hrootsA := Ψ.state.marginalA.pos.isHermitian.roots_charpoly_eq_eigenvalues
  have hrootsB := Ψ.state.marginalB.pos.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hrootsA, hrootsB] at hroot
  simpa [eigenvalueMultiset, Multiset.map_map, Function.comp_def] using hroot

/-- The von Neumann entropy of a one-dimensional (`PUnit`) state is zero. -/
theorem vonNeumann_punit_eq_zero (ρ : State PUnit.{u + 1}) :
    ρ.vonNeumann = 0 := by
  exact le_antisymm (by simpa [log2] using vonNeumann_le_log_card ρ) (vonNeumann_nonneg ρ)

end State

/-- Quantum mutual information I(X;B) of a bipartite state. -/
def mutualInformation {ι : Type u} {α : Type v} [Fintype ι] [Fintype α]
    [DecidableEq α] [DecidableEq ι] (ρ : State (Prod ι α)) : ℝ :=
  State.vonNeumann ρ.marginalA + State.vonNeumann ρ.marginalB
    - State.vonNeumann ρ

namespace State

/-- The quantum mutual information of a `PUnit × PUnit` state is zero. -/
theorem mutualInformation_punit_punit_eq_zero
    (ρ : State (Prod PUnit.{u + 1} PUnit.{v + 1})) :
    QIT.mutualInformation ρ = 0 := by
  have hA : ρ.marginalA.vonNeumann = 0 := vonNeumann_punit_eq_zero ρ.marginalA
  have hB : ρ.marginalB.vonNeumann = 0 := vonNeumann_punit_eq_zero ρ.marginalB
  have hAB : ρ.vonNeumann = 0 := by
    exact le_antisymm (by simpa [log2] using vonNeumann_le_log_card ρ) (vonNeumann_nonneg ρ)
  simp [QIT.mutualInformation, hA, hB, hAB]

end State

end

end QIT
