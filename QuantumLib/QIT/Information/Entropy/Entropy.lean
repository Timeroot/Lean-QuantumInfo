/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.PosSqrt
public import QuantumLib.QIT.States.Purification.Gram
public import QuantumLib.QIT.States.TraceNorm.Distance
public import QuantumLib.QIT.States.Topology
public import QuantumLib.QIT.Util.MatrixInstances
public import QuantumInfo.Entropy.VonNeumann
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

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator QIT.MatrixL2

open Matrix

noncomputable section
universe u v w
variable {a : Type u} [Fintype a] [DecidableEq a]

open QIT

namespace QIT

/-- log base 2. -/
def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- x log_2 x with the 0 log 0 := 0 convention. -/
def xlog2 (x : ℝ) : ℝ := if x = 0 then 0 else x * log2 x

/-- The `x log₂ x` convention agrees with `x log x` after multiplying by
`Real.log 2`, including at `x = 0`. -/
theorem xlog2_mul_log2_self {x : ℝ} (hx : 0 ≤ x) :
    xlog2 x * Real.log 2 = x * Real.log x := by
  by_cases hzx : x = 0
  · simp [xlog2, hzx, Real.log_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    simp only [xlog2, if_neg hzx, log2]
    field_simp

/-- Binary entropy in bits, with the repository's `0 log 0 = 0` convention. -/
def binaryEntropy (ε : ℝ) : ℝ := -xlog2 ε - xlog2 (1 - ε)

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

/-- Subtracting from a base-2 logarithm splits off a multiplicative factor:
`2 ^ (log₂ x - h) = x * 2 ^ (-h)` for positive `x`. -/
theorem rpow_two_log2_sub {x h : ℝ} (hx : 0 < x) :
    Real.rpow 2 (log2 x - h) = x * Real.rpow 2 (-h) := by
  have hadd : Real.rpow 2 (log2 x + -h) = Real.rpow 2 (log2 x) * Real.rpow 2 (-h) :=
    Real.rpow_add (by norm_num : (0 : ℝ) < 2) (log2 x) (-h)
  rw [sub_eq_add_neg, hadd, rpow_two_log2_pos hx]

/-- `-log₂ q ≤ C` is the exponential lower bound `2 ^ (-C) ≤ q` on positive `q`. -/
theorem rpow_two_neg_le_of_neg_log2_le {q C : ℝ} (hq : 0 < q)
    (h : -log2 q ≤ C) :
    Real.rpow 2 (-C) ≤ q := by
  have hexp : -C ≤ log2 q := by linarith
  have hpow :=
    Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
      (by norm_num : (1 : ℝ) ≤ 2) hexp
  rw [← rpow_two_log2_pos hq]
  exact hpow

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

/-- `xlog2` is physlib's `Real.negMulLog`, negated and rescaled to base two. -/
theorem neg_xlog2_eq_negMulLog_div (t : ℝ) : -xlog2 t = Real.negMulLog t / Real.log 2 := by
  rw [xlog2]
  by_cases ht : t = 0
  · simp [ht]
  · rw [if_neg ht, log2, Real.negMulLog]
    ring

/-- Finite weighted Jensen inequality for the scalar function `x log x`. -/
theorem weighted_sum_mul_log_le_sum_weighted_mul_log
    {idx : Type*} [Fintype idx] (w x : idx → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    (∑ i, w i * x i) * Real.log (∑ i, w i * x i) ≤
      ∑ i, w i * (x i * Real.log (x i)) := by
  classical
  have hw_nonneg' : ∀ i ∈ (Finset.univ : Finset idx), 0 ≤ w i :=
    fun i _ => hw_nonneg i
  have hx_mem : ∀ i ∈ (Finset.univ : Finset idx), x i ∈ Set.Ici (0 : ℝ) :=
    fun i _ => hx_nonneg i
  have hjensen :=
    Real.convexOn_mul_log.map_sum_le
      (t := (Finset.univ : Finset idx)) (w := w) (p := x)
      hw_nonneg' (by simpa using hw_sum) hx_mem
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hjensen

/-- Base-two version of `weighted_sum_mul_log_le_sum_weighted_mul_log`. -/
theorem weighted_sum_mul_log2_le_sum_weighted_mul_log2
    {idx : Type*} [Fintype idx] (w x : idx → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    (∑ i, w i * x i) * log2 (∑ i, w i * x i) ≤
      ∑ i, w i * (x i * log2 (x i)) := by
  classical
  have hnat :=
    weighted_sum_mul_log_le_sum_weighted_mul_log w x hw_nonneg hw_sum hx_nonneg
  have hscale : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (Real.log_pos one_lt_two))
  have hscaled := mul_le_mul_of_nonneg_right hnat hscale
  simpa [log2, div_eq_mul_inv, Finset.mul_sum, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using hscaled

/-- Finite-dimensional vector-state Jensen inequality for a positive
semidefinite matrix.

Each diagonal entry in a Hermitian eigenbasis is a convex combination of the
eigenvalues, so scalar Jensen for `g x = x log x` transfers to the matrix. -/
theorem posSemidef_diagonal_re_mul_log_le_eigenvalue_weighted_mul_log
    {B : CMatrix a} (hB : B.PosSemidef) (i : a) :
    (B i i).re * Real.log (B i i).re ≤
      ∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
        (hB.isHermitian.eigenvalues j * Real.log (hB.isHermitian.eigenvalues j)) := by
  classical
  let w : a → ℝ := fun j =>
    Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j)
  let evals : a → ℝ := fun j => hB.isHermitian.eigenvalues j
  have hw_nonneg : ∀ j, 0 ≤ w j := fun j => Complex.normSq_nonneg _
  have hw_sum : ∑ j, w j = 1 := by
    simpa [w] using unitary_row_normSq_sum hB.isHermitian.eigenvectorUnitary i
  have hevals_nonneg : ∀ j, 0 ≤ evals j := fun j => hB.eigenvalues_nonneg j
  have hjensen :=
    weighted_sum_mul_log_le_sum_weighted_mul_log w evals hw_nonneg hw_sum hevals_nonneg
  have hdiag :
      (B i i).re = ∑ j, w j * evals j := by
    simpa [w, evals, mul_comm] using
      posSemidef_diagonal_re_eq_eigenvalue_weighted_sum hB i
  rw [hdiag]
  simpa [w, evals, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hjensen

/-- Base-two form of
`posSemidef_diagonal_re_mul_log_le_eigenvalue_weighted_mul_log`, rescaled by
the positive constant `1 / log 2`. -/
theorem posSemidef_diagonal_re_mul_log2_le_eigenvalue_weighted_mul_log2
    {B : CMatrix a} (hB : B.PosSemidef) (i : a) :
    (B i i).re * log2 (B i i).re ≤
      ∑ j, Complex.normSq ((hB.isHermitian.eigenvectorUnitary : CMatrix a) i j) *
        (hB.isHermitian.eigenvalues j * log2 (hB.isHermitian.eigenvalues j)) := by
  classical
  have hnat :=
    posSemidef_diagonal_re_mul_log_le_eigenvalue_weighted_mul_log (B := B) hB i
  have hscale : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (Real.log_pos one_lt_two))
  have hscaled := mul_le_mul_of_nonneg_right hnat hscale
  simpa [log2, div_eq_mul_inv, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using
    hscaled

end QIT

namespace MState

open Set

/-- Von Neumann entropy S(ρ) = -Σ λᵢ log₂ λᵢ over the eigenvalues of ρ,
with 0 log 0 := 0. -/
def vonNeumann (ρ : MState a) : ℝ :=
  -(Finset.univ.sum fun i => xlog2 ((ρ.psd.isHermitian).eigenvalues i))

/-- The von Neumann entropy, rewritten as a multiset sum over the
eigenvalue multiset: `S(ρ) = -∑_{λ ∈ spec(ρ)} xlog2 λ`. -/
lemma vonNeumann_eq_neg_sum_eigenvalueMultiset (ρ : MState a) :
    vonNeumann ρ = -((eigenvalueMultiset ρ.psd.isHermitian).map xlog2).sum := by
  show -(Finset.univ.sum fun i => xlog2 (ρ.psd.isHermitian.eigenvalues i)) = _
  rw [eigenvalueMultiset, Finset.sum_eq_multiset_sum, Multiset.map_map]
  rfl

private theorem eigenvalues_congr {M N : CMatrix a} (hM : M.IsHermitian) (hN : N.IsHermitian)
    (h : M = N) : hM.eigenvalues = hN.eigenvalues := by
  subst h
  rfl

/-- Both libraries take the eigenvalues of the same matrix. -/
theorem eigenvalues_M (ρ : MState a) :
    ρ.M.H.eigenvalues = ρ.psd.isHermitian.eigenvalues :=
  eigenvalues_congr _ _ (DensityOp.mat_M ρ)

theorem coe_spectrum (ρ : MState a) (i : a) :
    (ρ.spectrum i : ℝ) = ρ.psd.isHermitian.eigenvalues i :=
  congrFun (eigenvalues_M ρ) i

/-- physlib's von Neumann entropy, as the eigenvalue sum that `vonNeumann` starts from. -/
theorem Sᵥₙ_eq_sum_negMulLog (ρ : MState a) :
    Sᵥₙ ρ = ∑ i, Real.negMulLog (ρ.psd.isHermitian.eigenvalues i) := by
  rw [Sᵥₙ_eq_Hₛ_spectrum, Hₛ]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg Real.negMulLog (coe_spectrum ρ i)

/-- `vonNeumann` is measured in bits and physlib's `Sᵥₙ` in nats. -/
theorem vonNeumann_eq_Sᵥₙ_div_log_two (ρ : MState a) :
    ρ.vonNeumann = Sᵥₙ ρ / Real.log 2 := by
  rw [vonNeumann, Sᵥₙ_eq_sum_negMulLog, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => neg_xlog2_eq_negMulLog_div _

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

private theorem vonNeumann_eq_cfc_trace (ρ : MState a) :
    ρ.vonNeumann = ((cfc entropyCfcComplex ρ.m).trace).re := by
  rw [MState.vonNeumann]
  have hreal :
      cfc entropyCfcScalar ρ.m = cfc entropyCfcComplex ρ.m :=
    cfc_real_eq_complex (a := ρ.m) entropyCfcScalar
      (ha := ρ.psd.isHermitian.isSelfAdjoint)
  rw [← hreal]
  have hcfc :
      cfc entropyCfcScalar ρ.m =
        ρ.psd.isHermitian.cfc entropyCfcScalar :=
    Matrix.IsHermitian.cfc_eq (𝕜 := ℂ) ρ.psd.isHermitian entropyCfcScalar
  rw [hcfc]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  rw [Matrix.trace_diagonal]
  simp only [Function.comp_apply, entropyCfcScalar_eq_neg_xlog2]
  simp [Finset.sum_neg_distrib]

/-- Eigenvalues of a state are bounded above by one. -/
private lemma eigenvalue_le_one (ρ : MState a) (i : a) :
    ρ.psd.isHermitian.eigenvalues i ≤ 1 := by
  have hnonneg (j : a) : 0 ≤ ρ.psd.isHermitian.eigenvalues j :=
    ρ.psd.eigenvalues_nonneg j
  have hsum : ∑ j, ρ.psd.isHermitian.eigenvalues j = 1 :=
    ρ.sum_eigenvalues_eq_one
  calc ρ.psd.isHermitian.eigenvalues i
      ≤ ρ.psd.isHermitian.eigenvalues i
        + ∑ j ∈ Finset.univ.erase i, ρ.psd.isHermitian.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
    _ = ∑ j, ρ.psd.isHermitian.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => ρ.psd.isHermitian.eigenvalues j) (Finset.mem_univ i)
    _ = 1 := hsum

private theorem spectrum_subset_stateInterval (ρ : MState a) :
    _root_.spectrum ℂ ρ.m ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
  intro z hz
  rw [ρ.psd.isHermitian.spectrum_eq_image_range] at hz
  rcases hz with ⟨x, ⟨i, rfl⟩, rfl⟩
  exact ⟨ρ.psd.isHermitian.eigenvalues i,
    ⟨ρ.psd.eigenvalues_nonneg i, eigenvalue_le_one ρ i⟩, rfl⟩

/-- Von Neumann entropy is continuous on finite-dimensional density states. -/
theorem vonNeumann_continuous : Continuous (fun ρ : MState a => ρ.vonNeumann) := by
  let K : Set ℂ := Complex.ofReal '' Set.Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    CompactIccSpace.isCompact_Icc.image Complex.continuous_ofReal
  have hcfc : Continuous fun ρ : MState a =>
      (cfc entropyCfcComplex (ρ.m : Matrix a a ℂ) : Matrix a a ℂ) := by
    exact Continuous.cfc' (A := Matrix a a ℂ) (p := IsStarNormal)
      (s := K) hK entropyCfcComplex MState.continuous_matrix
      (fun ρ => spectrum_subset_stateInterval ρ)
      (continuous_entropyCfcComplex.continuousOn)
      (fun ρ => ρ.psd.isHermitian.isSelfAdjoint.isStarNormal)
  have htrace : Continuous fun ρ : MState a =>
      ((cfc entropyCfcComplex ρ.m).trace).re :=
    Complex.continuous_re.comp (Continuous.matrix_trace hcfc)
  exact htrace.congr fun ρ => (vonNeumann_eq_cfc_trace ρ).symm

/-- Von Neumann entropy is nonnegative: S(rho) ≥ 0. -/
theorem vonNeumann_nonneg (ρ : MState a) : 0 ≤ vonNeumann ρ := by
  rw [vonNeumann_eq_Sᵥₙ_div_log_two]
  exact div_nonneg (Sᵥₙ_nonneg _) (Real.log_nonneg one_le_two)

/-- Von Neumann entropy is bounded by log2(dim).

S(rho) ≤ log2(Fintype.card a).
-/
theorem vonNeumann_le_log_card (ρ : MState a) :
    vonNeumann ρ ≤ log2 (Fintype.card a) := by
  have h : Sᵥₙ ρ ≤ Real.log (Fintype.card a) := by
    simpa [Finset.card_univ] using Sᵥₙ_le_log_d ρ
  rw [vonNeumann_eq_Sᵥₙ_div_log_two, log2]
  exact div_le_div_of_nonneg_right h (Real.log_nonneg one_le_two)

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
def relativeEntropyPosDefFinite (ρ σ : MState a)
    (hρ : ρ.m.PosDef) (hσ : σ.m.PosDef) : ℝ :=
  ((ρ.m * psdLog ρ.m hρ).trace.re
    - (ρ.m * psdLog σ.m hσ).trace.re) / Real.log 2

/-- The matrix-log trace expression for a positive-definite state expands to
the spectral `λ log λ` sum. -/
theorem trace_mul_psdLog_eq_sum_eigenvalues_mul_log
    (ρ : MState a) (hρ : ρ.m.PosDef) :
    ((ρ.m * psdLog ρ.m hρ).trace).re =
      ∑ i, hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i) := by
  classical
  let U : Matrix.unitaryGroup a ℂ := hρ.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ)
  let L : CMatrix a := Matrix.diagonal fun i => ((Real.log (hρ.1.eigenvalues i) : ℝ) : ℂ)
  have hmat : ρ.m = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Function.comp_def, Matrix.IsHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply] using hρ.1.spectral_theorem
  have hlog : psdLog ρ.m hρ = (U : CMatrix a) * L * star (U : CMatrix a) := by
    rw [psdLog, hρ.1.cfc_eq]
    simp [U, L, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def]
  calc
    ((ρ.m * psdLog ρ.m hρ).trace).re =
        ((ρ.m * ((U : CMatrix a) * L * star (U : CMatrix a))).trace).re := by
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
    (ρ : MState a) (hρ : ρ.m.PosDef) :
    ρ.vonNeumann =
      -((ρ.m * psdLog ρ.m hρ).trace.re) / Real.log 2 := by
  classical
  have htrace := trace_mul_psdLog_eq_sum_eigenvalues_mul_log ρ hρ
  have hHerm : hρ.1 = ρ.psd.isHermitian := Subsingleton.elim _ _
  have hxlog (i : a) :
      xlog2 (ρ.psd.isHermitian.eigenvalues i) =
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
def conditionalEntropy (ρ : MState (a × b)) : ℝ :=
  vonNeumann ρ - vonNeumann ρ.traceLeft

@[simp]
theorem conditionalEntropy_eq (ρ : MState (a × b)) :
    ρ.conditionalEntropy = vonNeumann ρ - vonNeumann ρ.traceLeft := rfl

/-- Conditional entropy is continuous on finite-dimensional bipartite states. -/
theorem conditionalEntropy_continuous :
    Continuous (fun ρ : MState (a × b) => ρ.conditionalEntropy) := by
  unfold conditionalEntropy
  exact MState.vonNeumann_continuous.sub
    (MState.vonNeumann_continuous.comp MState.traceLeft_continuous)

variable {c : Type w} [Fintype c] [DecidableEq c]

/-- Conditional mutual information
`I(A:C|B)_ρ = H(AB)_ρ + H(BC)_ρ - H(B)_ρ - H(ABC)_ρ`
for a left-associated tripartite state `ρ : MState ((A × B) × C)`. -/
def condMutualInfo (ρ : MState ((a × b) × c)) : ℝ :=
  vonNeumann ρ.marginalAB + vonNeumann ρ.marginalBC
    - vonNeumann ρ.marginalBOfABC - vonNeumann ρ

@[simp]
theorem condMutualInfo_eq (ρ : MState ((a × b) × c)) :
    ρ.condMutualInfo =
      vonNeumann ρ.marginalAB + vonNeumann ρ.marginalBC
        - vonNeumann ρ.marginalBOfABC - vonNeumann ρ := rfl

/-- Complementary marginals of a finite-dimensional pure bipartite state have
the same von Neumann entropy. -/
theorem ket_traceRight_vonNeumann_eq_traceLeft
    {r : Type u} {α : Type v} [Fintype r] [DecidableEq r] [Fintype α] [DecidableEq α]
    (Ψ : Ket (r × α)) :
    Ψ.state.traceRight.vonNeumann = Ψ.state.traceLeft.vonNeumann := by
  rw [vonNeumann_eq_Sᵥₙ_div_log_two, vonNeumann_eq_Sᵥₙ_div_log_two, Ket.state_eq_pure,
    Sᵥₙ_of_partial_eq]

/-- The von Neumann entropy of a one-dimensional (`PUnit`) state is zero. -/
theorem vonNeumann_punit_eq_zero (ρ : MState PUnit.{u + 1}) :
    ρ.vonNeumann = 0 := by
  exact le_antisymm (by simpa [log2] using vonNeumann_le_log_card ρ) (vonNeumann_nonneg ρ)

end MState

namespace QIT

open Set

/-- Quantum mutual information I(X;B) of a bipartite state. -/
def mutualInformation {ι : Type u} {α : Type v} [Fintype ι] [Fintype α]
    [DecidableEq α] [DecidableEq ι] (ρ : MState (ι × α)) : ℝ :=
  MState.vonNeumann ρ.traceRight + MState.vonNeumann ρ.traceLeft
    - MState.vonNeumann ρ

end QIT

namespace MState

open Set

/-- The quantum mutual information of a `PUnit × PUnit` state is zero. -/
theorem mutualInformation_punit_punit_eq_zero
    (ρ : MState (PUnit.{u + 1} × PUnit.{v + 1})) :
    QIT.mutualInformation ρ = 0 := by
  have hA : ρ.traceRight.vonNeumann = 0 := vonNeumann_punit_eq_zero ρ.traceRight
  have hB : ρ.traceLeft.vonNeumann = 0 := vonNeumann_punit_eq_zero ρ.traceLeft
  have hAB : ρ.vonNeumann = 0 := by
    exact le_antisymm (by simpa [log2] using vonNeumann_le_log_card ρ) (vonNeumann_nonneg ρ)
  simp [QIT.mutualInformation, hA, hB, hAB]

end MState

namespace QIT

open Set

end QIT
