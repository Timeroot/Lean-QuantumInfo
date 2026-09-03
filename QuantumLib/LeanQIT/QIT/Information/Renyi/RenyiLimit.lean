/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.Renyi
public import QIT.Information.BinaryHypothesisTest

/-!
# Petz--Renyi endpoint helpers

This module contains the small one-sided alpha-domain API used to state
source-shaped Petz--Renyi `alpha -> 1^-` limits.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology
open Filter

namespace QIT

universe u

noncomputable section

/-- The source order range for the barred Petz--Renyi branch, `0 < alpha < 1`. -/
def PetzRenyiAlpha : Type :=
  {alpha : ℝ // 0 < alpha ∧ alpha < 1}

namespace PetzRenyiAlpha

/-- The left endpoint filter `alpha -> 1^-` on the subtype `0 < alpha < 1`. -/
def leftToOne : Filter PetzRenyiAlpha :=
  Filter.comap (fun alpha : PetzRenyiAlpha => alpha.1)
    (nhdsWithin (1 : ℝ) (Set.Iio 1))

theorem val_pos (alpha : PetzRenyiAlpha) : 0 < alpha.1 :=
  alpha.2.1

theorem val_lt_one (alpha : PetzRenyiAlpha) : alpha.1 < 1 :=
  alpha.2.2

theorem val_ne_one (alpha : PetzRenyiAlpha) : alpha.1 ≠ 1 :=
  ne_of_lt alpha.val_lt_one

theorem one_sub_pos (alpha : PetzRenyiAlpha) : 0 < 1 - alpha.1 :=
  sub_pos.mpr alpha.val_lt_one

end PetzRenyiAlpha

namespace BinaryHypothesisTest

namespace ClassicalBinaryModel

variable {alpha : Type u} [Fintype alpha]

/-- The common-support partition has endpoint value one at `s = 1` when the
`p` distribution is supported by `q`. -/
theorem chernoffPartitionNNReal_one_of_p_supportedBy_q
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) :
    M.chernoffPartitionNNReal 1 = 1 := by
  classical
  have hfilter :
      (∑ x with M.p x ≠ 0, M.p x) = M.chernoffPartitionNNReal 1 := by
    unfold chernoffPartitionNNReal commonSupport
    exact Finset.sum_bij
      (fun x hx =>
        (⟨x, by
          have hx' : M.p x ≠ 0 := (Finset.mem_filter.mp hx).2
          exact ⟨hx', hpq x hx'⟩⟩ : M.commonSupport))
      (by
        intro x hx
        simp)
      (by
        intro x _ y _ hxy
        simpa using congrArg Subtype.val hxy)
      (by
        intro y _hy
        refine ⟨y.1, ?_, ?_⟩
        · simp [y.2.1]
        · rfl)
      (by
        intro x hx
        simp)
  have hfull_filter :
      (∑ x, M.p x) = ∑ x with M.p x ≠ 0, M.p x := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun x : alpha => M.p x ≠ 0) (f := fun x : alpha => M.p x)]
    have hzero : (∑ x with ¬ M.p x ≠ 0, M.p x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hx0 : M.p x = 0 := by
        simpa using (Finset.mem_filter.mp hx).2
      simp [hx0]
    rw [hzero, add_zero]
  calc
    M.chernoffPartitionNNReal 1 = ∑ x with M.p x ≠ 0, M.p x := hfilter.symm
    _ = ∑ x, M.p x := hfull_filter.symm
    _ = 1 := M.p_sum

/-- Real-valued endpoint form of `chernoffPartitionNNReal_one_of_p_supportedBy_q`. -/
theorem chernoffPartition_one_of_p_supportedBy_q
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) :
    M.chernoffPartition 1 = 1 := by
  have h := chernoffPartitionNNReal_one_of_p_supportedBy_q (M := M) hpq
  have hreal : ((M.chernoffPartitionNNReal 1 : ℝ) = 1) := by
    exact_mod_cast h
  simpa using hreal

/-- A nonzero `p` mass has the usual KL summand against `q` when `p` is
supported by `q`. -/
theorem relativeEntropySummandReal_pDistribution_qDistribution_of_p_ne_zero
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) {x : alpha}
    (hx : M.p x ≠ 0) :
    relativeEntropySummandReal M.pDistribution M.qDistribution x =
      (M.p x : ℝ) * (Real.log (M.p x : ℝ) - Real.log (M.q x : ℝ)) := by
  have hq : M.q x ≠ 0 := hpq x hx
  have hp_ne_real : (M.p x : ℝ) ≠ 0 := by exact_mod_cast hx
  have hq_ne_real : (M.q x : ℝ) ≠ 0 := by exact_mod_cast hq
  simp [relativeEntropySummandReal, pDistribution, qDistribution, hx,
    Real.log_div hp_ne_real hq_ne_real]

/-- The derivative of the common-support partition at `s = 1` is the
classical KL divergence `D(p || q)`. -/
theorem chernoffPartitionDeriv_one_eq_relativeEntropyReal_of_p_supportedBy_q
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) :
    M.chernoffPartitionDeriv 1 =
      relativeEntropyReal M.pDistribution M.qDistribution := by
  classical
  have hderiv_filter :
      (∑ x with M.p x ≠ 0,
        (M.p x : ℝ) * (Real.log (M.p x : ℝ) - Real.log (M.q x : ℝ))) =
        M.chernoffPartitionDeriv 1 := by
    unfold chernoffPartitionDeriv commonSupport
    exact Finset.sum_bij
      (fun x hx =>
        (⟨x, by
          have hx' : M.p x ≠ 0 := (Finset.mem_filter.mp hx).2
          exact ⟨hx', hpq x hx'⟩⟩ : M.commonSupport))
      (by
        intro x hx
        simp)
      (by
        intro x _ y _ hxy
        simpa using congrArg Subtype.val hxy)
      (by
        intro y _hy
        refine ⟨y.1, ?_, ?_⟩
        · simp [y.2.1]
        · rfl)
      (by
        intro x hx
        simp)
  have hrel_filter :
      relativeEntropyReal M.pDistribution M.qDistribution =
        ∑ x with M.p x ≠ 0,
          (M.p x : ℝ) * (Real.log (M.p x : ℝ) - Real.log (M.q x : ℝ)) := by
    unfold relativeEntropyReal
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun x : alpha => M.p x ≠ 0)
      (f := fun x : alpha =>
        relativeEntropySummandReal M.pDistribution M.qDistribution x)]
    have hzero :
        (∑ x with ¬ M.p x ≠ 0,
          relativeEntropySummandReal M.pDistribution M.qDistribution x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hx0 : M.p x = 0 := by
        simpa using (Finset.mem_filter.mp hx).2
      simp [relativeEntropySummandReal, pDistribution, hx0]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro x hxmem
    exact relativeEntropySummandReal_pDistribution_qDistribution_of_p_ne_zero
      (M := M) hpq (Finset.mem_filter.mp hxmem).2
  calc
    M.chernoffPartitionDeriv 1 =
        ∑ x with M.p x ≠ 0,
          (M.p x : ℝ) * (Real.log (M.p x : ℝ) - Real.log (M.q x : ℝ)) :=
      hderiv_filter.symm
    _ = relativeEntropyReal M.pDistribution M.qDistribution := hrel_filter.symm

/-- Natural-log slope form of the Petz/Chernoff partition limit at `s = 1`
from the left. -/
theorem chernoffLogPartition_slope_tendsto_relativeEntropyReal_left
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) :
    Tendsto
      (fun s : ℝ => Real.log (M.chernoffPartition s) / (s - 1))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (relativeEntropyReal M.pDistribution M.qDistribution)) := by
  have hZ1 : M.chernoffPartition 1 = 1 :=
    chernoffPartition_one_of_p_supportedBy_q (M := M) hpq
  have hderiv :
      HasDerivAt (fun s : ℝ => Real.log (M.chernoffPartition s))
        (relativeEntropyReal M.pDistribution M.qDistribution) 1 := by
    have hbase := M.hasDerivAt_chernoffPartition 1
    have hlog := hbase.log (by rw [hZ1]; norm_num)
    have hderiv_eq :
        M.chernoffPartitionDeriv 1 =
          relativeEntropyReal M.pDistribution M.qDistribution :=
      chernoffPartitionDeriv_one_eq_relativeEntropyReal_of_p_supportedBy_q
        (M := M) hpq
    simpa [hZ1, hderiv_eq] using hlog
  have htend :
      Tendsto (slope (fun s : ℝ => Real.log (M.chernoffPartition s)) 1)
        (nhdsWithin (1 : ℝ) ({1}ᶜ : Set ℝ))
        (nhds (relativeEntropyReal M.pDistribution M.qDistribution)) :=
    hderiv.tendsto_slope
  have hleft :
      Tendsto (slope (fun s : ℝ => Real.log (M.chernoffPartition s)) 1)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (relativeEntropyReal M.pDistribution M.qDistribution)) :=
    htend.mono_left (nhdsWithin_mono (1 : ℝ) (by
      intro s hs
      show s ≠ 1
      exact ne_of_lt hs))
  refine hleft.congr' ?_
  exact Eventually.of_forall fun s => by
    simp [slope, hZ1, div_eq_mul_inv, mul_comm]

/-- Base-2 slope form of the Petz/Chernoff partition limit at `s = 1` from
the left. -/
theorem petzChernoffLog2_tendsto_relativeEntropyReal_left
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) :
    Tendsto
      (fun s : ℝ => (1 / (s - 1)) * log2 (M.chernoffPartition s))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (relativeEntropyReal M.pDistribution M.qDistribution / Real.log 2)) := by
  have h :=
    chernoffLogPartition_slope_tendsto_relativeEntropyReal_left
      (M := M) hpq
  have hdiv := h.div_const (Real.log 2)
  refine hdiv.congr' ?_
  exact Eventually.of_forall fun s => by
    simp [log2, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- A `p`-supported binary model has nonempty common support. -/
theorem commonSupport_nonempty_of_p_supportedBy_q
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) :
    Nonempty M.commonSupport := by
  classical
  rcases ClassicalDistribution.exists_prob_ne_zero M.pDistribution with ⟨x, hx⟩
  exact ⟨⟨x, hx, hpq x hx⟩⟩

/-- In the source branch `0 < s < 1`, the common-support tilted distribution
dominates the original `p` distribution whenever `p` is supported by `q`. -/
theorem pDistribution_supportedBy_commonSupportTiltedDistribution
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) {s : ℝ}
    (_hs0 : 0 < s) (_hs1 : s < 1)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    M.pDistribution.SupportedBy
      (M.commonSupportTiltedDistribution s hZ).prob := by
  intro x hx
  have hq : M.q x ≠ 0 := hpq x hx
  have hxmem : M.p x ≠ 0 ∧ M.q x ≠ 0 := ⟨hx, hq⟩
  have hp_pos : 0 < M.p x := lt_of_le_of_ne (by positivity) (Ne.symm hx)
  have hq_pos : 0 < M.q x := lt_of_le_of_ne (by positivity) (Ne.symm hq)
  have hZ_pos : 0 < M.chernoffPartitionNNReal s :=
    lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hprob_pos :
      0 < (M.commonSupportTiltedDistribution s hZ).prob x := by
    rw [commonSupportTiltedDistribution_prob]
    simp [hxmem]
    positivity
  exact ne_of_gt hprob_pos

/-- Pointwise KL summand of `p` against the common-support tilted
distribution, in the `p ≠ 0` branch. -/
theorem relativeEntropySummandReal_p_commonSupportTilted_of_p_ne_zero
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) {s : ℝ}
    (_hs0 : 0 < s) (_hs1 : s < 1)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) {x : alpha}
    (hx : M.p x ≠ 0) :
    relativeEntropySummandReal
        M.pDistribution (M.commonSupportTiltedDistribution s hZ) x =
      (M.p x : ℝ) *
        ((1 - s) * (Real.log (M.p x : ℝ) - Real.log (M.q x : ℝ)) +
          Real.log (M.chernoffPartition s)) := by
  classical
  have hq : M.q x ≠ 0 := hpq x hx
  have hxmem : M.p x ≠ 0 ∧ M.q x ≠ 0 := ⟨hx, hq⟩
  have hp : 0 < (M.p x : ℝ) := by
    exact_mod_cast (lt_of_le_of_ne (by positivity) (Ne.symm hx))
  have hqpos : 0 < (M.q x : ℝ) := by
    exact_mod_cast (lt_of_le_of_ne (by positivity) (Ne.symm hq))
  have hZpos_nn : 0 < M.chernoffPartitionNNReal s :=
    lt_of_le_of_ne (by positivity) (Ne.symm hZ)
  have hZpos : 0 < M.chernoffPartition s := by
    rw [← chernoffPartitionNNReal_coe]
    exact_mod_cast hZpos_nn
  have ht :
      ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) =
        ((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
          M.chernoffPartition s :=
    commonSupportTiltedDistribution_prob_toReal_of_mem (M := M) (s := s) hZ hxmem
  have htpos :
      0 < ((M.commonSupportTiltedDistribution s hZ).prob x : ℝ) := by
    rw [ht]
    positivity
  have hdenom_pos :
      0 <
        ((M.p x : ℝ) ^ s) * ((M.q x : ℝ) ^ (1 - s)) /
          M.chernoffPartition s := by
    positivity
  rw [relativeEntropySummandReal]
  simp only [pDistribution]
  rw [if_neg hx]
  rw [ht]
  congr 1
  rw [Real.log_div hp.ne' hdenom_pos.ne']
  rw [Real.log_div
      (mul_ne_zero (Real.rpow_pos_of_pos hp s).ne'
        (Real.rpow_pos_of_pos hqpos (1 - s)).ne')
      hZpos.ne']
  rw [Real.log_mul (Real.rpow_pos_of_pos hp s).ne'
      (Real.rpow_pos_of_pos hqpos (1 - s)).ne']
  rw [Real.log_rpow hp, Real.log_rpow hqpos]
  ring

/-- KL from `p` to the common-support tilted distribution expands into the
source KL plus the log-partition term. -/
theorem relativeEntropyReal_p_commonSupportTilted
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hZ : M.chernoffPartitionNNReal s ≠ 0) :
    relativeEntropyReal
        M.pDistribution (M.commonSupportTiltedDistribution s hZ) =
      (1 - s) * relativeEntropyReal M.pDistribution M.qDistribution +
        Real.log (M.chernoffPartition s) := by
  classical
  have hterm :
      ∀ x : alpha,
        relativeEntropySummandReal
            M.pDistribution (M.commonSupportTiltedDistribution s hZ) x =
          (1 - s) *
              relativeEntropySummandReal M.pDistribution M.qDistribution x +
            (M.p x : ℝ) * Real.log (M.chernoffPartition s) := by
    intro x
    by_cases hx : M.p x = 0
    · simp [relativeEntropySummandReal, pDistribution, hx]
    · have htilt :=
        relativeEntropySummandReal_p_commonSupportTilted_of_p_ne_zero
          (M := M) hpq hs0 hs1 hZ (x := x) hx
      have hpqterm :=
        relativeEntropySummandReal_pDistribution_qDistribution_of_p_ne_zero
          (M := M) hpq (x := x) hx
      rw [htilt, hpqterm]
      ring
  unfold relativeEntropyReal
  calc
    (∑ x : alpha,
        relativeEntropySummandReal
          M.pDistribution (M.commonSupportTiltedDistribution s hZ) x)
        =
      ∑ x : alpha,
        ((1 - s) *
            relativeEntropySummandReal M.pDistribution M.qDistribution x +
          (M.p x : ℝ) * Real.log (M.chernoffPartition s)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact hterm x
    _ =
      (1 - s) * (∑ x : alpha,
          relativeEntropySummandReal M.pDistribution M.qDistribution x) +
        (∑ x : alpha, (M.p x : ℝ)) * Real.log (M.chernoffPartition s) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
        · rw [← Finset.sum_mul]
    _ =
      (1 - s) * (∑ x : alpha,
          relativeEntropySummandReal M.pDistribution M.qDistribution x) +
        Real.log (M.chernoffPartition s) := by
        have hp_sum : (∑ x : alpha, (M.p x : ℝ)) = 1 := by
          exact_mod_cast M.p_sum
        rw [hp_sum, one_mul]

/-- Classical Petz/Chernoff log-partition is bounded above by KL in the
source range `0 < s < 1`. -/
theorem petzChernoffLog2_le_relativeEntropyReal
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) :
    (1 / (s - 1)) * log2 (M.chernoffPartition s) ≤
      relativeEntropyReal M.pDistribution M.qDistribution / Real.log 2 := by
  classical
  let hZ : M.chernoffPartitionNNReal s ≠ 0 :=
    (chernoffPartitionNNReal_pos_of_commonSupport_nonempty
      (M := M) (commonSupport_nonempty_of_p_supportedBy_q (M := M) hpq) s).ne'
  have htilt_support :
      M.pDistribution.SupportedBy
        (M.commonSupportTiltedDistribution s hZ).prob :=
    pDistribution_supportedBy_commonSupportTiltedDistribution
      (M := M) hpq hs0 hs1 hZ
  have hnonneg :
      0 ≤ relativeEntropyReal
        M.pDistribution (M.commonSupportTiltedDistribution s hZ) :=
    relativeEntropyReal_nonneg _ _ htilt_support
  rw [relativeEntropyReal_p_commonSupportTilted
    (M := M) hpq hs0 hs1 hZ] at hnonneg
  have hden : 0 < 1 - s := sub_pos.mpr hs1
  have hlog_bound :
      -Real.log (M.chernoffPartition s) / (1 - s) ≤
        relativeEntropyReal M.pDistribution M.qDistribution := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hleft :
      (1 / (s - 1)) * log2 (M.chernoffPartition s) =
        (-Real.log (M.chernoffPartition s) / (1 - s)) / Real.log 2 := by
    have hsminus : s - 1 ≠ 0 := by linarith
    unfold log2
    field_simp [hsminus, hden.ne', hlog2_pos.ne']
    ring_nf
  rw [hleft]
  exact div_le_div_of_nonneg_right hlog_bound (le_of_lt hlog2_pos)

/-- Subtype-domain version of the base-2 Petz/Chernoff partition endpoint
limit. -/
theorem petzChernoffLog2_tendsto_relativeEntropyReal_subtype_left
    (M : ClassicalBinaryModel alpha)
    (hpq : M.pDistribution.SupportedBy M.q) :
    Tendsto
      (fun s : PetzRenyiAlpha =>
        (1 / (s.1 - 1)) * log2 (M.chernoffPartition s.1))
      PetzRenyiAlpha.leftToOne
      (nhds (relativeEntropyReal M.pDistribution M.qDistribution / Real.log 2)) := by
  have h :=
    petzChernoffLog2_tendsto_relativeEntropyReal_left (M := M) hpq
  have hval :
      Tendsto (fun s : PetzRenyiAlpha => s.1)
        PetzRenyiAlpha.leftToOne
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) := by
    simpa [PetzRenyiAlpha.leftToOne] using
      (Filter.tendsto_comap
        (f := fun s : PetzRenyiAlpha => s.1)
        (x := nhdsWithin (1 : ℝ) (Set.Iio 1)))
  exact h.comp hval

end ClassicalBinaryModel

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Matrix support domination lifts to support containment of the associated
Nussbaum--Szkola classical model. -/
theorem nussbaumSzkolaModel_p_supportedBy_q_of_matrix_support
    (rho sigma : State a)
    (hSupport : Matrix.Supports rho.matrix sigma.matrix) :
    (nussbaumSzkolaModel rho sigma).pDistribution.SupportedBy
      (nussbaumSzkolaModel rho sigma).q := by
  classical
  intro xy hp
  by_contra hq
  rcases xy with ⟨x, y⟩
  have hq_zero :
      (nussbaumSzkolaModel rho sigma).q (x, y) = 0 := by
    exact hq
  have hp_nonzero :
      (nussbaumSzkolaModel rho sigma).p (x, y) ≠ 0 := hp
  have hoverlap_or_sigma :
      stateSpectralWeight sigma y = 0 ∨
        nussbaumSzkolaOverlap rho sigma x y = 0 := by
    simpa [nussbaumSzkolaModel, mul_eq_zero] using hq_zero
  rcases hoverlap_or_sigma with hsigma_zero | hoverlap_zero
  · let Urho : Matrix.unitaryGroup a ℂ := rho.pos.isHermitian.eigenvectorUnitary
    let Usigma : Matrix.unitaryGroup a ℂ := sigma.pos.isHermitian.eigenvectorUnitary
    let T : CMatrix a := star (Urho : CMatrix a) * (Usigma : CMatrix a)
    have hsigma_eig : sigma.pos.isHermitian.eigenvalues y = 0 := by
      have hnn :
          (⟨sigma.pos.isHermitian.eigenvalues y,
            sigma.pos.eigenvalues_nonneg y⟩ : NNReal) = 0 := by
        change
          (⟨sigma.pos.isHermitian.eigenvalues y,
            sigma.pos.eigenvalues_nonneg y⟩ : NNReal) = 0 at hsigma_zero
        exact hsigma_zero
      simpa using congrArg Subtype.val hnn
    let v : a → ℂ := ⇑(sigma.pos.isHermitian.eigenvectorBasis y)
    have hsigma_v : sigma.matrix.mulVec v = 0 := by
      have h := sigma.pos.isHermitian.mulVec_eigenvectorBasis y
      rw [hsigma_eig] at h
      simpa [v] using h
    have hrho_v : rho.matrix.mulVec v = 0 := hSupport v hsigma_v
    have hcol : ∀ k, (rho.matrix * (Usigma : CMatrix a)) k y = 0 := by
      intro k
      have hk := congrFun hrho_v k
      simpa [v, Usigma, Matrix.mulVec, dotProduct, Matrix.mul_apply,
        Matrix.IsHermitian.eigenvectorUnitary_apply] using hk
    have hleft : (star (Urho : CMatrix a) * rho.matrix * (Usigma : CMatrix a)) x y = 0 := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, hcol]
    let Drho : CMatrix a :=
      Matrix.diagonal
        (fun i : a => ((rho.pos.isHermitian.eigenvalues i : ℝ) : ℂ))
    have hrho_diag :
        rho.matrix = (Urho : CMatrix a) * Drho * star (Urho : CMatrix a) := by
      simpa [Urho, Drho, Function.comp_def, Unitary.conjStarAlgAut_apply]
        using rho.pos.isHermitian.spectral_theorem
    have hleft_diag :
        (star (Urho : CMatrix a) * rho.matrix * (Usigma : CMatrix a)) x y =
          (((stateSpectralWeight rho x : ℝ) : ℂ) * T x y) := by
      have hmatrix :
          star (Urho : CMatrix a) * rho.matrix * (Usigma : CMatrix a) =
            Drho * T := by
        rw [hrho_diag]
        dsimp [Drho, T]
        calc
          star (Urho : CMatrix a) *
              ((Urho : CMatrix a) * Drho * star (Urho : CMatrix a)) *
                (Usigma : CMatrix a)
              =
                (star (Urho : CMatrix a) * (Urho : CMatrix a)) *
                  (Drho * (star (Urho : CMatrix a) * (Usigma : CMatrix a))) := by
                noncomm_ring
          _ =
                Drho * (star (Urho : CMatrix a) * (Usigma : CMatrix a)) := by
                rw [Unitary.coe_star_mul_self]
                simp
      have hentry := congrFun (congrFun hmatrix x) y
      simpa [Drho, T, Matrix.mul_apply, Matrix.diagonal, stateSpectralWeight] using hentry
    have hprod_zero :
        (((stateSpectralWeight rho x : ℝ) : ℂ) * T x y) = 0 := by
      rw [← hleft_diag]
      exact hleft
    have hp_zero :
        (nussbaumSzkolaModel rho sigma).p (x, y) = 0 := by
      rcases mul_eq_zero.mp hprod_zero with hweight | htransition
      · have hweight_real : (stateSpectralWeight rho x : ℝ) = 0 :=
          Complex.ofReal_eq_zero.mp hweight
        have hweight_nn : stateSpectralWeight rho x = 0 := by
          apply NNReal.eq
          simpa using hweight_real
        simp [nussbaumSzkolaModel, hweight_nn]
      · have hoverlap_nn : nussbaumSzkolaOverlap rho sigma x y = 0 := by
          have hT_entry :
              ((nussbaumSzkolaTransitionUnitary rho sigma : CMatrix a) x y) =
                T x y := by
            simp [nussbaumSzkolaTransitionUnitary, T, Urho, Usigma,
              Matrix.star_eq_conjTranspose]
          apply NNReal.eq
          change Complex.normSq
              ((nussbaumSzkolaTransitionUnitary rho sigma : CMatrix a) x y) = 0
          rw [hT_entry, htransition]
          simp [Complex.normSq]
        simp [nussbaumSzkolaModel, hoverlap_nn]
    exact hp_nonzero hp_zero
  · have hp_zero :
        (nussbaumSzkolaModel rho sigma).p (x, y) = 0 := by
      simp [nussbaumSzkolaModel, hoverlap_zero]
    exact hp_nonzero hp_zero

end BinaryHypothesisTest

namespace State

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- In the PSD branch `0 < alpha < 1`, the Petz--Renyi divergence is the
classical Nussbaum--Szkola log-partition with the repository's base-2
normalization. -/
theorem petzRenyiPSDFinite_eq_nussbaumSzkola_chernoffLog2
    (rho sigma : State a) {alpha : ℝ} (halpha0 : 0 < alpha)
    (halpha1 : alpha < 1) :
    rho.petzRenyiPSDFinite sigma alpha halpha0 (ne_of_lt halpha1) =
      (1 / (alpha - 1)) *
        log2 ((BinaryHypothesisTest.nussbaumSzkolaModel rho sigma).chernoffPartition alpha) := by
  classical
  let M := BinaryHypothesisTest.nussbaumSzkolaModel rho sigma
  have htrace :
      ((CFC.rpow rho.matrix alpha *
        CFC.rpow sigma.matrix (1 - alpha)).trace).re =
        (rho.petzRenyiCoefficient sigma alpha : ℝ) := by
    have h := State.petzRenyiCoefficient_trace_eq rho sigma alpha
    have hre := congrArg Complex.re h
    simpa using hre.symm
  have hpart :
      M.chernoffPartition alpha =
        (rho.petzRenyiCoefficient sigma alpha : ℝ) := by
    have hnn :
        M.chernoffPartitionNNReal alpha = M.petzChernoffCoefficient alpha :=
      BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_eq_petzChernoffCoefficient_of_mem_Ioo
        (M := M) halpha0 halpha1
    have hns :
        M.petzChernoffCoefficient alpha =
          rho.petzRenyiCoefficient sigma alpha :=
      BinaryHypothesisTest.nussbaumSzkolaModel_petzChernoffCoefficient_eq
        rho sigma (le_of_lt halpha0) (le_of_lt halpha1)
    calc
      M.chernoffPartition alpha =
          (M.chernoffPartitionNNReal alpha : ℝ) := by
            exact (BinaryHypothesisTest.ClassicalBinaryModel.chernoffPartitionNNReal_coe
              M alpha).symm
      _ = (M.petzChernoffCoefficient alpha : ℝ) := by rw [hnn]
      _ = (rho.petzRenyiCoefficient sigma alpha : ℝ) := by rw [hns]
  have hpart' :
      (BinaryHypothesisTest.nussbaumSzkolaModel rho sigma).chernoffPartition alpha =
        (rho.petzRenyiCoefficient sigma alpha : ℝ) := by
    simpa [M] using hpart
  unfold petzRenyiPSDFinite
  change
    (1 / (alpha - 1)) *
        log2 ((CFC.rpow rho.matrix alpha *
          CFC.rpow sigma.matrix (1 - alpha)).trace).re =
      (1 / (alpha - 1)) *
        log2 ((BinaryHypothesisTest.nussbaumSzkolaModel rho sigma).chernoffPartition alpha)
  rw [htrace, ← hpart']

/-- Canonical extended-real Petz divergence equals the finite
Nussbaum--Szkola log-partition whenever `rho` is supported on `sigma`. -/
theorem petzRenyiPSD_eq_nussbaumSzkola_chernoffLog2
    (rho sigma : State a) (hSupport : Matrix.Supports rho.matrix sigma.matrix)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    rho.petzRenyiPSD sigma alpha halpha0 halpha1 =
      (((1 / (alpha - 1)) *
        log2 ((BinaryHypothesisTest.nussbaumSzkolaModel rho sigma).chernoffPartition alpha) :
          ℝ) : EReal) := by
  rw [rho.petzRenyiPSD_eq_coe_finite_of_traceCoeff_pos]
  · exact_mod_cast
      petzRenyiPSDFinite_eq_nussbaumSzkola_chernoffLog2
        rho sigma halpha0 halpha1
  · exact rho.petzRenyiPSDTraceCoeff_pos_of_support sigma
      ((cMatrix_rpow_supports_self rho.pos halpha0).trans hSupport)

/-- The PSD Petz--Renyi divergence has the expected left endpoint limit when
the first state is supported on the second.  The endpoint is expressed through
the Nussbaum--Szkola classical relative entropy; later channel-level bridges
specialize this to entropy-form mutual information. -/
theorem petzRenyiPSDFinite_tendsto_nussbaumSzkola_relativeEntropyReal_left
    (rho sigma : State a)
    (hSupport : Matrix.Supports rho.matrix sigma.matrix) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        rho.petzRenyiPSDFinite sigma alpha.1 alpha.2.1 (ne_of_lt alpha.2.2))
      PetzRenyiAlpha.leftToOne
      (nhds
        (BinaryHypothesisTest.relativeEntropyReal
          (BinaryHypothesisTest.nussbaumSzkolaModel rho sigma).pDistribution
          (BinaryHypothesisTest.nussbaumSzkolaModel rho sigma).qDistribution /
            Real.log 2)) := by
  classical
  let M := BinaryHypothesisTest.nussbaumSzkolaModel rho sigma
  have hpq : M.pDistribution.SupportedBy M.q := by
    simpa [M] using
      BinaryHypothesisTest.nussbaumSzkolaModel_p_supportedBy_q_of_matrix_support
        rho sigma hSupport
  have hclassical :
      Tendsto
        (fun alpha : PetzRenyiAlpha =>
          (1 / (alpha.1 - 1)) * log2 (M.chernoffPartition alpha.1))
        PetzRenyiAlpha.leftToOne
        (nhds
          (BinaryHypothesisTest.relativeEntropyReal
            M.pDistribution M.qDistribution / Real.log 2)) :=
    BinaryHypothesisTest.ClassicalBinaryModel.petzChernoffLog2_tendsto_relativeEntropyReal_subtype_left
      (M := M) hpq
  refine hclassical.congr' ?_
  filter_upwards with alpha
  exact (by
    simpa [M] using
    (petzRenyiPSDFinite_eq_nussbaumSzkola_chernoffLog2
      (rho := rho) (sigma := sigma)
      (alpha := alpha.1) alpha.2.1 alpha.2.2).symm)

/-- Canonical extended-real PSD Petz divergence converges from the left to
the finite Umegaki endpoint under support inclusion. -/
theorem petzRenyiPSD_tendsto_nussbaumSzkola_relativeEntropyReal_left
    (rho sigma : State a)
    (hSupport : Matrix.Supports rho.matrix sigma.matrix) :
    Tendsto
      (fun alpha : PetzRenyiAlpha =>
        rho.petzRenyiPSD sigma alpha.1 alpha.2.1 alpha.2.2)
      PetzRenyiAlpha.leftToOne
      (nhds
        ((BinaryHypothesisTest.relativeEntropyReal
          (BinaryHypothesisTest.nussbaumSzkolaModel rho sigma).pDistribution
          (BinaryHypothesisTest.nussbaumSzkolaModel rho sigma).qDistribution /
            Real.log 2 : ℝ) : EReal)) := by
  refine (EReal.tendsto_coe.mpr
    (petzRenyiPSDFinite_tendsto_nussbaumSzkola_relativeEntropyReal_left
      rho sigma hSupport)).congr' ?_
  filter_upwards with alpha
  exact (rho.petzRenyiPSD_eq_coe_finite_of_traceCoeff_pos
    sigma alpha.1 alpha.2.1 alpha.2.2
      (rho.petzRenyiPSDTraceCoeff_pos_of_support sigma
        ((cMatrix_rpow_supports_self rho.pos alpha.2.1).trans hSupport))).symm

end State

end

end QIT
