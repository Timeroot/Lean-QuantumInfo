/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.SandwichedRenyiMonotonicity
public import QIT.States.TraceNorm.Spectral
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Optimized sandwiched Renyi upper semicontinuity support

This module isolates the full-rank approximation route for optimized
sandwiched Renyi mutual information.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Topology
open Filter

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Positive definiteness is eventually preserved along PSD-constrained
matrix paths converging to a positive-definite limit. -/
theorem eventually_posDef_of_tendsto_posDef
    {X : Type*} {l : Filter X} {M : X -> CMatrix a} {A : CMatrix a}
    (hM : Tendsto M l (nhds A))
    (hMpsd : Filter.Eventually (fun x => (M x).PosSemidef) l)
    (hA : A.PosDef) :
    Filter.Eventually (fun x => (M x).PosDef) l := by
  have hdet_ne : A.det ≠ 0 :=
    hA.posSemidef.posDef_iff_det_ne_zero.mp hA
  have hdet :
      Tendsto (fun x : X => (M x).det) l (nhds A.det) :=
    continuous_id.matrix_det.tendsto A |>.comp hM
  have hevent_det : Filter.Eventually (fun x : X => (M x).det ≠ 0) l :=
    hdet.eventually (isOpen_ne.mem_nhds hdet_ne)
  filter_upwards [hMpsd, hevent_det] with x hxpsd hxdet
  exact hxpsd.posDef_iff_det_ne_zero.mpr hxdet

/-- Kronecker products commute with `CFC.rpow` for positive semidefinite matrices
and arbitrary real exponents.

This removes the `0 ≤ s` restriction of `cMatrix_rpow_kronecker_nonneg` (and the
positive-definiteness restriction of `cMatrix_rpow_kronecker_posDef`): the
finite-spectrum polynomial-interpolation identity
`cMatrix_rpow_unitary_conj_diagonal_ofReal` computes the conjugation step for
every real exponent, including the negative powers `s = (1 - α) / (2 α) < 0`
that drive the high-`α` sandwiched Rényi inner operator at a singular product
reference. -/
theorem cMatrix_rpow_kronecker_psd
    {A : CMatrix a} {B : CMatrix b} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s : ℝ) :
    CFC.rpow (Matrix.kronecker A B) s =
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) := by
  let UA : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ := hB.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
      Matrix.kronecker_mem_unitary UA.2 UB.2⟩
  let da : a → ℝ := hA.isHermitian.eigenvalues
  let db : b → ℝ := hB.isHermitian.eigenvalues
  let dprod : Prod a b → ℝ := fun i => da i.1 * db i.2
  have hda : ∀ i, 0 ≤ da i := fun i => hA.eigenvalues_nonneg i
  have hdb : ∀ i, 0 ≤ db i := fun i => hB.eigenvalues_nonneg i
  have hdprod : ∀ i, 0 ≤ dprod i := fun i => mul_nonneg (hda i.1) (hdb i.2)
  have hA_spec :
      A = (UA : CMatrix a) * Matrix.diagonal (fun i => (da i : ℂ)) *
        star (UA : CMatrix a) := by
    simpa [UA, da, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hB_spec :
      B = (UB : CMatrix b) * Matrix.diagonal (fun i => (db i : ℂ)) *
        star (UB : CMatrix b) := by
    simpa [UB, db, Function.comp_def] using hB.isHermitian.spectral_theorem
  have hAB_spec :
      Matrix.kronecker A B =
        (U : CMatrix (Prod a b)) *
          Matrix.diagonal (fun i => (dprod i : ℂ)) *
          star (U : CMatrix (Prod a b)) := by
    rw [hA_spec, hB_spec]
    simp [U, dprod, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
      Matrix.mul_assoc]
  have hleft :
      CFC.rpow (Matrix.kronecker A B) s =
        (U : CMatrix (Prod a b)) *
          Matrix.diagonal (fun i => ((dprod i ^ s : ℝ) : ℂ)) *
          star (U : CMatrix (Prod a b)) := by
    rw [hAB_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U dprod hdprod s
  have hdiag :
      (Matrix.diagonal fun i : Prod a b => ((dprod i ^ s : ℝ) : ℂ)) =
        (Matrix.diagonal fun i : Prod a b =>
          (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [dprod, Real.mul_rpow (hda i.1) (hdb i.2)]
    · simp [hij]
  have hA_rpow :
      CFC.rpow A s =
        (UA : CMatrix a) *
          (Matrix.diagonal fun i => ((da i ^ s : ℝ) : ℂ)) *
          star (UA : CMatrix a) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal UA da hda s
  have hB_rpow :
      CFC.rpow B s =
        (UB : CMatrix b) *
          (Matrix.diagonal fun i => ((db i ^ s : ℝ) : ℂ)) *
          star (UB : CMatrix b) := by
    rw [hB_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal UB db hdb s
  have hright :
      Matrix.kronecker (CFC.rpow A s) (CFC.rpow B s) =
        (U : CMatrix (Prod a b)) *
          (Matrix.diagonal fun i : Prod a b =>
            (((da i.1 ^ s) * (db i.2 ^ s) : ℝ) : ℂ)) *
          star (U : CMatrix (Prod a b)) := by
    rw [hA_rpow, hB_rpow]
    simp [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
      Matrix.mul_assoc]
  rw [hleft, hdiag, hright]

/-- Real powers of a positive semidefinite matrix obey the exponent law
`A^p * A^q = A^(p + q)` whenever `p + q ≠ 0`.

Unlike `CFC.rpow_add` (which needs `A.IsUnit`, i.e. `A.PosDef`), this variant
covers singular positive semidefinite matrices via finite-spectrum polynomial
interpolation; it is the bookkeeping needed to combine the marginal factor
`A_x` with its negative powers `A_x^s` along a singular-marginal limit. -/
theorem cMatrix_rpow_add_psd {A : CMatrix a} (hA : A.PosSemidef) {p q : ℝ}
    (hpq : p + q ≠ 0) :
    CFC.rpow A p * CFC.rpow A q = CFC.rpow A (p + q) := by
  let U : Matrix.unitaryGroup a ℂ := hA.isHermitian.eigenvectorUnitary
  let d : a → ℝ := hA.isHermitian.eigenvalues
  have hd : ∀ i, 0 ≤ d i := fun i => hA.eigenvalues_nonneg i
  have hA_spec :
      A = (U : CMatrix a) *
        (Matrix.diagonal fun i => (d i : ℂ)) *
        star (U : CMatrix a) := by
    simpa [U, d, Function.comp_def] using hA.isHermitian.spectral_theorem
  have hDp :
      CFC.rpow A p =
        (U : CMatrix a) *
          (Matrix.diagonal fun i => ((d i ^ p : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U d hd p
  have hDq :
      CFC.rpow A q =
        (U : CMatrix a) *
          (Matrix.diagonal fun i => ((d i ^ q : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U d hd q
  have hDpq :
      CFC.rpow A (p + q) =
        (U : CMatrix a) *
          (Matrix.diagonal fun i => ((d i ^ (p + q) : ℝ) : ℂ)) *
          star (U : CMatrix a) := by
    rw [hA_spec]
    exact cMatrix_rpow_unitary_conj_diagonal_ofReal U d hd (p + q)
  have hconjConj (M : CMatrix a) :
      (U : CMatrix a) * M * star (U : CMatrix a) =
        (Unitary.conjStarAlgAut ℂ (CMatrix a) U) M := by
    simp [Unitary.conjStarAlgAut_apply]
  have hDiagMul :
      (Matrix.diagonal fun i => ((d i ^ p : ℝ) : ℂ) : CMatrix a) *
        (Matrix.diagonal fun i => ((d i ^ q : ℝ) : ℂ)) =
        (Matrix.diagonal fun i => ((d i ^ (p + q) : ℝ) : ℂ) : CMatrix a) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Real.rpow_add' (hd i) hpq]
    · simp [hij]
  rw [hDp, hDq, hDpq, hconjConj, hconjConj, hconjConj, ← map_mul, hDiagMul]

omit [DecidableEq a] in
/-- Trace pairing against a right identity Kronecker factor reduces to the
partial trace over the right subsystem.

This is the public form of the (otherwise `private`)
`partialTraceB_mul_trace_eq_trace_mul_kronecker_one_left`, needed to relate the
off-support mass of a bipartite state `ρ` to its left marginal. -/
theorem trace_mul_kronecker_one_right_eq_partialTraceB
    (X : CMatrix (Prod a b)) (U : CMatrix a) :
    (X * Matrix.kronecker U (1 : CMatrix b)).trace =
      (partialTraceB (a := a) (b := b) X * U).trace := by
  have h1 :
      partialTraceB (a := a) (b := b) (X * Matrix.kronecker U (1 : CMatrix b)) =
        partialTraceB (a := a) (b := b) X * U := by
    ext i i'
    simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [← h1, partialTraceB_trace]

/-- The PSD power trace is invariant between `B B*` and `B* B`.

This is the trace-similarity identity `Tr[(B B*)^p] = Tr[(B* B)^p]` for `p > 0`,
the cyclic handoff that lets the high-`α` sandwiched Rényi trace
`Tr[(σ^s ρ σ^s)^α]` be rewritten as `Tr[(ρ^{1/2} σ^{2s} ρ^{1/2})^α]` (set
`B = σ^s ρ^{1/2}`, using that `σ^s` and `ρ^{1/2}` are Hermitian). It is the
trace-only-cancellation primitive behind the singular-marginal USC route: the
rewritten matrix `ρ^{1/2} σ^{2s} ρ^{1/2}` exposes the partial-trace mass-vs-power
cancellation directly. Specialized via `cMatrix_rpow_kronecker_psd`, this is the
on-support/off-support split that replaces the withdrawn Davis–Kahan reduction. -/
theorem psdTracePower_mul_conjTranspose_eq
    {n : Type*} [Fintype n] [DecidableEq n] (B : CMatrix n) {p : ℝ} (hp : 0 < p) :
    psdTracePower (B * B.conjTranspose)
      (by simpa [Matrix.mul_one] using
        Matrix.PosSemidef.mul_mul_conjTranspose_same Matrix.PosSemidef.one B) p =
      psdTracePower (B.conjTranspose * B)
        (by simpa [Matrix.mul_one] using
          Matrix.PosSemidef.conjTranspose_mul_mul_same Matrix.PosSemidef.one B) p := by
  exact psdTracePower_mul_comm
    (by simpa [Matrix.mul_one] using
      Matrix.PosSemidef.mul_mul_conjTranspose_same Matrix.PosSemidef.one B)
    (by simpa [Matrix.mul_one] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same Matrix.PosSemidef.one B) hp

/-- The high-`α` sandwiched-Renyi trace `Tr[(σ^s ρ σ^s)^α]` equals the congruence
trace `Tr[(ρ^{1/2} σ^{2s} ρ^{1/2})^α]` for PSD `ρ, σ`, `s ≠ 0`, `0 < α`.

This is stated at the raw trace level (no `PosSemidef` witness arguments) so the
identity can be `rw`-driven at use sites without proof-irrelevance friction.
Setting `B = σ^s ρ^{1/2}` in `psdTracePower_mul_conjTranspose_eq` rewrites the
inner `σ^s ρ σ^s = B B*` as the congruence `ρ^{1/2} σ^{2s} ρ^{1/2} = B* B`, using
the PSD exponent laws `ρ^{1/2} ρ^{1/2} = ρ` and `σ^s σ^s = σ^{2s}` (the latter
needs `s ≠ 0`). The congruence form exposes the `A_x^{2s}` Kronecker factor and
the `ρ_x^{1/2}` sandwich that tames its small-eigenvalue blow-up along a
singular-marginal limit; it is the trace-similarity handoff behind the A2
cancellation route. -/
theorem sandwichedRenyiInner_trace_re_congruence
    {ρ σ : CMatrix a} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {s α : ℝ} (hs_ne : s ≠ 0) (hα_pos : 0 < α) :
    (CFC.rpow (CFC.rpow σ s * ρ * CFC.rpow σ s) α).trace.re =
      (CFC.rpow (CFC.rpow ρ (1 / 2) * CFC.rpow σ (2 * s) * CFC.rpow ρ (1 / 2)) α).trace.re := by
  have hρ_half_half : CFC.rpow ρ (1 / 2) * CFC.rpow ρ (1 / 2) = ρ := by
    have hlaw : CFC.rpow ρ (1 / 2) * CFC.rpow ρ (1 / 2) = CFC.rpow ρ (1 / 2 + 1 / 2) :=
      cMatrix_rpow_add_psd hρ (by norm_num)
    rw [hlaw, show (1 / 2 + 1 / 2 : ℝ) = 1 from by norm_num]
    exact CFC.rpow_one ρ (ha := Matrix.nonneg_iff_posSemidef.mpr hρ)
  have hσ_s_s : CFC.rpow σ s * CFC.rpow σ s = CFC.rpow σ (2 * s) := by
    have hss_ne : s + s ≠ 0 := fun h => hs_ne (by linarith)
    have hlaw : CFC.rpow σ s * CFC.rpow σ s = CFC.rpow σ (s + s) :=
      cMatrix_rpow_add_psd hσ hss_ne
    rw [hlaw, show (s + s : ℝ) = 2 * s from by ring]
  have hLHS_eq : CFC.rpow σ s * ρ * CFC.rpow σ s =
      (CFC.rpow σ s * CFC.rpow ρ (1 / 2)) * (CFC.rpow ρ (1 / 2) * CFC.rpow σ s) := by
    symm
    calc (CFC.rpow σ s * CFC.rpow ρ (1 / 2)) * (CFC.rpow ρ (1 / 2) * CFC.rpow σ s)
        = CFC.rpow σ s * (CFC.rpow ρ (1 / 2) * CFC.rpow ρ (1 / 2)) * CFC.rpow σ s := by ac_rfl
      _ = CFC.rpow σ s * ρ * CFC.rpow σ s := by rw [hρ_half_half]
  have hRHS_eq : CFC.rpow ρ (1 / 2) * CFC.rpow σ (2 * s) * CFC.rpow ρ (1 / 2) =
      (CFC.rpow ρ (1 / 2) * CFC.rpow σ s) * (CFC.rpow σ s * CFC.rpow ρ (1 / 2)) := by
    symm
    calc (CFC.rpow ρ (1 / 2) * CFC.rpow σ s) * (CFC.rpow σ s * CFC.rpow ρ (1 / 2))
        = CFC.rpow ρ (1 / 2) * (CFC.rpow σ s * CFC.rpow σ s) * CFC.rpow ρ (1 / 2) := by ac_rfl
      _ = CFC.rpow ρ (1 / 2) * CFC.rpow σ (2 * s) * CFC.rpow ρ (1 / 2) := by rw [hσ_s_s]
  have hAB : ((CFC.rpow σ s * CFC.rpow ρ (1 / 2)) * (CFC.rpow ρ (1 / 2) * CFC.rpow σ s)).PosSemidef
      := by
    rw [← hLHS_eq]
    have hCs_herm : (CFC.rpow σ s).conjTranspose = CFC.rpow σ s :=
      (cMatrix_rpow_posSemidef hσ).isHermitian.eq
    have hpre := Matrix.PosSemidef.conjTranspose_mul_mul_same hρ (CFC.rpow σ s)
    rwa [hCs_herm] at hpre
  have hBA : ((CFC.rpow ρ (1 / 2) * CFC.rpow σ s) * (CFC.rpow σ s * CFC.rpow ρ (1 / 2))).PosSemidef
      := by
    rw [← hRHS_eq]
    have hCs2 : (CFC.rpow σ (2 * s)).PosSemidef := cMatrix_rpow_posSemidef hσ
    have hCr_herm : (CFC.rpow ρ (1 / 2)).conjTranspose = CFC.rpow ρ (1 / 2) :=
      (cMatrix_rpow_posSemidef hρ).isHermitian.eq
    have hpre := Matrix.PosSemidef.conjTranspose_mul_mul_same hCs2 (CFC.rpow ρ (1 / 2))
    rwa [hCr_herm] at hpre
  rw [hLHS_eq, hRHS_eq]
  exact psdTracePower_mul_comm hAB hBA hα_pos

/-- Trace of a Kronecker-PSD product against a PSD matrix is bounded by the
right-factor trace times the partial-trace pairing.

For PSD `A, B, ρ`: `Tr[(A ⊗ B) ρ] ≤ B.trace.re · Tr[A · partialTraceB ρ]`.
The bound follows from `posSemidef_le_trace_re_smul_one` (`B ≤ B.trace.re · I`),
Kronecker order preservation, and the non-negativity
`Tr[(PSD ⊗ PSD) · PSD] ≥ 0` (`trace_mul_posSemidef_re_nonneg`). This is the
partial-trace / mass-cancellation primitive behind the off-support op-norm
bound for the sandwiched Rényi inner operator at a singular product reference. -/
theorem posSemidef_trace_mul_kronecker_le_partialTrace
    {ρ : CMatrix (Prod a b)} (hρ : ρ.PosSemidef)
    {A : CMatrix a} (hA : A.PosSemidef) {B : CMatrix b} (hB : B.PosSemidef) :
    ((Matrix.kronecker A B * ρ).trace).re ≤
      B.trace.re * (A * partialTraceB (a := a) (b := b) ρ).trace.re := by
  -- `c • 1 - B` is PSD where `c = B.trace.re`.
  have hC_psd : (((B.trace.re : ℝ) : ℂ) • (1 : CMatrix b) - B).PosSemidef := by
    have hle : B ≤ ((B.trace.re : ℝ) : ℂ) • (1 : CMatrix b) :=
      State.posSemidef_le_trace_re_smul_one hB
    exact Matrix.le_iff.mp hle
  -- `A ⊗ (c • 1 - B)` is PSD (Kronecker of PSD).
  have hAC_psd :
      (Matrix.kronecker A (((B.trace.re : ℝ) : ℂ) • (1 : CMatrix b) - B)).PosSemidef :=
    hA.kronecker hC_psd
  -- Non-negativity: `0 ≤ Tr[(A ⊗ (c • 1 - B)) ρ].re`.
  have hnn : 0 ≤
      ((Matrix.kronecker A (((B.trace.re : ℝ) : ℂ) • (1 : CMatrix b) - B) * ρ).trace).re :=
    trace_mul_posSemidef_re_nonneg hAC_psd hρ
  -- Distribute the Kronecker over the subtraction and scalar (entry-wise).
  rw [show Matrix.kronecker A (((B.trace.re : ℝ) : ℂ) • (1 : CMatrix b) - B) =
        ((B.trace.re : ℝ) : ℂ) • Matrix.kronecker A (1 : CMatrix b) -
          Matrix.kronecker A B by
      ext ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply,
                 Matrix.smul_apply]
      ring] at hnn
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
      Complex.sub_re] at hnn
  -- `(c • z).re = c.re * z.re` for real `c`; here `c = B.trace.re`.
  have h_smul_re : (((B.trace.re : ℝ) : ℂ) •
        ((Matrix.kronecker A (1 : CMatrix b) * ρ).trace)).re =
      B.trace.re * ((Matrix.kronecker A (1 : CMatrix b) * ρ).trace).re := by
    simp [Complex.ofReal_im]
  rw [h_smul_re] at hnn
  -- Partial-trace pairing: `Tr[(A ⊗ 1) ρ] = Tr[A · partialTraceB ρ]`.
  have hpair : ((Matrix.kronecker A (1 : CMatrix b) * ρ).trace).re =
      (A * partialTraceB (a := a) (b := b) ρ).trace.re := by
    rw [Matrix.trace_mul_comm (Matrix.kronecker A (1 : CMatrix b)) ρ,
        trace_mul_kronecker_one_right_eq_partialTraceB ρ A,
        Matrix.trace_mul_comm (partialTraceB (a := a) (b := b) ρ) A]
  rw [hpair] at hnn
  linarith

namespace State

/-- The high-parameter sandwiched trace power is continuous when the input
state and reference state vary together, provided the reference path is
eventually full-rank and the limiting reference is full-rank. -/
theorem sandwichedRenyiReferenceInner_tracePower_tendsto_of_tendsto_posDef_state_reference
    {X : Type*} {l : Filter X} {rhoF sigmaF : X -> State a} {rho sigma : State a}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hsigmaF : Tendsto sigmaF l (nhds sigma))
    (hsigmaFpd : Filter.Eventually (fun x => (sigmaF x).matrix.PosDef) l)
    (hsigma : sigma.matrix.PosDef)
    (alpha : Real) (halpha_pos : 0 < alpha) :
    Tendsto
      (fun x : X =>
        (((CFC.rpow
          (sandwichedRenyiReferenceInner (rhoF x) (sigmaF x).matrix alpha)
          alpha).trace).re))
      l
      (nhds
        (((CFC.rpow
          (sandwichedRenyiReferenceInner rho sigma.matrix alpha)
          alpha).trace).re)) := by
  let s : Real := (1 - alpha) / (2 * alpha)
  have hrhoMatrix :
      Tendsto (fun x : X => (rhoF x).matrix) l (nhds rho.matrix) :=
    State.continuous_matrix.tendsto rho |>.comp hrhoF
  have hsigmaMatrix :
      Tendsto (fun x : X => (sigmaF x).matrix) l (nhds sigma.matrix) :=
    State.continuous_matrix.tendsto sigma |>.comp hsigmaF
  have hsigmaPow :
      Tendsto (fun x : X => CFC.rpow (sigmaF x).matrix s) l
        (nhds (CFC.rpow sigma.matrix s)) :=
    _root_.QIT.cMatrix_rpow_tendsto_of_tendsto_posDef
      s hsigmaMatrix hsigmaFpd hsigma
  have hinner :
      Tendsto
        (fun x : X =>
          sandwichedRenyiReferenceInner (rhoF x) (sigmaF x).matrix alpha)
        l
        (nhds (sandwichedRenyiReferenceInner rho sigma.matrix alpha)) := by
    unfold sandwichedRenyiReferenceInner
    exact (hsigmaPow.mul hrhoMatrix).mul hsigmaPow
  have hinner_psd :
      Filter.Eventually
        (fun x : X =>
          (sandwichedRenyiReferenceInner (rhoF x) (sigmaF x).matrix alpha).PosSemidef)
        l :=
    hsigmaFpd.mono fun x hx =>
      sandwichedRenyiReferenceInner_posSemidef (rhoF x) hx.posSemidef alpha
  exact
    cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
      halpha_pos hinner hinner_psd
      (sandwichedRenyiReferenceInner_posSemidef rho hsigma.posSemidef alpha)

/-- The finite high-parameter PSD-reference branch is continuous when the
input state and a full-rank reference state vary together. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_of_tendsto_posDef_state_reference
    {X : Type*} {l : Filter X} {rhoF sigmaF : X -> State a} {rho sigma : State a}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hsigmaF : Tendsto sigmaF l (nhds sigma))
    (hsigmaFpd : Filter.Eventually (fun x => (sigmaF x).matrix.PosDef) l)
    (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    Tendsto
      (fun x : X =>
        sandwichedRenyiPSDReferenceHighAlphaFinite
          (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha)
      l
      (nhds
        (sandwichedRenyiPSDReferenceHighAlphaFinite
          rho sigma.matrix sigma.pos alpha)) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have htrace :=
    sandwichedRenyiReferenceInner_tracePower_tendsto_of_tendsto_posDef_state_reference
      hrhoF hsigmaF hsigmaFpd hsigma alpha halpha_pos
  have htarget_pos :
      0 <
        (((CFC.rpow
          (sandwichedRenyiReferenceInner rho sigma.matrix alpha)
          alpha).trace).re) := by
    simpa [psdTracePower] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_reference_posDef
        rho hsigma alpha
  have hlog :
      Tendsto
        (fun x : X =>
          log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner (rhoF x) (sigmaF x).matrix alpha)
              alpha).trace).re))
        l
        (nhds
          (log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner rho sigma.matrix alpha)
              alpha).trace).re))) := by
    have hrawLog := Filter.Tendsto.log htrace (ne_of_gt htarget_pos)
    simpa [log2] using
      hrawLog.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  simpa [sandwichedRenyiPSDReferenceHighAlphaFinite, psdTracePower] using
    tendsto_const_nhds.mul hlog

/-- The support-aware high-parameter PSD-reference branch is continuous as an
extended-real function along full-rank reference paths. -/
theorem sandwichedRenyiPSDReferenceHighAlphaE_tendsto_of_tendsto_posDef_state_reference
    {X : Type*} {l : Filter X} {rhoF sigmaF : X -> State a} {rho sigma : State a}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hsigmaF : Tendsto sigmaF l (nhds sigma))
    (hsigmaFpd : Filter.Eventually (fun x => (sigmaF x).matrix.PosDef) l)
    (hsigma : sigma.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    Tendsto
      (fun x : X =>
        sandwichedRenyiPSDReferenceHighAlphaE
          (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha)
      l
      (nhds
        (sandwichedRenyiPSDReferenceHighAlphaE
          rho sigma.matrix sigma.pos alpha)) := by
  have hfinite :
      Tendsto
        (fun x : X =>
          sandwichedRenyiPSDReferenceHighAlphaFinite
            (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha)
        l
        (nhds
          (sandwichedRenyiPSDReferenceHighAlphaFinite
            rho sigma.matrix sigma.pos alpha)) :=
    sandwichedRenyiPSDReferenceHighAlphaFinite_tendsto_of_tendsto_posDef_state_reference
      hrhoF hsigmaF hsigmaFpd hsigma halpha
  have htarget :
      sandwichedRenyiPSDReferenceHighAlphaE
          rho sigma.matrix sigma.pos alpha =
        (sandwichedRenyiPSDReferenceHighAlphaFinite
          rho sigma.matrix sigma.pos alpha : EReal) := by
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rho sigma.pos alpha
      (Matrix.Supports.of_right_posDef rho.matrix sigma.matrix hsigma)]
  have hcongr :
      (fun x : X =>
        sandwichedRenyiPSDReferenceHighAlphaE
          (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha)
        =ᶠ[l]
      (fun x : X =>
        (sandwichedRenyiPSDReferenceHighAlphaFinite
          (rhoF x) (sigmaF x).matrix (sigmaF x).pos alpha : EReal)) := by
    filter_upwards [hsigmaFpd] with x hx
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      (rhoF x) (sigmaF x).pos alpha
      (Matrix.Supports.of_right_posDef (rhoF x).matrix (sigmaF x).matrix hx)]
  simpa [htarget] using (EReal.tendsto_coe.mpr hfinite).congr' hcongr.symm

/-- Product states are continuous in both factors. -/
theorem prod_tendsto
    {X : Type*} {l : Filter X} {rhoF : X -> State a} {sigmaF : X -> State b}
    {rho : State a} {sigma : State b}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hsigmaF : Tendsto sigmaF l (nhds sigma)) :
    Tendsto (fun x : X => (rhoF x).prod (sigmaF x)) l (nhds (rho.prod sigma)) := by
  have hleft :
      Tendsto (fun x : X => (rhoF x).matrix) l (nhds rho.matrix) :=
    State.continuous_matrix.tendsto rho |>.comp hrhoF
  have hright :
      Tendsto (fun x : X => (sigmaF x).matrix) l (nhds sigma.matrix) :=
    State.continuous_matrix.tendsto sigma |>.comp hsigmaF
  have hpair :
      Tendsto
        (fun x : X => ((rhoF x).matrix, (sigmaF x).matrix))
        l
        (nhds (rho.matrix, sigma.matrix)) :=
    hleft.prodMk_nhds hright
  have hkr :
      Continuous fun M : CMatrix a × CMatrix b => Matrix.kronecker M.1 M.2 := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        (continuous_fst.matrix_elem x.1 y.1).mul
          (continuous_snd.matrix_elem x.2 y.2)
  have hmatrix :
      Tendsto (fun x : X => ((rhoF x).prod (sigmaF x)).matrix)
        l (nhds (rho.prod sigma).matrix) := by
    simpa [State.prod] using
      hkr.tendsto (rho.matrix, sigma.matrix) |>.comp hpair
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  exact hmatrix

/-- A fixed full-rank side-information candidate is continuous along input
state paths whose limiting left marginal is full-rank. -/
theorem sandwichedRenyiMutualInformationCandidateE_tendsto_of_tendsto_posDef
    {X : Type*} {l : Filter X}
    {rhoF : X -> State (Prod a b)} {rho : State (Prod a b)}
    (hrhoF : Tendsto rhoF l (nhds rho))
    (hrhoA : rho.marginalA.matrix.PosDef)
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    Tendsto
      (fun x : X => (rhoF x).sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
      l
      (nhds (rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)) := by
  have hmarg :
      Tendsto (fun x : X => (rhoF x).marginalA) l (nhds rho.marginalA) :=
    State.marginalA_continuous.tendsto rho |>.comp hrhoF
  have hmarg_matrix :
      Tendsto (fun x : X => (rhoF x).marginalA.matrix)
        l (nhds rho.marginalA.matrix) :=
    State.continuous_matrix.tendsto rho.marginalA |>.comp hmarg
  have hmarg_pd :
      Filter.Eventually (fun x : X => (rhoF x).marginalA.matrix.PosDef) l :=
    eventually_posDef_of_tendsto_posDef hmarg_matrix
      (Filter.Eventually.of_forall fun x => (rhoF x).marginalA.pos) hrhoA
  have href_tend :
      Tendsto (fun x : X => (rhoF x).marginalA.prod sigmaB)
        l (nhds (rho.marginalA.prod sigmaB)) :=
    State.prod_tendsto hmarg tendsto_const_nhds
  have href_pd :
      Filter.Eventually
        (fun x : X => ((rhoF x).marginalA.prod sigmaB).matrix.PosDef) l := by
    filter_upwards [hmarg_pd] with x hx
    exact State.prod_posDef hx hsigmaB
  have hhigh :
      Tendsto
        (fun x : X =>
          sandwichedRenyiPSDReferenceHighAlphaE
            (rhoF x) ((rhoF x).marginalA.prod sigmaB).matrix
            ((rhoF x).marginalA.prod sigmaB).pos alpha)
        l
        (nhds
          (sandwichedRenyiPSDReferenceHighAlphaE
            rho (rho.marginalA.prod sigmaB).matrix
            (rho.marginalA.prod sigmaB).pos alpha)) :=
    sandwichedRenyiPSDReferenceHighAlphaE_tendsto_of_tendsto_posDef_state_reference
      hrhoF href_tend href_pd (State.prod_posDef hrhoA hsigmaB) halpha
  have htarget :
      rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
        sandwichedRenyiPSDReferenceHighAlphaE
          rho (rho.marginalA.prod sigmaB).matrix
          (rho.marginalA.prod sigmaB).pos alpha := by
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
  have hcongr :
      (fun x : X => (rhoF x).sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
        =ᶠ[l]
      (fun x : X =>
        sandwichedRenyiPSDReferenceHighAlphaE
          (rhoF x) ((rhoF x).marginalA.prod sigmaB).matrix
          ((rhoF x).marginalA.prod sigmaB).pos alpha) := by
    filter_upwards with x
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
  simpa [htarget] using hhigh.congr' hcongr.symm

/-- Full-rank fixed-side candidates are continuous at states whose left
marginal is full-rank. -/
theorem sandwichedRenyiMutualInformationCandidateE_continuousAt_of_posDef
    (rho : State (Prod a b)) (hrhoA : rho.marginalA.matrix.PosDef)
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    ContinuousAt
      (fun rho' : State (Prod a b) =>
        rho'.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
      rho := by
  exact sandwichedRenyiMutualInformationCandidateE_tendsto_of_tendsto_posDef
    (rhoF := fun rho' : State (Prod a b) => rho')
    (rho := rho) tendsto_id hrhoA sigmaB hsigmaB halpha

/-- Full-rank fixed-side candidates are upper semicontinuous on the locus where
the left marginal is full-rank. -/
theorem sandwichedRenyiMutualInformationCandidateE_upperSemicontinuousOn_posDefMarginalA
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    UpperSemicontinuousOn
      (fun rho : State (Prod a b) =>
        rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
      {rho : State (Prod a b) | rho.marginalA.matrix.PosDef} := by
  intro rho hrho
  exact (sandwichedRenyiMutualInformationCandidateE_continuousAt_of_posDef
    rho hrho sigmaB hsigmaB halpha).continuousWithinAt.upperSemicontinuousWithinAt

/-- The unrestricted side-state infimum is bounded above by the infimum
restricted to full-rank side states. -/
theorem sandwichedRenyiMutualInformationE_le_iInf_posDef_candidates
    (rhoAB : State (Prod a b)) (alpha : Real) :
    rhoAB.sandwichedRenyiMutualInformationE alpha ≤
      ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha := by
  refine le_iInf fun sigmaB => ?_
  exact rhoAB.sandwichedRenyiMutualInformationE_le_candidate sigmaB.1 alpha

/-- In the high-`alpha` branch, a fixed side-information candidate is `+∞`
when the bipartite state is not supported by the product reference. -/
theorem sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_supports
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    {alpha : Real} (halpha : 1 < alpha)
    (hSupport :
      ¬ Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix) :
    rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha = ⊤ := by
  rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
  rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
  exact sandwichedRenyiPSDReferenceHighAlphaE_eq_top_of_not_supports
    rhoAB (rhoAB.marginalA.prod sigmaB).pos alpha hSupport

/-- A full-rank side state is already present in the restricted candidate
domain, so the restricted infimum is below that candidate. -/
theorem iInf_posDef_candidates_le_sandwichedRenyiMutualInformationCandidateE_of_posDef
    (rhoAB : State (Prod a b)) (alpha : Real)
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef) :
    (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  exact iInf_le
    (fun tauB : {tauB : State b // tauB.matrix.PosDef} =>
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha)
    ⟨sigmaB, hsigmaB⟩

/-- A full-rank approximating path gives the reverse inequality needed for the
full-rank side-state restriction.

This is the order/topology handoff for the singular side-state branch: once a
path of full-rank side states has candidate values converging to the target
candidate, the restricted infimum is below the target candidate. -/
theorem iInf_posDef_candidates_le_sandwichedRenyiMutualInformationCandidateE_of_tendsto
    {X : Type*} {l : Filter X} [NeBot l]
    (rhoAB : State (Prod a b)) (alpha : Real)
    (sigmaF : X -> State b) (sigmaB : State b)
    (hposDef : ∀ᶠ x in l, (sigmaF x).matrix.PosDef)
    (htend :
      Tendsto
        (fun x : X => rhoAB.sandwichedRenyiMutualInformationCandidateE (sigmaF x) alpha)
        l
        (nhds (rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha))) :
    (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  refine ge_of_tendsto htend ?_
  filter_upwards [hposDef] with x hx
  exact iInf_le
    (fun tauB : {tauB : State b // tauB.matrix.PosDef} =>
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha)
    ⟨sigmaF x, hx⟩

/-- The unsupported high-`alpha` branch is automatic for the full-rank
restriction: the target fixed candidate is `+∞`. -/
theorem iInf_posDef_candidates_le_sandwichedRenyiMutualInformationCandidateE_of_not_supports
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    {alpha : Real} (halpha : 1 < alpha)
    (hSupport :
      ¬ Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix) :
    (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  rw [sandwichedRenyiMutualInformationCandidateE_eq_top_of_not_supports
    rhoAB sigmaB halpha hSupport]
  exact le_top

/-- Full-rank restriction reduces to the genuinely singular supported case.

For high `alpha`, a side state which is already full-rank is in the restricted
domain, while an unsupported side state has candidate value `+∞`. Therefore the
only remaining approximation obligation is the supported non-full-rank case. -/
theorem posDef_candidate_approx_of_supported_singular
    (rhoAB : State (Prod a b)) {alpha : Real} (halpha : 1 < alpha)
    (hsingular :
      ∀ sigmaB : State b,
        Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix →
          ¬ sigmaB.matrix.PosDef →
            (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
              rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
                rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha) :
    ∀ sigmaB : State b,
      (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
        rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  intro sigmaB
  by_cases hsigmaB : sigmaB.matrix.PosDef
  · exact
      iInf_posDef_candidates_le_sandwichedRenyiMutualInformationCandidateE_of_posDef
        rhoAB alpha sigmaB hsigmaB
  · by_cases hSupport :
        Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix
    · exact hsingular sigmaB hSupport hsigmaB
    · exact
        iInf_posDef_candidates_le_sandwichedRenyiMutualInformationCandidateE_of_not_supports
          rhoAB sigmaB halpha hSupport

/-- A pointwise approximation lower bound against every side state gives the
reverse inequality needed to restrict the optimized infimum to full-rank side
states. -/
theorem iInf_posDef_candidates_le_sandwichedRenyiMutualInformationE_of_le_candidate
    (rhoAB : State (Prod a b)) (alpha : Real)
    (happrox :
      ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha) :
    (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
        rhoAB.sandwichedRenyiMutualInformationE alpha := by
  haveI : Nonempty b := by
    rcases rhoAB.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  rw [State.sandwichedRenyiMutualInformationE_eq_sInf]
  refine le_csInf (rhoAB.sandwichedRenyiMutualInformationEValueSet_nonempty alpha) ?_
  intro y hy
  rcases hy with ⟨sigmaB, rfl⟩
  exact happrox sigmaB

/-- The full-rank side-state restriction is equivalent to the original
optimized infimum once every side state is dominated by full-rank
approximants. -/
theorem sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
    (rhoAB : State (Prod a b)) (alpha : Real)
    (happrox :
      ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha) :
    rhoAB.sandwichedRenyiMutualInformationE alpha =
      ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha := by
  exact le_antisymm
    (sandwichedRenyiMutualInformationE_le_iInf_posDef_candidates rhoAB alpha)
    (iInf_posDef_candidates_le_sandwichedRenyiMutualInformationE_of_le_candidate
      rhoAB alpha happrox)

/-- State optimized monotonicity from the full-rank side-state approximation
lower bound and monotonicity of all full-rank fixed candidates. -/
theorem sandwichedRenyiMutualInformationE_mono_of_posDef_candidate_approx_and_candidate_mono
    (rhoAB : State (Prod a b))
    (happrox :
      ∀ gamma : {gamma : Real // 1 < gamma}, ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 gamma.1) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB gamma.1)
    (hmono :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        ∀ alpha beta : {alpha : Real // 1 < alpha},
          alpha.1 ≤ beta.1 →
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha.1 ≤
              rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 beta.1) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  refine
    sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_candidate_mono
      rhoAB ?_ hmono
  intro gamma
  exact sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
    rhoAB gamma.1 (happrox gamma)

/-- State optimized monotonicity from the full-rank side-state approximation
lower bound and a derivative-sign proof for all full-rank fixed candidates. -/
theorem sandwichedRenyiMutualInformationE_mono_of_posDef_candidate_approx_and_deriv_nonneg
    (rhoAB : State (Prod a b)) (hrhoA : rhoAB.marginalA.matrix.PosDef)
    (happrox :
      ∀ gamma : {gamma : Real // 1 < gamma}, ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 gamma.1) ≤
            rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB gamma.1)
    (hcont :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        ContinuousOn
          (fun alpha : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.marginalA.prod sigmaB.1).matrix
              (rhoAB.marginalA.prod sigmaB.1).pos alpha)
          (Set.Ioi (1 : Real)))
    (hdiff :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        DifferentiableOn Real
          (fun alpha : Real =>
            sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (rhoAB.marginalA.prod sigmaB.1).matrix
              (rhoAB.marginalA.prod sigmaB.1).pos alpha)
          (Set.Ioi (1 : Real)))
    (hderiv :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        ∀ alpha : Real, 1 < alpha →
          0 ≤ deriv
            (fun beta : Real =>
              sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
                (rhoAB.marginalA.prod sigmaB.1).matrix
                (rhoAB.marginalA.prod sigmaB.1).pos beta)
            alpha) :
    ∀ alpha beta : {alpha : Real // 1 < alpha},
      alpha.1 ≤ beta.1 →
        rhoAB.sandwichedRenyiMutualInformationE alpha.1 ≤
          rhoAB.sandwichedRenyiMutualInformationE beta.1 := by
  refine
    sandwichedRenyiMutualInformationE_mono_of_iInf_posDef_candidates_and_deriv_nonneg
      rhoAB hrhoA ?_ hcont hdiff hderiv
  intro gamma
  exact sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
    rhoAB gamma.1 (happrox gamma)

/-- If the side-state infimum has been restricted to full-rank candidates,
full-rank candidate upper semicontinuity gives optimized upper semicontinuity
on any locus with full-rank left marginal. -/
theorem sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_iInf_posDef_candidates
    {s : Set (State (Prod a b))}
    {alpha : Real} (halpha : 1 < alpha)
    (hposA : ∀ rho ∈ s, rho.marginalA.matrix.PosDef)
    (hfullRankInf :
      ∀ rho : State (Prod a b),
        rho.sandwichedRenyiMutualInformationE alpha =
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha) :
    UpperSemicontinuousOn
      (fun rho : State (Prod a b) => rho.sandwichedRenyiMutualInformationE alpha)
      s := by
  have hcandidates :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        UpperSemicontinuousOn
          (fun rho : State (Prod a b) =>
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha)
          s := by
    intro sigmaB
    exact
      (sandwichedRenyiMutualInformationCandidateE_upperSemicontinuousOn_posDefMarginalA
        sigmaB.1 sigmaB.2 halpha).mono hposA
  have hiInf :
      UpperSemicontinuousOn
        (fun rho : State (Prod a b) =>
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha)
        s :=
    upperSemicontinuousOn_iInf hcandidates
  have hfun :
      (fun rho : State (Prod a b) => rho.sandwichedRenyiMutualInformationE alpha) =
        (fun rho : State (Prod a b) =>
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha) := by
    funext rho
    exact hfullRankInf rho
  simpa [hfun] using hiInf

/-- Optimized upper semicontinuity from the full-rank approximation lower-bound
form of the side-state restriction. -/
theorem sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_posDef_candidate_approx
    {s : Set (State (Prod a b))}
    {alpha : Real} (halpha : 1 < alpha)
    (hposA : ∀ rho ∈ s, rho.marginalA.matrix.PosDef)
    (happrox :
      ∀ rho : State (Prod a b), ∀ sigmaB : State b,
        (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
          rho.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha) :
    UpperSemicontinuousOn
      (fun rho : State (Prod a b) => rho.sandwichedRenyiMutualInformationE alpha)
      s :=
  sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_iInf_posDef_candidates
    halpha hposA fun rho =>
      sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
        rho alpha (happrox rho)

/-- Affine full-rank approximation matrix for a side state.

The path is `(1 - delta) * sigma + delta * mu`; when `mu` is full-rank and
`delta > 0`, the corresponding normalized state is full-rank. -/
def fullRankApproxMatrix (sigma mu : State a) (delta : Real) : CMatrix a :=
  regularizedStateMatrix sigma mu delta

/-- Affine full-rank approximation state for a side state. -/
def fullRankApproxState (sigma mu : State a) (delta : Real)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) : State a :=
  regularizedWithState sigma mu delta hdelta0 hdelta1

@[simp]
theorem fullRankApproxState_matrix (sigma mu : State a) (delta : Real)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (fullRankApproxState sigma mu delta hdelta0 hdelta1).matrix =
      fullRankApproxMatrix sigma mu delta := by
  rfl

/-- Positive regularization by a full-rank noise state is full-rank. -/
theorem fullRankApproxState_posDef_of_noise
    (sigma mu : State a) (hmu : mu.matrix.PosDef) {delta : Real}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) (hdelta_pos : 0 < delta) :
    (fullRankApproxState sigma mu delta hdelta0 hdelta1).matrix.PosDef := by
  exact regularizedWithState_posDef_of_noise sigma mu hmu hdelta0 hdelta1 hdelta_pos

/-- The full-rank approximation matrix differs from the scaled base state by
the scaled noise state. -/
theorem fullRankApproxMatrix_sub_smul_left
    (sigma mu : State a) (delta : Real) :
    fullRankApproxMatrix sigma mu delta -
        (((1 - delta : Real) : ℂ) • sigma.matrix) =
      ((delta : Real) : ℂ) • mu.matrix := by
  ext i j
  simp [fullRankApproxMatrix, regularizedStateMatrix, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- The full-rank approximation matrix dominates the scaled base state in
Loewner order. -/
theorem smul_left_le_fullRankApproxMatrix
    (sigma mu : State a) {delta : Real} (hdelta : 0 ≤ delta) :
    (((1 - delta : Real) : ℂ) • sigma.matrix) ≤ fullRankApproxMatrix sigma mu delta := by
  rw [Matrix.le_iff]
  rw [fullRankApproxMatrix_sub_smul_left]
  have hdeltaC : (0 : ℂ) ≤ ((delta : Real) : ℂ) := by
    exact_mod_cast hdelta
  exact Matrix.PosSemidef.smul mu.pos hdeltaC

/-- The full-rank approximation matrix path converges back to the side state. -/
theorem fullRankApproxMatrix_tendsto_zero (sigma mu : State a) :
    Tendsto (fun delta : Real => fullRankApproxMatrix sigma mu delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma.matrix) := by
  simpa [fullRankApproxMatrix] using regularizedStateMatrix_tendsto_zero sigma mu

/-- Total full-rank approximation path, filled in by the limiting state outside
the probability interval. -/
def fullRankApproxStatePath (sigma mu : State a) (delta : Real) : State a :=
  if hdelta : delta ∈ Set.Ioo (0 : Real) 1 then
    fullRankApproxState sigma mu delta hdelta.1.le hdelta.2.le
  else
    sigma

theorem fullRankApproxStatePath_eq_of_mem
    (sigma mu : State a) {delta : Real} (hdelta : delta ∈ Set.Ioo (0 : Real) 1) :
    fullRankApproxStatePath sigma mu delta =
      fullRankApproxState sigma mu delta hdelta.1.le hdelta.2.le := by
  rw [fullRankApproxStatePath, dif_pos hdelta]

/-- The in-interval full-rank approximation path dominates the scaled base
state in Loewner order. -/
theorem smul_left_le_fullRankApproxStatePath_matrix_of_mem
    (sigma mu : State a) {delta : Real} (hdelta : delta ∈ Set.Ioo (0 : Real) 1) :
    (((1 - delta : Real) : ℂ) • sigma.matrix) ≤
      (fullRankApproxStatePath sigma mu delta).matrix := by
  rw [fullRankApproxStatePath, dif_pos hdelta]
  simpa [fullRankApproxState_matrix] using
    smul_left_le_fullRankApproxMatrix sigma mu hdelta.1.le

/-- The full-rank approximation path converges back to the side state. -/
theorem fullRankApproxStatePath_tendsto_zero (sigma mu : State a) :
    Tendsto (fun delta : Real => fullRankApproxStatePath sigma mu delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  refine Tendsto.congr' ?_ (fullRankApproxMatrix_tendsto_zero sigma mu)
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  change fullRankApproxMatrix sigma mu delta =
    (fullRankApproxStatePath sigma mu delta).matrix
  rw [fullRankApproxStatePath, dif_pos hdelta]
  rfl

/-- The side-state approximation is eventually full-rank when the noise is
full-rank. -/
theorem fullRankApproxStatePath_eventually_posDef_of_noise
    (sigma mu : State a) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxStatePath sigma mu delta).matrix.PosDef := by
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  rw [fullRankApproxStatePath, dif_pos hdelta]
  exact fullRankApproxState_posDef_of_noise
    sigma mu hmu hdelta.1.le hdelta.2.le hdelta.1

/-- A full-rank approximation reference eventually supports every fixed input
matrix. -/
theorem fullRankApproxStatePath_eventually_supports_of_noise
    (rho : State a) (sigma mu : State a) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rho.matrix (fullRankApproxStatePath sigma mu delta).matrix := by
  filter_upwards [fullRankApproxStatePath_eventually_posDef_of_noise sigma mu hmu]
    with delta hdelta
  exact Matrix.Supports.of_right_posDef rho.matrix
    (fullRankApproxStatePath sigma mu delta).matrix hdelta

/-- Canonical full-rank approximation path using the maximally mixed state as
noise. -/
def fullRankApproxMaximallyMixedStatePath (sigma : State a) (delta : Real) : State a :=
  letI : Nonempty a := sigma.nonempty
  fullRankApproxStatePath sigma (maximallyMixed a) delta

/-- On `0 < delta < 1`, the canonical maximally mixed full-rank approximation
is a scalar multiple of the unnormalized `sigma + epsilon I` regularization. -/
theorem fullRankApproxMaximallyMixedStatePath_matrix_eq_smul_referenceRegularization
    (sigma : State a) {delta : Real} (hdelta : delta ∈ Set.Ioo (0 : Real) 1) :
    (fullRankApproxMaximallyMixedStatePath sigma delta).matrix =
      (((1 - delta : Real) : ℂ) •
        sandwichedRenyiReferenceRegularization sigma.matrix
          (delta / ((1 - delta) * (Fintype.card a : Real)))) := by
  letI : Nonempty a := sigma.nonempty
  have hcard_ne : (Fintype.card a : Real) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hdelta_ne : 1 - delta ≠ 0 := by
    linarith [hdelta.2]
  ext i j
  simp [fullRankApproxMaximallyMixedStatePath, fullRankApproxStatePath,
    fullRankApproxState, regularizedStateMatrix,
    sandwichedRenyiReferenceRegularization, maximallyMixed_matrix, hdelta,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp
    have hdelta_complex_ne : (1 - (delta : ℂ)) ≠ 0 := by
      exact_mod_cast hdelta_ne
    have hcard_complex_ne : (((Fintype.card a : Real) : ℂ)) ≠ 0 := by
      exact_mod_cast hcard_ne
    have hden_ne :
        (1 - (delta : ℂ)) * (((Fintype.card a : Real) : ℂ)) ≠ 0 :=
      mul_ne_zero hdelta_complex_ne hcard_complex_ne
    field_simp [hcard_ne, hdelta_ne, hdelta_complex_ne, hcard_complex_ne, hden_ne]
  · simp [hij]

/-- Filter form of the scalar-regularization bridge for the canonical
maximally mixed full-rank approximation path. -/
theorem fullRankApproxMaximallyMixedStatePath_matrix_eventuallyEq_smul_referenceRegularization
    (sigma : State a) :
    (fun delta : Real => (fullRankApproxMaximallyMixedStatePath sigma delta).matrix) =ᶠ[
        nhdsWithin (0 : Real) (Set.Ioo 0 1)]
      (fun delta : Real =>
        (((1 - delta : Real) : ℂ) •
          sandwichedRenyiReferenceRegularization sigma.matrix
            (delta / ((1 - delta) * (Fintype.card a : Real))))) := by
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  exact fullRankApproxMaximallyMixedStatePath_matrix_eq_smul_referenceRegularization sigma hdelta

omit [DecidableEq a] in
/-- The regularization parameter induced by the canonical full-rank state
path tends to zero from the positive side. -/
theorem fullRankApproxMaximallyMixedRegularizationParameter_tendsto_zero
    [Nonempty a] :
    Tendsto
      (fun delta : Real => delta / ((1 - delta) * (Fintype.card a : Real)))
      (nhdsWithin (0 : Real) (Set.Ioo 0 1))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hdelta :
        Tendsto (fun delta : Real => delta)
          (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds (0 : Real)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hden :
        Tendsto (fun delta : Real => (1 - delta) * (Fintype.card a : Real))
          (nhdsWithin (0 : Real) (Set.Ioo 0 1))
          (nhds ((1 - (0 : Real)) * (Fintype.card a : Real))) :=
      (tendsto_const_nhds.sub hdelta).mul tendsto_const_nhds
    have hcard_ne : ((1 - (0 : Real)) * (Fintype.card a : Real)) ≠ 0 := by
      have hcard_pos : 0 < (Fintype.card a : Real) := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card a)
      nlinarith
    simpa using hdelta.div hden hcard_ne
  · filter_upwards [self_mem_nhdsWithin] with delta hdelta
    have hcard_pos : 0 < (Fintype.card a : Real) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card a)
    have hden_pos : 0 < (1 - delta) * (Fintype.card a : Real) :=
      mul_pos (sub_pos.mpr hdelta.2) hcard_pos
    exact div_pos hdelta.1 hden_pos

/-- The canonical full-rank approximation path converges back to the target
state. -/
theorem fullRankApproxMaximallyMixedStatePath_tendsto_zero (sigma : State a) :
    Tendsto (fun delta : Real => fullRankApproxMaximallyMixedStatePath sigma delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma) := by
  classical
  letI : Nonempty a := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedStatePath] using
    fullRankApproxStatePath_tendsto_zero sigma (maximallyMixed a)

/-- The canonical full-rank approximation path is eventually full-rank. -/
theorem fullRankApproxMaximallyMixedStatePath_eventually_posDef (sigma : State a) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxMaximallyMixedStatePath sigma delta).matrix.PosDef := by
  classical
  letI : Nonempty a := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedStatePath] using
    fullRankApproxStatePath_eventually_posDef_of_noise
      sigma (maximallyMixed a) (maximallyMixed_posDef (a := a))

/-- The canonical full-rank approximation path eventually supports every fixed
input matrix. -/
theorem fullRankApproxMaximallyMixedStatePath_eventually_supports
    (rho sigma : State a) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rho.matrix (fullRankApproxMaximallyMixedStatePath sigma delta).matrix := by
  classical
  letI : Nonempty a := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedStatePath] using
    fullRankApproxStatePath_eventually_supports_of_noise
      rho sigma (maximallyMixed a) (maximallyMixed_posDef (a := a))

/-- Canonical maximally mixed full-rank approximation version of the
full-rank-restriction handoff. -/
theorem iInf_posDef_candidates_le_sandwichedRenyiMutualInformationCandidateE_of_fullRankApprox
    (rhoAB : State (Prod a b)) (sigmaB : State b) (alpha : Real)
    (htend :
      Tendsto
        (fun delta : Real =>
          rhoAB.sandwichedRenyiMutualInformationCandidateE
            (fullRankApproxMaximallyMixedStatePath sigmaB delta) alpha)
        (nhdsWithin (0 : Real) (Set.Ioo 0 1))
        (nhds (rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha))) :
    (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
      rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  haveI : NeBot (nhdsWithin (0 : Real) (Set.Ioo 0 1)) :=
    left_nhdsWithin_Ioo_neBot zero_lt_one
  exact
    iInf_posDef_candidates_le_sandwichedRenyiMutualInformationCandidateE_of_tendsto
      rhoAB alpha
      (fun delta : Real => fullRankApproxMaximallyMixedStatePath sigmaB delta)
      sigmaB
      (fullRankApproxMaximallyMixedStatePath_eventually_posDef sigmaB)
      htend

/-- Full-rank side-state restriction from convergence of the canonical
full-rank approximation in the only nontrivial branch. -/
theorem posDef_candidate_approx_of_supported_singular_fullRankApprox_tendsto
    (rhoAB : State (Prod a b)) {alpha : Real} (halpha : 1 < alpha)
    (hsingular :
      ∀ sigmaB : State b,
        Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix →
          ¬ sigmaB.matrix.PosDef →
            Tendsto
              (fun delta : Real =>
                rhoAB.sandwichedRenyiMutualInformationCandidateE
                  (fullRankApproxMaximallyMixedStatePath sigmaB delta) alpha)
              (nhdsWithin (0 : Real) (Set.Ioo 0 1))
              (nhds (rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha))) :
    ∀ sigmaB : State b,
      (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
        rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  refine posDef_candidate_approx_of_supported_singular rhoAB halpha ?_
  intro sigmaB hSupport hsigmaB
  exact
    iInf_posDef_candidates_le_sandwichedRenyiMutualInformationCandidateE_of_fullRankApprox
      rhoAB sigmaB alpha (hsingular sigmaB hSupport hsigmaB)

/-- If the fixed left reference is full-rank, the product with the full-rank
side-state approximation is full-rank. -/
theorem prod_fullRankApproxState_posDef_of_left
    (rhoA : State a) (sigma mu : State b)
    (hrhoA : rhoA.matrix.PosDef) (hmu : mu.matrix.PosDef) {delta : Real}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) (hdelta_pos : 0 < delta) :
    (rhoA.prod (fullRankApproxState sigma mu delta hdelta0 hdelta1)).matrix.PosDef := by
  exact State.prod_posDef hrhoA
    (fullRankApproxState_posDef_of_noise sigma mu hmu hdelta0 hdelta1 hdelta_pos)

/-- Product reference path obtained by regularizing only the side state. -/
def fullRankApproxProductReferencePath
    (rhoA : State a) (sigma mu : State b) (delta : Real) : State (Prod a b) :=
  rhoA.prod (fullRankApproxStatePath sigma mu delta)

/-- Matrix reference obtained by regularizing only the right tensor factor,
while keeping the left state fixed. -/
def fixedLeftReferenceRegularization
    (rhoA : State a) (sigma : State b) (epsilon : Real) : CMatrix (Prod a b) :=
  Matrix.kronecker rhoA.matrix
    (sandwichedRenyiReferenceRegularization sigma.matrix epsilon)

/-- Product eigenbasis for a tensor-product reference. -/
def productReferenceEigenvectorUnitary
    (rhoA : State a) (sigmaB : State b) : Matrix.unitaryGroup (Prod a b) ℂ :=
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    sigmaB.pos.isHermitian.eigenvectorUnitary
  ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
    Matrix.kronecker_mem_unitary UA.2 UB.2⟩

/-- A tensor-product reference is diagonal in the product of the single-system
eigenbases. -/
theorem productReference_matrix_eq_productEigenbasis_diagonal
    (rhoA : State a) (sigmaB : State b) :
    (rhoA.prod sigmaB).matrix =
      (productReferenceEigenvectorUnitary rhoA sigmaB : CMatrix (Prod a b)) *
        Matrix.diagonal
          (fun y : Prod a b =>
            ((rhoA.pos.isHermitian.eigenvalues y.1 *
                sigmaB.pos.isHermitian.eigenvalues y.2 : Real) : ℂ)) *
        star (productReferenceEigenvectorUnitary rhoA sigmaB : CMatrix (Prod a b)) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    sigmaB.pos.isHermitian.eigenvectorUnitary
  have hA :
      rhoA.matrix =
        (UA : CMatrix a) *
          Matrix.diagonal
            (fun x : a =>
              ((rhoA.pos.isHermitian.eigenvalues x : Real) : ℂ)) *
          star (UA : CMatrix a) := by
    simpa [UA, Function.comp_def,
      Unitary.conjStarAlgAut_apply] using rhoA.pos.isHermitian.spectral_theorem
  have hB :
      sigmaB.matrix =
        (UB : CMatrix b) *
          Matrix.diagonal
            (fun y : b =>
              ((sigmaB.pos.isHermitian.eigenvalues y : Real) : ℂ)) *
          star (UB : CMatrix b) := by
    simpa [UB, Function.comp_def,
      Unitary.conjStarAlgAut_apply] using sigmaB.pos.isHermitian.spectral_theorem
  change Matrix.kronecker rhoA.matrix sigmaB.matrix =
    Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) *
      Matrix.diagonal
        (fun y : Prod a b =>
          ((rhoA.pos.isHermitian.eigenvalues y.1 *
              sigmaB.pos.isHermitian.eigenvalues y.2 : Real) : ℂ)) *
      star (Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b))
  conv_lhs =>
    rw [hA, hB]
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
    Matrix.mul_assoc]

omit [Fintype a] [DecidableEq a] in
/-- Source reference regularization is diagonal in the original reference
eigenbasis, with eigenvalues shifted by the regularization parameter. -/
theorem referenceRegularization_matrix_eq_eigenbasis_diagonal
    (sigma : State b) (epsilon : Real) :
    sandwichedRenyiReferenceRegularization sigma.matrix epsilon =
      (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix b) *
        Matrix.diagonal
          (fun y : b =>
            ((sigma.pos.isHermitian.eigenvalues y + epsilon : Real) : ℂ)) *
        star (sigma.pos.isHermitian.eigenvectorUnitary : CMatrix b) := by
  classical
  let U : Matrix.unitaryGroup b ℂ := sigma.pos.isHermitian.eigenvectorUnitary
  let D : CMatrix b :=
    Matrix.diagonal fun y : b => ((sigma.pos.isHermitian.eigenvalues y : Real) : ℂ)
  have hSigma :
      sigma.matrix = (U : CMatrix b) * D * star (U : CMatrix b) := by
    simpa [U, D, Function.comp_def, Unitary.conjStarAlgAut_apply] using
      sigma.pos.isHermitian.spectral_theorem
  have hOne :
      (1 : CMatrix b) = (U : CMatrix b) * (1 : CMatrix b) * star (U : CMatrix b) := by
    symm
    simp
  have hsmul :
      (epsilon • ((U : CMatrix b) * (1 : CMatrix b) * star (U : CMatrix b)) :
          CMatrix b) =
        (U : CMatrix b) * (epsilon • (1 : CMatrix b)) * star (U : CMatrix b) := by
    calc
      (epsilon • ((U : CMatrix b) * (1 : CMatrix b) * star (U : CMatrix b)) :
          CMatrix b) =
          (epsilon • ((U : CMatrix b) * (1 : CMatrix b)) : CMatrix b) *
            star (U : CMatrix b) := by
            rw [Matrix.smul_mul]
      _ = (U : CMatrix b) * (epsilon • (1 : CMatrix b)) *
            star (U : CMatrix b) := by
            rw [Matrix.mul_smul]
  have hdiag :
      D + epsilon • (1 : CMatrix b) =
        Matrix.diagonal
          (fun y : b =>
            ((sigma.pos.isHermitian.eigenvalues y + epsilon : Real) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.diagonal, Matrix.smul_apply, add_comm]
    · simp [D, Matrix.diagonal, Matrix.smul_apply, hij]
  change sigma.matrix + epsilon • (1 : CMatrix b) =
      (U : CMatrix b) *
        Matrix.diagonal
          (fun y : b =>
            ((sigma.pos.isHermitian.eigenvalues y + epsilon : Real) : ℂ)) *
        star (U : CMatrix b)
  conv_lhs =>
    rw [hSigma, hOne]
  rw [hsmul]
  calc
    (U : CMatrix b) * D * star (U : CMatrix b) +
        (U : CMatrix b) * (epsilon • (1 : CMatrix b)) * star (U : CMatrix b) =
        (U : CMatrix b) * (D + epsilon • (1 : CMatrix b)) *
          star (U : CMatrix b) := by
          noncomm_ring
    _ = (U : CMatrix b) *
        Matrix.diagonal
          (fun y : b =>
            ((sigma.pos.isHermitian.eigenvalues y + epsilon : Real) : ℂ)) *
        star (U : CMatrix b) := by
          rw [hdiag]

/-- Fixed-left side regularization is diagonal in the tensor product of the
left and right reference eigenbases. -/
theorem fixedLeftReferenceRegularization_matrix_eq_productEigenbasis_diagonal
    (rhoA : State a) (sigma : State b) (epsilon : Real) :
    fixedLeftReferenceRegularization rhoA sigma epsilon =
      (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)) *
        Matrix.diagonal
          (fun y : Prod a b =>
            ((rhoA.pos.isHermitian.eigenvalues y.1 *
                (sigma.pos.isHermitian.eigenvalues y.2 + epsilon) : Real) : ℂ)) *
        star (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)) := by
  classical
  let UA : Matrix.unitaryGroup a ℂ :=
    rhoA.pos.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ :=
    sigma.pos.isHermitian.eigenvectorUnitary
  have hA :
      rhoA.matrix =
        (UA : CMatrix a) *
          Matrix.diagonal
            (fun x : a =>
              ((rhoA.pos.isHermitian.eigenvalues x : Real) : ℂ)) *
          star (UA : CMatrix a) := by
    simpa [UA, Function.comp_def, Unitary.conjStarAlgAut_apply] using
      rhoA.pos.isHermitian.spectral_theorem
  have hB :
      sandwichedRenyiReferenceRegularization sigma.matrix epsilon =
        (UB : CMatrix b) *
          Matrix.diagonal
            (fun y : b =>
              ((sigma.pos.isHermitian.eigenvalues y + epsilon : Real) : ℂ)) *
          star (UB : CMatrix b) := by
    simpa [UB] using referenceRegularization_matrix_eq_eigenbasis_diagonal sigma epsilon
  change Matrix.kronecker rhoA.matrix
      (sandwichedRenyiReferenceRegularization sigma.matrix epsilon) =
    Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b) *
      Matrix.diagonal
        (fun y : Prod a b =>
          ((rhoA.pos.isHermitian.eigenvalues y.1 *
              (sigma.pos.isHermitian.eigenvalues y.2 + epsilon) : Real) : ℂ)) *
      star (Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b))
  conv_lhs =>
    rw [hA, hB]
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
    Matrix.mul_assoc]

/-- Fixed-left side-regularized sandwiched Renyi inner operator in the product
reference eigenbasis. -/
theorem sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) (alpha : Real) :
    let s : Real := (1 - alpha) / (2 * alpha)
    let U : Matrix.unitaryGroup (Prod a b) ℂ :=
      productReferenceEigenvectorUnitary rhoA sigma
    let Depsilon : CMatrix (Prod a b) := Matrix.diagonal
      (fun y : Prod a b =>
        (((rhoA.pos.isHermitian.eigenvalues y.1 *
            (sigma.pos.isHermitian.eigenvalues y.2 + epsilon)) ^ s : Real) : ℂ))
    star (U : CMatrix (Prod a b)) *
        sandwichedRenyiReferenceInner rhoAB
          (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha *
        (U : CMatrix (Prod a b)) =
      Depsilon * (star (U : CMatrix (Prod a b)) * rhoAB.matrix *
        (U : CMatrix (Prod a b))) * Depsilon := by
  classical
  dsimp
  let s : Real := (1 - alpha) / (2 * alpha)
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    productReferenceEigenvectorUnitary rhoA sigma
  let depsilon : Prod a b -> Real := fun y =>
    rhoA.pos.isHermitian.eigenvalues y.1 *
      (sigma.pos.isHermitian.eigenvalues y.2 + epsilon)
  let Depsilon : CMatrix (Prod a b) :=
    Matrix.diagonal fun y : Prod a b => ((depsilon y ^ s : Real) : ℂ)
  have hdepsilon_nonneg : ∀ y : Prod a b, 0 ≤ depsilon y := by
    intro y
    exact mul_nonneg (rhoA.pos.eigenvalues_nonneg y.1)
      (add_nonneg (sigma.pos.eigenvalues_nonneg y.2) hepsilon)
  have hpow :
      CFC.rpow (fixedLeftReferenceRegularization rhoA sigma epsilon) s =
        (U : CMatrix (Prod a b)) * Depsilon *
          star (U : CMatrix (Prod a b)) := by
    rw [fixedLeftReferenceRegularization_matrix_eq_productEigenbasis_diagonal
      rhoA sigma epsilon]
    simpa [U, depsilon, Depsilon] using
      cMatrix_rpow_unitary_conj_diagonal_ofReal U depsilon hdepsilon_nonneg s
  have hUstarU :
      star (U : CMatrix (Prod a b)) * (U : CMatrix (Prod a b)) = 1 := by
    simp
  change star (U : CMatrix (Prod a b)) *
      ((CFC.rpow (fixedLeftReferenceRegularization rhoA sigma epsilon) s) *
        rhoAB.matrix *
        (CFC.rpow (fixedLeftReferenceRegularization rhoA sigma epsilon) s)) *
      (U : CMatrix (Prod a b)) =
    Depsilon * (star (U : CMatrix (Prod a b)) * rhoAB.matrix *
      (U : CMatrix (Prod a b))) * Depsilon
  rw [hpow]
  calc
    star (U : CMatrix (Prod a b)) *
        (((U : CMatrix (Prod a b)) * Depsilon *
            star (U : CMatrix (Prod a b))) * rhoAB.matrix *
          ((U : CMatrix (Prod a b)) * Depsilon *
            star (U : CMatrix (Prod a b)))) *
        (U : CMatrix (Prod a b)) =
        Depsilon * (star (U : CMatrix (Prod a b)) * rhoAB.matrix *
          (U : CMatrix (Prod a b))) * Depsilon := by
          simp [Matrix.mul_assoc, hUstarU]
          rw [← Matrix.mul_assoc, hUstarU, Matrix.one_mul]

/-- Entrywise fixed-left side-regularized inner-operator formula in the
product reference eigenbasis. -/
theorem sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis_entry
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) (alpha : Real)
    (i j : Prod a b) :
    let s : Real := (1 - alpha) / (2 * alpha)
    let U : Matrix.unitaryGroup (Prod a b) ℂ :=
      productReferenceEigenvectorUnitary rhoA sigma
    (star (U : CMatrix (Prod a b)) *
        sandwichedRenyiReferenceInner rhoAB
          (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha *
        (U : CMatrix (Prod a b))) i j =
      (((rhoA.pos.isHermitian.eigenvalues i.1 *
          (sigma.pos.isHermitian.eigenvalues i.2 + epsilon)) ^ s : Real) : ℂ) *
        (star (U : CMatrix (Prod a b)) * rhoAB.matrix *
          (U : CMatrix (Prod a b))) i j *
        (((rhoA.pos.isHermitian.eigenvalues j.1 *
          (sigma.pos.isHermitian.eigenvalues j.2 + epsilon)) ^ s : Real) : ℂ) := by
  classical
  dsimp
  let s : Real := (1 - alpha) / (2 * alpha)
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    productReferenceEigenvectorUnitary rhoA sigma
  let Depsilon : CMatrix (Prod a b) := Matrix.diagonal
    (fun y : Prod a b =>
      (((rhoA.pos.isHermitian.eigenvalues y.1 *
          (sigma.pos.isHermitian.eigenvalues y.2 + epsilon)) ^ s : Real) : ℂ))
  let M : CMatrix (Prod a b) :=
    star (U : CMatrix (Prod a b)) * rhoAB.matrix * (U : CMatrix (Prod a b))
  have hform :=
    sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis
      rhoAB rhoA sigma hepsilon alpha
  rw [hform]
  change (Depsilon * M * Depsilon) i j =
    (((rhoA.pos.isHermitian.eigenvalues i.1 *
        (sigma.pos.isHermitian.eigenvalues i.2 + epsilon)) ^ s : Real) : ℂ) *
      M i j *
      (((rhoA.pos.isHermitian.eigenvalues j.1 *
        (sigma.pos.isHermitian.eigenvalues j.2 + epsilon)) ^ s : Real) : ℂ)
  simp [Depsilon, M, Matrix.mul_apply, Matrix.diagonal]

/-- Entrywise product-reference inner-operator formula in the product
reference eigenbasis. -/
theorem sandwichedRenyiReferenceInner_productReference_conj_productEigenbasis_entry
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    (alpha : Real) (i j : Prod a b) :
    let s : Real := (1 - alpha) / (2 * alpha)
    let U : Matrix.unitaryGroup (Prod a b) ℂ :=
      productReferenceEigenvectorUnitary rhoA sigma
    (star (U : CMatrix (Prod a b)) *
        sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
        (U : CMatrix (Prod a b))) i j =
      (((rhoA.pos.isHermitian.eigenvalues i.1 *
          sigma.pos.isHermitian.eigenvalues i.2) ^ s : Real) : ℂ) *
        (star (U : CMatrix (Prod a b)) * rhoAB.matrix *
          (U : CMatrix (Prod a b))) i j *
        (((rhoA.pos.isHermitian.eigenvalues j.1 *
          sigma.pos.isHermitian.eigenvalues j.2) ^ s : Real) : ℂ) := by
  classical
  dsimp
  let hzero : (0 : Real) ≤ (0 : Real) := le_rfl
  have hentry :=
    sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis_entry
      rhoAB rhoA sigma hzero alpha i j
  simpa [fixedLeftReferenceRegularization, sandwichedRenyiReferenceRegularization,
    State.prod_matrix_kronecker] using hentry

private theorem diagonalSupport_entry_eq_zero_of_left_or_right_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CMatrix ι} {d : ι -> Real}
    (hM : M.PosSemidef)
    (hSupport :
      Matrix.Supports M
        (Matrix.diagonal fun k : ι => ((d k : Real) : ℂ)))
    {i j : ι} (hzero : d i = 0 ∨ d j = 0) :
    M i j = 0 := by
  classical
  let D : CMatrix ι := Matrix.diagonal fun k : ι => ((d k : Real) : ℂ)
  have hcol_zero : ∀ {k : ι}, d k = 0 -> ∀ r : ι, M r k = 0 := by
    intro k hk r
    let e : ι -> ℂ := Pi.single k 1
    have hDVec : Matrix.mulVec D e = 0 := by
      ext x
      rw [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single k]
      · by_cases hxk : x = k
        · subst x
          simp [D, e, Matrix.diagonal, hk]
        · simp [D, e, Matrix.diagonal, hxk]
      · intro y _ hy
        simp [D, e, Matrix.diagonal, hy]
      · intro hk_not
        simp at hk_not
    have hMVec := hSupport e (by simpa [D] using hDVec)
    have hEntry := congrFun hMVec r
    rw [Matrix.mulVec, dotProduct] at hEntry
    have hSum : (∑ y, M r y * e y) = M r k := by
      rw [Finset.sum_eq_single k]
      · simp [e]
      · intro y _ hy
        simp [e, hy]
      · intro hk_not
        simp at hk_not
    simpa [hSum] using hEntry
  rcases hzero with hi | hj
  · have hji : M j i = 0 := hcol_zero hi j
    have hherm : star M = M := hM.isHermitian.eq
    have hij : M i j = star (M j i) := by
      rw [show M i j = star M i j from by rw [hherm],
        Matrix.star_apply M i j]
    rw [hij, hji, star_zero]
  · exact hcol_zero hj i

/-- In the product reference eigenbasis, support by the product reference kills
entries touching zero product-reference eigenvalues. -/
theorem productReference_support_conj_entry_eq_zero_of_left_or_right_zero
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoA.prod sigma).matrix)
    {i j : Prod a b}
    (hzero :
      rhoA.pos.isHermitian.eigenvalues i.1 *
          sigma.pos.isHermitian.eigenvalues i.2 = 0 ∨
        rhoA.pos.isHermitian.eigenvalues j.1 *
          sigma.pos.isHermitian.eigenvalues j.2 = 0) :
    (star (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)) *
        rhoAB.matrix *
        (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b))) i j = 0 := by
  classical
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    productReferenceEigenvectorUnitary rhoA sigma
  let M : CMatrix (Prod a b) := star (U : CMatrix (Prod a b)) *
    rhoAB.matrix * (U : CMatrix (Prod a b))
  let d : Prod a b -> Real := fun y =>
    rhoA.pos.isHermitian.eigenvalues y.1 *
      sigma.pos.isHermitian.eigenvalues y.2
  let D : CMatrix (Prod a b) := Matrix.diagonal fun y : Prod a b => ((d y : Real) : ℂ)
  let Uinv : Matrix.unitaryGroup (Prod a b) ℂ := U⁻¹
  have hRefSpec :
      (rhoA.prod sigma).matrix =
        (U : CMatrix (Prod a b)) * D * star (U : CMatrix (Prod a b)) := by
    simpa [U, D, d] using productReference_matrix_eq_productEigenbasis_diagonal rhoA sigma
  have hRefDiag :
      (Uinv : CMatrix (Prod a b)) * (rhoA.prod sigma).matrix *
          star (Uinv : CMatrix (Prod a b)) =
        D := by
    have hUinv : (Uinv : CMatrix (Prod a b)) =
        star (U : CMatrix (Prod a b)) := by
      rfl
    rw [hUinv, star_star, hRefSpec]
    have hUstarU :
        star (U : CMatrix (Prod a b)) * (U : CMatrix (Prod a b)) = 1 := by
      simp
    calc
      star (U : CMatrix (Prod a b)) *
            ((U : CMatrix (Prod a b)) * D * star (U : CMatrix (Prod a b))) *
          (U : CMatrix (Prod a b)) =
          (star (U : CMatrix (Prod a b)) * (U : CMatrix (Prod a b))) *
            D * (star (U : CMatrix (Prod a b)) * (U : CMatrix (Prod a b))) := by
            noncomm_ring
      _ = D := by
            rw [hUstarU]
            simp
  have hSupportBasis : Matrix.Supports M D := by
    have hconj := Matrix.Supports.unitary_conj hSupport Uinv
    rw [hRefDiag] at hconj
    simpa [M, Uinv] using hconj
  have hMpsd : M.PosSemidef := by
    simpa [M, U] using posSemidef_unitary_conj rhoAB.pos U
  simpa [M, U, d] using
    diagonalSupport_entry_eq_zero_of_left_or_right_zero
      (M := M) (d := d) hMpsd hSupportBasis (by simpa [d] using hzero)

/-- Entrywise convergence of the fixed-left side-regularized inner operator in
the product reference eigenbasis. -/
theorem sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis_entry_tendsto
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoA.prod sigma).matrix)
    (alpha : Real) (i j : Prod a b) :
    Filter.Tendsto
      (fun epsilon : Real =>
        (star (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)) *
          sandwichedRenyiReferenceInner rhoAB
            (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha *
          (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b))) i j)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds
        ((star (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)) *
          sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
          (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b))) i j)) := by
  classical
  let l := nhdsWithin (0 : Real) (Set.Ioi 0)
  let s : Real := (1 - alpha) / (2 * alpha)
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    productReferenceEigenvectorUnitary rhoA sigma
  let M : CMatrix (Prod a b) :=
    star (U : CMatrix (Prod a b)) * rhoAB.matrix * (U : CMatrix (Prod a b))
  let d : Prod a b -> Real := fun y =>
    rhoA.pos.isHermitian.eigenvalues y.1 *
      sigma.pos.isHermitian.eigenvalues y.2
  let depsilon : Real -> Prod a b -> Real := fun epsilon y =>
    rhoA.pos.isHermitian.eigenvalues y.1 *
      (sigma.pos.isHermitian.eigenvalues y.2 + epsilon)
  have hd_nonneg : ∀ y : Prod a b, 0 ≤ d y := by
    intro y
    exact mul_nonneg (rhoA.pos.eigenvalues_nonneg y.1)
      (sigma.pos.eigenvalues_nonneg y.2)
  by_cases hi0 : d i = 0
  · have hMzero : M i j = 0 := by
      simpa [M, U, d] using
        productReference_support_conj_entry_eq_zero_of_left_or_right_zero
          rhoAB rhoA sigma hSupport (i := i) (j := j) (Or.inl hi0)
    have htarget :
        (star (U : CMatrix (Prod a b)) *
          sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
          (U : CMatrix (Prod a b))) i j = 0 := by
      have hentry :=
        sandwichedRenyiReferenceInner_productReference_conj_productEigenbasis_entry
          rhoAB rhoA sigma alpha i j
      rw [hentry]
      simp [U, M, hMzero]
    rw [htarget]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    symm
    have hentry :=
      sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis_entry
        rhoAB rhoA sigma (le_of_lt hepsilon) alpha i j
    rw [hentry]
    simp [U, M, hMzero]
  by_cases hj0 : d j = 0
  · have hMzero : M i j = 0 := by
      simpa [M, U, d] using
        productReference_support_conj_entry_eq_zero_of_left_or_right_zero
          rhoAB rhoA sigma hSupport (i := i) (j := j) (Or.inr hj0)
    have htarget :
        (star (U : CMatrix (Prod a b)) *
          sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
          (U : CMatrix (Prod a b))) i j = 0 := by
      have hentry :=
        sandwichedRenyiReferenceInner_productReference_conj_productEigenbasis_entry
          rhoAB rhoA sigma alpha i j
      rw [hentry]
      simp [U, M, hMzero]
    rw [htarget]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    symm
    have hentry :=
      sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis_entry
        rhoAB rhoA sigma (le_of_lt hepsilon) alpha i j
    rw [hentry]
    simp [U, M, hMzero]
  have hdi_pos : 0 < d i := by
    exact lt_of_le_of_ne (hd_nonneg i) (by
      intro h
      exact hi0 h.symm)
  have hdj_pos : 0 < d j := by
    exact lt_of_le_of_ne (hd_nonneg j) (by
      intro h
      exact hj0 h.symm)
  have hepsilon_tendsto :
      Filter.Tendsto (fun epsilon : Real => epsilon) l (nhds (0 : Real)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlin_i :
      Filter.Tendsto (fun epsilon : Real => depsilon epsilon i) l (nhds (d i)) := by
    have hright :
        Filter.Tendsto
          (fun epsilon : Real => sigma.pos.isHermitian.eigenvalues i.2 + epsilon)
          l (nhds (sigma.pos.isHermitian.eigenvalues i.2 + 0)) :=
      tendsto_const_nhds.add hepsilon_tendsto
    have hmul :=
      (tendsto_const_nhds :
        Filter.Tendsto
          (fun _ : Real => rhoA.pos.isHermitian.eigenvalues i.1)
          l (nhds (rhoA.pos.isHermitian.eigenvalues i.1))).mul hright
    simpa [depsilon, d] using hmul
  have hlin_j :
      Filter.Tendsto (fun epsilon : Real => depsilon epsilon j) l (nhds (d j)) := by
    have hright :
        Filter.Tendsto
          (fun epsilon : Real => sigma.pos.isHermitian.eigenvalues j.2 + epsilon)
          l (nhds (sigma.pos.isHermitian.eigenvalues j.2 + 0)) :=
      tendsto_const_nhds.add hepsilon_tendsto
    have hmul :=
      (tendsto_const_nhds :
        Filter.Tendsto
          (fun _ : Real => rhoA.pos.isHermitian.eigenvalues j.1)
          l (nhds (rhoA.pos.isHermitian.eigenvalues j.1))).mul hright
    simpa [depsilon, d] using hmul
  have hpow_i :
      Filter.Tendsto (fun epsilon : Real => depsilon epsilon i ^ s)
        l (nhds (d i ^ s)) := by
    exact
      (Real.continuousAt_rpow_const (d i) s (Or.inl (ne_of_gt hdi_pos))).tendsto.comp
        hlin_i
  have hpow_j :
      Filter.Tendsto (fun epsilon : Real => depsilon epsilon j ^ s)
        l (nhds (d j ^ s)) := by
    exact
      (Real.continuousAt_rpow_const (d j) s (Or.inl (ne_of_gt hdj_pos))).tendsto.comp
        hlin_j
  have hcpow_i :
      Filter.Tendsto
        (fun epsilon : Real => ((depsilon epsilon i ^ s : Real) : ℂ))
        l (nhds (((d i ^ s : Real) : ℂ))) :=
    Complex.continuous_ofReal.tendsto _ |>.comp hpow_i
  have hcpow_j :
      Filter.Tendsto
        (fun epsilon : Real => ((depsilon epsilon j ^ s : Real) : ℂ))
        l (nhds (((d j ^ s : Real) : ℂ))) :=
    Complex.continuous_ofReal.tendsto _ |>.comp hpow_j
  have hexplicit :
      Filter.Tendsto
        (fun epsilon : Real =>
          ((depsilon epsilon i ^ s : Real) : ℂ) * M i j *
            ((depsilon epsilon j ^ s : Real) : ℂ))
        l
        (nhds (((d i ^ s : Real) : ℂ) * M i j *
          ((d j ^ s : Real) : ℂ))) := by
    exact (hcpow_i.mul tendsto_const_nhds).mul hcpow_j
  have htarget :
      (star (U : CMatrix (Prod a b)) *
          sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
          (U : CMatrix (Prod a b))) i j =
        ((d i ^ s : Real) : ℂ) * M i j * ((d j ^ s : Real) : ℂ) := by
    have hentry :=
      sandwichedRenyiReferenceInner_productReference_conj_productEigenbasis_entry
        rhoAB rhoA sigma alpha i j
    simpa [s, U, M, d] using hentry
  rw [htarget]
  refine hexplicit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  symm
  have hentry :=
    sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis_entry
      rhoAB rhoA sigma (le_of_lt hepsilon) alpha i j
  simpa [s, U, M, depsilon] using hentry

/-- Matrix convergence of the fixed-left side-regularized inner operator in the
product reference eigenbasis. -/
theorem sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis_tendsto
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoA.prod sigma).matrix)
    (alpha : Real) :
    Filter.Tendsto
      (fun epsilon : Real =>
        star (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)) *
          sandwichedRenyiReferenceInner rhoAB
            (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha *
          (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)))
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds
        (star (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)) *
          sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
          (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)))) := by
  change Filter.Tendsto
      (fun epsilon : Real => fun i => fun j =>
        (star (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)) *
          sandwichedRenyiReferenceInner rhoAB
            (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha *
          (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b))) i j)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds
        (fun i => fun j =>
          (star (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b)) *
            sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
            (productReferenceEigenvectorUnitary rhoA sigma : CMatrix (Prod a b))) i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact
    sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis_entry_tendsto
      rhoAB rhoA sigma hSupport alpha i j

/-- Supported fixed-left side regularization converges for the high-parameter
inner operator. -/
theorem sandwichedRenyiReferenceInner_fixedLeftRegularization_tendsto_of_supports
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoA.prod sigma).matrix)
    (alpha : Real) :
    Filter.Tendsto
      (fun epsilon : Real =>
        sandwichedRenyiReferenceInner rhoAB
          (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha)) := by
  classical
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    productReferenceEigenvectorUnitary rhoA sigma
  have hconj :=
    sandwichedRenyiReferenceInner_fixedLeftRegularized_conj_productEigenbasis_tendsto
      rhoAB rhoA sigma hSupport alpha
  have hcont :
      Continuous fun X : CMatrix (Prod a b) =>
        (U : CMatrix (Prod a b)) * X * star (U : CMatrix (Prod a b)) := by
    fun_prop
  have hback :=
    (hcont.tendsto
      (star (U : CMatrix (Prod a b)) *
        sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
        (U : CMatrix (Prod a b)))).comp hconj
  have hUstarU :
      star (U : CMatrix (Prod a b)) * (U : CMatrix (Prod a b)) = 1 := by
    simp
  have hUUstar :
      (U : CMatrix (Prod a b)) * star (U : CMatrix (Prod a b)) = 1 := by
    simp
  change Filter.Tendsto
      (fun epsilon : Real =>
        (U : CMatrix (Prod a b)) *
          (star (U : CMatrix (Prod a b)) *
            sandwichedRenyiReferenceInner rhoAB
              (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha *
            (U : CMatrix (Prod a b))) *
          star (U : CMatrix (Prod a b)))
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds
        ((U : CMatrix (Prod a b)) *
          (star (U : CMatrix (Prod a b)) *
            sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
            (U : CMatrix (Prod a b))) *
          star (U : CMatrix (Prod a b)))) at hback
  have htarget :
      (U : CMatrix (Prod a b)) *
          (star (U : CMatrix (Prod a b)) *
            sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
            (U : CMatrix (Prod a b))) *
          star (U : CMatrix (Prod a b)) =
        sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha := by
    calc
      (U : CMatrix (Prod a b)) *
          (star (U : CMatrix (Prod a b)) *
            sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
            (U : CMatrix (Prod a b))) *
          star (U : CMatrix (Prod a b)) =
          ((U : CMatrix (Prod a b)) * star (U : CMatrix (Prod a b))) *
            sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha *
            ((U : CMatrix (Prod a b)) * star (U : CMatrix (Prod a b))) := by
            noncomm_ring
      _ = sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha := by
            rw [hUUstar]
            simp
  rw [htarget] at hback
  refine hback.congr' ?_
  filter_upwards with epsilon
  calc
    (U : CMatrix (Prod a b)) *
        (star (U : CMatrix (Prod a b)) *
          sandwichedRenyiReferenceInner rhoAB
            (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha *
          (U : CMatrix (Prod a b))) *
        star (U : CMatrix (Prod a b)) =
        ((U : CMatrix (Prod a b)) * star (U : CMatrix (Prod a b))) *
          sandwichedRenyiReferenceInner rhoAB
            (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha *
          ((U : CMatrix (Prod a b)) * star (U : CMatrix (Prod a b))) := by
          noncomm_ring
    _ = sandwichedRenyiReferenceInner rhoAB
          (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha := by
          rw [hUUstar]
          simp

/-- Fixed-left side regularization is positive semidefinite for nonnegative
regularization parameters. -/
theorem fixedLeftReferenceRegularization_posSemidef
    (rhoA : State a) (sigma : State b) {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    (fixedLeftReferenceRegularization rhoA sigma epsilon).PosSemidef := by
  exact rhoA.pos.kronecker
    (sandwichedRenyiReferenceRegularization_posSemidef sigma.pos hepsilon)

/-- The high-parameter raw power trace of the supported fixed-left
side-regularized inner operator converges to the supported product-reference
finite branch. -/
theorem sandwichedRenyiReferenceInner_tracePower_fixedLeftRegularization_tendsto_of_supports
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoA.prod sigma).matrix)
    (alpha : Real) (halpha_pos : 0 < alpha) :
    Filter.Tendsto
      (fun epsilon : Real =>
        ((CFC.rpow
          (sandwichedRenyiReferenceInner rhoAB
            (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha)
          alpha).trace).re)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds
        ((CFC.rpow
          (sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha)
          alpha).trace).re) := by
  have hinner :=
    sandwichedRenyiReferenceInner_fixedLeftRegularization_tendsto_of_supports
      rhoAB rhoA sigma hSupport alpha
  have hinner_psd_event :
      ∀ᶠ epsilon in nhdsWithin (0 : Real) (Set.Ioi 0),
        (sandwichedRenyiReferenceInner rhoAB
          (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact
      sandwichedRenyiReferenceInner_posSemidef rhoAB
        (fixedLeftReferenceRegularization_posSemidef rhoA sigma (le_of_lt hepsilon))
        alpha
  exact
    cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
      halpha_pos hinner hinner_psd_event
      (sandwichedRenyiReferenceInner_posSemidef rhoAB (rhoA.prod sigma).pos alpha)

/-- Input-side fixed-left side-regularization curve for the finite high-parameter
PSD-reference branch. -/
def sandwichedRenyiPSDReferenceHighAlphaFiniteFixedLeftRegularizationCurve
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    (alpha : Real) (epsilon : Real) : Real :=
  if hepsilon : 0 ≤ epsilon then
    sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
      (fixedLeftReferenceRegularization rhoA sigma epsilon)
      (fixedLeftReferenceRegularization_posSemidef rhoA sigma hepsilon) alpha
  else
    sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
      (rhoA.prod sigma).matrix (rhoA.prod sigma).pos alpha

/-- The fixed-left side-regularized high-parameter finite branch converges to
the supported product-reference finite branch. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFiniteFixedLeftRegularizationCurve_tendsto_of_supports
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoA.prod sigma).matrix)
    (alpha : Real) (halpha : 1 < alpha) :
    Filter.Tendsto
      (sandwichedRenyiPSDReferenceHighAlphaFiniteFixedLeftRegularizationCurve
        rhoAB rhoA sigma alpha)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds
        (sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
          (rhoA.prod sigma).matrix (rhoA.prod sigma).pos alpha)) := by
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have htrace :=
    sandwichedRenyiReferenceInner_tracePower_fixedLeftRegularization_tendsto_of_supports
      rhoAB rhoA sigma hSupport alpha halpha_pos
  have htarget_pos :
      0 <
        ((CFC.rpow
          (sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha)
          alpha).trace).re := by
    simpa [psdTracePower] using
      sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
        rhoAB (rhoA.prod sigma).pos hSupport alpha
  have hlog :
      Filter.Tendsto
        (fun epsilon : Real =>
          log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner rhoAB
                (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha)
              alpha).trace).re))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds
          (log2
            (((CFC.rpow
              (sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha)
              alpha).trace).re))) := by
    have hrawLog := Filter.Tendsto.log htrace (ne_of_gt htarget_pos)
    simpa [log2] using
      hrawLog.div tendsto_const_nhds (ne_of_gt (Real.log_pos one_lt_two))
  have hraw :
      Filter.Tendsto
        (fun epsilon : Real =>
          (1 / (alpha - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner rhoAB
                  (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha)
                alpha).trace).re))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds
          ((1 / (alpha - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner rhoAB (rhoA.prod sigma).matrix alpha)
                alpha).trace).re))) :=
    tendsto_const_nhds.mul hlog
  have hcurve :
      (fun epsilon : Real =>
          (1 / (alpha - 1)) *
            log2
              (((CFC.rpow
                (sandwichedRenyiReferenceInner rhoAB
                  (fixedLeftReferenceRegularization rhoA sigma epsilon) alpha)
                alpha).trace).re))
        =ᶠ[nhdsWithin (0 : Real) (Set.Ioi 0)]
      sandwichedRenyiPSDReferenceHighAlphaFiniteFixedLeftRegularizationCurve
        rhoAB rhoA sigma alpha := by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    have hepsilon_nonneg : 0 ≤ epsilon := le_of_lt hepsilon
    simp [sandwichedRenyiPSDReferenceHighAlphaFiniteFixedLeftRegularizationCurve,
      sandwichedRenyiPSDReferenceHighAlphaFinite, psdTracePower, hepsilon_nonneg]
  exact Filter.Tendsto.congr' hcurve hraw

/-- Scaling a supported PSD reference shifts the high-parameter finite branch
by the logarithm of the scaling factor. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference_of_supports
    (rho : State a) {sigma : CMatrix a} (hsigma : sigma.PosSemidef)
    (hSupport : Matrix.Supports rho.matrix sigma)
    {lambda : Real} (hlambda : 0 < lambda)
    (alpha : Real) (halpha : 1 < alpha) :
    sandwichedRenyiPSDReferenceHighAlphaFinite rho
        (lambda • sigma : CMatrix a)
        (Matrix.PosSemidef.smul hsigma (le_of_lt hlambda)) alpha =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha -
        log2 lambda := by
  let s : Real := (1 - alpha) / (2 * alpha)
  have halpha_pos : 0 < alpha := lt_trans zero_lt_one halpha
  have halpha_ne_one : alpha ≠ 1 := ne_of_gt halpha
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
  have htrace_scale :
      psdTracePower
          (sandwichedRenyiReferenceInner rho (lambda • sigma : CMatrix a) alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho
            (Matrix.PosSemidef.smul hsigma hlambda_nonneg) alpha)
          alpha =
        ((lambda ^ s * lambda ^ s) ^ alpha) *
          psdTracePower
            (sandwichedRenyiReferenceInner rho sigma alpha)
            (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
            alpha := by
    simpa [s] using
      sandwichedRenyiReferenceInner_psdTracePower_real_smul_reference
        rho hsigma hlambda_nonneg alpha
  have hfactor :
      (lambda ^ s * lambda ^ s) ^ alpha = lambda ^ (1 - alpha) := by
    have hmul : lambda ^ s * lambda ^ s = lambda ^ (s + s) := by
      rw [Real.rpow_add hlambda]
    calc
      (lambda ^ s * lambda ^ s) ^ alpha = (lambda ^ (s + s)) ^ alpha := by
        rw [hmul]
      _ = lambda ^ ((s + s) * alpha) := by
        rw [← Real.rpow_mul hlambda_nonneg]
      _ = lambda ^ (1 - alpha) := by
        congr 1
        dsimp [s]
        field_simp [ne_of_gt halpha_pos]
        ring_nf
  have hfactor_pos : 0 < lambda ^ (1 - alpha) :=
    Real.rpow_pos_of_pos hlambda _
  have hTpos :
      0 <
        psdTracePower
          (sandwichedRenyiReferenceInner rho sigma alpha)
          (sandwichedRenyiReferenceInner_posSemidef rho hsigma alpha)
          alpha :=
    sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports
      rho hsigma hSupport alpha
  have hlog_factor : log2 (lambda ^ (1 - alpha)) = (1 - alpha) * log2 lambda := by
    unfold log2
    rw [Real.log_rpow hlambda]
    ring
  have hcoef :
      (1 / (alpha - 1)) * ((1 - alpha) * log2 lambda) = -log2 lambda := by
    field_simp [halpha_ne_one]
    ring
  simp only [sandwichedRenyiPSDReferenceHighAlphaFinite]
  rw [htrace_scale, hfactor]
  rw [log2_mul (ne_of_gt hfactor_pos) (ne_of_gt hTpos), hlog_factor]
  rw [mul_add, hcoef]
  ring

/-- The side scaling factor in the canonical full-rank approximation has
vanishing base-two logarithm at the endpoint. -/
theorem log2_one_sub_tendsto_zero :
    Tendsto (fun delta : Real => log2 (1 - delta))
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds 0) := by
  have hcont : ContinuousAt (fun delta : Real => log2 (1 - delta)) 0 := by
    unfold log2
    exact
      ((Real.continuousAt_log (by norm_num : (1 - (0 : Real)) ≠ 0)).comp
        (continuousAt_const.sub continuousAt_id)).div_const _
  simpa [log2, Real.log_one] using hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- The finite high-parameter branch is congruent in the PSD reference matrix. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_congr_reference
    (rho : State a) {sigma tau : CMatrix a}
    (hsigma : sigma.PosSemidef) (htau : tau.PosSemidef)
    (h : sigma = tau) (alpha : Real) :
    sandwichedRenyiPSDReferenceHighAlphaFinite rho sigma hsigma alpha =
      sandwichedRenyiPSDReferenceHighAlphaFinite rho tau htau alpha := by
  cases h
  simp [sandwichedRenyiPSDReferenceHighAlphaFinite]

/-- Fixed-left side regularization is positive definite when the fixed left
state is full-rank and the side regularization parameter is positive. -/
theorem fixedLeftReferenceRegularization_posDef_of_left
    (rhoA : State a) (sigma : State b) (hrhoA : rhoA.matrix.PosDef)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    (fixedLeftReferenceRegularization rhoA sigma epsilon).PosDef := by
  exact hrhoA.kronecker
    (sandwichedRenyiReferenceRegularization_posDef sigma.pos hepsilon)

/-- Fixed-left side regularization converges back to the product reference
matrix as the side regularization parameter tends to zero. -/
theorem fixedLeftReferenceRegularization_tendsto_zero
    (rhoA : State a) (sigma : State b) :
    Tendsto (fun epsilon : Real => fixedLeftReferenceRegularization rhoA sigma epsilon)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (rhoA.prod sigma).matrix) := by
  have hside :
      Tendsto (fun epsilon : Real =>
          sandwichedRenyiReferenceRegularization sigma.matrix epsilon)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds sigma.matrix) :=
    sandwichedRenyiReferenceRegularization_tendsto sigma.matrix
  have hkr :
      Continuous fun M : CMatrix b => Matrix.kronecker rhoA.matrix M := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        continuous_const.mul (continuous_id.matrix_elem x.2 y.2)
  simpa [fixedLeftReferenceRegularization, State.prod_matrix_kronecker] using
    hkr.tendsto sigma.matrix |>.comp hside

/-- Support is preserved when a supported product reference is regularized only
on the right tensor factor. -/
theorem supports_fixedLeftReferenceRegularization_of_supports
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoA.prod sigma).matrix) :
    Matrix.Supports rhoAB.matrix
      (fixedLeftReferenceRegularization rhoA sigma epsilon) := by
  classical
  let M : CMatrix (Prod a b) := (rhoA.prod sigma).matrix
  let N : CMatrix (Prod a b) :=
    Matrix.kronecker rhoA.matrix (((epsilon : Real) : Complex) • (1 : CMatrix b))
  have hfixed_eq :
      fixedLeftReferenceRegularization rhoA sigma epsilon = N + (1 : Real) • M := by
    ext i j
    simp [fixedLeftReferenceRegularization, sandwichedRenyiReferenceRegularization,
      State.prod, M, N, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.add_apply,
      Matrix.smul_apply]
    ring
  have hM : M.PosSemidef := by
    simpa [M] using (rhoA.prod sigma).pos
  have hN : N.PosSemidef := by
    have hepsilonC : (0 : Complex) ≤ ((epsilon : Real) : Complex) := by
      exact_mod_cast hepsilon
    exact rhoA.pos.kronecker
      (Matrix.PosSemidef.smul Matrix.PosSemidef.one hepsilonC)
  have hM_fixed : Matrix.Supports M
      (fixedLeftReferenceRegularization rhoA sigma epsilon) := by
    have hM_sum : Matrix.Supports M (N + (1 : Real) • M) :=
      Matrix.Supports.of_pos_smul_right_add hM hN (by norm_num : (0 : Real) < 1)
    simpa [hfixed_eq] using hM_sum
  exact hSupport.trans hM_fixed

/-- The fixed-left regularization induced by the canonical full-rank side
state parameter converges to the product reference matrix. -/
theorem fixedLeftReferenceRegularization_fullRankParameter_tendsto_zero
    (rhoA : State a) (sigma : State b) :
    Tendsto
      (fun delta : Real =>
        fixedLeftReferenceRegularization rhoA sigma
          (delta / ((1 - delta) * (Fintype.card b : Real))))
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds (rhoA.prod sigma).matrix) := by
  letI : Nonempty b := sigma.nonempty
  exact
    (fixedLeftReferenceRegularization_tendsto_zero rhoA sigma).comp
      (fullRankApproxMaximallyMixedRegularizationParameter_tendsto_zero (a := b))

/-- Canonical side-state full-rank approximation as a scaled fixed-left
reference regularization. -/
theorem fullRankApproxMaximallyMixedProductReference_matrix_eq_smul_fixedLeftReferenceRegularization
    (rhoA : State a) (sigma : State b) {delta : Real}
    (hdelta : delta ∈ Set.Ioo (0 : Real) 1) :
    (rhoA.prod (fullRankApproxMaximallyMixedStatePath sigma delta)).matrix =
      (((1 - delta : Real) : ℂ) •
        fixedLeftReferenceRegularization rhoA sigma
          (delta / ((1 - delta) * (Fintype.card b : Real)))) := by
  rw [State.prod_matrix_kronecker]
  rw [fullRankApproxMaximallyMixedStatePath_matrix_eq_smul_referenceRegularization
    sigma hdelta]
  ext i j
  simp [fixedLeftReferenceRegularization, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul,
    mul_comm, mul_assoc]

/-- Filter form of the canonical side-state full-rank approximation as a
scaled fixed-left reference regularization. -/
theorem fullRankApproxMaximallyMixedProductReference_matrix_eventuallyEq_smul_fixedLeftReferenceRegularization
    (rhoA : State a) (sigma : State b) :
    (fun delta : Real =>
        (rhoA.prod (fullRankApproxMaximallyMixedStatePath sigma delta)).matrix) =ᶠ[
      nhdsWithin (0 : Real) (Set.Ioo 0 1)]
      (fun delta : Real =>
        (((1 - delta : Real) : ℂ) •
          fixedLeftReferenceRegularization rhoA sigma
            (delta / ((1 - delta) * (Fintype.card b : Real))))) := by
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  exact
    fullRankApproxMaximallyMixedProductReference_matrix_eq_smul_fixedLeftReferenceRegularization
      rhoA sigma hdelta

/-- The fixed-left product reference path differs from the scaled base product
reference by tensoring the fixed left state with the scaled noise state. -/
theorem fullRankApproxProductReferencePath_matrix_sub_smul_left
    (rhoA : State a) (sigma mu : State b) {delta : Real}
    (hdelta : delta ∈ Set.Ioo (0 : Real) 1) :
    (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix -
        (((1 - delta : Real) : ℂ) • (rhoA.prod sigma).matrix) =
      Matrix.kronecker rhoA.matrix (((delta : Real) : ℂ) • mu.matrix) := by
  ext i j
  simp [fullRankApproxProductReferencePath, fullRankApproxStatePath,
    fullRankApproxState, regularizedStateMatrix, State.prod,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, hdelta]
  ring

/-- The fixed-left product reference path dominates the scaled base product
reference in Loewner order. -/
theorem smul_left_le_fullRankApproxProductReferencePath_matrix_of_mem
    (rhoA : State a) (sigma mu : State b) {delta : Real}
    (hdelta : delta ∈ Set.Ioo (0 : Real) 1) :
    (((1 - delta : Real) : ℂ) • (rhoA.prod sigma).matrix) ≤
      (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix := by
  rw [Matrix.le_iff]
  rw [fullRankApproxProductReferencePath_matrix_sub_smul_left rhoA sigma mu hdelta]
  have hdeltaC : (0 : ℂ) ≤ ((delta : Real) : ℂ) := by
    exact_mod_cast hdelta.1.le
  exact rhoA.pos.kronecker (Matrix.PosSemidef.smul mu.pos hdeltaC)

/-- Candidate-reference form of the canonical full-rank side-state
approximation lower bound. -/
theorem smul_left_le_fullRankApproxMaximallyMixedCandidateReference_matrix_of_mem
    (rhoA : State a) (sigma : State b) {delta : Real}
    (hdelta : delta ∈ Set.Ioo (0 : Real) 1) :
    (((1 - delta : Real) : ℂ) • (rhoA.prod sigma).matrix) ≤
      (rhoA.prod (fullRankApproxMaximallyMixedStatePath sigma delta)).matrix := by
  letI : Nonempty b := sigma.nonempty
  simpa [fullRankApproxProductReferencePath, fullRankApproxMaximallyMixedStatePath] using
    smul_left_le_fullRankApproxProductReferencePath_matrix_of_mem
      rhoA sigma (maximallyMixed b) hdelta

/-- Support is preserved by the canonical full-rank side-state approximation
of a supported product reference. -/
theorem supports_fullRankApproxMaximallyMixedProductReference_of_supports
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b)
    {delta : Real} (hdelta : delta ∈ Set.Ioo (0 : Real) 1)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoA.prod sigma).matrix) :
    Matrix.Supports rhoAB.matrix
      (rhoA.prod (fullRankApproxMaximallyMixedStatePath sigma delta)).matrix := by
  classical
  letI : Nonempty b := sigma.nonempty
  let M : CMatrix (Prod a b) := (rhoA.prod sigma).matrix
  let N : CMatrix (Prod a b) :=
    Matrix.kronecker rhoA.matrix (((delta : Real) : ℂ) • (maximallyMixed b).matrix)
  have hpath_eq :
      (rhoA.prod (fullRankApproxMaximallyMixedStatePath sigma delta)).matrix =
        N + ((1 - delta : Real) • M) := by
    ext i j
    simp [fullRankApproxMaximallyMixedStatePath, fullRankApproxStatePath,
      fullRankApproxState, regularizedStateMatrix, State.prod, M, N,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.add_apply,
      Matrix.smul_apply, maximallyMixed_matrix, smul_eq_mul, hdelta]
    ring
  have hM : M.PosSemidef := by
    simpa [M] using (rhoA.prod sigma).pos
  have hN : N.PosSemidef := by
    have hdeltaC : (0 : ℂ) ≤ ((delta : Real) : ℂ) := by
      exact_mod_cast hdelta.1.le
    exact rhoA.pos.kronecker
      (Matrix.PosSemidef.smul (maximallyMixed b).pos hdeltaC)
  have hscale : 0 < 1 - delta := sub_pos.mpr hdelta.2
  have hM_path : Matrix.Supports M
      (rhoA.prod (fullRankApproxMaximallyMixedStatePath sigma delta)).matrix := by
    have hM_sum :
        Matrix.Supports M (N + (1 - delta : Real) • M) :=
      Matrix.Supports.of_pos_smul_right_add hM hN hscale
    simpa [hpath_eq] using hM_sum
  exact hSupport.trans hM_path

/-- The finite supported branch converges along the canonical full-rank
side-state approximation path. -/
theorem sandwichedRenyiPSDReferenceHighAlphaFinite_fullRankApproxMaximallyMixedProductReference_tendsto_of_supports
    (rhoAB : State (Prod a b)) (sigmaB : State b)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix)
    (alpha : Real) (halpha : 1 < alpha) :
    Tendsto
      (fun delta : Real =>
        sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
          (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).matrix
          (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).pos
          alpha)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1))
      (nhds
        (sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
          (rhoAB.marginalA.prod sigmaB).matrix
          (rhoAB.marginalA.prod sigmaB).pos alpha)) := by
  classical
  letI : Nonempty b := sigmaB.nonempty
  let eps : Real → Real := fun delta =>
    delta / ((1 - delta) * (Fintype.card b : Real))
  let fixedCurve : Real → Real := fun delta =>
    sandwichedRenyiPSDReferenceHighAlphaFiniteFixedLeftRegularizationCurve
      rhoAB rhoAB.marginalA sigmaB alpha (eps delta)
  let target : Real :=
    sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
      (rhoAB.marginalA.prod sigmaB).matrix
      (rhoAB.marginalA.prod sigmaB).pos alpha
  have hfixed : Tendsto fixedCurve
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds target) := by
    simpa [fixedCurve, eps, target] using
      (sandwichedRenyiPSDReferenceHighAlphaFiniteFixedLeftRegularizationCurve_tendsto_of_supports
        rhoAB rhoAB.marginalA sigmaB hSupport alpha halpha).comp
        (fullRankApproxMaximallyMixedRegularizationParameter_tendsto_zero (a := b))
  have hlog :
      Tendsto (fun delta : Real => log2 (1 - delta))
        (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds 0) :=
    log2_one_sub_tendsto_zero
  have hscaled : Tendsto (fun delta : Real => fixedCurve delta - log2 (1 - delta))
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds target) := by
    simpa using hfixed.sub hlog
  have hpath :
      (fun delta : Real =>
        sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
          (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).matrix
          (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).pos
          alpha) =ᶠ[nhdsWithin (0 : Real) (Set.Ioo 0 1)]
      (fun delta : Real => fixedCurve delta - log2 (1 - delta)) := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    have hscale_pos : 0 < 1 - delta := sub_pos.mpr hdelta.2
    have hcard_pos : 0 < (Fintype.card b : Real) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card b)
    have hden_pos : 0 < (1 - delta) * (Fintype.card b : Real) :=
      mul_pos hscale_pos hcard_pos
    have heps_pos : 0 < eps delta := by
      simp [eps]
      exact div_pos hdelta.1 hden_pos
    have heps_nonneg : 0 ≤ eps delta := le_of_lt heps_pos
    have hfixedSupport :
        Matrix.Supports rhoAB.matrix
          (fixedLeftReferenceRegularization rhoAB.marginalA sigmaB (eps delta)) :=
      supports_fixedLeftReferenceRegularization_of_supports
        rhoAB rhoAB.marginalA sigmaB heps_nonneg hSupport
    have hpath_matrix :
        (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).matrix =
          ((1 - delta : Real) •
            fixedLeftReferenceRegularization rhoAB.marginalA sigmaB (eps delta)) := by
      have hcomplex :=
        fullRankApproxMaximallyMixedProductReference_matrix_eq_smul_fixedLeftReferenceRegularization
          rhoAB.marginalA sigmaB hdelta
      ext i j
      rw [hcomplex]
      simp [eps, Matrix.smul_apply]
    have hscale :
        sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            ((1 - delta : Real) •
              fixedLeftReferenceRegularization rhoAB.marginalA sigmaB (eps delta))
            (Matrix.PosSemidef.smul
              (fixedLeftReferenceRegularization_posSemidef
                rhoAB.marginalA sigmaB heps_nonneg)
              (le_of_lt hscale_pos))
            alpha =
          sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
              (fixedLeftReferenceRegularization rhoAB.marginalA sigmaB (eps delta))
              (fixedLeftReferenceRegularization_posSemidef
                rhoAB.marginalA sigmaB heps_nonneg)
              alpha -
            log2 (1 - delta) :=
      sandwichedRenyiPSDReferenceHighAlphaFinite_real_smul_reference_of_supports
        rhoAB
        (fixedLeftReferenceRegularization_posSemidef rhoAB.marginalA sigmaB heps_nonneg)
        hfixedSupport hscale_pos alpha halpha
    have hcurve_eval :
        fixedCurve delta =
          sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (fixedLeftReferenceRegularization rhoAB.marginalA sigmaB (eps delta))
            (fixedLeftReferenceRegularization_posSemidef
              rhoAB.marginalA sigmaB heps_nonneg)
            alpha := by
      simp [fixedCurve,
        sandwichedRenyiPSDReferenceHighAlphaFiniteFixedLeftRegularizationCurve,
        heps_nonneg]
    calc
      sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
          (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).matrix
          (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).pos
          alpha =
        sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
          ((1 - delta : Real) •
            fixedLeftReferenceRegularization rhoAB.marginalA sigmaB (eps delta))
          (Matrix.PosSemidef.smul
            (fixedLeftReferenceRegularization_posSemidef
              rhoAB.marginalA sigmaB heps_nonneg)
            (le_of_lt hscale_pos))
          alpha := by
            exact
              sandwichedRenyiPSDReferenceHighAlphaFinite_congr_reference
                rhoAB
                (rhoAB.marginalA.prod
                  (fullRankApproxMaximallyMixedStatePath sigmaB delta)).pos
                (Matrix.PosSemidef.smul
                  (fixedLeftReferenceRegularization_posSemidef
                    rhoAB.marginalA sigmaB heps_nonneg)
                  (le_of_lt hscale_pos))
                hpath_matrix
                alpha
      _ =
        sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
          (fixedLeftReferenceRegularization rhoAB.marginalA sigmaB (eps delta))
          (fixedLeftReferenceRegularization_posSemidef
            rhoAB.marginalA sigmaB heps_nonneg)
          alpha - log2 (1 - delta) := hscale
      _ = fixedCurve delta - log2 (1 - delta) := by
        rw [hcurve_eval]
  exact hscaled.congr' hpath.symm

/-- Candidate-level convergence along the canonical full-rank side-state path
follows from finite-branch convergence on the supported domain. -/
theorem sandwichedRenyiMutualInformationCandidateE_fullRankApprox_tendsto_of_highAlphaFinite_tendsto
    (rhoAB : State (Prod a b)) (sigmaB : State b) {alpha : Real}
    (halpha : 1 < alpha)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix)
    (hfinite :
      Tendsto
        (fun delta : Real =>
          sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.marginalA.prod
              (fullRankApproxMaximallyMixedStatePath sigmaB delta)).matrix
            (rhoAB.marginalA.prod
              (fullRankApproxMaximallyMixedStatePath sigmaB delta)).pos
            alpha)
        (nhdsWithin (0 : Real) (Set.Ioo 0 1))
        (nhds
          (sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
            (rhoAB.marginalA.prod sigmaB).matrix
            (rhoAB.marginalA.prod sigmaB).pos alpha))) :
    Tendsto
      (fun delta : Real =>
        rhoAB.sandwichedRenyiMutualInformationCandidateE
          (fullRankApproxMaximallyMixedStatePath sigmaB delta) alpha)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1))
      (nhds (rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)) := by
  have htarget :
      rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
        (sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
          (rhoAB.marginalA.prod sigmaB).matrix
          (rhoAB.marginalA.prod sigmaB).pos alpha : EReal) := by
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rhoAB (rhoAB.marginalA.prod sigmaB).pos alpha hSupport]
  have hpath :
      (fun delta : Real =>
        rhoAB.sandwichedRenyiMutualInformationCandidateE
          (fullRankApproxMaximallyMixedStatePath sigmaB delta) alpha)
        =ᶠ[nhdsWithin (0 : Real) (Set.Ioo 0 1)]
      (fun delta : Real =>
        (sandwichedRenyiPSDReferenceHighAlphaFinite rhoAB
          (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).matrix
          (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).pos
          alpha : EReal)) := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    have hpathSupport :
        Matrix.Supports rhoAB.matrix
          (rhoAB.marginalA.prod
            (fullRankApproxMaximallyMixedStatePath sigmaB delta)).matrix :=
      supports_fullRankApproxMaximallyMixedProductReference_of_supports
        rhoAB rhoAB.marginalA sigmaB hdelta hSupport
    rw [State.sandwichedRenyiMutualInformationCandidateE_eq]
    rw [sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha]
    rw [sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports
      rhoAB
      (rhoAB.marginalA.prod
        (fullRankApproxMaximallyMixedStatePath sigmaB delta)).pos
      alpha hpathSupport]
  simpa [htarget] using (EReal.tendsto_coe.mpr hfinite).congr' hpath.symm

/-- Candidate-level convergence along the canonical full-rank side-state path,
with the finite-branch approximation proved from the supported fixed-left
regularization path. -/
theorem sandwichedRenyiMutualInformationCandidateE_fullRankApprox_tendsto_of_supports
    (rhoAB : State (Prod a b)) (sigmaB : State b) {alpha : Real}
    (halpha : 1 < alpha)
    (hSupport : Matrix.Supports rhoAB.matrix (rhoAB.marginalA.prod sigmaB).matrix) :
    Tendsto
      (fun delta : Real =>
        rhoAB.sandwichedRenyiMutualInformationCandidateE
          (fullRankApproxMaximallyMixedStatePath sigmaB delta) alpha)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1))
      (nhds (rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)) :=
  sandwichedRenyiMutualInformationCandidateE_fullRankApprox_tendsto_of_highAlphaFinite_tendsto
    rhoAB sigmaB halpha hSupport
    (sandwichedRenyiPSDReferenceHighAlphaFinite_fullRankApproxMaximallyMixedProductReference_tendsto_of_supports
      rhoAB sigmaB hSupport alpha halpha)

/-- Full-rank side-state approximation supplies the lower bound needed to
restrict the optimized infimum to full-rank side states. -/
theorem posDef_candidate_approx_of_fullRankApprox
    (rhoAB : State (Prod a b)) {alpha : Real} (halpha : 1 < alpha) :
    ∀ sigmaB : State b,
      (⨅ tauB : {tauB : State b // tauB.matrix.PosDef},
        rhoAB.sandwichedRenyiMutualInformationCandidateE tauB.1 alpha) ≤
          rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB alpha := by
  refine posDef_candidate_approx_of_supported_singular_fullRankApprox_tendsto
    rhoAB halpha ?_
  intro sigmaB hSupport _hsigmaB
  exact
    sandwichedRenyiMutualInformationCandidateE_fullRankApprox_tendsto_of_supports
      rhoAB sigmaB halpha hSupport

/-- For high parameters, optimizing over all side states is equivalent to
optimizing over full-rank side states. -/
theorem sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_highAlpha
    (rhoAB : State (Prod a b)) {alpha : Real} (halpha : 1 < alpha) :
    rhoAB.sandwichedRenyiMutualInformationE alpha =
      ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        rhoAB.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha :=
  sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_of_le_candidate
    rhoAB alpha (posDef_candidate_approx_of_fullRankApprox rhoAB halpha)

/-- Optimized sandwiched-Renyi mutual information is upper semicontinuous on any
locus on which every full-rank side-state candidate is upper semicontinuous.

This is the `hposA`-free lift: the only role of `hposA` in
`..._upperSemicontinuousOn_of_iInf_posDef_candidates` is to localize the
candidate-level USC theorem
`sandwichedRenyiMutualInformationCandidateE_upperSemicontinuousOn_posDefMarginalA`
(USC over the PosDef-left-marginal locus). Feeding candidate-level USC directly
as a hypothesis removes the `hposA` assumption. The full-rank candidate
restriction is supplied unconditionally by
`sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_highAlpha` above, so
the only remaining obstruction to a fully unconditional optimized USC theorem is
candidate-level USC at a singular left marginal; see the bridge-B note in
`.tmp/2026-07-05-task-A2-report.md`. -/
theorem sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_posDef_candidate
    {s : Set (State (Prod a b))} {alpha : Real} (halpha : 1 < alpha)
    (hcandUSC :
      ∀ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
        UpperSemicontinuousOn
          (fun rho : State (Prod a b) =>
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha)
          s) :
    UpperSemicontinuousOn
      (fun rho : State (Prod a b) => rho.sandwichedRenyiMutualInformationE alpha)
      s := by
  have hfullRankInf :
      ∀ rho : State (Prod a b),
        rho.sandwichedRenyiMutualInformationE alpha =
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha :=
    fun rho =>
      sandwichedRenyiMutualInformationE_eq_iInf_posDef_candidates_highAlpha rho halpha
  have hiInf :
      UpperSemicontinuousOn
        (fun rho : State (Prod a b) =>
          ⨅ sigmaB : {sigmaB : State b // sigmaB.matrix.PosDef},
            rho.sandwichedRenyiMutualInformationCandidateE sigmaB.1 alpha)
        s :=
    upperSemicontinuousOn_iInf hcandUSC
  convert hiInf using 1
  ext rho
  exact hfullRankInf rho

/-- Matrix convergence of the product reference path with a fixed left state. -/
theorem fullRankApproxProductReferencePath_matrix_tendsto_zero
    (rhoA : State a) (sigma mu : State b) :
    Tendsto
      (fun delta : Real =>
        (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1))
      (nhds (rhoA.prod sigma).matrix) := by
  have hside :
      Tendsto (fun delta : Real => (fullRankApproxStatePath sigma mu delta).matrix)
        (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma.matrix) :=
    State.continuous_matrix.tendsto sigma |>.comp
      (fullRankApproxStatePath_tendsto_zero sigma mu)
  have hkr :
      Continuous fun M : CMatrix b => Matrix.kronecker rhoA.matrix M := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        continuous_const.mul (continuous_id.matrix_elem x.2 y.2)
  simpa [fullRankApproxProductReferencePath, State.prod] using
    hkr.tendsto sigma.matrix |>.comp hside

/-- State-level convergence of the product reference path with a fixed left
state. -/
theorem fullRankApproxProductReferencePath_tendsto_zero
    (rhoA : State a) (sigma mu : State b) :
    Tendsto (fun delta : Real => fullRankApproxProductReferencePath rhoA sigma mu delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds (rhoA.prod sigma)) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  exact fullRankApproxProductReferencePath_matrix_tendsto_zero rhoA sigma mu

/-- The product reference path with fixed full-rank left state is eventually
full-rank. -/
theorem fullRankApproxProductReferencePath_eventually_posDef_of_left
    (rhoA : State a) (sigma mu : State b)
    (hrhoA : rhoA.matrix.PosDef) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix.PosDef := by
  filter_upwards [fullRankApproxStatePath_eventually_posDef_of_noise sigma mu hmu] with delta hdelta
  simpa [fullRankApproxProductReferencePath] using State.prod_posDef hrhoA hdelta

/-- A fixed-left product reference path eventually supports every fixed input
matrix when both product factors are full-rank along the path. -/
theorem fullRankApproxProductReferencePath_eventually_supports_of_left
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma mu : State b)
    (hrhoA : rhoA.matrix.PosDef) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rhoAB.matrix
        (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix := by
  filter_upwards [
      fullRankApproxProductReferencePath_eventually_posDef_of_left
        rhoA sigma mu hrhoA hmu] with delta hdelta
  exact Matrix.Supports.of_right_posDef rhoAB.matrix
    (fullRankApproxProductReferencePath rhoA sigma mu delta).matrix hdelta

/-- Product reference path obtained by regularizing both marginal reference
states. -/
def fullRankApproxProductReferenceBothPath
    (rhoA muA : State a) (sigma mu : State b) (delta : Real) : State (Prod a b) :=
  (fullRankApproxStatePath rhoA muA delta).prod
    (fullRankApproxStatePath sigma mu delta)

/-- Matrix convergence of the product reference path when both sides are
regularized. -/
theorem fullRankApproxProductReferenceBothPath_matrix_tendsto_zero
    (rhoA muA : State a) (sigma mu : State b) :
    Tendsto
      (fun delta : Real =>
        (fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta).matrix)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1))
      (nhds (rhoA.prod sigma).matrix) := by
  have hleft :
      Tendsto (fun delta : Real => (fullRankApproxStatePath rhoA muA delta).matrix)
        (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds rhoA.matrix) :=
    State.continuous_matrix.tendsto rhoA |>.comp
      (fullRankApproxStatePath_tendsto_zero rhoA muA)
  have hright :
      Tendsto (fun delta : Real => (fullRankApproxStatePath sigma mu delta).matrix)
        (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds sigma.matrix) :=
    State.continuous_matrix.tendsto sigma |>.comp
      (fullRankApproxStatePath_tendsto_zero sigma mu)
  have hpair :
      Tendsto
        (fun delta : Real =>
          ((fullRankApproxStatePath rhoA muA delta).matrix,
            (fullRankApproxStatePath sigma mu delta).matrix))
        (nhdsWithin (0 : Real) (Set.Ioo 0 1))
        (nhds (rhoA.matrix, sigma.matrix)) :=
    hleft.prodMk_nhds hright
  have hkr :
      Continuous fun M : CMatrix a × CMatrix b => Matrix.kronecker M.1 M.2 := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        (continuous_fst.matrix_elem x.1 y.1).mul
          (continuous_snd.matrix_elem x.2 y.2)
  simpa [fullRankApproxProductReferenceBothPath, State.prod] using
    hkr.tendsto (rhoA.matrix, sigma.matrix) |>.comp hpair

/-- State-level convergence of the product reference path when both sides are
regularized. -/
theorem fullRankApproxProductReferenceBothPath_tendsto_zero
    (rhoA muA : State a) (sigma mu : State b) :
    Tendsto (fun delta : Real => fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds (rhoA.prod sigma)) := by
  rw [Filter.tendsto_iff_comap]
  rw [nhds_induced]
  rw [Filter.comap_comap]
  rw [← Filter.tendsto_iff_comap]
  exact fullRankApproxProductReferenceBothPath_matrix_tendsto_zero rhoA muA sigma mu

/-- Regularizing both marginal reference states by full-rank noise makes the
product reference path eventually full-rank. -/
theorem fullRankApproxProductReferenceBothPath_eventually_posDef_of_noise
    (rhoA muA : State a) (sigma mu : State b)
    (hmuA : muA.matrix.PosDef) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta).matrix.PosDef := by
  filter_upwards [
      fullRankApproxStatePath_eventually_posDef_of_noise rhoA muA hmuA,
      fullRankApproxStatePath_eventually_posDef_of_noise sigma mu hmu] with delta hleft hright
  simpa [fullRankApproxProductReferenceBothPath] using State.prod_posDef hleft hright

/-- A product reference path regularized on both factors eventually supports
every fixed input matrix. -/
theorem fullRankApproxProductReferenceBothPath_eventually_supports_of_noise
    (rhoAB : State (Prod a b)) (rhoA muA : State a) (sigma mu : State b)
    (hmuA : muA.matrix.PosDef) (hmu : mu.matrix.PosDef) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rhoAB.matrix
        (fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta).matrix := by
  filter_upwards [
      fullRankApproxProductReferenceBothPath_eventually_posDef_of_noise
        rhoA muA sigma mu hmuA hmu] with delta hdelta
  exact Matrix.Supports.of_right_posDef rhoAB.matrix
    (fullRankApproxProductReferenceBothPath rhoA muA sigma mu delta).matrix hdelta

/-- Canonical product reference path obtained by regularizing both factors
with maximally mixed noise. -/
def fullRankApproxMaximallyMixedProductReferenceBothPath
    (rhoA : State a) (sigma : State b) (delta : Real) : State (Prod a b) :=
  letI : Nonempty a := rhoA.nonempty
  letI : Nonempty b := sigma.nonempty
  fullRankApproxProductReferenceBothPath rhoA (maximallyMixed a) sigma (maximallyMixed b) delta

/-- The canonical product reference path converges back to the target product
state. -/
theorem fullRankApproxMaximallyMixedProductReferenceBothPath_tendsto_zero
    (rhoA : State a) (sigma : State b) :
    Tendsto
      (fun delta : Real =>
        fullRankApproxMaximallyMixedProductReferenceBothPath rhoA sigma delta)
      (nhdsWithin (0 : Real) (Set.Ioo 0 1)) (nhds (rhoA.prod sigma)) := by
  classical
  letI : Nonempty a := rhoA.nonempty
  letI : Nonempty b := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedProductReferenceBothPath] using
    fullRankApproxProductReferenceBothPath_tendsto_zero
      rhoA (maximallyMixed a) sigma (maximallyMixed b)

/-- The canonical product reference path is eventually full-rank. -/
theorem fullRankApproxMaximallyMixedProductReferenceBothPath_eventually_posDef
    (rhoA : State a) (sigma : State b) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      (fullRankApproxMaximallyMixedProductReferenceBothPath rhoA sigma delta).matrix.PosDef := by
  classical
  letI : Nonempty a := rhoA.nonempty
  letI : Nonempty b := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedProductReferenceBothPath] using
    fullRankApproxProductReferenceBothPath_eventually_posDef_of_noise
      rhoA (maximallyMixed a) sigma (maximallyMixed b)
      (maximallyMixed_posDef (a := a)) (maximallyMixed_posDef (a := b))

/-- The canonical product reference path eventually supports every fixed input
state. -/
theorem fullRankApproxMaximallyMixedProductReferenceBothPath_eventually_supports
    (rhoAB : State (Prod a b)) (rhoA : State a) (sigma : State b) :
    ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioo 0 1),
      Matrix.Supports rhoAB.matrix
        (fullRankApproxMaximallyMixedProductReferenceBothPath rhoA sigma delta).matrix := by
  classical
  letI : Nonempty a := rhoA.nonempty
  letI : Nonempty b := sigma.nonempty
  simpa [fullRankApproxMaximallyMixedProductReferenceBothPath] using
    fullRankApproxProductReferenceBothPath_eventually_supports_of_noise
      rhoAB rhoA (maximallyMixed a) sigma (maximallyMixed b)
      (maximallyMixed_posDef (a := a)) (maximallyMixed_posDef (a := b))

/-! ### A2 crux: cutoff-regularized negative-power CFC continuity

The high-`α` candidate `σ^s ρ σ^s` involves a negative reference power
`s = (1 - α) / (2 α) < 0`, which is discontinuous in the matrix argument at any
singular reference. The cancellation mechanism (validated in
`.tmp/2026-07-05-task-A2-report.md`, pass 6 / pass 7) is the `g`-continuity
trick: replace the reference power by a continuous cutoff `f` that agrees with
`(·)^s` on the support of the limiting reference, and bound the off-support
error by a trace term whose vanish is forced by CFC-continuity applied to the
auxiliary function `g(t) = t · (t^s - f t)²` (continuous at `0` precisely
because `2 s + 1 = 1 / α > 0`). The whole assembly needs no eigenvalue
perturbation bound (no Weyl / Davis-Kahan); it composes from
`Filter.Tendsto.cfc_nnreal` plus the committed
`posSemidef_trace_mul_kronecker_le_partialTrace` off-support partial-trace
bound. -/

open scoped NNReal

/-- Cutoff approximating `t^s` (for any real `s`, designed for `s < 0`) as an
`ℝ≥0 → ℝ≥0` function: linear ramp `(γ/2)^(s-1) · t` on `[0, γ/2]`, `t^s` on
`[γ/2, ∞)`. Continuous on every compact interval of `ℝ≥0`; regularizes the
negative-power blow-up at `0` so that `Filter.Tendsto.cfc_nnreal` applies. -/
def rpowCutoff (γ : ℝ≥0) (s : ℝ) : ℝ≥0 → ℝ≥0 := fun t =>
  if t < γ / 2 then (γ / 2) ^ (s - 1) * t
  else t ^ s

/-- `rpowCutoff γ s` is continuous on every compact interval `Icc 0 M` of `ℝ≥0`.
The two pieces (linear ramp on `[0, γ/2]`, `t^s` on `[γ/2, M]`) are individually
continuous and match at the boundary `γ/2`. -/
theorem rpowCutoff_continuousOn_Icc {γ : ℝ≥0} (hγ : 0 < γ) (s : ℝ) (M : ℝ≥0) :
    ContinuousOn (rpowCutoff γ s) (Set.Icc 0 M) := by
  have hγ2_pos : 0 < γ / 2 := by
    have h2pos : (0 : ℝ≥0) < 2 := by norm_num
    exact div_pos hγ h2pos
  have hramp_eq : ∀ t ∈ Set.Icc 0 (γ / 2), rpowCutoff γ s t = (γ / 2) ^ (s - 1) * t := by
    intro t ⟨ht0, ht2⟩
    by_cases h2 : t < γ / 2
    · simp only [rpowCutoff, if_pos h2]
    · simp only [rpowCutoff, if_neg h2]
      have hteq : t = γ / 2 := le_antisymm ht2 (le_of_not_gt h2)
      rw [hteq]
      conv_lhs => rw [show s = (s - 1) + 1 from by linarith]
      rw [NNReal.rpow_add hγ2_pos.ne' (s - 1) 1, NNReal.rpow_one]
  have hrpow_eq : ∀ t ∈ Set.Icc (γ / 2) M, rpowCutoff γ s t = t ^ (s : ℝ) := by
    intro t ⟨ht2, _⟩
    simp only [rpowCutoff, if_neg (not_lt.mpr ht2)]
  have hRamp : ContinuousOn (fun t : ℝ≥0 => (γ / 2) ^ (s - 1) * t) (Set.Icc 0 (γ / 2)) :=
    (continuous_const.mul continuous_id).continuousOn
  have h0_notin : (0 : ℝ≥0) ∉ Set.Icc (γ / 2) M :=
    fun h => absurd h.1 (not_le.mpr hγ2_pos)
  have hRpow : ContinuousOn (fun t : ℝ≥0 => t ^ (s : ℝ)) (Set.Icc (γ / 2) M) :=
    NNReal.continuousOn_rpow_const (Or.inl h0_notin)
  by_cases hM : γ / 2 ≤ M
  · have hUnion : Set.Icc 0 M = Set.Icc 0 (γ / 2) ∪ Set.Icc (γ / 2) M := by
      ext t
      constructor
      · rintro ⟨ht0, htM⟩
        by_cases h2 : t < γ / 2
        · exact Or.inl ⟨ht0, le_of_lt h2⟩
        · exact Or.inr ⟨le_of_not_gt h2, htM⟩
      · rintro (⟨ht0, ht2⟩ | ⟨ht2, htM⟩)
        · exact ⟨ht0, ht2.trans hM⟩
        · exact ⟨hγ2_pos.le.trans ht2, htM⟩
    rw [hUnion]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hRamp.congr hramp_eq
    · exact hRpow.congr hrpow_eq
  · have hsub : Set.Icc 0 M ⊆ Set.Icc 0 (γ / 2) := fun t ht ↦
      ⟨ht.1, ht.2.trans (le_of_not_ge hM)⟩
    exact (hRamp.congr hramp_eq).mono hsub

/-- The off-support half of the `g`-trick: `g(t) = t · (t^s - rpowCutoff γ s t)²`
(`rpowCutoffErr γ s` regularizes the negative-power blow-up of `t^s` at `0` by
multiplying the squared cutoff-error by `t`, which forces the limit `0` whenever
`2 s + 1 > 0`). Used as the second `Filter.Tendsto.cfc_nnreal` input (alongside
`rpowCutoff`), it witnesses `Tr[cfc g A_x] → Tr[cfc g A_0] = 0` for the off-support
half of the inner op-norm convergence. -/
def rpowCutoffErr (γ : ℝ≥0) (s : ℝ) : ℝ≥0 → ℝ≥0 := fun t =>
  t * (t^s - rpowCutoff γ s t)^2

/-- `rpowCutoffErr γ s` is continuous on every compact interval `Icc 0 M` of `ℝ≥0`
(for `2 s + 1 > 0` and `s ≤ 1`). On `[γ/2, M]` the cutoff agrees with `t^s` so the
error vanishes; on `[0, γ/2]` the cutoff ramp `rpowCutoff γ s t = (γ/2)^(s-1) · t`
makes the truncated subtraction exact (`(γ/2)^(s-1) · t ≤ t^s` for `s ≤ 1`), and
the closed form `t^{2s+1} - 2·c·t^{s+2} + c²·t³` (continuous in `t` for `2s+1 > 0`,
`s+2 > 0`, `3 > 0`) witnesses continuity via the `ℝ≥0 ↔ ℝ` coercion. -/
theorem rpowCutoffErr_continuousOn_Icc {γ : ℝ≥0} (hγ : 0 < γ)
    (s : ℝ) (hs_pos : 0 < 2 * s + 1) (hs_le : s ≤ 1) (M : ℝ≥0) :
    ContinuousOn (rpowCutoffErr γ s) (Set.Icc 0 M) := by
  have h2_pos : (0 : ℝ≥0) < 2 := by norm_num
  have hγ2_pos : 0 < γ / 2 := div_pos hγ h2_pos
  have hγ2_ne : γ / 2 ≠ 0 := hγ2_pos.ne'
  have hs_neg_le : s - 1 ≤ 0 := by linarith
  have hsP2_pos : 0 < s + 2 := by linarith
  have h2s1_ne : (2 * s + 1 : ℝ) ≠ 0 := hs_pos.ne'
  have hs2_ne : (s + 2 : ℝ) ≠ 0 := hsP2_pos.ne'
  have h3_ne : (3 : ℝ) ≠ 0 := by norm_num
  have h3_nonneg : (0 : ℝ) ≤ 3 := by norm_num
  -- (1) ramp_eq: rpowCutoff = (γ/2)^(s-1) * t on [0, γ/2]
  have hramp_eq : ∀ t ∈ Set.Icc 0 (γ/2),
      rpowCutoff γ s t = (γ/2)^(s-1) * t := by
    intro t ⟨ht0, ht2⟩
    by_cases h2 : t < γ/2
    · simp only [rpowCutoff, if_pos h2]
    · simp only [rpowCutoff, if_neg h2]
      have hteq : t = γ/2 := le_antisymm ht2 (le_of_not_gt h2)
      rw [hteq]
      conv_lhs => rw [show s = (s - 1) + 1 from by linarith]
      rw [NNReal.rpow_add hγ2_ne (s-1) 1, NNReal.rpow_one]
  -- (2) sub_exact: (γ/2)^(s-1) * t ≤ t^s on [0, γ/2]
  have hsub_exact : ∀ t ∈ Set.Icc 0 (γ/2), (γ/2)^(s-1) * t ≤ t^s := by
    intro t ⟨ht0_le, ht2⟩
    by_cases ht0 : t = 0
    · rw [ht0, mul_zero]
      by_cases hs : s = 0
      · rw [hs, NNReal.rpow_zero]; exact zero_le_one
      · rw [NNReal.zero_rpow hs]
    · have ht_pos : 0 < t := lt_of_le_of_ne ht0_le (Ne.symm ht0)
      have hts : t^s = t^(s-1) * t := by
        conv_lhs => rw [show s = (s - 1) + 1 from by linarith]
        rw [NNReal.rpow_add ht_pos.ne' (s-1) 1, NNReal.rpow_one]
      rw [hts]
      have hle : (γ/2)^(s-1) ≤ t^(s-1) :=
        NNReal.rpow_le_rpow_of_nonpos ht_pos ht2 hs_neg_le
      exact mul_le_mul_of_nonneg_right hle ht_pos.le
  -- (3) err_eq_zero on [γ/2, M]
  have hErr_zero : ∀ t ∈ Set.Icc (γ/2) M, rpowCutoffErr γ s t = 0 := by
    rintro t ⟨ht2, -⟩
    have hcut : rpowCutoff γ s t = t^s := by
      simp only [rpowCutoff, if_neg (not_lt.mpr ht2)]
    simp only [rpowCutoffErr, hcut, tsub_self, pow_two, mul_zero]
  -- (4) Closed form on [0, γ/2]: the cast of the err to ℝ equals a sum of
  -- positive-power rpow terms (continuous at `0`).
  have hClosedForm : ∀ t ∈ Set.Icc 0 (γ/2),
      ((rpowCutoffErr γ s t : ℝ≥0) : ℝ) =
      (t:ℝ)^(2*s+1) - 2 * ((γ/2 : ℝ≥0) : ℝ)^(s-1) * (t:ℝ)^(s+2)
        + (((γ/2 : ℝ≥0) : ℝ)^(s-1))^2 * (t:ℝ)^3 := by
    intro t ht
    rw [rpowCutoffErr, hramp_eq t ht, NNReal.coe_mul, NNReal.coe_pow,
        NNReal.coe_sub (hsub_exact t ht), NNReal.coe_mul, NNReal.coe_rpow,
        NNReal.coe_rpow]
    by_cases ht0 : t = 0
    · -- t = 0 case: both sides equal 0 (positive powers of 0 are 0)
      subst ht0
      simp only [NNReal.coe_zero]
      rw [Real.zero_rpow h2s1_ne, Real.zero_rpow hs2_ne]
      ring
    · -- t > 0 case: expand the square and combine rpow products via Real.rpow_add
      have ht_pos : 0 < (t : ℝ) := by exact mod_cast lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have h_2s1 : (t:ℝ)^(2*s+1) = (t:ℝ)^s * (t:ℝ)^s * (t:ℝ) := by
        rw [show (2*s+1 : ℝ) = s + s + 1 from by ring,
            Real.rpow_add ht_pos, Real.rpow_add ht_pos, Real.rpow_one]
      have h_t2 : (t:ℝ)^(2:ℝ) = (t:ℝ) * (t:ℝ) := by
        rw [show (2:ℝ) = 1 + 1 from by norm_num,
            Real.rpow_add ht_pos, Real.rpow_one]
      have h_s2 : (t:ℝ)^(s+2) = (t:ℝ)^s * ((t:ℝ) * (t:ℝ)) := by
        rw [Real.rpow_add ht_pos, h_t2]
      have h_3 : (t:ℝ)^3 = (t:ℝ) * ((t:ℝ) * (t:ℝ)) := by ring
      rw [h_2s1, h_s2, h_3, sub_sq]
      simp only [pow_two]
      ring
  -- (5) Continuity on [0, γ/2] via the closed form (cast through ℝ).
  have hCont_ramp : ContinuousOn (rpowCutoffErr γ s) (Set.Icc 0 (γ/2)) := by
    have hClosed_cont : ContinuousOn (fun t : ℝ≥0 =>
        ((t : ℝ≥0) : ℝ) ^ (2 * s + 1)
          - 2 * ((γ / 2 : ℝ≥0) : ℝ) ^ (s - 1) * ((t : ℝ≥0) : ℝ) ^ (s + 2)
          + (((γ / 2 : ℝ≥0) : ℝ) ^ (s - 1)) ^ 2 * ((t : ℝ≥0) : ℝ) ^ 3)
        (Set.Icc 0 (γ/2)) := by
      have h_2s1 : Continuous (fun t : ℝ≥0 => ((t : ℝ≥0) : ℝ) ^ (2 * s + 1)) :=
        (Real.continuous_rpow_const hs_pos.le).comp NNReal.continuous_coe
      have h_s2 : Continuous (fun t : ℝ≥0 => ((t : ℝ≥0) : ℝ) ^ (s + 2)) :=
        (Real.continuous_rpow_const hsP2_pos.le).comp NNReal.continuous_coe
      fun_prop
    rw [NNReal.isEmbedding_coe.continuousOn_iff]
    exact hClosed_cont.congr (fun t ht => hClosedForm t ht)
  -- (6) Continuity on [γ/2, M]: err = 0, constant.
  have hCont_rpow : ContinuousOn (rpowCutoffErr γ s) (Set.Icc (γ/2) M) :=
    continuousOn_const.congr (fun t ht => hErr_zero t ht)
  -- (7) Combine via ContinuousOn.union_of_isClosed.
  by_cases hM : γ/2 ≤ M
  · have hUnion : Set.Icc 0 M = Set.Icc 0 (γ/2) ∪ Set.Icc (γ/2) M := by
      ext t
      constructor
      · rintro ⟨ht0, htM⟩
        by_cases h2 : t < γ/2
        · exact Or.inl ⟨ht0, le_of_lt h2⟩
        · exact Or.inr ⟨le_of_not_gt h2, htM⟩
      · rintro (⟨ht0, ht2⟩ | ⟨ht2, htM⟩)
        · exact ⟨ht0, ht2.trans hM⟩
        · exact ⟨hγ2_pos.le.trans ht2, htM⟩
    rw [hUnion]
    exact ContinuousOn.union_of_isClosed hCont_ramp hCont_rpow isClosed_Icc isClosed_Icc
  · have hsub : Set.Icc 0 M ⊆ Set.Icc 0 (γ/2) := fun t ht =>
      ⟨ht.1, ht.2.trans (le_of_not_ge hM)⟩
    exact hCont_ramp.mono hsub

/-- Spectral-gap extraction (Step 2 of the g-trick assembly): a PSD `CMatrix`
with strictly positive real trace has a smallest positive eigenvalue `γ > 0`,
and `γ` lower-bounds every strictly-positive eigenvalue. Used as the cutoff
parameter for `rpowCutoff` / `rpowCutoffErr` in the on-support CFC step. -/
lemma CMatrix.exists_minPositiveEigenvalue
    {a : Type*} [Fintype a] [DecidableEq a]
    {A : CMatrix a} (hA : A.PosSemidef) (htr_pos : 0 < A.trace.re) :
    ∃ (γ : ℝ≥0), 0 < γ ∧
      ∀ i : a, 0 < hA.isHermitian.eigenvalues i →
        (γ : ℝ) ≤ hA.isHermitian.eigenvalues i := by
  set evals : a → ℝ := hA.isHermitian.eigenvalues with hevals
  -- The Finset ℝ of positive eigenvalue values (LinearOrder ℝ for `min'`).
  set posValsFinset : Finset ℝ :=
    ((Finset.univ : Finset a).image evals).filter (fun μ => 0 < μ) with hvf
  -- `posValsFinset` is nonempty: if it were empty, all `evals i = 0`, hence
  -- `A.trace = 0`, contradicting `htr_pos`.
  have hne : posValsFinset.Nonempty := by
    by_contra hne'
    rw [Finset.not_nonempty_iff_eq_empty] at hne'
    have hzero : ∀ i, evals i = 0 := fun i => by
      rcases lt_trichotomy (evals i) 0 with hneg | hzero | hpos
      · exact absurd hneg (not_lt.mpr (hA.eigenvalues_nonneg i))
      · exact hzero
      · exfalso
        have hi_img : evals i ∈ (Finset.univ : Finset a).image evals :=
          Finset.mem_image_of_mem evals (Finset.mem_univ _)
        have hi_in : evals i ∈ posValsFinset :=
          Finset.mem_filter.mpr ⟨hi_img, hpos⟩
        exact absurd hi_in (by rw [hne']; exact Finset.notMem_empty _)
    have htr_sum : A.trace = ∑ i, ((evals i) : ℂ) :=
      hA.isHermitian.trace_eq_sum_eigenvalues
    have hsum_zero : (∑ i, ((evals i) : ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hzero]
      rfl
    have htr_zero : A.trace = 0 := by rw [htr_sum]; exact hsum_zero
    rw [htr_zero, Complex.zero_re] at htr_pos
    exact absurd htr_pos (lt_irrefl _)
  set γReal : ℝ := posValsFinset.min' hne with hγReal_def
  have hγ_pos_real : 0 < γReal :=
    (Finset.mem_filter.mp (Finset.min'_mem _ _)).2
  refine ⟨⟨γReal, le_of_lt hγ_pos_real⟩, hγ_pos_real, ?_⟩
  intro i hi
  have hi_img : evals i ∈ (Finset.univ : Finset a).image evals :=
    Finset.mem_image_of_mem evals (Finset.mem_univ _)
  have hi_in : evals i ∈ posValsFinset :=
    Finset.mem_filter.mpr ⟨hi_img, hi⟩
  exact Finset.min'_le _ _ hi_in

open scoped Matrix.Norms.L2Operator

local instance cMatrixNonUnitalCStarAlgebraForCutoffCFC
    (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (Matrix n n ℂ) := ⟨⟩

local instance cMatrixCStarAlgebraForCutoffCFC
    (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) := ⟨⟩

local instance matrixNormalCFCForCutoffCFC
    (n : Type*) [Fintype n] [DecidableEq n] :
    ContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance matrixNormalIsometricCFCForCutoffCFC
    (n : Type*) [Fintype n] [DecidableEq n] :
    IsometricContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
  IsStarNormal.instIsometricContinuousFunctionalCalculus

/-- `rpowCutoff γ s` is continuous on all of `ℝ≥0` (the per-`M` `Icc 0 M`
continuity from `rpowCutoff_continuousOn_Icc` lifts to `Set.univ` because every
`t : ℝ≥0` lies in the interior of `Icc 0 (t + 1)` relative to `ℝ≥0`). -/
theorem rpowCutoff_continuousOn_univ {γ : ℝ≥0} (hγ : 0 < γ) (s : ℝ) :
    ContinuousOn (rpowCutoff γ s) (Set.univ : Set ℝ≥0) := by
  apply Continuous.continuousOn
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst ht
    have hM_nhds : (Set.Icc 0 1 : Set ℝ≥0) ∈ 𝓝 0 :=
      mem_nhds_iff.mpr ⟨Set.Iio 1,
        fun x hx => Set.mem_Icc.mpr ⟨x.2, le_of_lt hx⟩,
        isOpen_Iio, Set.mem_Iio.mpr (by norm_num : (0 : ℝ≥0) < 1)⟩
    exact (rpowCutoff_continuousOn_Icc hγ s 1).continuousAt hM_nhds
  · have ht_pos : 0 < t := by positivity
    have hM_nhds : (Set.Icc 0 (t + 1) : Set ℝ≥0) ∈ 𝓝 t :=
      mem_nhds_iff.mpr ⟨Set.Ioo 0 (t + 1),
        fun x hx => Set.mem_Icc.mpr ⟨x.2, le_of_lt hx.2⟩,
        isOpen_Ioo, Set.mem_Ioo.mpr ⟨ht_pos, lt_add_one t⟩⟩
    exact (rpowCutoff_continuousOn_Icc hγ s (t + 1)).continuousAt hM_nhds

/-- `rpowCutoffErr γ s` is continuous on all of `ℝ≥0`. -/
theorem rpowCutoffErr_continuousOn_univ {γ : ℝ≥0} (hγ : 0 < γ)
    (s : ℝ) (hs_pos : 0 < 2 * s + 1) (hs_le : s ≤ 1) :
    ContinuousOn (rpowCutoffErr γ s) (Set.univ : Set ℝ≥0) := by
  apply Continuous.continuousOn
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst ht
    have hM_nhds : (Set.Icc 0 1 : Set ℝ≥0) ∈ 𝓝 0 :=
      mem_nhds_iff.mpr ⟨Set.Iio 1,
        fun x hx => Set.mem_Icc.mpr ⟨x.2, le_of_lt hx⟩,
        isOpen_Iio, Set.mem_Iio.mpr (by norm_num : (0 : ℝ≥0) < 1)⟩
    exact (rpowCutoffErr_continuousOn_Icc hγ s hs_pos hs_le 1).continuousAt hM_nhds
  · have ht_pos : 0 < t := by positivity
    have hM_nhds : (Set.Icc 0 (t + 1) : Set ℝ≥0) ∈ 𝓝 t :=
      mem_nhds_iff.mpr ⟨Set.Ioo 0 (t + 1),
        fun x hx => Set.mem_Icc.mpr ⟨x.2, le_of_lt hx.2⟩,
        isOpen_Ioo, Set.mem_Ioo.mpr ⟨ht_pos, lt_add_one t⟩⟩
    exact (rpowCutoffErr_continuousOn_Icc hγ s hs_pos hs_le (t + 1)).continuousAt hM_nhds

/-- Step 3a of the g-trick assembly: `cfc (rpowCutoff γ s) (F x) → cfc (rpowCutoff γ s) A`
along a PSD-convergent filter `F x → A`. This is the on-support half: the cutoff
regularizes the negative-power blow-up of `t^s` near `0`. -/
theorem cMatrix_cfc_rpowCutoff_tendsto_of_tendsto_posSemidef
    {X : Type*} {l : Filter X} {F : X → CMatrix a} {A : CMatrix a}
    {γ : ℝ≥0} {s : ℝ} (hγ : 0 < γ)
    (hF : Filter.Tendsto F l (nhds A))
    (hFpsd : ∀ᶠ x in l, (F x).PosSemidef)
    (hA : A.PosSemidef) :
    Filter.Tendsto (fun x => cfc (rpowCutoff γ s) (F x)) l
      (nhds (cfc (rpowCutoff γ s) A)) := by
  let f : ℝ≥0 → ℝ≥0 := rpowCutoff γ s
  have hcontOn :
      ContinuousOn (fun A : CMatrix a => cfc f A)
        {A : CMatrix a | 0 ≤ A} := by
    exact ContinuousOn.cfc_nnreal_of_mem_nhdsSet
      (A := CMatrix a) (s := Set.univ) (f := f)
      (by simp)
      continuousOn_id
      (by intro x hx; exact hx)
      (rpowCutoff_continuousOn_univ hγ s)
  have hcont := hcontOn.continuousWithinAt
    (by simpa using (Matrix.nonneg_iff_posSemidef.mpr hA))
  have hwithin : Filter.Tendsto F l
      (nhdsWithin A {A : CMatrix a | 0 ≤ A}) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hF, hFpsd.mono fun x hx => by
      simpa using (Matrix.nonneg_iff_posSemidef.mpr hx)⟩
  exact hcont.tendsto.comp hwithin

/-- Step 3b of the g-trick assembly: `Tr[cfc (rpowCutoffErr γ s) (F x)] →
Tr[cfc (rpowCutoffErr γ s) A]` along a PSD-convergent filter. When additionally
`rpowCutoffErr γ s` vanishes on `spectrum ℝ≥0 A`, the limit trace is `0`. -/
theorem cMatrix_cfc_rpowCutoffErr_trace_re_tendsto_of_tendsto_posSemidef
    {X : Type*} {l : Filter X} {F : X → CMatrix a} {A : CMatrix a}
    {γ : ℝ≥0} {s : ℝ} (hγ : 0 < γ) (hs_pos : 0 < 2 * s + 1) (hs_le : s ≤ 1)
    (hF : Filter.Tendsto F l (nhds A))
    (hFpsd : ∀ᶠ x in l, (F x).PosSemidef)
    (hA : A.PosSemidef) :
    Filter.Tendsto (fun x => (cfc (rpowCutoffErr γ s) (F x)).trace.re) l
      (nhds (cfc (rpowCutoffErr γ s) A).trace.re) := by
  let g : ℝ≥0 → ℝ≥0 := rpowCutoffErr γ s
  have hcontOn :
      ContinuousOn (fun A : CMatrix a => cfc g A)
        {A : CMatrix a | 0 ≤ A} := by
    exact ContinuousOn.cfc_nnreal_of_mem_nhdsSet
      (A := CMatrix a) (s := Set.univ) (f := g)
      (by simp)
      continuousOn_id
      (by intro x hx; exact hx)
      (rpowCutoffErr_continuousOn_univ hγ s hs_pos hs_le)
  have hcont := hcontOn.continuousWithinAt
    (by simpa using (Matrix.nonneg_iff_posSemidef.mpr hA))
  have hwithin : Filter.Tendsto F l
      (nhdsWithin A {A : CMatrix a | 0 ≤ A}) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hF, hFpsd.mono fun x hx => by
      simpa using (Matrix.nonneg_iff_posSemidef.mpr hx)⟩
  have hnn : Filter.Tendsto (fun x => cfc g (F x)) l (nhds (cfc g A)) :=
    hcont.tendsto.comp hwithin
  have htraceCont : Continuous fun M : CMatrix a => M.trace :=
    Continuous.matrix_trace continuous_id
  exact (Complex.continuous_re.tendsto _).comp (htraceCont.tendsto _ |>.comp hnn)

/-! ## Step 4: CFC homomorphism identity (bridge to `ℝ`-CFC)

The off-support half of the g-trick needs the algebraic identity
`cfc (rpowCutoffErr γ s) A = A * (A^s - cfc (rpowCutoff γ s) A)²`. The `ℝ≥0`-CFC
has no subtraction, so we bridge to the `ℝ`-CFC (where `cfc_sub` / `cfc_mul` /
`cfc_pow` / `cfc_id'` all hold), decompose via the CFC *-algebra homomorphism, and
bridge back. This closes the last hard sub-lemma of A2. -/

/-- `rpowCutoff γ s t ≤ t ^ s` on all of `ℝ≥0`: the `ℝ≥0`-truncated subtraction in
`rpowCutoffErr γ s t = t * (t^s - rpowCutoff γ s t)²` is therefore exact when cast to
`ℝ` (via `NNReal.coe_sub`). On `[γ/2, ∞)` this is equality (`rpowCutoff = t^s` by
definition); on `[0, γ/2]` it is the `(γ/2)^(s-1) · t ≤ t^s` ramp bound (valid for
`s ≤ 1`, mirroring the per-`Icc` `hsub_exact` of `rpowCutoffErr_continuousOn_Icc`). -/
lemma rpowCutoff_le_rpow {γ : ℝ≥0} (hγ : 0 < γ) (s : ℝ) (hs_le : s ≤ 1) (t : ℝ≥0) :
    rpowCutoff γ s t ≤ t ^ s := by
  have h2_pos : (0 : ℝ≥0) < 2 := by norm_num
  have hγ2_pos : 0 < γ / 2 := div_pos hγ h2_pos
  have hs_neg_le : s - 1 ≤ 0 := by linarith
  by_cases ht2 : t < γ / 2
  · simp only [rpowCutoff, if_pos ht2]
    by_cases ht0 : t = 0
    · subst ht0
      simp only [mul_zero]
        -- goal: `0 ≤ 0 ^ s`, true since `0 ^ s ∈ {0, 1}` and both are `≥ 0`
      by_cases hs : s = 0
      · simp only [hs, NNReal.rpow_zero, zero_le_one]
      · simp only [NNReal.zero_rpow hs, le_rfl]
    · have ht_pos : 0 < t := lt_of_le_of_ne t.2 (Ne.symm ht0)
      have hts : t ^ s = t ^ (s - 1) * t := by
        conv_lhs => rw [show s = (s - 1) + 1 from by linarith]
        rw [NNReal.rpow_add ht_pos.ne' (s - 1) 1, NNReal.rpow_one]
      rw [hts]
      refine mul_le_mul_of_nonneg_right ?_ ht_pos.le
      exact NNReal.rpow_le_rpow_of_nonpos ht_pos (le_of_lt ht2) hs_neg_le
  · have heq : rpowCutoff γ s t = t ^ s := by
      simp only [rpowCutoff, if_neg ht2]
    rw [heq]

/-- `ℝ`-extension of `rpowCutoff γ s` via `Real.toNNReal`: agrees with `rpowCutoff γ s`
on `ℝ≥0` and is constant on `(-∞, 0]`. The `ℝ`-CFC avatar of `rpowCutoff γ s` used in
the CFC *-algebra homomorphism identity (the `ℝ`-CFC has `cfc_sub`; the `ℝ≥0`-CFC
does not). -/
def rpowCutoffReal (γ : ℝ≥0) (s : ℝ) : ℝ → ℝ := fun t =>
  ((rpowCutoff γ s t.toNNReal : ℝ≥0) : ℝ)

/-- The CFC *-algebra homomorphism identity underlying the g-trick: for PSD `A` with
spectral-gap `γ > 0` and `2 * s + 1 > 0`, `s ≤ 1`,
  `cfc (rpowCutoffErr γ s) A = A * (A^s - cfc (rpowCutoff γ s) A)²`
where `A^s = CFC.rpow A s`. This is the algebraic identity converting the off-support
`Tr[cfc (rpowCutoffErr γ s) A_x] → 0` (Step 3b) into `Tr[A_x · E_x²] → 0` for
`E_x := A_x^s - cfc (rpowCutoff γ s) A_x`. Proven by bridging the `ℝ≥0`-CFC to the
`ℝ`-CFC (where `cfc_sub` exists), decomposing via the CFC homomorphism (`cfc_mul`,
`cfc_pow`, `cfc_sub`, `cfc_id'`), and bridging back. -/
lemma cfc_rpowCutoffErr_eq_mul_sq
    {A : CMatrix a} (hA : A.PosSemidef) {γ : ℝ≥0} (hγ : 0 < γ)
    {s : ℝ} (_hs_pos : 0 < 2 * s + 1) (hs_le : s ≤ 1) :
    cfc (rpowCutoffErr γ s) A =
      A * (CFC.rpow A s - cfc (rpowCutoff γ s) A)^2 := by
  have hnnA : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hself : IsSelfAdjoint A := Matrix.IsHermitian.isSelfAdjoint hA.isHermitian
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := hfin.continuousOn f
  -- Bridge the `ℝ≥0`-CFC cutoff to its `ℝ`-CFC avatar `rpowCutoffReal γ s`.
  -- (`rpowCutoffReal γ s` is definitionally the `Real.toNNReal` pullback, so the
  -- `cfc_nnreal_eq_real` equation type-checks against it directly.)
  have hCut_bridge : cfc (rpowCutoff γ s) A = cfc (rpowCutoffReal γ s) A :=
    cfc_nnreal_eq_real _ A (ha := hnnA)
  -- Bridge the `ℝ≥0`-CFC error to its `ℝ`-CFC avatar (the `toNNReal` pullback).
  rw [cfc_nnreal_eq_real _ A (ha := hnnA)]
  -- On `spectrum ℝ A` (⊆ `ℝ≥0` for PSD `A`), the pullback equals the decomposable form.
  have hcongr : (spectrum ℝ A).EqOn
      (fun x ↦ (rpowCutoffErr γ s) x.toNNReal : ℝ → ℝ)
      (fun x : ℝ => x * (x ^ s - rpowCutoffReal γ s x)^2) := by
    intro x hx
    have hxnn : 0 ≤ x := spectrum_nonneg_of_nonneg hnnA hx
    have htnn : ((x.toNNReal : ℝ≥0) : ℝ) = x := Real.coe_toNNReal _ hxnn
    have hsub : rpowCutoff γ s x.toNNReal ≤ x.toNNReal ^ s :=
      rpowCutoff_le_rpow hγ s hs_le _
    simp only [rpowCutoffReal, rpowCutoffErr, NNReal.coe_mul, NNReal.coe_pow,
        NNReal.coe_sub hsub, NNReal.coe_rpow, htnn]
  rw [cfc_congr hcongr]
  -- Decompose via the `ℝ`-CFC *-algebra homomorphism.
  rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => (x^s - rpowCutoffReal γ s x)^2) A
      (hcont _) (hcont _)]
  rw [cfc_id' ℝ A (ha := hself)]
  rw [cfc_pow (fun x : ℝ => x^s - rpowCutoffReal γ s x) 2 A (hcont _) (ha := hself)]
  rw [cfc_sub (fun x : ℝ => x^s) (rpowCutoffReal γ s) A (hcont _) (hcont _)]
  -- Bridge the `ℝ`-CFC pieces back: `cfc (fun x => x^s) A = CFC.rpow A s`,
  -- `cfc (rpowCutoffReal γ s) A = cfc (rpowCutoff γ s) A`.
  rw [← CFC.rpow_eq_cfc_real (a := A) (y := s) (ha := hnnA), ← hCut_bridge]
  simp only [CFC.rpow_eq_pow]

/-- On-spectrum agreement (the linchpin of the on-support convergence): when every
strictly-positive spectral point of PSD `A` is `≥ γ`, the cutoff `rpowCutoff γ s`
agrees with `t^s` on `spectrum ℝ≥0 A` (at `0`: `rpowCutoff γ s 0 = 0 = 0^s` for
`s ≠ 0`; on `[γ, ∞) ⊇ [γ/2, ∞)`: `rpowCutoff γ s t = t^s` by the else-branch). Hence
`cfc (rpowCutoff γ s) A = CFC.rpow A s` — the on-support CFC limit (Step 3a) IS `A^s`. -/
lemma cfc_rpowCutoff_eq_rpow_of_spectralGap
    {A : CMatrix a} (_hA : A.PosSemidef) {γ : ℝ≥0} (hγ : 0 < γ) {s : ℝ} (hs : s ≠ 0)
    (hgap : ∀ μ ∈ spectrum ℝ≥0 A, μ ≠ 0 → γ ≤ μ) :
    cfc (rpowCutoff γ s) A = CFC.rpow A s := by
  have hγ2_pos : (0 : ℝ≥0) < γ / 2 := by positivity
  have h2_pos : (0 : ℝ≥0) < 2 := by norm_num
  have hγ2_lt_γ : γ / 2 < γ := by
    rw [div_lt_iff₀ h2_pos]
    exact lt_mul_of_one_lt_right hγ (by norm_num : (1:ℝ≥0) < 2)
  refine cfc_congr (fun μ hμ => ?_)
  by_cases hμ0 : μ = 0
  · subst hμ0
    simp only [rpowCutoff, if_pos hγ2_pos, mul_zero, NNReal.zero_rpow hs]
  · have hγle : γ ≤ μ := hgap μ hμ hμ0
    by_cases hmg : μ < γ / 2
    · exfalso
      exact lt_irrefl γ ((hγle.trans_lt hmg).trans hγ2_lt_γ)
    · simp only [rpowCutoff, if_neg hmg]

/-- Off-support vanishing: under the same spectral-gap hypothesis, `rpowCutoffErr γ s`
vanishes on `spectrum ℝ≥0 A` (at `0`: `0 * (...)² = 0`; on `[γ, ∞)`: `rpowCutoff = t^s`
so the error is `0`). Hence `cfc (rpowCutoffErr γ s) A = 0`, so the Step-3b limit trace is
`Tr[0].re = 0` — the off-support error trace tends to `0` along `A_x → A`. -/
lemma cfc_rpowCutoffErr_eq_zero_of_spectralGap
    {A : CMatrix a} (_hA : A.PosSemidef) {γ : ℝ≥0} (hγ : 0 < γ) {s : ℝ}
    (hgap : ∀ μ ∈ spectrum ℝ≥0 A, μ ≠ 0 → γ ≤ μ) :
    cfc (rpowCutoffErr γ s) A = 0 := by
  have hγ2_pos : (0 : ℝ≥0) < γ / 2 := by positivity
  have h2_pos : (0 : ℝ≥0) < 2 := by norm_num
  have hγ2_lt_γ : γ / 2 < γ := by
    rw [div_lt_iff₀ h2_pos]
    exact lt_mul_of_one_lt_right hγ (by norm_num : (1:ℝ≥0) < 2)
  have hcongr : (spectrum ℝ≥0 A).EqOn (rpowCutoffErr γ s) (fun _ => (0 : ℝ≥0)) := by
    intro μ hμ
    by_cases hμ0 : μ = 0
    · subst hμ0
      simp only [rpowCutoffErr, rpowCutoff, if_pos hγ2_pos, mul_zero, zero_mul]
    · have hγle : γ ≤ μ := hgap μ hμ hμ0
      by_cases hmg : μ < γ / 2
      · exfalso
        exact lt_irrefl γ ((hγle.trans_lt hmg).trans hγ2_lt_γ)
      · simp only [rpowCutoffErr, rpowCutoff, if_neg hmg, tsub_self, pow_two, mul_zero]
  rw [cfc_congr hcongr]
  show cfc (0 : ℝ≥0 → ℝ≥0) A = 0
  simp only [cfc_zero]

/-- Op-norm bound for a sandwiched Kronecker product: for a state `ρ` on `Prod a b`
and PSD `A` (on `a`), PSD `B` (on `b`),
  `‖ρ.sqrtMatrix * (A ⊗ B) * ρ.sqrtMatrix‖ ≤ B.trace.re * Tr[A · ρ.marginalA.matrix].re`.

The sandwiched product is PSD (a congruence of the PSD Kronecker `A ⊗ B` by
`ρ.sqrtMatrix`), so its op-norm is at most its trace; trace cyclicity reduces
`Tr[ρ.sqrtMatrix · (A⊗B) · ρ.sqrtMatrix]` to `Tr[(A⊗B) · ρ.matrix]`, which
`posSemidef_trace_mul_kronecker_le_partialTrace` bounds by
`B.trace.re * Tr[A · ρ.marginalA.matrix].re`. This is the off-support op-norm
bound core of the singular-marginal USC proof (Step 4b). -/
lemma norm_sqrtMatrix_kronecker_mul_sqrtMatrix_le
    (ρ : State (Prod a b)) {A : CMatrix a} (hA : A.PosSemidef) {B : CMatrix b} (hB : B.PosSemidef) :
    ‖ρ.sqrtMatrix * Matrix.kronecker A B * ρ.sqrtMatrix‖ ≤
      B.trace.re * (A * ρ.marginalA.matrix).trace.re := by
  have hK_psd : (Matrix.kronecker A B).PosSemidef := hA.kronecker hB
  have hpsd : (ρ.sqrtMatrix * Matrix.kronecker A B * ρ.sqrtMatrix).PosSemidef := by
    have h := hK_psd.mul_mul_conjTranspose_same ρ.sqrtMatrix
    rwa [ρ.sqrtMatrix_isHermitian.eq] at h
  have htr : (ρ.sqrtMatrix * Matrix.kronecker A B * ρ.sqrtMatrix).trace =
      (Matrix.kronecker A B * ρ.matrix).trace := by
    rw [Matrix.trace_mul_cycle, ρ.sqrtMatrix_mul_self, Matrix.trace_mul_comm]
  have hone : ‖(1 : CMatrix (Prod a b))‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def]
    simpa using ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := EuclideanSpace ℂ (Prod a b))
  have htrnn : 0 ≤ (ρ.sqrtMatrix * Matrix.kronecker A B * ρ.sqrtMatrix).trace.re :=
    (Matrix.PosSemidef.trace_nonneg hpsd).1
  calc ‖ρ.sqrtMatrix * Matrix.kronecker A B * ρ.sqrtMatrix‖
      ≤ (ρ.sqrtMatrix * Matrix.kronecker A B * ρ.sqrtMatrix).trace.re *
          ‖(1 : CMatrix (Prod a b))‖ :=
        norm_le_trace_re_mul_norm_one_of_posSemidef hpsd
    _ ≤ (ρ.sqrtMatrix * Matrix.kronecker A B * ρ.sqrtMatrix).trace.re * 1 :=
        mul_le_mul_of_nonneg_left hone htrnn
    _ = (Matrix.kronecker A B * ρ.matrix).trace.re := by rw [mul_one, htr]
    _ ≤ B.trace.re * (A * ρ.marginalA.matrix).trace.re :=
        posSemidef_trace_mul_kronecker_le_partialTrace ρ.pos hA hB

/-- The cutoff CFC image `cfc (rpowCutoff γ s) A` of a Hermitian matrix is
Hermitian, since `rpowCutoff γ s : ℝ≥0 → ℝ≥0` is fixed pointwise by `star` (the
`ℝ≥0` `star` is the identity). This is the small Hermitian-witness needed so
that the off-support error `E_x = A_x^s - cfc (rpowCutoff γ s) A_x` is
Hermitian, which in turn makes `E_x²` positive semidefinite. -/
lemma cfc_rpowCutoff_isHermitian
    {A : CMatrix a} (_hA : A.IsHermitian) {γ : ℝ≥0} (s : ℝ) :
    (cfc (rpowCutoff γ s) A).IsHermitian := by
  apply IsSelfAdjoint.isHermitian
  apply isSelfAdjoint_iff.mpr
  rw [← cfc_star]
  exact cfc_congr (fun _ _ => star_trivial _)

/-- Step 4b+5 of the singular-marginal optimized sandwiched-Renyi USC proof (the
g-trick assembly, on-support plus off-support): for a fixed positive-definite
side state `sigmaB`, the reference inner trace-power
`Tr[(sigma_x^s rho_x sigma_x^s)^alpha].re` converges to
`Tr[(sigma^s rho sigma^s)^alpha].re` along `rho_x -> rho` whenever the limit
marginal `A = rho.marginalA.matrix` has spectral gap `gamma > 0` away from zero
on its support.

The proof uses the `T T*` factorization `inner = T T*` with
`T := sigma^s * rho.sqrtMatrix` (Hermitian `sigma^s`, `rho.matrix =
rho.sqrtMatrix^2`), and splits `T_x = T_x^reg + T_x^err` via the cutoff
decomposition `A_x^s = cfc (rpowCutoff gamma s) A_x + E_x`. The on-support piece
`T_x^reg` converges by Step 3a plus `cfc_rpowCutoff_eq_rpow_of_spectralGap` and
Kronecker and `sqrtMatrix` continuity; the off-support piece `T_x^err` is
annihilated in op-norm by `norm_sqrtMatrix_kronecker_mul_sqrtMatrix_le`
together with Step 3b and `cfc_rpowCutoffErr_eq_zero_of_spectralGap`. Step 5
then lifts the matrix tendsto to the trace-power tendsto via
`cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef` (positive `alpha`). -/
theorem sandwichedRenyiReferenceInner_rpow_trace_re_tendsto_of_tendsto_state
    {X : Type*} {l : Filter X} {rhoF : X → State (Prod a b)} {rho : State (Prod a b)}
    (hrhoF : Filter.Tendsto rhoF l (nhds rho))
    {α : ℝ} (halpha : 1 < α) {γ : ℝ≥0} (hγ : 0 < γ)
    (hgap : ∀ μ ∈ spectrum ℝ≥0 rho.marginalA.matrix, μ ≠ 0 → γ ≤ μ)
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef) :
    Filter.Tendsto (fun x =>
      (CFC.rpow (sandwichedRenyiReferenceInner (rhoF x)
        (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) α) α).trace.re) l
      (nhds (CFC.rpow (sandwichedRenyiReferenceInner rho
        (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) α) α).trace.re) := by
  -- (1) Scalar bookkeeping: s = (1-alpha)/(2 alpha) is negative, nonzero, <= 1,
  -- and 2*s + 1 = 1/alpha > 0.
  have hα_pos : 0 < α := lt_trans zero_lt_one halpha
  have h2α_pos : 0 < 2 * α := by linarith
  set s : ℝ := (1 - α) / (2 * α) with hs_def
  have hs_neg : s < 0 := by
    rw [hs_def]; exact div_neg_of_neg_of_pos (by linarith) h2α_pos
  have hs_ne : s ≠ 0 := ne_of_lt hs_neg
  have hs_le : s ≤ 1 := by linarith
  have h2s1_eq : 2 * s + 1 = 1 / α := by
    have h2s_eq : 2 * s = (1 - α) / α := by rw [hs_def]; field_simp
    rw [h2s_eq]; field_simp; ring
  have h2s1_pos : 0 < 2 * s + 1 := by rw [h2s1_eq]; exact one_div_pos.mpr hα_pos
  -- (2) Marginal matrix tendsto + PSD witnesses.
  have hAmarg : Filter.Tendsto (fun x => (rhoF x).marginalA.matrix) l
      (nhds rho.marginalA.matrix) :=
    (State.continuous_matrix.comp State.marginalA_continuous).tendsto rho |>.comp hrhoF
  have hAx_psd : ∀ᶠ x in l, (rhoF x).marginalA.matrix.PosSemidef :=
    Filter.Eventually.of_forall fun x => (rhoF x).marginalA.pos
  have hA0_psd : rho.marginalA.matrix.PosSemidef := rho.marginalA.pos
  -- (3) `sqrtMatrix` tendsto (`sqrtMatrix_tendsto_of_tendsto` is in a downstream
  -- module; re-derive it from `cMatrix_rpow_tendsto_of_tendsto_posSemidef` for `1/2`).
  have hsqrt : Filter.Tendsto (fun x => (rhoF x).sqrtMatrix) l (nhds rho.sqrtMatrix) := by
    have hmatrix : Filter.Tendsto (fun x => (rhoF x).matrix) l (nhds rho.matrix) :=
      State.continuous_matrix.tendsto rho |>.comp hrhoF
    have hpsd : ∀ᶠ x in l, (rhoF x).matrix.PosSemidef :=
      Filter.Eventually.of_forall fun x => (rhoF x).pos
    have hpow :=
      cMatrix_rpow_tendsto_of_tendsto_posSemidef (a := Prod a b) (p := (1 / 2 : ℝ))
        (by norm_num) hmatrix hpsd rho.pos
    simpa [State.sqrtMatrix, psdSqrt, CFC.sqrt_eq_rpow] using hpow
  -- `Bs := CFC.rpow sigmaB.matrix s` (Hermitian, PSD); `sigmaB.matrix` is PSD.
  set Bs : CMatrix b := CFC.rpow sigmaB.matrix s with hBs_def
  have hBs_psd : Bs.PosSemidef := cMatrix_rpow_posSemidef hsigmaB.posSemidef
  have hBs_herm : Bs.IsHermitian := hBs_psd.isHermitian
  -- (4) On-support cutoff tendsto: `Cut_x -> CFC.rpow A s` (Step 3a + linchpin 1).
  have hCut : Filter.Tendsto
      (fun x => cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix) l
      (nhds (CFC.rpow rho.marginalA.matrix s)) := by
    have hstep :=
      cMatrix_cfc_rpowCutoff_tendsto_of_tendsto_posSemidef (s := s) hγ hAmarg hAx_psd hA0_psd
    rw [cfc_rpowCutoff_eq_rpow_of_spectralGap hA0_psd hγ hs_ne hgap] at hstep
    exact hstep
  -- (5) Off-support trace tendsto: `(cfc (rpowCutoffErr gamma s) A_x).trace.re -> 0`
  -- (Step 3b + linchpin 2: `cfc (rpowCutoffErr gamma s) A = 0`).
  have herrTrace : Filter.Tendsto (fun x =>
      (cfc (rpowCutoffErr γ s) (rhoF x).marginalA.matrix).trace.re) l (nhds 0) := by
    have hstep := cMatrix_cfc_rpowCutoffErr_trace_re_tendsto_of_tendsto_posSemidef
      hγ h2s1_pos hs_le hAmarg hAx_psd hA0_psd
    rw [cfc_rpowCutoffErr_eq_zero_of_spectralGap hA0_psd hγ hgap] at hstep
    simpa using hstep
  -- (6) Kronecker continuity in the left factor (right factor `Bs` fixed).
  have hKronCont : Continuous fun M : CMatrix a => Matrix.kronecker M Bs := by
    unfold Matrix.kronecker
    exact _root_.continuous_matrix fun x y => by
      simpa [Matrix.kroneckerMap_apply] using
        (continuous_id.matrix_elem x.1 y.1).mul continuous_const
  -- (7) Off-support op-norm annihilation: with
  -- `E_x := CFC.rpow A_x s - cfc (rpowCutoff gamma s) A_x`,
  -- the off-support product `(E_x ⊗ Bs) * rho_x.sqrtMatrix` tends to `0` in op-norm.
  -- The bound is `‖M_x‖^2 ≤ (Bs*Bs).trace.re * (cfc (rpowCutoffErr gamma s) A_x).trace.re`,
  -- and the RHS tends to `(Bs*Bs).trace.re * 0 = 0`.
  have herrNorm : Filter.Tendsto (fun x =>
      Matrix.kronecker (CFC.rpow (rhoF x).marginalA.matrix s -
        cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix) Bs * (rhoF x).sqrtMatrix) l
      (nhds 0) := by
    -- Per-element squared-norm bound.
    have hSq_bound : ∀ x : X,
        ‖Matrix.kronecker (CFC.rpow (rhoF x).marginalA.matrix s -
          cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix) Bs * (rhoF x).sqrtMatrix‖^2 ≤
          (Bs * Bs).trace.re * (cfc (rpowCutoffErr γ s) (rhoF x).marginalA.matrix).trace.re := by
      intro x
      set Ax : CMatrix a := (rhoF x).marginalA.matrix with hAx_def
      set Cut : CMatrix a := cfc (rpowCutoff γ s) Ax with hCut_def
      set E : CMatrix a := CFC.rpow Ax s - Cut with hE_def
      have hAx_psd : Ax.PosSemidef := (rhoF x).marginalA.pos
      have hAxrpow_herm : (CFC.rpow Ax s).IsHermitian :=
        (cMatrix_rpow_posSemidef hAx_psd).isHermitian
      have hCut_herm : Cut.IsHermitian :=
        cfc_rpowCutoff_isHermitian hAx_psd.isHermitian s
      have hE_herm : E.IsHermitian := hAxrpow_herm.sub hCut_herm
      have hEE_psd : (E * E).PosSemidef := by
        have hhh := Matrix.posSemidef_conjTranspose_mul_self E
        rwa [hE_herm.eq] at hhh
      have hBsBs_psd : (Bs * Bs).PosSemidef := by
        have hhh := Matrix.posSemidef_conjTranspose_mul_self Bs
        rwa [hBs_herm.eq] at hhh
      -- `cfc (rpowCutoffErr γ s) Ax = Ax * (E * E)` (linchpin `cfc_rpowCutoffErr_eq_mul_sq`).
      have hErr : cfc (rpowCutoffErr γ s) Ax = Ax * (E * E) := by
        have hlin := cfc_rpowCutoffErr_eq_mul_sq hAx_psd hγ h2s1_pos hs_le
        rw [← hCut_def, ← hE_def, pow_two] at hlin
        exact hlin
      -- `star M = sqrtMatrix * kronecker E Bs` (Hermitian factors).
      have hstarM : star (Matrix.kronecker E Bs * (rhoF x).sqrtMatrix) =
          (rhoF x).sqrtMatrix * Matrix.kronecker E Bs := by
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
        unfold Matrix.kronecker
        simp only [Matrix.conjTranspose_kronecker, (rhoF x).sqrtMatrix_isHermitian.eq,
          hE_herm.eq, hBs_herm.eq]
      have hKron_mul : Matrix.kronecker E Bs * Matrix.kronecker E Bs =
          Matrix.kronecker (E * E) (Bs * Bs) :=
        (Matrix.mul_kronecker_mul E E Bs Bs).symm
      -- `star M * M = sqrtMatrix * kronecker (E*E) (Bs*Bs) * sqrtMatrix`.
      have hstarMstarM : star (Matrix.kronecker E Bs * (rhoF x).sqrtMatrix) *
          (Matrix.kronecker E Bs * (rhoF x).sqrtMatrix) =
          (rhoF x).sqrtMatrix * Matrix.kronecker (E * E) (Bs * Bs) * (rhoF x).sqrtMatrix := by
        rw [hstarM, ← hKron_mul]
        noncomm_ring
      -- Assemble the squared-norm bound.
      calc ‖Matrix.kronecker E Bs * (rhoF x).sqrtMatrix‖^2
          = ‖star (Matrix.kronecker E Bs * (rhoF x).sqrtMatrix) *
               (Matrix.kronecker E Bs * (rhoF x).sqrtMatrix)‖ := by
            rw [pow_two, ← CStarRing.norm_star_mul_self]
        _ = ‖(rhoF x).sqrtMatrix * Matrix.kronecker (E * E) (Bs * Bs) *
               (rhoF x).sqrtMatrix‖ := by rw [hstarMstarM]
        _ ≤ (Bs * Bs).trace.re * ((E * E) * Ax).trace.re := by
            exact norm_sqrtMatrix_kronecker_mul_sqrtMatrix_le (rhoF x) hEE_psd hBsBs_psd
        _ ≤ (Bs * Bs).trace.re * (cfc (rpowCutoffErr γ s) Ax).trace.re := by
            apply mul_le_mul_of_nonneg_left _ (Matrix.PosSemidef.trace_nonneg hBsBs_psd).1
            rw [Matrix.trace_mul_comm, ← hErr]
    -- Squeeze `‖M_x‖ -> 0` from `‖M_x‖^2 ≤ bound_x` and `bound_x -> 0`.
    set bound : X → ℝ := fun x =>
      (Bs * Bs).trace.re * (cfc (rpowCutoffErr γ s) (rhoF x).marginalA.matrix).trace.re
    have hbound_tendsto : Filter.Tendsto bound l (nhds 0) := by
      have h := Tendsto.mul (tendsto_const_nhds (x := (Bs * Bs).trace.re)) herrTrace
      rwa [mul_zero] at h
    have hSq_tendsto : Filter.Tendsto (fun x =>
        ‖Matrix.kronecker (CFC.rpow (rhoF x).marginalA.matrix s -
          cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix) Bs * (rhoF x).sqrtMatrix‖^2) l
        (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound_tendsto
        (fun _ => pow_nonneg (norm_nonneg _) 2) (fun x => hSq_bound x)
    have hnorm : Filter.Tendsto (fun x =>
        ‖Matrix.kronecker (CFC.rpow (rhoF x).marginalA.matrix s -
          cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix) Bs * (rhoF x).sqrtMatrix‖) l
        (nhds 0) := by
      have h2 : Filter.Tendsto (fun x =>
          Real.sqrt (‖Matrix.kronecker (CFC.rpow (rhoF x).marginalA.matrix s -
            cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix) Bs * (rhoF x).sqrtMatrix‖ ^ 2)) l
          (nhds 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp hSq_tendsto
        rwa [show (nhds (Real.sqrt 0) : Filter ℝ) = nhds 0 from by rw [Real.sqrt_zero]] at h
      refine h2.congr' ?_
      filter_upwards with x
      exact Real.sqrt_sq (norm_nonneg _)
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hnorm)
  -- (8) On-support matrix tendsto: `(Cut_x ⊗ Bs) * sqrtMatrix_x -> (A^s ⊗ Bs) * sqrtMatrix`.
  have hOn : Filter.Tendsto (fun x =>
      Matrix.kronecker (cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix) Bs *
        (rhoF x).sqrtMatrix) l
    (nhds (Matrix.kronecker (CFC.rpow rho.marginalA.matrix s) Bs * rho.sqrtMatrix)) :=
    (hKronCont.tendsto _).comp hCut |>.mul hsqrt
  -- (9) T_x -> T: full matrix T_x = CFC.rpow (kronecker A_x sigmaB.matrix) s * sqrtMatrix_x
  -- tends to T = CFC.rpow (kronecker A sigmaB.matrix) s * rho.sqrtMatrix, via
  -- the kron-rpow identity, decomposing `CFC.rpow A_x s = Cut_x + E_x`, and
  -- `Tendsto.add hOn herrNorm`.
  have hTx : Filter.Tendsto (fun x =>
      CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s *
        (rhoF x).sqrtMatrix) l
    (nhds (CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s *
      rho.sqrtMatrix)) := by
    have hkron_x : ∀ x,
        CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s =
          Matrix.kronecker (CFC.rpow (rhoF x).marginalA.matrix s) Bs := fun x =>
      cMatrix_rpow_kronecker_psd ((rhoF x).marginalA.pos) hsigmaB.posSemidef s
    have hkron_lim :
        CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s =
          Matrix.kronecker (CFC.rpow rho.marginalA.matrix s) Bs :=
      cMatrix_rpow_kronecker_psd rho.marginalA.pos hsigmaB.posSemidef s
    rw [hkron_lim]
    have hTx_kron : Filter.Tendsto (fun x =>
        Matrix.kronecker (CFC.rpow (rhoF x).marginalA.matrix s) Bs *
          (rhoF x).sqrtMatrix) l
      (nhds (Matrix.kronecker (CFC.rpow rho.marginalA.matrix s) Bs * rho.sqrtMatrix)) := by
      have hsum := hOn.add herrNorm
      rw [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards with x
      have hK : (cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix +
          (CFC.rpow (rhoF x).marginalA.matrix s -
            cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix)).kronecker Bs =
          (cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix).kronecker Bs +
          Matrix.kronecker (CFC.rpow (rhoF x).marginalA.matrix s -
            cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix) Bs :=
        Matrix.add_kronecker _ _ _
      have hA : cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix +
          (CFC.rpow (rhoF x).marginalA.matrix s -
            cfc (rpowCutoff γ s) (rhoF x).marginalA.matrix) =
          CFC.rpow (rhoF x).marginalA.matrix s := by
        rw [add_comm, sub_add_cancel]
      rw [← Matrix.add_mul, ← hK, hA]
    refine hTx_kron.congr' ?_
    filter_upwards with x
    rw [hkron_x]
  -- (10) inner_x -> inner: `inner_x = T_x * star T_x` (Hermitian factors, sqrt square).
  have hinner : Filter.Tendsto (fun x =>
      sandwichedRenyiReferenceInner (rhoF x)
        (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) α) l
    (nhds (sandwichedRenyiReferenceInner rho
      (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) α)) := by
    have hCx_herm : ∀ x,
        (CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s).IsHermitian :=
      fun x =>
        (cMatrix_rpow_posSemidef
          (Matrix.PosSemidef.kronecker (rhoF x).marginalA.pos hsigmaB.posSemidef)).isHermitian
    have hC0_herm :
        (CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s).IsHermitian :=
      (cMatrix_rpow_posSemidef
        (Matrix.PosSemidef.kronecker rho.marginalA.pos hsigmaB.posSemidef)).isHermitian
    have hinner_eq : ∀ x,
        sandwichedRenyiReferenceInner (rhoF x)
          (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) α =
        (CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s *
          (rhoF x).sqrtMatrix) *
        star (CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s *
          (rhoF x).sqrtMatrix) := by
      intro x
      show CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s *
            (rhoF x).matrix *
          CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s =
        (CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s *
          (rhoF x).sqrtMatrix) *
        star (CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s *
          (rhoF x).sqrtMatrix)
      rw [show (rhoF x).matrix = (rhoF x).sqrtMatrix * (rhoF x).sqrtMatrix from
        (rhoF x).sqrtMatrix_mul_self.symm]
      have hstar_eq : star
          (CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s *
            (rhoF x).sqrtMatrix) =
          (rhoF x).sqrtMatrix *
            CFC.rpow (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) s := by
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
        simp only [(rhoF x).sqrtMatrix_isHermitian.eq, (hCx_herm x).eq]
      rw [hstar_eq]
      noncomm_ring
    have hinner_eq_lim :
        sandwichedRenyiReferenceInner rho
          (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) α =
        (CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s *
          rho.sqrtMatrix) *
        star (CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s *
          rho.sqrtMatrix) := by
      show CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s *
            rho.matrix *
          CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s =
        (CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s *
          rho.sqrtMatrix) *
        star (CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s *
          rho.sqrtMatrix)
      rw [show rho.matrix = rho.sqrtMatrix * rho.sqrtMatrix from
        rho.sqrtMatrix_mul_self.symm]
      have hstar_eq : star
          (CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s *
            rho.sqrtMatrix) =
          rho.sqrtMatrix *
            CFC.rpow (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) s := by
        rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
        simp only [rho.sqrtMatrix_isHermitian.eq, hC0_herm.eq]
      rw [hstar_eq]
      noncomm_ring
    rw [hinner_eq_lim]
    refine (hTx.mul hTx.star).congr' ?_
    filter_upwards with x
    exact (hinner_eq x).symm
  -- (11) Trace-tendsto conclusion: lift `hinner` to the trace-power via the
  -- Schatten PSD trace-power continuity at positive `alpha`.
  have hinner_psd : ∀ᶠ x in l,
      (sandwichedRenyiReferenceInner (rhoF x)
        (Matrix.kronecker (rhoF x).marginalA.matrix sigmaB.matrix) α).PosSemidef :=
    Filter.Eventually.of_forall fun x =>
      sandwichedRenyiReferenceInner_posSemidef (rhoF x)
        (Matrix.PosSemidef.kronecker (rhoF x).marginalA.pos hsigmaB.posSemidef) α
  have hinner_lim_psd :
      (sandwichedRenyiReferenceInner rho
        (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) α).PosSemidef :=
    sandwichedRenyiReferenceInner_posSemidef rho
      (Matrix.PosSemidef.kronecker rho.marginalA.pos hsigmaB.posSemidef) α
  exact cMatrix_rpow_trace_re_tendsto_of_tendsto_posSemidef
    hα_pos hinner hinner_psd hinner_lim_psd

/-- Local copy of `Matrix.Supports.kronecker_right_of_posDef` (which lives in
the downstream `EntanglementAssistedSandwichedAdditivity` module and so cannot
be imported here): a positive-definite right tensor factor can be substituted
into the right-hand side of support domination without losing the support
relation. -/
private lemma supports_kronecker_right_of_posDef_local
    {a : Type*} [Fintype a] [DecidableEq a]
    {b : Type*} [Fintype b] [DecidableEq b]
    (A : CMatrix a) (B C : CMatrix b) (hC : C.PosDef) :
    Matrix.Supports (Matrix.kronecker A B) (Matrix.kronecker A C) := by
  let L : CMatrix (Prod a b) := Matrix.kronecker (1 : CMatrix a) (B * C⁻¹)
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have hleft : C⁻¹ * C = (1 : CMatrix b) := Matrix.nonsing_inv_mul C hCdet
  have hfactor : Matrix.kronecker A B = L * Matrix.kronecker A C := by
    calc Matrix.kronecker A B =
        Matrix.kronecker (A * (1 : CMatrix a)) (B * (1 : CMatrix b)) := by simp
      _ = Matrix.kronecker (A * (1 : CMatrix a)) (B * (C⁻¹ * C)) := by rw [hleft]
      _ = Matrix.kronecker ((1 : CMatrix a) * A) ((B * C⁻¹) * C) := by
        simp [Matrix.mul_assoc]
      _ = L * Matrix.kronecker A C := by
        simpa [L, Matrix.kronecker] using
          (Matrix.mul_kronecker_mul (1 : CMatrix a) A (B * C⁻¹) C)
  intro v hv
  calc Matrix.mulVec (Matrix.kronecker A B) v
      = Matrix.mulVec (L * Matrix.kronecker A C) v := by rw [hfactor]
    _ = Matrix.mulVec L (Matrix.mulVec (Matrix.kronecker A C) v) := by
        rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hv]; simp

lemma CMatrix.exists_minPositiveSpectralValue
    {a : Type*} [Fintype a] [DecidableEq a]
    {A : CMatrix a} (hA : A.PosSemidef) (htr_pos : 0 < A.trace.re) :
    ∃ (γ : ℝ≥0), 0 < γ ∧
      ∀ μ ∈ spectrum ℝ≥0 A, μ ≠ 0 → γ ≤ μ := by
  rcases CMatrix.exists_minPositiveEigenvalue hA htr_pos with ⟨γ, hγ_pos, hgap_eig⟩
  refine ⟨γ, hγ_pos, ?_⟩
  intro μ hμ_spec hμ_ne
  have hA_nnneg : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hμ_real_spec : (μ : ℝ) ∈ spectrum ℝ A :=
    (coe_mem_spectrum_real_of_nonneg (a := A) hA_nnneg).mpr hμ_spec
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hμ_real_spec
  obtain ⟨i, hi⟩ := hμ_real_spec
  have hi_pos : 0 < hA.isHermitian.eigenvalues i := by
    refine lt_of_le_of_ne (hA.eigenvalues_nonneg i) ?_
    intro hzero
    apply hμ_ne
    have hμ_coe_zero : (μ : ℝ) = 0 := by rw [← hi, hzero]
    exact NNReal.coe_eq_zero.mp hμ_coe_zero
  have hγle_eig : (γ : ℝ) ≤ hA.isHermitian.eigenvalues i := hgap_eig i hi_pos
  have hγle_mu_coe : (γ : ℝ) ≤ (μ : ℝ) := by rw [← hi]; exact hγle_eig
  exact NNReal.coe_le_coe.mp hγle_mu_coe

/-- Step 6 (singular-marginal candidate USC, faithful KW route): for a fixed
positive-definite side state `sigmaB`, the
`sandwichedRenyiMutualInformationCandidateE sigmaB alpha` curve is upper
semicontinuous on `Set.univ` for `1 < alpha`.

At every bipartite state `rho`, the left marginal `rho.marginalA.matrix`
carries a strictly positive `ℝ≥0`-spectral gap `gamma`
(`CMatrix.exists_minPositiveSpectralValue`), so the Step 4b+5 reference-trace
tendsto `sandwichedRenyiReferenceInner_rpow_trace_re_tendsto_of_tendsto_state`
fires along any `rhoF -> rho`. The KW support convention
`Matrix.Supports rho.matrix (rho.marginalA.prod sigmaB).matrix` holds at every
state because the right tensor factor `sigmaB.matrix` is positive definite,
discharging it via `Matrix.Supports.kronecker_right_of_posDef` on top of
`State.matrix_supports_prod_marginals`; this pins the high-`alpha` PSD-reference
candidate at every state to its finite power-trace branch
(`sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports`). Composing the
trace-power tendsto with `log2` (continuous at the strictly positive limit
trace, by `sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports`) and the
scalar `1/(alpha-1)` gives `ContinuousAt` at `rho`; pointwise continuity on
`Set.univ` is upper semicontinuity. The full-rank-left-marginal restriction of
`..._upperSemicontinuousOn_posDefMarginalA` is thereby removed; faithful to KW
(cited `ψ`-continuity, no `alpha`-dependent unit-ball shortcut, no `hposA`). -/
theorem sandwichedRenyiMutualInformationCandidateE_upperSemicontinuousOn
    (sigmaB : State b) (hsigmaB : sigmaB.matrix.PosDef)
    {alpha : Real} (halpha : 1 < alpha) :
    UpperSemicontinuousOn
      (fun rho : State (Prod a b) =>
        rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
      Set.univ := by
  intro rho _hrho
  -- (1) Spectral gap `gamma` of `rho.marginalA.matrix` (free at any state).
  have hmargA_trace_pos : 0 < rho.marginalA.matrix.trace.re := by
    have htr := rho.marginalA.trace_eq_one
    rw [htr]; exact zero_lt_one
  obtain ⟨γ, hγ_pos, hgap⟩ :=
    CMatrix.exists_minPositiveSpectralValue rho.marginalA.pos hmargA_trace_pos
  -- (2) The KW support convention holds at every state (`sigmaB` is full rank).
  have hsupports : ∀ (rho' : State (Prod a b)),
      Matrix.Supports rho'.matrix (rho'.marginalA.prod sigmaB).matrix := by
    intro rho'
    rw [State.prod_matrix_kronecker]
    exact Matrix.Supports.trans rho'.matrix_supports_prod_marginals
      (supports_kronecker_right_of_posDef_local
        rho'.marginalA.matrix rho'.marginalB.matrix sigmaB.matrix hsigmaB)
  have hα_pos : 0 < alpha := lt_trans zero_lt_one halpha
  -- (3) Step 4b+5 trace-power tendsto along the identity filter `nhds rho`.
  have htpow :
      Filter.Tendsto (fun rho' =>
        (CFC.rpow (sandwichedRenyiReferenceInner rho'
          (Matrix.kronecker rho'.marginalA.matrix sigmaB.matrix) alpha) alpha).trace.re)
        (nhds rho)
        (nhds (CFC.rpow (sandwichedRenyiReferenceInner rho
          (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) alpha) alpha).trace.re) :=
    sandwichedRenyiReferenceInner_rpow_trace_re_tendsto_of_tendsto_state
      (rhoF := fun rho' : State (Prod a b) => rho') tendsto_id halpha hγ_pos hgap
      sigmaB hsigmaB
  -- (4) Limit trace positivity (supports holds at `rho`).
  have hkr_psd : (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix).PosSemidef :=
    Matrix.PosSemidef.kronecker rho.marginalA.pos hsigmaB.posSemidef
  have htpow_pos :
      0 < (CFC.rpow (sandwichedRenyiReferenceInner rho
        (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) alpha) alpha).trace.re := by
    have := sandwichedRenyiReferenceInner_psdTracePower_pos_of_supports rho
      hkr_psd (hsupports rho) alpha
    exact this
  -- (5) Compose with `log2` (continuous at the strictly positive limit trace).
  have hlog2_cont : ContinuousAt (fun y : ℝ => log2 y)
      (CFC.rpow (sandwichedRenyiReferenceInner rho
        (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) alpha) alpha).trace.re := by
    unfold log2
    refine ContinuousAt.div ?_ continuousAt_const ?_
    · exact Real.continuousAt_log htpow_pos.ne'
    · exact (Real.log_pos one_lt_two).ne'
  have hlog2_tendsto :
      Filter.Tendsto (fun rho' =>
        log2 ((CFC.rpow (sandwichedRenyiReferenceInner rho'
          (Matrix.kronecker rho'.marginalA.matrix sigmaB.matrix) alpha) alpha).trace.re))
        (nhds rho)
        (nhds (log2 ((CFC.rpow (sandwichedRenyiReferenceInner rho
          (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) alpha) alpha).trace.re))) :=
    hlog2_cont.tendsto.comp htpow
  -- (6) Scalar multiplication by `1/(alpha-1)` is continuous.
  have hmul_tendsto :
      Filter.Tendsto (fun rho' =>
        (1 / (alpha - 1)) *
          log2 ((CFC.rpow (sandwichedRenyiReferenceInner rho'
            (Matrix.kronecker rho'.marginalA.matrix sigmaB.matrix) alpha) alpha).trace.re))
        (nhds rho)
        (nhds ((1 / (alpha - 1)) *
          log2 ((CFC.rpow (sandwichedRenyiReferenceInner rho
            (Matrix.kronecker rho.marginalA.matrix sigmaB.matrix) alpha) alpha).trace.re))) :=
    (continuous_const_mul _).tendsto _ |>.comp hlog2_tendsto
  -- (7) Real-valued finite-branch tendsto: unfold the finite definition to the
  -- scalar-`log2` form and discharge with `hmul_tendsto`.
  have hfinite_real_tendsto :
      Filter.Tendsto (fun rho' =>
        sandwichedRenyiPSDReferenceHighAlphaFinite rho'
          (rho'.marginalA.prod sigmaB).matrix (rho'.marginalA.prod sigmaB).pos alpha)
        (nhds rho)
        (nhds (sandwichedRenyiPSDReferenceHighAlphaFinite rho
          (rho.marginalA.prod sigmaB).matrix (rho.marginalA.prod sigmaB).pos alpha)) := by
    simp only [sandwichedRenyiPSDReferenceHighAlphaFinite, State.prod_matrix_kronecker,
      psdTracePower_eq]
    exact hmul_tendsto
  -- (8) The candidate equals the coe of the real finite branch at every state
  -- (high-`alpha` branch, supports holds everywhere via `sigmaB` full rank).
  have hcand_eq_finE : ∀ (rho' : State (Prod a b)),
      rho'.sandwichedRenyiMutualInformationCandidateE sigmaB alpha =
        (sandwichedRenyiPSDReferenceHighAlphaFinite rho'
          (rho'.marginalA.prod sigmaB).matrix (rho'.marginalA.prod sigmaB).pos alpha : EReal) := by
    intro rho'
    rw [sandwichedRenyiMutualInformationCandidateE_eq,
      sandwichedRenyiPSDReferenceE_eq_highAlphaE_of_one_lt _ _ halpha,
      sandwichedRenyiPSDReferenceHighAlphaE_eq_coe_of_supports _ _ _ (hsupports rho')]
  -- (9) Assemble candidate tendsto via EReal coe and congruence.
  have hfiniteE_tendsto :
      Filter.Tendsto (fun rho' =>
        (sandwichedRenyiPSDReferenceHighAlphaFinite rho'
          (rho'.marginalA.prod sigmaB).matrix (rho'.marginalA.prod sigmaB).pos alpha : EReal))
        (nhds rho)
        (nhds (sandwichedRenyiPSDReferenceHighAlphaFinite rho
          (rho.marginalA.prod sigmaB).matrix (rho.marginalA.prod sigmaB).pos alpha : EReal)) :=
    EReal.tendsto_coe.mpr hfinite_real_tendsto
  have hcand_tendsto :
      Filter.Tendsto
        (fun rho' : State (Prod a b) =>
          rho'.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
        (nhds rho)
        (nhds (rho.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)) := by
    have h := hfiniteE_tendsto.congr'
      (Filter.Eventually.of_forall fun rho' => (hcand_eq_finE rho').symm)
    rwa [← hcand_eq_finE] at h
  -- (10) `ContinuousAt` at `rho` implies USC-within at `rho`.
  have hcontAt :
      ContinuousAt
        (fun rho' : State (Prod a b) =>
          rho'.sandwichedRenyiMutualInformationCandidateE sigmaB alpha)
        rho := hcand_tendsto
  exact hcontAt.continuousWithinAt.upperSemicontinuousWithinAt

/-- Step 7 (deliverable, closes Bridge B): the optimized state sandwiched-Renyi
mutual information `I~_alpha(A;B)_rho = inf_sigmaB D~_alpha(rho_AB || rho_A ⊗
sigma_B)` is upper semicontinuous on every locus for `1 < alpha`.

Composes the candidate USC of Step 6 with the `hposA`-free lift
`sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_posDef_candidate`
(the infimum of upper semicontinuous functions is upper semicontinuous); the
unconditional candidate USC at `Set.univ` from Step 6 supplies USC at every
subset via `UpperSemicontinuousOn.mono`. Faithful to KW (no `hposA`, no
`alpha`-dependent unit-ball shortcut). -/
theorem sandwichedRenyiMutualInformationE_upperSemicontinuousOn
    {s : Set (State (Prod a b))} {alpha : Real} (halpha : 1 < alpha) :
    UpperSemicontinuousOn
      (fun rho : State (Prod a b) => rho.sandwichedRenyiMutualInformationE alpha)
      s := by
  exact sandwichedRenyiMutualInformationE_upperSemicontinuousOn_of_posDef_candidate
    halpha fun sigmaB_hpd =>
      (sandwichedRenyiMutualInformationCandidateE_upperSemicontinuousOn
        sigmaB_hpd.1 sigmaB_hpd.2 halpha).mono (Set.subset_univ _)

end State

end

end QIT
